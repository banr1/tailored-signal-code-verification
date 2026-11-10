/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import ToMathlib.MeasureTheory.Measure.Bool
import ProofLib.Lemmas
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

/-!
# Epoch-cap reachability invariant and `qep` clamping for `gameRTrackHalted`

**Checked by Lean.**

Proves that `q` queries to `gameRTrackHalted` on `sessionSchemeFixedSpk` advance epochs by at most
`q` (`SmEpochBounded`), so `gameRTrackHalted` is distributionally invariant under clamping `qep` to
`min qep (q + 4)`.
-/

namespace Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp

open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (GhostState Params SessionState SignalMessage ShaCompress)
open CryptoGames.SM (Adversary ConfigR GameState MakesAtMostQueries Pos RecvResult
  corrR deliverR inWindow initState injectR spec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes SampledSessionKey liftStateT sessionSchemeFixedSpk)

/-- Upper bound `k` on SM game-state epochs and `GhostState` ratchet epochs. -/
structure SmEpochBounded {PQ Msg C : Type} (k : ℕ)
    (gs : GameState (GhostState PQ) Msg C) : Prop where
  gs_epoch_le : ∀ P : Party, gs.epoch P ≤ k
  st_epoch_le : ∀ P : Party, (gs.st P).epoch ≤ k
  chains_le : ∀ P : Party, ∀ e ∈ (gs.st P).chainEpochs, e ≤ (gs.st P).epoch
  trans_epoch_le : ∀ r ∈ gs.trans, r.pos.epoch ≤ k

theorem SmEpochBounded.mono {PQ Msg C : Type} {k k' : ℕ}
    {gs : GameState (GhostState PQ) Msg C}
    (h : SmEpochBounded k gs) (hle : k ≤ k') : SmEpochBounded k' gs where
  gs_epoch_le P := (h.gs_epoch_le P).trans hle
  st_epoch_le P := (h.st_epoch_le P).trans hle
  chains_le := h.chains_le
  trans_epoch_le r hr := (h.trans_epoch_le r hr).trans hle

theorem smEpochBounded_initState_fixedSpk {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) (s : BitVec 256) (key : SampledSessionKey) (b : Bool) :
    SmEpochBounded 0 (initState (sessionSchemeFixedSpk P ℓ s).sendPart key b) where
  gs_epoch_le _ := Nat.le_refl 0
  st_epoch_le Q := by
    cases Q
    · dsimp [initState, SMSchemeR.sendPart, sessionSchemeFixedSpk, Params.initA]
      split <;> exact Nat.le_refl 0
    · dsimp [initState, SMSchemeR.sendPart, sessionSchemeFixedSpk, Params.initB]
      exact Nat.le_refl 0
  chains_le Q e he := by
    cases Q
    · dsimp [initState, SMSchemeR.sendPart, sessionSchemeFixedSpk, Params.initA] at he ⊢
      split at he <;> simp_all
    · dsimp [initState, SMSchemeR.sendPart, sessionSchemeFixedSpk, Params.initB] at he
      nomatch he
  trans_epoch_le _ hr := nomatch hr

theorem epMgmt_eq_of_epoch_lt {St Msg C : Type}
    (gs : GameState St Msg C) (Δ qep₁ qep₂ : ℕ) (P : Party) (bad : Bool)
    (h₁ : gs.epoch P + 1 ≤ qep₁) (h₂ : gs.epoch P + 1 ≤ qep₂) :
    gs.epMgmt Δ qep₁ P bad = gs.epMgmt Δ qep₂ P bad := by
  unfold GameState.epMgmt
  have hn₁ : ¬ (qep₁ < gs.epoch P + 1) := by omega
  have hn₂ : ¬ (qep₂ < gs.epoch P + 1) := by omega
  have hn₁' : ¬ (qep₁ < gs.epoch P) := by omega
  have hn₂' : ¬ (qep₂ < gs.epoch P) := by omega
  simp only [hn₁, hn₂, hn₁', hn₂', ↓reduceIte]

theorem fixedSpk_send_epoch_le {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) (s : BitVec 256)
    (g : GhostState PQ) (m : Plain ℓ) (r : PQC)
    (hch : ∀ e ∈ g.chainEpochs, e ≤ g.epoch) :
    let out := (sessionSchemeFixedSpk P ℓ s).send g m r
    out.1.epoch ≤ g.epoch + 1 ∧ ∀ e ∈ out.1.chainEpochs, e ≤ out.1.epoch := by
  dsimp only [sessionSchemeFixedSpk, Params.send]
  split
  · refine ⟨by split <;> dsimp only <;> omega,
      fun e he => (hch e he).trans (by split <;> dsimp only <;> omega)⟩
  · exact ⟨Nat.le_succ g.epoch, hch⟩

theorem fixedSpk_receive_epoch_le {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) (s : BitVec 256)
    (g : GhostState PQ) (c : Bytes) (rc : BitVec 256)
    {st' : GhostState PQ} {t' i' : ℕ} {m' : Plain ℓ}
    (hch : ∀ e ∈ g.chainEpochs, e ≤ g.epoch)
    (hrecv : (sessionSchemeFixedSpk P ℓ s).receive g c rc = some (st', t', i', m')) :
    t' ≤ g.epoch + 1 ∧ st'.epoch ≤ g.epoch + 1 ∧ ∀ e ∈ st'.chainEpochs, e ≤ st'.epoch := by
  dsimp only [sessionSchemeFixedSpk, Params.receive] at hrecv
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp [htry] at hrecv
  | ok msg =>
    rw [htry] at hrecv
    dsimp only at hrecv
    rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
        rc g.session with ⟨errOrPlain, sess⟩
    cases errOrPlain with
    | error _ => simp [hdec] at hrecv
    | ok plain =>
      rw [hdec] at hrecv
      dsimp only [Option.map] at hrecv
      injection hrecv with hquad
      rcases Prod.mk.inj hquad with ⟨hst', hrest⟩
      rcases Prod.mk.inj hrest with ⟨ht', _⟩
      subst hst' ht'
      cases g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      | some idx =>
        dsimp only
        refine ⟨?_, Nat.le_succ g.epoch, fun e he => hch e (List.mem_of_mem_drop he)⟩
        unfold List.getD
        cases hget : g.chainEpochs[idx]? with
        | none => exact Nat.zero_le _
        | some v => exact (hch v (List.mem_of_getElem? hget)).trans (Nat.le_succ g.epoch)
      | none =>
        dsimp only
        refine ⟨Nat.le_refl _, Nat.le_refl _, fun e he => ?_⟩
        rcases List.mem_append.mp (List.mem_of_mem_drop he) with he₀ | he₁
        · exact (hch e he₀).trans (Nat.le_succ g.epoch)
        · simp only [List.mem_singleton] at he₁
          omega

theorem smEpochBounded_accept {PQ Msg C : Type} [DecidableEq C] {k : ℕ}
    {gs : GameState (GhostState PQ) Msg C} {Q : Party} {st' : GhostState PQ} {pos : Pos}
    (h : SmEpochBounded k gs) (hpos : pos.epoch ≤ k + 1)
    (hst' : st'.epoch ≤ k + 1) (hch' : ∀ e ∈ st'.chainEpochs, e ≤ st'.epoch) :
    SmEpochBounded (k + 1) (gs.accept Q st' pos) where
  gs_epoch_le P := by
    dsimp only [GameState.accept, GameState.delete]
    by_cases hPQ : P = Q
    · subst hPQ; simp only [Function.update_self]; exact max_le ((h.gs_epoch_le P).trans (Nat.le_succ k)) hpos
    · simp only [Function.update_of_ne hPQ]; exact (h.gs_epoch_le P).trans (Nat.le_succ k)
  st_epoch_le P := by
    dsimp only [GameState.accept, GameState.delete]
    by_cases hPQ : P = Q
    · subst hPQ; simp only [Function.update_self]; exact hst'
    · simp only [Function.update_of_ne hPQ]; exact (h.st_epoch_le P).trans (Nat.le_succ k)
  chains_le P e he := by
    dsimp only [GameState.accept, GameState.delete] at he ⊢
    by_cases hPQ : P = Q
    · subst hPQ; simp only [Function.update_self] at he ⊢; exact hch' e he
    · simp only [Function.update_of_ne hPQ] at he ⊢; exact h.chains_le P e he
  trans_epoch_le r hr := by
    dsimp only [GameState.accept, GameState.delete] at hr
    exact (h.trans_epoch_le r (List.mem_of_mem_filter hr)).trans (Nat.le_succ k)

theorem SmEpochBounded.setWin {PQ Msg C : Type} {k : ℕ}
    {gs : GameState (GhostState PQ) Msg C} (h : SmEpochBounded k gs) (w : Bool) :
    SmEpochBounded k { gs with win := w } :=
  ⟨h.gs_epoch_le, h.st_epoch_le, h.chains_le, h.trans_epoch_le⟩

theorem epMgmt_epoch_st_trans {St Msg C : Type} {k Δ qep : ℕ}
    {gs gs₁ : GameState St Msg C} {Q : Party} {bad : Bool}
    (hgs : ∀ P : Party, gs.epoch P ≤ k)
    (hep : gs.epMgmt Δ qep Q bad = some gs₁) :
    (∀ P : Party, gs₁.epoch P ≤ k + 1) ∧ gs₁.st = gs.st ∧ gs₁.trans = gs.trans := by
  unfold GameState.epMgmt at hep
  by_cases hs : Q.sendsIn (gs.epoch Q + 1)
  · simp only [hs, ↓reduceIte] at hep
    by_cases hlt : qep < gs.epoch Q + 1
    · simp [hlt] at hep
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      refine ⟨fun P => ?_, by split <;> rfl, by split <;> rfl⟩
      by_cases hPQ : P = Q
      · subst hPQ; simp only [Function.update_self]; split <;> exact Nat.succ_le_succ (hgs P)
      · simp only [Function.update_of_ne hPQ]; split <;> exact (hgs P).trans (Nat.le_succ k)
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hlt : qep < gs.epoch Q
    · simp [hlt] at hep
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨fun P => (hgs P).trans (Nat.le_succ k), rfl, rfl⟩

theorem smEpochBounded_epMgmt_record {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ : ℕ) (s : BitVec 256)
    {k Δ qep : ℕ} {gs gs₁ : GameState (GhostState PQ) (Plain ℓ) Bytes}
    {Q : Party} {bad isChall : Bool} (m : Plain ℓ) (coins : PQC)
    (h : SmEpochBounded k gs) (hep : gs.epMgmt Δ qep Q bad = some gs₁) :
    let out := (sessionSchemeFixedSpk P ℓ s).send (gs₁.st Q) m coins
    SmEpochBounded (k + 1)
      (gs₁.record Δ Q out.1 ⟨⟨Q, gs₁.epoch Q, gs₁.idx Q + 1⟩, m, out.2⟩ isChall) := by
  obtain ⟨hep_le, hst, htr⟩ := epMgmt_epoch_st_trans h.gs_epoch_le hep
  have hsend := fixedSpk_send_epoch_le P ℓ s (gs₁.st Q) m coins (by rw [hst]; exact h.chains_le Q)
  refine ⟨hep_le, fun R => ?_, fun R e he => ?_, fun r hr => ?_⟩
  · dsimp only [GameState.record]
    by_cases hRQ : R = Q
    · subst hRQ; simp only [Function.update_self]; exact hsend.1.trans (by rw [hst]; exact Nat.succ_le_succ (h.st_epoch_le R))
    · simp only [Function.update_of_ne hRQ]; rw [hst]; exact (h.st_epoch_le R).trans (Nat.le_succ k)
  · dsimp only [GameState.record] at he ⊢
    by_cases hRQ : R = Q
    · subst hRQ; simp only [Function.update_self] at he ⊢; exact hsend.2 e he
    · simp only [Function.update_of_ne hRQ] at he ⊢; rw [hst] at he ⊢; exact h.chains_le R e he
  · dsimp only [GameState.record] at hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact hep_le Q
    · rw [htr] at hr'
      exact (h.trans_epoch_le r hr').trans (Nat.le_succ k)

theorem smEpochBounded_deliverR {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (arg : Party × Bytes)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes}
    (h : SmEpochBounded k gs)
    {out : Option (RecvResult (Plain ℓ)) × GameState (GhostState PQ) (Plain ℓ) Bytes}
    (hout : out ∈ support ((deliverR (sessionSchemeFixedSpk P ℓ s) cfg arg).run gs)) :
    SmEpochBounded (k + 1) out.2 := by
  rcases arg with ⟨Q, c⟩
  unfold deliverR at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases hwin : gs.win
  · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout; exact h.mono (Nat.le_succ k)
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hout
    cases htr : gs.inTransit Q.other c with
    | none =>
      simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h.mono (Nat.le_succ k)
    | some rec_ =>
      have hrec_mem : rec_ ∈ gs.trans := List.mem_of_find?_eq_some htr
      simp only [htr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨rc, s0⟩, ⟨_, -, hpair⟩, hout⟩
      have hgs : s0 = gs := (Prod.mk.inj hpair).2
      subst s0
      dsimp only at hout
      cases hrecv : (sessionSchemeFixedSpk P ℓ s).receive (gs.st Q) c rc with
      | none =>
        rw [hrecv] at hout; dsimp only at hout
        by_cases hmust : cfg.base.deliverWin && cfg.must gs Q rec_
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact (h.setWin true).mono (Nat.le_succ k)
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact h.mono (Nat.le_succ k)
      | some quad =>
        rcases quad with ⟨st', t', i', m'⟩
        rw [hrecv] at hout; dsimp only at hout
        obtain ⟨_, hst', hch'⟩ := fixedSpk_receive_epoch_le P ℓ s (gs.st Q) c rc (h.chains_le Q) hrecv
        have hacc : SmEpochBounded (k + 1) (gs.accept Q st' rec_.pos) :=
          smEpochBounded_accept h ((h.trans_epoch_le rec_ hrec_mem).trans (Nat.le_succ k))
            (hst'.trans (Nat.succ_le_succ (h.st_epoch_le Q))) hch'
        by_cases hbad : cfg.base.deliverWin && cfg.must gs Q rec_ &&
            !decide ((t', i', m') = (rec_.pos.epoch, rec_.pos.idx, rec_.msg))
        · simp only [hbad, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact hacc.setWin true
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact hacc

theorem smEpochBounded_injectR {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ Δ qep k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (arg : Party × Bytes)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes}
    (h : SmEpochBounded k gs)
    {out : Option (RecvResult (Plain ℓ)) × GameState (GhostState PQ) (Plain ℓ) Bytes}
    (hout : out ∈ support ((injectR (sessionSchemeFixedSpk P ℓ s) Δ qep cfg arg).run gs)) :
    SmEpochBounded (k + 1) out.2 := by
  rcases arg with ⟨Q, c⟩
  unfold injectR at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases href : gs.win || (gs.inTransit Q.other c).isSome || !gs.safeInj Δ || !cfg.injOK c
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout; exact h.mono (Nat.le_succ k)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨rc, s0⟩, ⟨_, -, hpair⟩, hout⟩
    have hgs : s0 = gs := (Prod.mk.inj hpair).2
    subst s0
    dsimp only at hout
    cases hrecv : (sessionSchemeFixedSpk P ℓ s).receive (gs.st Q) c rc with
    | none =>
      rw [hrecv] at hout; dsimp only at hout
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h.mono (Nat.le_succ k)
    | some quad =>
      rcases quad with ⟨st', t', i', m'⟩
      rw [hrecv] at hout; dsimp only at hout
      obtain ⟨ht', hst', hch'⟩ := fixedSpk_receive_epoch_le P ℓ s (gs.st Q) c rc (h.chains_le Q) hrecv
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact h.mono (Nat.le_succ k)
      · simp only [hqep, ↓reduceIte] at hout
        by_cases htriv : gs.trivial Δ ⟨Q.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact smEpochBounded_accept h (ht'.trans (Nat.succ_le_succ (h.st_epoch_le Q)))
            (hst'.trans (Nat.succ_le_succ (h.st_epoch_le Q))) hch'
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hout
          by_cases hfull : cfg.base.injectFull t'
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact (h.setWin true).mono (Nat.le_succ k)
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact h.mono (Nat.le_succ k)

theorem injectR_run_eq_of_smEpochBounded {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (ℓ Δ qep₁ qep₂ k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (arg : Party × Bytes)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes}
    (h : SmEpochBounded k gs) (h₁ : k + 1 ≤ qep₁ + 1) (h₂ : k + 1 ≤ qep₂ + 1) :
    (injectR (sessionSchemeFixedSpk P ℓ s) Δ qep₁ cfg arg).run gs =
      (injectR (sessionSchemeFixedSpk P ℓ s) Δ qep₂ cfg arg).run gs := by
  rcases arg with ⟨Q, c⟩
  unfold injectR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : gs.win || (gs.inTransit Q.other c).isSome || !gs.safeInj Δ || !cfg.injOK c
  · simp only [href, ↓reduceIte]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind]
    refine bind_congr fun rc => ?_
    cases hrecv : (sessionSchemeFixedSpk P ℓ s).receive (gs.st Q) c rc with
    | none => rfl
    | some quad =>
      rcases quad with ⟨st', t', i', m'⟩
      obtain ⟨ht', _, _⟩ := fixedSpk_receive_epoch_le P ℓ s (gs.st Q) c rc (h.chains_le Q) hrecv
      have ht_le : t' ≤ k + 1 := ht'.trans (Nat.succ_le_succ (h.st_epoch_le Q))
      have hn₁ : ¬ (qep₁ + 1 < t') := by omega
      have hn₂ : ¬ (qep₂ + 1 < t') := by omega
      simp only [hn₁, hn₂, ↓reduceIte]

theorem smEpochBounded_corrR {PQ : Type} (ℓ k : ℕ)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes) (Q : Party)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes}
    (h : SmEpochBounded k gs)
    {out : Option (GhostState PQ) × GameState (GhostState PQ) (Plain ℓ) Bytes}
    (hout : out ∈ support ((corrR cfg Q).run gs)) :
    SmEpochBounded (k + 1) out.2 := by
  unfold corrR at hout
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
  by_cases href : gs.win || !gs.corrAllowed Q || (cfg.r1 && inWindow gs Q) || !cfg.corrOK gs Q
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst hout; exact h.mono (Nat.le_succ k)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact (⟨h.gs_epoch_le, h.st_epoch_le, h.chains_le, h.trans_epoch_le⟩ :
      SmEpochBounded k (gs.afterCorr Q)).mono (Nat.le_succ k)

private theorem liftM_state_run' {τ α : Type} (c : ProbComp α) (t : τ) :
    (liftM c : StateT τ ProbComp α).run t = (c >>= fun a => pure (a, t)) := rfl

private theorem liftStateT_run_state' {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT (n := StateT τ ProbComp) x).run s).run t = (x.run s >>= fun a => pure (a, t)) := rfl

private theorem stateT_lift_run_state' {σ τ α : Type}
    (x : StateT τ ProbComp α) (s : σ) (t : τ) :
    ((StateT.lift (m := StateT τ ProbComp) x).run s).run t =
      (x.run t >>= fun p => pure ((p.1, s), p.2)) := rfl

private theorem stateT_run_modify' {σ : Type} (f : σ → σ) (s : σ) :
    (modify f : StateT σ ProbComp PUnit).run s = pure ((), f s) := rfl

private theorem transmitRTrackHalted_run_eq {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ Δ qep₁ qep₂ : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (Q : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (gs : GameState (GhostState PQ) (Plain ℓ) Bytes)
    (tr : KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes)
    (h₁ : gs.epoch Q + 1 ≤ qep₁) (h₂ : gs.epoch Q + 1 ≤ qep₂) :
    (((KemFailTrackBridge.transmitRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) Δ qep₁ cfg
        (Q, m, r)).run gs).run tr) =
      (((KemFailTrackBridge.transmitRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) Δ qep₂ cfg
        (Q, m, r)).run gs).run tr) := by
  refine congrArg (StateT.run · tr) ?_
  unfold KemFailTrackBridge.transmitRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : !(cfg.sendOK gs Q)
  · simp only [hok, ↓reduceIte]
  · simp only [hok, Bool.false_eq_true, ↓reduceIte]
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte]
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
      refine congrArg (StateT.run · gs) (bind_congr fun x => ?_)
      rw [epMgmt_eq_of_epoch_lt gs Δ qep₁ qep₂ Q x.2 h₁ h₂]

private theorem challRTrackHalted_run_eq {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ Δ qep₁ qep₂ : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (gs : GameState (GhostState PQ) (Plain ℓ) Bytes)
    (tr : KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes)
    (h₁ : gs.epoch Q + 1 ≤ qep₁) (h₂ : gs.epoch Q + 1 ≤ qep₂) :
    (((KemFailTrackBridge.challRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) Δ qep₁ cfg
        (Q, m₀, m₁, r)).run gs).run tr) =
      (((KemFailTrackBridge.challRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) Δ qep₂ cfg
        (Q, m₀, m₁, r)).run gs).run tr) := by
  refine congrArg (StateT.run · tr) ?_
  unfold KemFailTrackBridge.challRTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : !(cfg.sendOK gs Q)
  · simp only [hok, ↓reduceIte]
  · simp only [hok, Bool.false_eq_true, ↓reduceIte]
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte]
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
      refine congrArg (StateT.run · gs) (bind_congr fun x => ?_)
      rw [epMgmt_eq_of_epoch_lt gs Δ qep₁ qep₂ Q x.2 h₁ h₂]

private theorem transmitRTrackHalted_epoch {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ Δ qep k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (Q : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes} (h : SmEpochBounded k gs)
    (tr : KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) :
    ∀ z ∈ support
      (((KemFailTrackBridge.transmitRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) Δ qep cfg
          (Q, m, r)).run gs).run tr),
      SmEpochBounded (k + 1) z.1.2 := by
  intro z hz
  unfold KemFailTrackBridge.transmitRTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : !(cfg.sendOK gs Q)
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact h.mono (Nat.le_succ k)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte] at hz
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact h.mono (Nat.le_succ k)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_state',
        liftM_state_run', bind_assoc, pure_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, -, hz⟩
      cases hep : gs.epMgmt Δ qep Q bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact h.mono (Nat.le_succ k)
      | some s₁ =>
        rcases tr with ⟨tr0, hw0⟩
        simp only [hep, StateT.run_bind, stateT_lift_run_state', StateT.run_get, pure_bind] at hz
        by_cases hcand : (KemFailTrackBridge.stepKemFailSend P.C.F K tr0 Q coins).cand.isSome
        · simp only [hcand, ↓reduceIte, StateT.run_bind, stateT_lift_run_state', StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact h.mono (Nat.le_succ k)
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_state',
            StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact smEpochBounded_epMgmt_record P ℓ s m coins h hep

private theorem challRTrackHalted_epoch {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ Δ qep k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes} (h : SmEpochBounded k gs)
    (tr : KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) :
    ∀ z ∈ support
      (((KemFailTrackBridge.challRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) Δ qep cfg
          (Q, m₀, m₁, r)).run gs).run tr),
      SmEpochBounded (k + 1) z.1.2 := by
  intro z hz
  unfold KemFailTrackBridge.challRTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : !(cfg.sendOK gs Q)
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact h.mono (Nat.le_succ k)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte] at hz
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact h.mono (Nat.le_succ k)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_state',
        liftM_state_run', bind_assoc, pure_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, -, hz⟩
      cases hep : gs.epMgmt Δ qep Q bad with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact h.mono (Nat.le_succ k)
      | some s₁ =>
        simp only [hep] at hz
        by_cases hsafe : !(s₁.safeCh Δ Q) || !(cfg.base.challAllowedIn (s₁.epoch Q))
        · simp only [hsafe, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact h.mono (Nat.le_succ k)
        · rcases tr with ⟨tr0, hw0⟩
          simp only [hsafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_state',
            StateT.run_get, pure_bind] at hz
          by_cases hcand : (KemFailTrackBridge.stepKemFailSend P.C.F K tr0 Q coins).cand.isSome
          · simp only [hcand, ↓reduceIte, StateT.run_bind, stateT_lift_run_state', StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact h.mono (Nat.le_succ k)
          · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_state',
              StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact smEpochBounded_epMgmt_record P ℓ s _ coins h hep

private theorem deliverRTrackHalted_epoch {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (Q : Party) (w : Bytes)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes} (h : SmEpochBounded k gs)
    (tr : KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) :
    ∀ z ∈ support
      (((KemFailTrackBridge.deliverRTrackHalted P.C.F K (sessionSchemeFixedSpk P ℓ s) cfg
          (Q, w)).run gs).run tr),
      SmEpochBounded (k + 1) z.1.2 := by
  intro z hz
  rcases tr with ⟨tr0, hw0⟩
  unfold KemFailTrackBridge.deliverRTrackHalted at hz
  simp only [StateT.run_bind, stateT_lift_run_state', liftStateT_run_state', StateT.run_get,
    bind_assoc, pure_bind, mem_support_bind_iff] at hz
  rcases hz with ⟨⟨res, gs₁⟩, hdel, hz⟩
  have hgs₁ : SmEpochBounded (k + 1) gs₁ :=
    smEpochBounded_deliverR P ℓ k s cfg (Q, w) h hdel
  split at hz
  · simp only [StateT.run_bind, stateT_lift_run_state', stateT_run_modify', StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hgs₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hgs₁

private theorem oracleImplRTrackHalted_step_eq_and_epoch {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ Δ qep₁ qep₂ k : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes} (hgs : SmEpochBounded k gs)
    (h₁ : k + 1 ≤ qep₁) (h₂ : k + 1 ≤ qep₂)
    (tr : KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes)
    (o : (spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    let sm := sessionSchemeFixedSpk P ℓ s
    (((KemFailTrackBridge.oracleImplRTrackHalted P.C.F K sm Δ qep₁ cfg o).run gs).run tr =
      ((KemFailTrackBridge.oracleImplRTrackHalted P.C.F K sm Δ qep₂ cfg o).run gs).run tr) ∧
    ∀ z ∈ support (((KemFailTrackBridge.oracleImplRTrackHalted P.C.F K sm Δ qep₁ cfg o).run gs).run tr),
      SmEpochBounded (k + 1) z.1.2 := by
  intro sm
  rcases o with (((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
  · have hQ₁ : gs.epoch Q + 1 ≤ qep₁ := Nat.le_trans (Nat.add_le_add_right (hgs.gs_epoch_le Q) 1) h₁
    have hQ₂ : gs.epoch Q + 1 ≤ qep₂ := Nat.le_trans (Nat.add_le_add_right (hgs.gs_epoch_le Q) 1) h₂
    exact ⟨transmitRTrackHalted_run_eq P K ℓ Δ qep₁ qep₂ s cfg Q m r gs tr hQ₁ hQ₂,
      transmitRTrackHalted_epoch P K ℓ Δ qep₁ k s cfg Q m r hgs tr⟩
  · have hQ₁ : gs.epoch Q + 1 ≤ qep₁ := Nat.le_trans (Nat.add_le_add_right (hgs.gs_epoch_le Q) 1) h₁
    have hQ₂ : gs.epoch Q + 1 ≤ qep₂ := Nat.le_trans (Nat.add_le_add_right (hgs.gs_epoch_le Q) 1) h₂
    exact ⟨challRTrackHalted_run_eq P K ℓ Δ qep₁ qep₂ s cfg Q m₀ m₁ r gs tr hQ₁ hQ₂,
      challRTrackHalted_epoch P K ℓ Δ qep₁ k s cfg Q m₀ m₁ r hgs tr⟩
  · exact ⟨rfl, deliverRTrackHalted_epoch P K ℓ k s cfg Q w hgs tr⟩
  · refine ⟨?_, ?_⟩
    · change ((liftStateT (n := StateT (KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) ProbComp)
          (injectR sm Δ qep₁ cfg (Q, w))).run gs).run tr =
        ((liftStateT (n := StateT (KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) ProbComp)
          (injectR sm Δ qep₂ cfg (Q, w))).run gs).run tr
      simp only [liftStateT_run_state']
      rw [injectR_run_eq_of_smEpochBounded P ℓ Δ qep₁ qep₂ k s cfg (Q, w) hgs
        (Nat.le_succ_of_le h₁) (Nat.le_succ_of_le h₂)]
    · intro z hz
      change z ∈ support (((liftStateT
        (n := StateT (KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) ProbComp)
        (injectR sm Δ qep₁ cfg (Q, w))).run gs).run tr) at hz
      simp only [liftStateT_run_state', mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      rcases hz with ⟨a, ha, rfl⟩
      exact smEpochBounded_injectR P ℓ Δ qep₁ k s cfg (Q, w) hgs ha
  · refine ⟨rfl, ?_⟩
    intro z hz
    change z ∈ support (((liftStateT
      (n := StateT (KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) ProbComp)
      (corrR cfg Q)).run gs).run tr) at hz
    simp only [liftStateT_run_state', mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨a, ha, rfl⟩
    exact smEpochBounded_corrR ℓ k cfg Q hgs ha

private theorem probComp_bind_congr_of_support {α β : Type}
    (m : ProbComp α) (f g : α → ProbComp β) (h : ∀ z ∈ support m, f z = g z) :
    m >>= f = m >>= g := by
  induction m using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t cont ih =>
    simp only [bind_assoc]
    congr 1; funext u
    exact ih u fun z hz => h z (by
      simp only [mem_support_bind_iff]
      exact ⟨u, by simp, hz⟩)

theorem simulateQ_track_run_eq_of_step {PQ Tr : Type} {ℓ qep₁ qep₂ : ℕ}
    (impl₁ impl₂ : QueryImpl
      (unifSpec + spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState PQ) (Plain ℓ) Bytes) (StateT Tr ProbComp)))
    (hunif : ∀ (u : unifSpec.Domain) gs tr,
      (((impl₁ (.inl u)).run gs).run tr) = (((impl₂ (.inl u)).run gs).run tr) ∧
      ∀ z ∈ support (((impl₁ (.inl u)).run gs).run tr), z.1.2 = gs)
    (hsm : ∀ {k : ℕ} {gs : GameState (GhostState PQ) (Plain ℓ) Bytes} (tr : Tr),
      SmEpochBounded k gs → k + 1 ≤ qep₁ → k + 1 ≤ qep₂ →
      ∀ o,
        (((impl₁ (.inr o)).run gs).run tr) = (((impl₂ (.inr o)).run gs).run tr) ∧
        ∀ z ∈ support (((impl₁ (.inr o)).run gs).run tr), SmEpochBounded (k + 1) z.1.2)
    {oa : Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    {rem k : ℕ} (hoa : MakesAtMostQueries oa rem)
    {gs : GameState (GhostState PQ) (Plain ℓ) Bytes} (hgs : SmEpochBounded k gs)
    (h₁ : k + rem ≤ qep₁) (h₂ : k + rem ≤ qep₂)
    (tr : Tr) :
    (((simulateQ impl₁ oa).run gs).run tr) =
      (((simulateQ impl₂ oa).run gs).run tr) := by
  unfold MakesAtMostQueries at hoa
  induction oa using OracleComp.inductionOn generalizing rem k gs tr with
  | pure a => rfl
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    cases t with
    | inl u =>
      have hstep := hunif u gs tr
      rw [← hstep.1]
      exact probComp_bind_congr_of_support _ _ _ fun z hz => by
        have hrem := hoa.2 z.1.1
        dsimp only at hrem
        exact ih z.1.1 hrem (hstep.2 z hz ▸ hgs) h₁ h₂ z.2
    | inr o =>
      have hpos : 0 < rem := hoa.1.resolve_left (by simp)
      have hstep := hsm tr hgs (by omega) (by omega) o
      rw [← hstep.1]
      exact probComp_bind_congr_of_support _ _ _ fun z hz => by
        have hrem := hoa.2 z.1.1
        simp only [ite_true] at hrem
        exact ih z.1.1 hrem (hstep.2 z hz) (by omega) (by omega) z.2

/-- Clamping `qep` to `min qep (q + 4)` preserves `gameRTrackHalted` on `sessionSchemeFixedSpk` when
`MakesAtMostQueries A q`. -/
theorem gameRTrackHalted_single_min_eq {PQ : Type} [Inhabited PQ]
    (pqrOf : SampledSessionKey → BitVec 256)
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ Δ qep q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (A : Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    let sm := sessionSchemeFixedSpk P ℓ s
    KemFailTrackBridge.gameRTrackHalted pqrOf P.C.F K sm Δ qep cfg A =
      KemFailTrackBridge.gameRTrackHalted pqrOf P.C.F K sm Δ (min qep (q + 4)) cfg A := by
  intro sm
  by_cases hle : qep ≤ q + 4
  · rw [Nat.min_eq_left hle]
  · rw [Nat.min_eq_right (by omega)]
    unfold KemFailTrackBridge.gameRTrackHalted
    let uImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState (GhostState PQ) (Plain ℓ) Bytes)
        (StateT (KemFailTrackBridge.KemFailSessionTrack P.C.F Bytes) ProbComp))
    refine bind_congr fun b => bind_congr fun k => congrArg (· >>= _) ?_
    refine simulateQ_track_run_eq_of_step
      (uImpl + KemFailTrackBridge.oracleImplRTrackHalted P.C.F K sm Δ qep cfg)
      (uImpl + KemFailTrackBridge.oracleImplRTrackHalted P.C.F K sm Δ (q + 4) cfg)
      (fun u gs tr => ⟨rfl, fun z hz => ?_⟩)
      (fun {k₀ gs} tr hgs h₁ h₂ o =>
        oracleImplRTrackHalted_step_eq_and_epoch P K ℓ Δ qep (q + 4) k₀ s cfg hgs h₁ h₂ tr o)
      hq (smEpochBounded_initState_fixedSpk P ℓ s k b) (by omega) (by omega) _
    change z ∈ support
      ((QueryImpl.ofLift unifSpec ProbComp u >>= fun a => pure (a, tr)) >>=
        fun p => pure ((p.1, gs), p.2)) at hz
    simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, -, rfl⟩
    rfl

theorem evalDist_gameRTrackHalted_single_min_eq {PQ : Type} [Inhabited PQ]
    (pqrOf : SampledSessionKey → BitVec 256)
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ Δ qep q : ℕ) (s : BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (A : Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    let sm := sessionSchemeFixedSpk P ℓ s
    𝒟[Prod.fst <$> KemFailTrackBridge.gameRTrackHalted pqrOf P.C.F K sm Δ qep cfg A] =
      𝒟[Prod.fst <$> KemFailTrackBridge.gameRTrackHalted pqrOf P.C.F K sm Δ (min qep (q + 4)) cfg A] := by
  intro sm
  rw [gameRTrackHalted_single_min_eq pqrOf P K ℓ Δ qep q s cfg A hq]

/-- Prefix-averaged `Measure Bool` invariance of `gameRTrackHalted` under `qep ↦ min qep (q + 4)`. -/
theorem evalDist_mixGameRTrackHalted_min_eq {α PQ : Type} [Inhabited PQ]
    (pqrOf : SampledSessionKey → BitVec 256)
    (F : ShaCompress) (K : MlKem)
    (P : α → Params PQ (BitVec 512)) (hF : ∀ o, (P o).C.F = F)
    (ℓ Δ qep q : ℕ) (s : α → BitVec 256)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) Bytes)
    (oa : ProbComp α)
    (A : α → Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o ∈ support oa, MakesAtMostQueries (A o) q) :
    𝒟[oa >>= fun o =>
        Prod.fst <$> KemFailTrackBridge.gameRTrackHalted pqrOf F K
          (sessionSchemeFixedSpk (P o) ℓ (s o)) Δ qep cfg (A o)] =
      𝒟[oa >>= fun o =>
        Prod.fst <$> KemFailTrackBridge.gameRTrackHalted pqrOf F K
          (sessionSchemeFixedSpk (P o) ℓ (s o)) Δ (min qep (q + 4)) cfg (A o)] := by
  refine congrArg evalDist (probComp_bind_congr_of_support oa _ _ fun o ho => ?_)
  cases hF o
  rw [gameRTrackHalted_single_min_eq pqrOf (P o) K ℓ Δ qep q (s o) cfg (A o) (hq o ho)]

end Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp
