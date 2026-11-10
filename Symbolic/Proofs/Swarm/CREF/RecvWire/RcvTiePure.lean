/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.SlotsZ6Pure
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyRunInvPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# No-Ratchet `SkippedInstallByteFresh` Preservation for Whisper Decrypt

Proves `decTailTr` / `decRatchetPreTr` trace prefix and `SkippedKeyStored` inversion lemmas,
together with `SkippedInstallByteFresh` preservation across a no-ratchet `Move.decrypt` step.
-/

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain kdfCk)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR

variable (interpretation : ExternInterpretation)

private theorem rcvTie_invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, rcvTie_invisible_vis_nil δ (m.next tr) hδ, List.nil_append]

private theorem rcvTie_block_vis {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
  have hm := hB.matched
  rw [b5_runMoves_append_snd, rcvTie_invisible_vis_nil pre _ hpre, List.nil_append,
    runMoves_cons_snd, rcvTie_invisible_vis_nil post _ hpost, List.append_nil] at hm
  rwa [TR.runTrace_append]

abbrev TieStEntry :=
  DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState)

abbrev TieTREntry := TR.RecvDec.TREntry

theorem le_logSkippedKeysTr_tie (s : SessionInfo) (pk : DY.Bytes) (rIdx srcIdx : Nat)
    (ck : DY.Bytes) (idx : UInt32) :
    ∀ (cnt : Nat) (tr : ExecTrace),
      tr ≤ TR.RecvDec.logSkippedKeysTr s pk rIdx srcIdx ck idx cnt tr
  | 0, tr => DY.Trace.le_refl tr
  | cnt + 1, _tr =>
    DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
      (le_logSkippedKeysTr_tie s pk rIdx srcIdx (kdfCk ck).1 (idx + 1) cnt _)

theorem le_decTailTr (tr₀ : ExecTrace) (me : Participant) (stateIdx : Nat) (st : TRState)
    (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    tr₀ ≤ TR.RecvDec.decTailTr tr₀ me stateIdx st c c' pk seed pqSalt ptTerm spqr' n := by
  unfold TR.RecvDec.decTailTr
  exact DY.Trace.le_trans _ _ _ (le_logSkippedKeysTr_tie _ _ _ _ _ _ _ _)
    (DY.Trace.le_trans _ _ _
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))
      (DY.Trace.append_le _ _))

theorem le_decRatchetPreTr (tr₀ : ExecTrace) (me : Participant) (st1 : TRState)
    (pk key : DY.Bytes) :
    tr₀ ≤ TR.RecvDec.decRatchetPreTr tr₀ me st1 pk key := by
  unfold TR.RecvDec.decRatchetPreTr
  exact DY.Trace.le_trans _ _ _
    (DY.Trace.le_trans _ _ _
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))
      (DY.Trace.append_le _ _))
    (DY.Trace.append_le _ _)

theorem eventLoggedAt_decTailTr_skippedKeyStored
    {tr₀ : ExecTrace} {me : Participant} {stateIdx : Nat} {st : TRState}
    {c c' : RecvChain} {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s' : SessionInfo} {pk' seed' : DY.Bytes} {n' : UInt32} {rIdx' src' i' : Nat}
    (h : (TR.RecvDec.decTailTr tr₀ me stateIdx st c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i') :
    tr₀.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' ∨
      (pk' = pk ∧ src' = stateIdx) := by
  let tr_sk := TR.RecvDec.logSkippedKeysTr (st.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr₀
  have hlog_sk : tr_sk.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    have hlog' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp h
    unfold TR.RecvDec.decTailTr at hlog'; dsimp only at hlog'
    rw [TR.RecvDec.at?_append_non_entry _ _ rfl] at hlog'
    rcases Nat.lt_or_ge i' (tr_sk.length + 1) with hlt1 | hge1
    · rw [TR.RecvDec.at?_append_of_lt _ _ (by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        exact hlt1)] at hlog'
      rcases Nat.lt_or_ge i' tr_sk.length with hlt0 | hge0
      · rw [TR.RecvDec.at?_append_of_lt _ _ hlt0] at hlog'; exact hlog'
      · have heq0 : i' = tr_sk.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hlt1) hge0
        subst heq0; rw [Trace.at?_append] at hlog'; nomatch hlog'
    · rcases Nat.eq_or_lt_of_le hge1 with heq1 | hgt1
      · have hlen_rcv : tr_sk.length + 1 =
            (tr_sk.append (⟨TREvent.Received me st.peer pk n ptTerm⟩ : TieTREntry)).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        rw [← heq1, hlen_rcv, Trace.at?_append] at hlog'; nomatch hlog'
      · rw [TR.RecvDec.at?_eq_none_of_le _ (by
          simp only [tr_sk, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hgt1 ⊢
          omega)] at hlog'
        nomatch hlog'
  by_cases hi : i' < tr₀.length
  · have hlog0 : tr₀.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      rw [← TR.RecvDec.at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]
      exact (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog_sk
    exact Or.inl hlog0
  · have hi_lt : i' < tr_sk.length := by
      by_contra hge
      have hnone : (tr_sk.at? i' : Option TieTREntry) = none :=
        TR.RecvDec.at?_eq_none_of_le tr_sk (Nat.le_of_not_lt hge)
      have hlog_sk' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog_sk
      rw [hnone] at hlog_sk'; cases hlog_sk'
    have hlen_sk : tr_sk.length = tr₀.length + (n.toNat - c.index.toNat) :=
      TR.RecvDec.logSkippedKeysTr_length _ _ _ _ _ _ _ _
    have hj : i' - tr₀.length < n.toNat - c.index.toNat := by omega
    have hi_eq : i' = tr₀.length + (i' - tr₀.length) := by omega
    have hat := TR.RecvDec.at?_trEntry_logSkippedKeysTr_add (st.sessionInfo me) pk c.rIdx stateIdx
      c.chainKey c.index (n.toNat - c.index.toNat) tr₀ hj
    have hlog_sk' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog_sk
    rw [hi_eq, hat] at hlog_sk'; cases hlog_sk'; exact Or.inr ⟨rfl, rfl⟩

theorem eventLoggedAt_decRatchetPreTr_skippedKeyStored
    {tr₀ : ExecTrace} {me : Participant} {st1 : TRState} {pk key : DY.Bytes}
    {s' : SessionInfo} {pk' seed' : DY.Bytes} {n' : UInt32} {rIdx' src' i' : Nat}
    (h : (TR.RecvDec.decRatchetPreTr tr₀ me st1 pk key).EventLoggedAt
      (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i') :
    tr₀.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  have hlog' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp h
  unfold TR.RecvDec.decRatchetPreTr at hlog'
  let tr2 := (tr₀.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : DY.Network.ExecEntryT)
  rcases Nat.lt_or_ge i' (tr2.length + 1) with hlt1 | hge1
  · rw [TR.RecvDec.at?_append_of_lt _ _ (by
      simp only [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hlt1 ⊢
      omega)] at hlog'
    rcases Nat.lt_or_ge i' tr2.length with hlt0 | hge0
    · rw [TR.RecvDec.at?_append_of_lt _ _ hlt0] at hlog'; dsimp only [tr2] at hlog'
      rw [TR.RecvDec.at?_append_non_entry _ _ rfl, TR.RecvDec.at?_append_non_entry _ _ rfl] at hlog'
      exact hlog'
    · have heq0 : i' = tr2.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hlt1) hge0
      subst heq0; rw [Trace.at?_append] at hlog'; nomatch hlog'
  · rcases Nat.eq_or_lt_of_le hge1 with heq1 | hgt1
    · have hlen_dh : tr2.length + 1 =
          (tr2.append (⟨TREvent.DHRatchet me st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : TieTREntry)).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [← heq1, hlen_dh, Trace.at?_append] at hlog'; nomatch hlog'
    · rw [TR.RecvDec.at?_eq_none_of_le _ (by
        simp only [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hgt1 ⊢
        omega)] at hlog'
      nomatch hlog'

/-- Under `XplBlock` on `.recv (wireWhisperTag :: body) :: [.accept sm.message]`, a `Move.decrypt`
step takes the no-ratchet branch and preserves `SkippedInstallByteFresh`. -/
theorem rcv_skippedInstallByteFresh_decrypt_noRatchet
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ pre post : List Move}
    {p : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {acc : List MachineEvent} {body : HwBytes} {sm : StateAndMessage}
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (.recv (wireWhisperTag :: body) :: [.accept sm.message]))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hBF : TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre)) :
    TR.SkippedInstallByteFresh interpretation S g r₀
      (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) := by
  let ms := ms₀ ++ pre
  have hmatch := rcvTie_block_vis interpretation hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, _hidx, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch
      (fun d hd => by
        rcases hd with _ | ⟨_, _ | ⟨_, hd⟩⟩
        · intro h; cases h
        · intro h; cases h
        · cases hd)
      ⟨.accept sm.message, by simp, rfl⟩
  let tr₀ := runTraceMoves r₀ ms
  let tr_k := tr₀.append (⟨key⟩ : DY.Network.ExecEntryT)
  have htr_post :
      runTraceMoves r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) =
      TR.RecvDec.decTailTr tr_k p stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
    rw [TR.runTrace_snoc]
    exact TR.RecvDec.decrypt_next_noRatchet_eq hst hmsg hparse hver hfind hcons hspqr hpqSalt hmac_eq hdec
  have htr_le : tr₀ ≤ tr_k := Trace.append_le tr₀ _
  have hno_new_pre : ∀ s' pk' n' seed' rIdx' src' i',
      tr_k.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' →
      tr₀.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
    intro s' pk' n' seed' rIdx' src' i' hlog
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog ⊢
    dsimp only [tr_k] at hlog
    rw [TR.RecvDec.at?_append_non_entry _ _ rfl] at hlog
    exact hlog
  have hst_pre : ∀ {p₀ : Participant} {st₀ : TRState} {src : Nat},
      src < tr₀.length →
      TR.TRStateStoredAt p₀ st₀ src
        (TR.RecvDec.decTailTr tr_k p stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter) →
      TR.TRStateStoredAt p₀ st₀ src tr₀ := by
    intro p₀ st₀ src hlt hst_tail
    have hle_tail : tr₀ ≤
        TR.RecvDec.decTailTr tr_k p stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
      rw [← htr_post, TR.runTrace_snoc]
      exact TR.le_runMoves_fst [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped] tr₀
    exact TR.trStateStoredAt_of_le_of_lt hle_tail hlt hst_tail
  have hstH : TR.TRStateStoredAt p st stateIdx tr_k := by
    have hat0 : TR.TRStateStoredAt p st stateIdx tr₀ :=
      TR.FreshSigma.at?_eq_some_of_getLocalState_some hst
    change (tr_k.at? stateIdx : Option TieStEntry) = some ⟨⟨p, st⟩⟩
    dsimp only [tr_k]
    rw [TR.RecvDec.at?_append_non_entry _ _ rfl]
    exact hat0
  intro s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog hst₀ hrc c_m hc_m
  rw [htr_post] at hlog hst₀
  exact TR.skippedInstallByteFresh_decTailTr_of_findRecvChain_some interpretation S g r₀ ms
    htr_le hno_new_pre hst_pre hstH hfind (RpkCli.Skr.skippedKeySrcLt_runTrace r₀ ms) hBF
    s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog hst₀ hrc c_m hc_m

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
