/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.QuietTransferPure
public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplPure
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.MessageKeyCurrentInv
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistDecAvail
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Promoted Prekey Receive Block Inversion, Snapshot Uniqueness, and Clean-Read Extraction

Provides quiet-extension and block-visibility helpers for `OneMove` decompositions, current
snapshot uniqueness, `CHist` step combinators across `DecryptBy p m`, and `PromCurrentRead` /
`¬ RecvCollision` extraction from a `Clean` explanation of `promAccBlk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.TR.CHistStep (RecRecvRkOk)

local notation "PromHStE" =>
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

theorem prom_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)

theorem prom_quietPost {r : ProtocolSetup} {ms₀ pre post : List Move} {m : Move}
    (hpost : MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₀ ++ pre))) post) :
    Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m])) (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) := by
  rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
    TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc]
  exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)

theorem prom_invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, prom_invisible_vis_nil δ (m.next tr) hδ, List.nil_append]

/-- The active move `m` between invisible no-effect `pre` and `post` matches the whole block `blk`. -/
theorem prom_block_vis {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) blk (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
  have hm := hB.matched
  rw [b5_runMoves_append_snd, prom_invisible_vis_nil pre _ hpre, List.nil_append,
    runMoves_cons_snd, prom_invisible_vis_nil post _ hpost, List.append_nil] at hm
  rwa [TR.runTrace_append]

private theorem prom_not_lt_of_current {tr : ExecTrace} {p : Participant} {a b : Nat}
    {sa sb : TRState}
    (ha : (tr.at? a : Option PromHStE) = some ⟨⟨p, sa⟩⟩)
    (hb : (tr.at? b : Option PromHStE) = some ⟨⟨p, sb⟩⟩)
    (hca : isCurrentSnapshot tr a = true) (hinit : sa.initiator = sb.initiator) : ¬ a < b := by
  intro hlt
  have hblt : b < tr.length := by
    by_contra hge
    have hnone : (tr.at? b : Option PromHStE) = none := by
      simp only [Trace.at?, hge, ↓reduceDIte]
    rw [hnone] at hb; cases hb
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hca
  rw [ha] at hca
  have hmem : b ∈ List.range' (a + 1) (tr.length - (a + 1)) :=
    List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have hall := List.all_eq_true.mp hca b hmem
  rw [hb] at hall
  simp [hinit] at hall

/-- Two current snapshots of `p` with the same role have the same trace index. -/
theorem prom_currentSnapshot_unique {tr : ExecTrace} {p : Participant} {i j : Nat}
    {st₁ st₂ : TRState}
    (h₁ : ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st₁)
    (h₂ : ((PersistentLocalState.getLocalState p j : Traceful TRState).run tr).1 = some st₂)
    (hc₁ : isCurrentSnapshot tr i = true) (hc₂ : isCurrentSnapshot tr j = true)
    (hinit : st₁.initiator = st₂.initiator) : i = j := by
  have ha₁ := FreshSigma.at?_eq_some_of_getLocalState_some h₁
  have ha₂ := FreshSigma.at?_eq_some_of_getLocalState_some h₂
  rcases lt_trichotomy i j with h | h | h
  · exact absurd h (prom_not_lt_of_current ha₁ ha₂ hc₁ hinit)
  · exact h
  · exact absurd h (prom_not_lt_of_current ha₂ ha₁ hc₂ hinit.symm)

theorem prom_currentSnapshot_unique_of_role {r : ProtocolSetup} {tr : ExecTrace} {p : Participant}
    {i j : Nat} {st₁ st₂ : TRState} (hrole : RoleSnapshots r tr)
    (h₁ : ((PersistentLocalState.getLocalState p i : Traceful TRState).run tr).1 = some st₁)
    (h₂ : ((PersistentLocalState.getLocalState p j : Traceful TRState).run tr).1 = some st₂)
    (hc₁ : isCurrentSnapshot tr i = true) (hc₂ : isCurrentSnapshot tr j = true) : i = j :=
  prom_currentSnapshot_unique h₁ h₂ hc₁ hc₂
    ((hrole p st₁ i (FreshSigma.at?_eq_some_of_getLocalState_some h₁)).trans
      (hrole p st₂ j (FreshSigma.at?_eq_some_of_getLocalState_some h₂)).symm)

theorem prom_hist_avail_cases {r : ProtocolSetup} {ms : List Move} {p : Participant} {m : Move}
    (hm : DecryptBy p m) :
    ∀ st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r (ms ++ [m])),
      st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r ms) ∨
        ((runTraceMoves r (ms ++ [m])).at? ((runTraceMoves r (ms ++ [m])).length - 1) : Option PromHStE) =
          some ⟨⟨p, st⟩⟩ := by
  match m, hm with
  | .decrypt _ stateIdx msgIdx pqIdx spqrMsgIdx wrapped, rfl =>
    exact TR.availableStates_move_decrypt_cases r ms p stateIdx msgIdx pqIdx spqrMsgIdx wrapped
  | .decryptSkipped _ stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped, rfl =>
    exact TR.availableStates_move_decryptSkipped_cases r ms p stateIdx msgIdx skIdx pqIdx
      spqrMsgIdx wrapped

/-- Steps `CHist` across `DecryptBy p m` from byte-freshness and a stored-state witness. -/
theorem prom_hist_snoc_of_parts {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {m : Move}
    (hm : DecryptBy p m) (hch : CHist interpretation r S g ms)
    (hbf : TR.SkippedInstallByteFresh interpretation S g r ms →
      TR.SkippedInstallByteFresh interpretation S g r (ms ++ [m]))
    (hstore : ∀ newSt : TRState,
      ((runTraceMoves r (ms ++ [m])).at? ((runTraceMoves r (ms ++ [m])).length - 1) : Option PromHStE) =
        some ⟨⟨p, newSt⟩⟩ →
      ∃ rec' : RecordRec, StateRel interpretation S g newSt rec' ∧
        (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
        TR.CHistStep.RecRecvRkOk rec') :
    CHist interpretation r S g (ms ++ [m]) := by
  by_cases hs : ∃ newSt : TRState,
      ((runTraceMoves r (ms ++ [m])).at? ((runTraceMoves r (ms ++ [m])).length - 1) : Option PromHStE) =
        some ⟨⟨p, newSt⟩⟩
  · obtain ⟨newSt, hlast⟩ := hs
    obtain ⟨rec', hrel', hnd', hok'⟩ := hstore newSt hlast
    refine TR.CHistStep.cHist_step hch (fun st hst => ?_) hrel' hnd' hok' hbf
    rcases prom_hist_avail_cases hm st hst with h | h
    · exact Or.inl h
    · rw [hlast] at h; cases h; exact Or.inr rfl
  · refine TR.CHistStep.cHist_of_noStore hch (fun st hst => ?_) hbf
    rcases prom_hist_avail_cases hm st hst with h | h
    · exact h
    · exact absurd ⟨st, h⟩ hs

private theorem prom_hist_idx_of_current {tr : ExecTrace} {p : Participant} {i : Nat}
    {st newSt : TRState}
    (hat : (tr.at? i : Option PromHStE) = some ⟨⟨p, st⟩⟩)
    (hlast : (tr.at? (tr.length - 1) : Option PromHStE) = some ⟨⟨p, newSt⟩⟩)
    (hcur : isCurrentSnapshot tr i = true) (hinit : newSt.initiator = st.initiator) :
    i = tr.length - 1 := by
  have hlt : i < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := PromHStE) tr i
    rw [hat] at this; exact this
  by_contra hne
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur
  rw [hat] at hcur
  simp only [List.all_eq_true] at hcur
  have hj := hcur (tr.length - 1) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rw [hlast] at hj
  simp [hinit] at hj

theorem prom_hist_storeRel_of_inv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes}
    {newSt : TRState}
    (hinv : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = p then some b else none))
    (hlast : ((runTraceMoves r ms).at? ((runTraceMoves r ms).length - 1) : Option PromHStE) =
      some ⟨⟨p, newSt⟩⟩)
    (hrole : ∀ (st₁ st₂ : TRState) (i j : Nat),
      ((runTraceMoves r ms).at? i : Option PromHStE) = some ⟨⟨p, st₁⟩⟩ →
      ((runTraceMoves r ms).at? j : Option PromHStE) = some ⟨⟨p, st₂⟩⟩ →
      st₁.initiator = st₂.initiator) :
    ∃ rec' : RecordRec, b = recordBytes rec' ∧ StateRel interpretation S g newSt rec' ∧
      (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup := by
  obtain ⟨_, rec, st, stateIdx, hb, hget, hcur, hrel, _, _, _, hnd⟩ := hinv p b (by simp)
  have hat : ((runTraceMoves r ms).at? stateIdx : Option PromHStE) = some ⟨⟨p, st⟩⟩ :=
    TR.FreshSigma.at?_eq_some_of_getLocalState_some hget
  have hidx := prom_hist_idx_of_current hat hlast hcur (hrole _ _ _ _ hlast hat)
  rw [hidx, hlast] at hat
  cases hat
  exact ⟨rec, hb, hrel, hnd.1⟩

theorem prom_hist_store_of_inv {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes}
    (hinv : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = p then some b else none))
    (hrole : ∀ (st₁ st₂ : TRState) (i j : Nat),
      ((runTraceMoves r ms).at? i : Option PromHStE) = some ⟨⟨p, st₁⟩⟩ →
      ((runTraceMoves r ms).at? j : Option PromHStE) = some ⟨⟨p, st₂⟩⟩ →
      st₁.initiator = st₂.initiator)
    (hok : ∀ rec' : RecordRec, b = recordBytes rec' → TR.CHistStep.RecRecvRkOk rec') :
    ∀ newSt : TRState,
      ((runTraceMoves r ms).at? ((runTraceMoves r ms).length - 1) : Option PromHStE) =
        some ⟨⟨p, newSt⟩⟩ →
      ∃ rec' : RecordRec, StateRel interpretation S g newSt rec' ∧
        (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
        TR.CHistStep.RecRecvRkOk rec' := by
  intro newSt hlast
  obtain ⟨rec', hb, hrel, hnd⟩ := prom_hist_storeRel_of_inv hinv hlast hrole
  exact ⟨rec', hrel, hnd, hok rec' hb⟩

/-- On either branch of `PureCRecRel`, `CHist` yields a `RecordRec` decoding `rec` with `RecRecvRkOk`. -/
theorem prom_recRecvRkOk_entry_of_cRecRel
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {rec : HwBytes}
    (hch : CHist interpretation r S g ms)
    (hcr : PureCRecRel interpretation r S g ms p rec) :
    ∃ rr : RecordRec, rec = recordBytes rr ∧ rr.current.sessionVersion = 4#32 ∧ RecRecvRkOk rr := by
  rcases hcr with htr | ⟨rfl, hp⟩
  · obtain ⟨_, rr, st, _stateIdx, hb, hget, _, hst_rel, _, _, _, _⟩ := htr p rec (by simp)
    have hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r ms) :=
      TR.mem_availableStates_of_trStateStoredAt r ms
        (TR.FreshSigma.at?_eq_some_of_getLocalState_some hget)
    exact ⟨rr, hb, congrArg SessionRec.sessionVersion hst_rel.2,
      TR.CHistStep.recRecvRkOk_of_cHist_frame hch hst hst_rel (fun _ hk => hk)⟩
  · obtain ⟨_sess, _sc, _remote, _items, _kpk, st, _stateIdx, _ekIdx, _ctIdx, _ek, _ct,
      _hcanon, _hscope, _hscopeP, hget, _h5, _h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _hrem,
      _h15, _h16, _h17, _h18, _h19, _h20, _h21, _h22, _h23, _h24, _h25, rr, hb, hst_rel, _⟩ := hp
    have hst : st ∈ DY.Libsignal.Composed.Refinement.availableStates r (runTraceMoves r ms) :=
      TR.mem_availableStates_of_trStateStoredAt r ms
        (TR.FreshSigma.at?_eq_some_of_getLocalState_some hget)
    exact ⟨rr, hb, congrArg SessionRec.sessionVersion hst_rel.2,
      TR.CHistStep.recRecvRkOk_of_cHist_frame hch hst hst_rel (fun _ hk => hk)⟩

/-! ## Clean-Explanation Read Extraction on `promAccBlk` -/

private theorem prom_attackerKnows_of_getMessageSentAt {tr : ExecTrace} {idx : Nat} {t : DY.Bytes}
    (hget : tr.getMessageSentAt idx = some t) : t.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr t idx
    ((Trace.MessageSentAt_eq_getMessageSentAt t idx tr).mpr hget)

/-- On a `Clean` explanation `ms₀ ++ (pre ++ m :: post)` of `acc ++ promAccBlk b mid pt`, the
active decrypt move's read term `t` belongs to `recvRepresentations` of `pf.message`. -/
theorem prom_rep_of_clean {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc mid : List MachineEvent}
    {b pt : HwBytes} {pf : PreKeyFields} {t : DY.Bytes}
    (hpf : parsePreKeyWire b = some pf)
    (hc : Clean interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ promAccBlk b mid pt))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (ht : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t) :
    t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) pf.message := by
  have hpre_vis : (runMoves pre (runTraceMoves r ms₀)).2 = [] := prom_invisible_vis_nil pre _ hpre
  have hpost_vis : (runMoves post (m.next (runMoves pre (runTraceMoves r ms₀)).1)).2 = [] :=
    prom_invisible_vis_nil post _ hpost
  have hvis_all : runVis r (ms₀ ++ (pre ++ m :: post)) =
      runVis r ms₀ ++ m.vis (runTraceMoves r (ms₀ ++ pre)) := by
    rw [runVis_append, b5_runMoves_append_snd, hpre_vis, List.nil_append,
      runMoves_cons_snd, hpost_vis, List.append_nil, TR.runTrace_append]
  have hlen_acc : acc.length = (runVis r ms₀).length := hB.pre.2.2.2.2.2.length_eq
  have hbv := prom_block_vis hB hpre hpost
  have hwrap_vis : ∀ stateIdx msgIdx wrapped,
      (runTraceMoves r (ms₀ ++ pre)).getMessageSentAt msgIdx = some t →
      m.vis (runTraceMoves r (ms₀ ++ pre)) =
        decVis (runTraceMoves r (ms₀ ++ pre)) (m.next (runTraceMoves r (ms₀ ++ pre))) stateIdx msgIdx wrapped ++
          exposures (runTraceMoves r (ms₀ ++ pre)) (m.next (runTraceMoves r (ms₀ ++ pre))) →
      t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) pf.message := by
    intro stateIdx msgIdx wrapped hget hmvis
    cases wrapped with
    | false =>
      have hmvis' : ∃ vs, m.vis (runTraceMoves r (ms₀ ++ pre)) =
          ⟨.recv, [t], .whisper, none⟩ :: vs := by
        rw [hmvis]; unfold decVis; rw [hget]; exact ⟨_, rfl⟩
      obtain ⟨vs, hmvis_cons⟩ := hmvis'
      rw [hmvis_cons] at hbv
      cases hbv with
      | cons hhead _ =>
        obtain ⟨_, t', _, hb_eq⟩ := hhead
        change b = _ at hb_eq
        subst hb_eq
        exact False.elim (promXpl_tag_ne_wireWhisperTag_of_parsePreKeyWire hpf rfl)
    | true =>
      let v₀ : VisEntry :=
        ⟨.recv, [t], .preKeyInner (sessionBaseKeys (runTraceMoves r (ms₀ ++ pre)) stateIdx), none⟩
      have hmvis' : ∃ vs, m.vis (runTraceMoves r (ms₀ ++ pre)) = v₀ :: vs := by
        rw [hmvis]; unfold decVis; rw [hget]; exact ⟨_, rfl⟩
      obtain ⟨vs, hmvis_cons⟩ := hmvis'
      have hmem_zip : (MachineEvent.recv b, v₀) ∈
          (acc ++ promAccBlk b mid pt).zip (runVis r (ms₀ ++ (pre ++ m :: post))) := by
        rw [hvis_all, hmvis_cons, List.zip_append hlen_acc]
        exact List.mem_append_right _ List.mem_cons_self
      have hrf := hc.matched.2.2.2.2.1 (MachineEvent.recv b, v₀) hmem_zip rfl pf hpf
      exact ⟨prom_attackerKnows_of_getMessageSentAt hget, hrf.2⟩
  cases m with
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    exact hwrap_vis stateIdx msgIdx wrapped ht rfl
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    exact hwrap_vis stateIdx msgIdx wrapped ht rfl
  | _ => simp [rcvMoveTerm, Move.decryptMsgIdx?] at ht

/-- Extracts `¬ RecvCollision` on the active decrypt move's read term `t` at `ms₀ ++ pre` from
`hc.not_readCollision`. -/
theorem prom_not_recvCollision_of_clean {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc mid : List MachineEvent}
    {b pt : HwBytes} {pf : PreKeyFields} {t : DY.Bytes}
    (hpf : parsePreKeyWire b = some pf)
    (hc : Clean interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ promAccBlk b mid pt))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32)
    (ht : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t) :
    ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t :=
  not_recvCollision_of_not_readCollision hc.not_readCollision
    hB.pre.2.2.2.2.2 (prom_invisible_vis_nil pre _ hpre)
    (prom_hmid_filter_head hmid) (prom_recvBody_of_parsePreKeyWire hpf) ht

/-- Current-snapshot and `recvRepresentations` premise for a decrypt move `m` at `ms`. -/
def PromCurrentRead (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (msgBytes : HwBytes) (m : Move) : Prop :=
  match m with
  | .decrypt _ stateIdx .. =>
    isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
      ∀ t, rcvMoveTerm (runTraceMoves r ms) m = some t →
        t ∈ recvRepresentations interpretation r S g ms msgBytes
  | .decryptSkipped _ stateIdx .. =>
    isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
      ∀ t, rcvMoveTerm (runTraceMoves r ms) m = some t →
        t ∈ recvRepresentations interpretation r S g ms msgBytes
  | _ => True

theorem prom_currentRead_of_clean {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc mid : List MachineEvent}
    {b pt : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire b = some pf)
    (hc : Clean interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ promAccBlk b mid pt))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    PromCurrentRead interpretation r S g (ms₀ ++ pre) pf.message m := by
  have hsnap := TR.rcvCurrentSnapshot_of_xplBlock hB hpre hpost (prom_accBlk_has_accept b mid pt)
  cases m with
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    exact ⟨hsnap, fun _t ht => prom_rep_of_clean hpf hc hB hpre hpost ht⟩
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    exact ⟨hsnap, fun _t ht => prom_rep_of_clean hpf hc hB hpre hpost ht⟩
  | _ => trivial

end Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
