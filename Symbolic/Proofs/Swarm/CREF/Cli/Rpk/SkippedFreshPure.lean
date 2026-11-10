/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
public import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkSincePure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Pre-Start Skipped-Seed Freshness

Proves that at a fresh `Move.bobStart` explaining an accepting new-session
pre-key receive block `[.recv b, .rng d, .accept pt]`, every skipped-key seed on
`bobRatchetedChain` satisfies `receiverKeyUsedB = false` on `runTraceMoves r (ms₀ ++ pre)`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (kdfCk chainKeyAt SessionInfo TREvent receiverKeyUsedB)
open PQXDH (PQXDHEvent pqxdhIkm pqxdhKdf agree)
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompRatchet

private theorem rpkSF_at?_tr_step {tr : ExecTrace} {m : Move} (h : NoSessionEffect tr m) (i : Nat) :
    (((m.next tr).at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent))) =
      (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) := by
  have hle : tr ≤ m.next tr := ((Move.act m).run tr).2.property
  by_cases hi : i < tr.length
  · have hi' : i < (m.next tr).length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr (m.next tr) hle)
    simp only [DY.Trace.at?, hi, hi', dite_true, DY.Trace.at_le tr (m.next tr) i hi hle]
  · have hnone : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
      simp only [DY.Trace.at?, hi, dite_false]
    rw [hnone]
    by_cases hi' : i < (m.next tr).length
    · exact (h i (by simp only [newIndices, List.mem_range'_1]; omega)).2.2.1
    · simp only [DY.Trace.at?, hi', dite_false]

private theorem rpkSF_at?_tr_of_quiet :
    ∀ {tr : ExecTrace} {pre : List Move},
      MovesFrom InvisibleNoEffect tr pre →
      ∀ i, (((runMoves pre tr).1).at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent))
  | _, [], _, _ => rfl
  | _, _ :: _, ⟨⟨_, hno⟩, hrest⟩, i => by
    rw [runMoves_cons_fst, rpkSF_at?_tr_of_quiet hrest i, rpkSF_at?_tr_step hno i]

/-- Transfer a `TREvent` logged on `runTraceMoves r (ms₀ ++ pre)` back to `runTraceMoves r ms₀` across
an `InvisibleNoEffect` prefix `pre`. -/
theorem rpkSF_eventLoggedAt_tr_of_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    {ev : TREvent} {i : Nat}
    (hev : (runTraceMoves r (ms₀ ++ pre)).EventLoggedAt ev i) :
    (runTraceMoves r ms₀).EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev ⊢
  rw [runTrace_append, rpkSF_at?_tr_of_quiet hpre i] at hev
  exact hev

/-- If a `PQXDHEvent.BobDone` with base key `ek` is logged at `doneIdx` on `tr`, then
`ek ∈ bobDoneBaseKeys tr`. -/
theorem rpkSF_mem_bobDoneBaseKeys_of_eventLoggedAt {tr : ExecTrace}
    {b' a' : Participant} {ikB ikA spkSk pqsk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : PQXDH.HandshakeKeys} {doneIdx : Nat}
    (hev : tr.EventLoggedAt
      (PQXDHEvent.BobDone b' a' ikB ikA spkSk pqsk opk ek ct keys) doneIdx) :
    ek ∈ bobDoneBaseKeys tr := by
  have hlt : doneIdx < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length _ _ _ hev
  rw [rpkT_bobDoneBaseKeys_eq, List.mem_filterMap]
  refine ⟨doneIdx, List.mem_range.2 hlt, ?_⟩
  unfold rpkT_bdKey
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  have hget : tr.getEventAt PQXDHEvent doneIdx =
      some (PQXDHEvent.BobDone b' a' ikB ikA spkSk pqsk opk ek ct keys) := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hev]
  rw [hget]

/-- `bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk` has a `CompChainRootFrom1`
derivation from `w`'s PQXDH IKM at step `1`. -/
theorem rpkSF_bobRatchetedChain_root {tr : ExecTrace} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) :
    ∃ ikm_w e_w,
      e_w = (PQXDH.errToOption (DY.PQKem.kemDecap w.pqsk w.ct)).getD
        (DY.PQKem.kemRejKey w.pqsk w.ct) ∧
      ikm_w = pqxdhIkm (agree w.ikAPk w.spk) (agree w.ek w.ikB) (agree w.ek w.spk)
        (w.opk.map (agree w.ek ·)) e_w ∧
      w.keys = pqxdhKdf ikm_w ∧
      CompChainRootFrom1 (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key w.msg.ratchetKey) w.spk)
        ikm_w 1 (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey := by
  have hbob := w.hagree
  dsimp only [PQXDH.bobAgreement, Option.pure_def] at hbob
  injection hbob with hkeys
  refine ⟨_, _, rfl, rfl, hkeys.symm, ?_⟩
  dsimp only [bobRatchetedChain, BobStartOk.out, bobOut, DY.Libsignal.TripleRatchet.createChain,
    DY.X25519.agree, CompChainRootFrom1]
  rw [← hkeys]
  rfl

/-- If a responder `CompSessionAt tr₀ s doneIdx ikm dh₁` has `ikm` equal to `w`'s PQXDH IKM,
then its `BobDone` event at `doneIdx` has base key `w.ek`, so `w.ek ∈ bobDoneBaseKeys tr₀`. -/
theorem rpkSF_mem_bobDoneBaseKeys_of_sessionAt_ikm_eq {tr₀ tr : ExecTrace}
    (hreach : tr₀.Reachable reachability)
    {b a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx)
    {s : SessionInfo} (hs_resp : s.initiator = false)
    {doneIdx : Nat} {ikm dh₁ : DY.Bytes}
    (hs : CompSessionAt tr₀ s doneIdx ikm dh₁)
    {e_w : DY.Bytes}
    (hikm_w : ikm = pqxdhIkm (agree w.ikAPk w.spk) (agree w.ek w.ikB) (agree w.ek w.spk)
      (w.opk.map (agree w.ek ·)) e_w) :
    w.ek ∈ bobDoneBaseKeys tr₀ := by
  obtain ⟨_, _, hrole⟩ := hs
  simp only [hs_resp, Bool.false_eq_true, ↓reduceIte] at hrole
  obtain ⟨b', a', t_spk, ikB', ikA', spkSk', pqsk', opk', ek', ct', dh4', e',
    _, _, hne_ik_spk, hevB, _, _, hikm', _⟩ := hrole
  have hikm_eq :
      pqxdhIkm (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key ikA') spkSk')
        (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key ek') ikB')
        (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key ek') spkSk')
        dh4' e' =
      pqxdhIkm (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key w.ikAPk) w.spk)
        (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key w.ek) w.ikB)
        (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key w.ek) w.spk)
        (w.opk.map (agree w.ek ·)) e_w := by
    simpa only [PQXDH.agree] using hikm'.symm.trans hikm_w
  have hparts := pqxdhIkm_inj_parts hikm_eq
  have hdh2_eq := hparts.2.1
  have hdh3_eq := hparts.2.2.1
  have hspk_eq : spkSk' = w.spk := Classical.byContradiction fun hne_spk => by
    obtain ⟨hek₁, hek₂⟩ := dh_eq_of_sk_ne hne_spk hdh3_eq
    rw [hek₁, hek₂] at hdh2_eq
    rcases dh_eq_dh_dhPk_cases hdh2_eq with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hne_spk (dhPk_inj h1).symm
    · exact hne_ik_spk h2
  subst hspk_eq
  have hx_eq : DY.X25519.normalizeX25519Key ek' = DY.X25519.normalizeX25519Key w.ek :=
    dh_right_inj hdh3_eq
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcan', -⟩ :=
    (_root_.Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr₀ hreach).bobDone
      _ _ _ _ _ _ _ _ _ _ doneIdx hevB
  have hek_eq : ek' = w.ek := by
    rw [← x25519Key_of_isCanonicalKey hcan', ← x25519Key_of_isCanonicalKey w.hcan, hx_eq]
  subst hek_eq
  exact rpkSF_mem_bobDoneBaseKeys_of_eventLoggedAt hevB

/-- At a fresh `Move.bobStart` explaining an accepting new-session pre-key receive block
with `q.baseKey.take 33 ∉ accepted`, every skipped-key seed on `bobRatchetedChain` satisfies
`receiverKeyUsedB = false` on the pre-start trace `runTraceMoves r (ms₀ ++ pre)`. -/
theorem rpk_skipped_fresh {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    {accepted : List HwBytes} {q : PreKeyFields}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown :: post)
      acc [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob r.alice kh regA mh pqIdx spqrMsgIdx)
    (ha2₀ : ∀ ek ∈ bobDoneBaseKeys (runTraceMoves r ms₀), ecKey (gamma interpretation S g ek) ∈ accepted)
    (hq : parsePreKeyWire b = some q)
    (hfresh : q.baseKey.take 33 ∉ accepted) :
    ∀ j < w.msg.counter.toNat,
      receiverKeyUsedB (runTraceMoves r (ms₀ ++ pre))
        ((rpkR_finalSt w).sessionInfo r.bob)
        (kdfCk (chainKeyAt
          (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2
        (UInt32.ofNat j) 2 = false := by
  intro j _
  apply TR.receiverKeyUsedB_false_of_no_messageKey_tr
  intro pqSalt n rIdx pIdx i hev
  have hev₀ : (runTraceMoves r ms₀).EventLoggedAt
      (TREvent.MessageKey ((rpkR_finalSt w).sessionInfo r.bob) .receiver
        (kdfCk (chainKeyAt
          (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2
        pqSalt n rIdx pIdx) i :=
    rpkSF_eventLoggedAt_tr_of_quietPre hpre hev
  have hreach₀ : (runTraceMoves r ms₀).Reachable reachability :=
    matchedPrefix_prefix_reachable hB.pre ms₀ [] (List.append_nil _).symm
  obtain ⟨_, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ :=
    (compScheduleInv_reachable hreach₀).eventOK _ ⟨i, hev₀⟩
  obtain ⟨ikm_w, e_w, _, hikm_w_def, _, hroot_w⟩ := rpkSF_bobRatchetedChain_root w
  have hck_eq : chainKeyAt (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j =
      chainKeyAt ck₀ n.toNat :=
    kdfCk_snd_inj hseed
  have hck₀_eq : ck₀ = (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey :=
    (chainKeyAt_root_inj hroot_w.isChainRoot hroot.isChainRoot hck_eq).1.symm
  subst hck₀_eq
  have hikm_eq : ikm = ikm_w := (hroot.eq_iff hroot_w).2.1
  have hs_resp : ((rpkR_finalSt w).sessionInfo r.bob).initiator = false := rfl
  have hek_mem : w.ek ∈ bobDoneBaseKeys (runTraceMoves r ms₀) :=
    rpkSF_mem_bobDoneBaseKeys_of_sessionAt_ikm_eq hreach₀ w hs_resp hs (hikm_eq.trans hikm_w_def)
  have hshown : 1 ≤ shown := rpkT_bobStart_shown_pos hB
  obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, (Nat.sub_add_cancel hshown).symm⟩
  have hF : List.Forall₂ (EventMatchesEntry interpretation r S g) [.recv b, .rng d, .accept pt]
      ((Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx (k + 1)).vis
        (runTraceMoves r (ms₀ ++ pre))) :=
    (rpkT_bobStart_block hB hpre).1
  have hγ : ecKey (gamma interpretation S g w.ek) = q.baseKey.take 33 :=
    rpkT_bobStart_gamma w hF hq
  have hmem_acc : q.baseKey.take 33 ∈ accepted := hγ ▸ ha2₀ w.ek hek_mem
  exact hfresh hmem_acc

end Symbolic.Swarm.CREF.CliPure
