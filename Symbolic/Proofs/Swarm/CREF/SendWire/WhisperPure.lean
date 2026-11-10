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
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
public import Symbolic.Proofs.Swarm.CREF.XplSnapshot
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Initiate.TransferPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.GhostInvariance
import Symbolic.Proofs.Swarm.CREF.SendWire.StateInv
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
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

/-!
# Whisper `SendWire` Ghost Transport, Frame, and `Clean` Step Lemmas

Proves `StateRel` transport across `sendGhost`, snapshot uniqueness under `RoleSnapshots`,
cross-party `PureCRecRel` framing (`snd_frame_other`), and `Clean` step lemmas (`clean_sendGhost`,
`clean_sendPendingGhost`, `snd_clean_snoc`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.IniSndPure
open Symbolic.Swarm.CREF.SendWire
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.Swarm.COMPOSED

theorem gamma'_setSendAddr_updateFreshAt₂_of_stampsLt
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {pt coins addr : HwBytes} {b : DY.Bytes}
    (h : TR.FreshSigma.StampsLt interpretation S g ts b) :
    let g₁ : Ghost := { g with σ := TR.FreshSigma.updateFreshAt g.σ ts 32 pt }
    let g₂ : Ghost := { g₁ with σ := TR.FreshSigma.updateFreshAt g₁.σ (ts + 1) coins.length coins }
    gamma' interpretation S (setSendAddr g₂ ts addr) b = gamma' interpretation S g b := by
  intro g₁ g₂
  have h1 : TR.FreshSigma.StampsLt interpretation S g₁ ts b :=
    TR.FreshSigma.stampsLt_updateFreshAt_iff h
  have h1' : TR.FreshSigma.StampsLt interpretation S g₁ (ts + 1) b :=
    TR.FreshSigma.stampsLt_mono (Nat.le_succ ts) h1
  have h2_ts : TR.FreshSigma.StampsLt interpretation S g₂ ts b := by
    unfold TR.FreshSigma.StampsLt
    rw [TR.FreshSigma.gamma'_updateFreshAt_of_stampsLt interpretation S g₁ (ts + 1) coins.length coins b h1']
    exact h1
  rw [gamma'_setSendAddr_of_stampsLt interpretation S g₂ ts addr b h2_ts,
      TR.FreshSigma.gamma'_updateFreshAt_of_stampsLt interpretation S g₁ (ts + 1) coins.length coins b h1',
      TR.FreshSigma.gamma'_updateFreshAt_of_stampsLt interpretation S g ts 32 pt b h]

theorem gamma_sendGhost_of_stampsLt {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {pt coins : HwBytes} {b : DY.Bytes}
    (h : TR.FreshSigma.StampsLt interpretation S g ts b) :
    gamma interpretation S (sendGhost g ts pt coins) b = gamma interpretation S g b :=
  congrArg ConcretizedTerm.bytes (gamma'_setSendAddr_updateFreshAt₂_of_stampsLt (pt := pt) (coins := coins) (addr := []) h)

theorem gamma_sendPendingGhost_of_stampsLt {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {pt coins : HwBytes} {b : DY.Bytes}
    (h : TR.FreshSigma.StampsLt interpretation S g ts b) :
    gamma interpretation S (sendPendingGhost g ts pt coins) b = gamma interpretation S g b :=
  congrArg ConcretizedTerm.bytes
    (gamma'_setSendAddr_updateFreshAt₂_of_stampsLt
      (pt := pt) (coins := coins) (addr := pqHarnessAddrBytes) h)

theorem gamma_sendGhost_coins_all (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    gamma interpretation S (sendGhost g ts pt coins) (randTerm (ts + 1) coins.length) = coins := by
  cases coins with
  | nil =>
    unfold gamma gamma' randTerm
    rw [DY.Bytes.rec_eq (concretizeRandom (sendGhost g ts pt [])) (concretizeAll interpretation S (sendGhost g ts pt []))]
    rfl
  | cons b tl =>
    exact gamma_sendGhost_coins interpretation S g ts pt (b :: tl) (by simp)

theorem snd_stateRel_keyShape_sendGhost {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {st : TripleRatchet.TRState} {pt coins : HwBytes} {rec : RecordRec}
    (hst_lt : TR.FreshSigma.StateStampsLt interpretation S g ts st)
    (hrel : TR.StateRel interpretation S g st rec)
    (hks : TR.TRKeyShape interpretation S g st) :
    TR.StateRel interpretation S (sendGhost g ts pt coins) st rec ∧
      TR.TRKeyShape interpretation S (sendGhost g ts pt coins) st := by
  rcases hst_lt with ⟨hmy, hpeer, hrk, hdhs, hcks, hspqr, hrecv⟩
  refine ⟨⟨hrel.1, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine hrel.2.trans (?_ :
      TR.sessionOf interpretation (gamma interpretation S (sendGhost g ts pt coins)) st =
        TR.sessionOf interpretation (gamma interpretation S g) st).symm
    unfold TR.sessionOf
    dsimp only
    rw [gamma_sendGhost_of_stampsLt hdhs, gamma_sendGhost_of_stampsLt hmy,
        gamma_sendGhost_of_stampsLt hpeer, gamma_sendGhost_of_stampsLt hrk,
        gamma_sendGhost_of_stampsLt hcks, gamma_sendGhost_of_stampsLt hspqr]
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [gamma_sendGhost_of_stampsLt (hrecv c hc).1, gamma_sendGhost_of_stampsLt (hrecv c hc).2]
  · rw [gamma_sendGhost_of_stampsLt hdhs]; exact hks.dhs_len
  · rw [gamma_sendGhost_of_stampsLt hcks]; exact hks.cks_len
  · rw [gamma_sendGhost_of_stampsLt hmy]; exact hks.myIk_ser
  · rw [gamma_sendGhost_of_stampsLt hpeer]; exact hks.peerIk_ser

theorem snd_stateRel_encSt_of_sendGhost {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts cLen : Nat} {st : TripleRatchet.TRState} {pt coins : HwBytes} {rec' : RecordRec}
    (hst_lt : TR.FreshSigma.StateStampsLt interpretation S g ts st)
    (hcoins : gamma interpretation S g (randTerm (ts + 1) cLen) = coins)
    (hrel' : TR.StateRel interpretation S (sendGhost g ts pt coins)
      (encSt st coins.length ts) rec') :
    TR.StateRel interpretation S g (encSt st cLen ts) rec' := by
  let g' := sendGhost g ts pt coins
  rcases hst_lt with ⟨hmy, hpeer, hrk, hdhs, hcks, hspqr, hrecv⟩
  have hcks' : gamma interpretation S g' (TripleRatchet.kdfCk st.cks).1 =
      gamma interpretation S g (TripleRatchet.kdfCk st.cks).1 :=
    gamma_sendGhost_of_stampsLt (TR.FreshSigma.stampsLt_kdfCk hcks).1
  have hspqr' : gamma interpretation S g' (DY.Spqr.spqrSend st.spqr (randTerm (ts + 1) coins.length)).1 =
      gamma interpretation S g (DY.Spqr.spqrSend st.spqr (randTerm (ts + 1) cLen)).1 := by
    have hspqr_eq := gamma_sendGhost_of_stampsLt (pt := pt) (coins := coins) hspqr
    have hc_eq : gamma interpretation S g' (randTerm (ts + 1) coins.length) =
        gamma interpretation S g (randTerm (ts + 1) cLen) := by
      rw [gamma_sendGhost_coins_all, hcoins]
    unfold DY.Spqr.spqrSend; dsimp only
    rw [TR.SendRetCoinsCliPure.gamma_spqrSendState, TR.SendRetCoinsCliPure.gamma_spqrSendState, hspqr_eq, hc_eq]
  refine ⟨hrel'.1, hrel'.2.trans ?_⟩
  unfold TR.sessionOf encSt; dsimp only
  rw [gamma_sendGhost_of_stampsLt hdhs, gamma_sendGhost_of_stampsLt hmy,
      gamma_sendGhost_of_stampsLt hpeer, gamma_sendGhost_of_stampsLt hrk,
      hcks', hspqr']
  congr 1; apply List.map_congr_left; intro c hc
  rw [gamma_sendGhost_of_stampsLt (hrecv c hc).1, gamma_sendGhost_of_stampsLt (hrecv c hc).2]

theorem isCurrentSnapshot_lt_false {tr : ExecTrace} {p : Participant} {st₁ st₂ : TripleRatchet.TRState}
    {i₁ i₂ : Nat} (hlt : i₁ < i₂) (ht₁ : (tr.at? i₁ : Option XplStEntry) = some ⟨⟨p, st₁⟩⟩)
    (ht₂ : (tr.at? i₂ : Option XplStEntry) = some ⟨⟨p, st₂⟩⟩)
    (hcur₁ : TripleRatchet.isCurrentSnapshot tr i₁ = true) (hinit : st₁.initiator = st₂.initiator) :
    False := by
  have hi₂_lt : i₂ < tr.length := by
    have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := XplStEntry) tr i₂
    rw [ht₂] at h; exact h
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur₁; rw [ht₁] at hcur₁; dsimp only at hcur₁
  have hmem : i₂ ∈ List.range' (i₁ + 1) (tr.length - (i₁ + 1)) := by rw [List.mem_range'_1]; omega
  have hall := List.all_eq_true.mp hcur₁ i₂ hmem; rw [ht₂] at hall; simp [hinit] at hall

theorem isCurrentSnapshot_unique_of_role {r : ProtocolSetup} {tr : ExecTrace} {p : Participant}
    {st₁ st₂ : TripleRatchet.TRState} {i₁ i₂ : Nat} (hrole : RoleSnapshots r tr)
    (hst₁ : ((PersistentLocalState.getLocalState p i₁ : Traceful TripleRatchet.TRState).run tr).1 = some st₁)
    (hst₂ : ((PersistentLocalState.getLocalState p i₂ : Traceful TripleRatchet.TRState).run tr).1 = some st₂)
    (hcur₁ : TripleRatchet.isCurrentSnapshot tr i₁ = true)
    (hcur₂ : TripleRatchet.isCurrentSnapshot tr i₂ = true) : i₁ = i₂ ∧ st₁ = st₂ := by
  have ht₁ := TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₁
  have ht₂ := TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₂
  have hinit : st₁.initiator = st₂.initiator := (hrole p st₁ i₁ ht₁).trans (hrole p st₂ i₂ ht₂).symm
  have hi : i₁ = i₂ := by
    rcases Nat.lt_trichotomy i₁ i₂ with hlt | heq | hgt
    · exact False.elim (isCurrentSnapshot_lt_false hlt ht₁ ht₂ hcur₁ hinit)
    · exact heq
    · exact False.elim (isCurrentSnapshot_lt_false hgt ht₂ ht₁ hcur₂ hinit.symm)
  subst hi; rw [hst₁, Option.some.injEq] at hst₂; exact ⟨rfl, hst₂⟩

theorem snd_isCurrentSnapshot_of_encrypt {r : ProtocolSetup} {ms₀ pre post : List Move}
    {p : Participant} {stateIdx cLen : Nat} {wrap : Option (Nat × Nat)}
    {st : TripleRatchet.TRState}
    (hreach : (runTraceMoves r
      (ms₀ ++ (pre ++ .encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post))).Reachable
        reachability)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r (ms₀ ++ pre))).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    TripleRatchet.isCurrentSnapshot (runTraceMoves r (ms₀ ++ pre)) stateIdx = true := by
  set tr₁ := runTraceMoves r (ms₀ ++ pre)
  let tr₂ := encTr tr₁ p stateIdx cLen st
  let tr₃ := runTraceMoves r (ms₀ ++ (pre ++ .encrypt p stateIdx cLen (tr₁.length + 2) wrap :: post))
  have hnext_wrap : (Move.encrypt p stateIdx cLen (tr₁.length + 2) wrap).next tr₁ = tr₂ :=
    encrypt_wrap_next_of_some (wrap := wrap) hst hns
  have htr₃_eq : tr₃ = (runMoves post tr₂).1 := by
    dsimp only [tr₃]
    rw [show ms₀ ++ (pre ++ .encrypt p stateIdx cLen (tr₁.length + 2) wrap :: post) =
        ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen (tr₁.length + 2) wrap]) ++ post by simp,
      runTrace_append, TR.runTrace_snoc]
    change (runMoves post ((Move.encrypt p stateIdx cLen (tr₁.length + 2) wrap).next tr₁)).1 = _
    rw [hnext_wrap]
  have hle₂₃ : tr₂ ≤ tr₃ := by rw [htr₃_eq]; exact runMoves_le post tr₂
  have ht₁ : (tr₁.at? stateIdx : Option XplStEntry) = some ⟨⟨p, st⟩⟩ :=
    TR.FreshSigma.at?_eq_some_of_getLocalState_some hst
  have hst_lt : stateIdx < tr₁.length := by
    have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := XplStEntry) tr₁ stateIdx
    rw [ht₁] at h; exact h
  have ht₂ : (tr₂.at? stateIdx : Option XplStEntry) = some ⟨⟨p, st⟩⟩ := by
    dsimp only [tr₂]; rw [at?_encTr_of_lt _ _ _ _ _ hst_lt]; exact ht₁
  have ht₃ : (tr₃.at? stateIdx : Option XplStEntry) = some ⟨⟨p, st⟩⟩ :=
    Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle₂₃ ht₂
  let ev₀ := TripleRatchet.TREvent.MessageKey (st.sessionInfo p) .sender
    (TripleRatchet.kdfCk st.cks).2 (DY.Spqr.spqrSend st.spqr (randTerm (tr₁.length + 1) cLen)).2.1
    st.ns st.rIdx stateIdx
  have hev₂ : (tr₂.at? (tr₁.length + 4) : Option XplEvEntry) = some ⟨ev₀⟩ := by
    dsimp only [tr₂, encTr]
    rw [TR.RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        TR.RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        at?_append_eq_some _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])]
  have hev₃ : (tr₃.at? (tr₁.length + 4) : Option XplEvEntry) = some ⟨ev₀⟩ :=
    Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle₂₃ hev₂
  obtain ⟨_, _, hbetween⟩ := snapshotChain_of_reachable hreach hev₃ rfl ht₃
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]; rw [ht₁]; dsimp only; rw [List.all_eq_true]
  intro j hj; rw [List.mem_range'_1] at hj
  rcases hj₁ : (tr₁.at? j : Option XplStEntry) with _ | e''
  · rfl
  · have hj₂ : (tr₂.at? j : Option XplStEntry) = some e'' := by
      dsimp only [tr₂]; rw [at?_encTr_of_lt _ _ _ _ _ (by omega : j < tr₁.length)]; exact hj₁
    exact hbetween j (by omega) (by omega) e''
      (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle₂₃ hj₂)

theorem snd_callCount_of_forall₂ {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {τ : List MachineEvent} {vis : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) τ vis) :
    callCount vis = (callStarts τ).length := by
  induction h with
  | nil => rfl
  | @cons hw ev τ vis hrel _ ih =>
    have hk : ev.kind = eventKind hw := hrel.1.symm
    unfold callCount callStarts at ih ⊢; simp only [List.filter_cons, hk]; split <;> simp [ih]

theorem snd_invisible_runMoves {tr : ExecTrace} {ms : List Move}
    (h : MovesFrom InvisibleNoEffect tr ms) :
    (runMoves ms tr).2 = [] ∧ visActorsFrom ms tr = [] := by
  induction ms generalizing tr with
  | nil => exact ⟨rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨⟨hvis, _⟩, hms⟩ := h; obtain ⟨hrun, hact⟩ := ih hms
    exact ⟨by simp [runMoves, hvis, hrun], by simp [visActorsFrom, hvis, hact]⟩

theorem snd_moveActor_eq_party {m : Move} (h : ¬ LeakKind m) : moveActor m = m.party? := by
  cases m <;> first | rfl | exact False.elim (h trivial)

theorem snd_deltaFaithful_of_roleFaithful
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ δ : List Move} {acc tail : List MachineEvent} {p : Participant} {pt : HwBytes}
    (hB : XplBlock interpretation r S who g ms₀ δ acc (.pt pt :: tail))
    (htail : ∀ e ∈ tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak)
    (hrf : RoleFaithful r who (ms₀ ++ δ)) (hwho : who[(callStarts acc).length]? = some p) :
    DeltaFaithful p (runTraceMoves r ms₀) δ := by
  obtain ⟨pre, m, post, hδ, hpre, ⟨_, _, hm_rel⟩, hpost⟩ :=
    xpl_oneMove hB (snd_fail_blockHead pt tail) (List.cons_ne_nil _ _) htail
  subst hδ
  obtain ⟨hpre_vis, hpre_act⟩ := snd_invisible_runMoves hpre
  obtain ⟨_, hpost_act⟩ := snd_invisible_runMoves hpost
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm_rel (List.head?_cons ..)
  have hsk : SendKind m := by
    rcases xpl_vis_kind m _ hv with h | ⟨h, _⟩ | ⟨_, h⟩
    · rw [hvk] at h; cases h
    · exact h
    · rw [hvk] at h; rcases h with h | h | h <;> cases h
  have hnot_leak : ¬ LeakKind m := by cases m <;> first | exact not_false | cases hsk
  have hidx : (ms₀ ++ (pre ++ m :: post))[ms₀.length + pre.length]? = some m := by
    rw [← List.append_assoc, ← List.length_append, List.getElem?_append_right (Nat.le_refl _)]; simp
  have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
    rw [← List.append_assoc, ← List.length_append, List.take_left]
  have hcc : callCount (runVis r (ms₀ ++ pre)) = (callStarts acc).length := by
    rw [runVis_append, hpre_vis, List.append_nil]; exact snd_callCount_of_forall₂ hB.pre.2.2.2.2.2
  unfold DeltaFaithful; rw [visActorsFrom_append, hpre_act, List.nil_append]
  simp only [visActorsFrom, hpost_act, List.append_nil]
  intro a ha; obtain ⟨_, rfl⟩ := List.mem_replicate.mp ha
  cases hact : moveActor m with
  | none => exact Or.inl rfl
  | some q =>
    have hparty : m.party? = some q := by rw [← snd_moveActor_eq_party hnot_leak, hact]
    have hrf_m := hrf (ms₀.length + pre.length) m q hidx hparty
    rw [htake, hcc, hwho] at hrf_m
    exact Or.inr (Or.inr (congrArg some (Option.some.inj hrf_m).symm))

theorem snd_recordBytes_ne_nil (rec : RecordRec) : recordBytes rec ≠ [] := by
  unfold recordBytes msgField DY.Libsignal.Refinement.encodeField
  have hl : DY.Libsignal.Refinement.paddedVarint (1 * 8 + 2) 0 = [BitVec.ofNat 8 (1 * 8 + 2)] := by
    rw [DY.Libsignal.Refinement.paddedVarint]; simp
  rw [hl]; simp

theorem snd_frame_bobDoneBaseKeys {r : ProtocolSetup} {ms₀ pre post : List Move}
    {p : Participant} {stateIdx cLen : Nat} {wrap : Option (Nat × Nat)}
    {st : TripleRatchet.TRState}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r (ms₀ ++ pre))).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap).next
        (runTraceMoves r (ms₀ ++ pre))) post) :
    bobDoneBaseKeys
      (runTraceMoves r (ms₀ ++ (pre ++ .encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post))) =
      bobDoneBaseKeys (runTraceMoves r ms₀) := by
  have hq1 : XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hpost' : MovesFrom InvisibleNoEffect
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap])) post := by
    rwa [TR.runTrace_snoc]
  have hq2 : XplQuiet.QuietExt
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]))
      (runTraceMoves r (((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post)) := by
    rw [TR.runTrace_append r _ post]
    exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost')
  rw [show ms₀ ++ (pre ++ .encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post) =
      ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post by simp,
    XplQuiet.quiet_bobDoneBaseKeys hq2,
    bobDoneBaseKeys_snoc_encrypt_wrap hst hns,
    XplQuiet.quiet_bobDoneBaseKeys hq1]

theorem ns_ne_u32Max_of_trNsBound {r₀ : ProtocolSetup} {ms₀ : List Move} {sent : List HwBytes}
    {p : Participant} {stateIdx₀ : Nat} {st₀ : TripleRatchet.TRState}
    (hnsBound : TR.TRNsBound r₀ ms₀ sent)
    (hsent_lt : sent.length < 2 ^ 32 - 1)
    (hst₀ : ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TripleRatchet.TRState).run
      (runTraceMoves r₀ ms₀)).1 = some st₀) :
    st₀.ns ≠ TripleRatchet.u32Max := by
  have hb := hnsBound p stateIdx₀ st₀ hst₀
  intro heq
  rw [heq] at hb
  simp [TripleRatchet.u32Max] at hb
  omega

theorem snd_frame_other {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre post : List Move}
    {p q : Participant} {stateIdx cLen : Nat} {wrap : Option (Nat × Nat)}
    {st : TripleRatchet.TRState} {b : HwBytes}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r (ms₀ ++ pre))).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap).next
        (runTraceMoves r (ms₀ ++ pre))) post)
    (hqp : q ≠ p)
    (hc₀ : PureCRecRel interpretation r S g ms₀ q b) :
    PureCRecRel interpretation r S g
      (ms₀ ++ (pre ++ .encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post))
      q b := by
  have hq1 : XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hc₁ : PureCRecRel interpretation r S g (ms₀ ++ pre) q b :=
    XplQuiet.quiet_pureCRecRel hq1 hc₀
  have htr_enc : runTraceMoves r
      ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) =
      encTr (runTraceMoves r (ms₀ ++ pre)) p stateIdx cLen st := by
    rw [TR.runTrace_snoc, encrypt_wrap_next_of_some (wrap := wrap) hst hns]
  have hc₂ : PureCRecRel interpretation r S g
      ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap])
      q b := by
    rcases hc₁ with hinv₁ | ⟨rfl, hpend₁⟩
    · refine Or.inl fun x bx hxb => ?_
      by_cases hxq : x = q
      · subst x
        simp only [↓reduceIte, Option.some.injEq] at hxb
        subst hxb
        obtain ⟨hq_mem, rec_q, st_q, stateIdx_q, hb, hst_q, hcur_q, hrel_q, hsk_q,
          hcanon_q, hks_q, hnd_q⟩ := hinv₁ q b (by simp)
        have ht_q := TR.FreshSigma.at?_eq_some_of_getLocalState_some hst_q
        have hlt_q : stateIdx_q < (runTraceMoves r (ms₀ ++ pre)).length := by
          have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := StEntry)
            (runTraceMoves r (ms₀ ++ pre)) stateIdx_q
          rw [ht_q] at h; exact h
        refine ⟨hq_mem, rec_q, st_q, stateIdx_q, hb,
          by rw [htr_enc, getLocalState_fst_encTr_of_lt _ _ _ _ _ _ hlt_q]; exact hst_q,
          by rw [htr_enc]; exact isCurrentSnapshot_encTr_of_ne _ p q stateIdx cLen st st_q
              stateIdx_q hqp ht_q hcur_q,
          hrel_q, ?_, hcanon_q, hks_q, hnd_q⟩
        intro c hc k hk
        obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam⟩ := hsk_q c hc k hk
        have hsk_lt : skIdx < (runTraceMoves r (ms₀ ++ pre)).length := by
          have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := TREntry)
            (runTraceMoves r (ms₀ ++ pre)) skIdx
          have hlog' := hlog
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
          rw [hlog'] at h; exact h
        exact ⟨pk, rIdx, srcIdx, skIdx, seed,
          by rw [htr_enc, eventLoggedAt_encTr_of_lt _ _ _ _ _ hsk_lt]; exact hlog,
          by rw [htr_enc, skippedKeyUsedB_encTr]; exact hsu,
          by rw [htr_enc, receiverKeyUsedB_encTr]; exact hru,
          hgam⟩
      · simp [hxq] at hxb
    · refine Or.inr ⟨rfl, ?_⟩
      obtain ⟨sess, sc, remote, items, kpk, st_q, stateIdx_q, ekIdx, ctIdx, ek, ct,
        hrc, hs1, hs2, hget_q, hcur_q, hinit_q, hpeer_q, hek, hct, hrest⟩ := hpend₁
      have ht_q := TR.FreshSigma.at?_eq_some_of_getLocalState_some hget_q
      have hlt_q : stateIdx_q < (runTraceMoves r (ms₀ ++ pre)).length := by
        have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := StEntry)
          (runTraceMoves r (ms₀ ++ pre)) stateIdx_q
        rw [ht_q] at h; exact h
      have hek_lt : ekIdx < (runTraceMoves r (ms₀ ++ pre)).length := by
        simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hek
        rcases hat : ((runTraceMoves r (ms₀ ++ pre)).at? ekIdx : Option DY.Network.ExecEntryT) with _ | ⟨m⟩
        · rw [hat] at hek; cases hek
        · have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := DY.Network.ExecEntryT)
            (runTraceMoves r (ms₀ ++ pre)) ekIdx
          rw [hat] at h; exact h
      have hct_lt : ctIdx < (runTraceMoves r (ms₀ ++ pre)).length := by
        simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hct
        rcases hat : ((runTraceMoves r (ms₀ ++ pre)).at? ctIdx : Option DY.Network.ExecEntryT) with _ | ⟨m⟩
        · rw [hat] at hct; cases hct
        · have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := DY.Network.ExecEntryT)
            (runTraceMoves r (ms₀ ++ pre)) ctIdx
          rw [hat] at h; exact h
      refine ⟨sess, sc, remote, items, kpk, st_q, stateIdx_q, ekIdx, ctIdx, ek, ct,
        hrc, hs1, hs2,
        by rw [htr_enc, getLocalState_fst_encTr_of_lt _ _ _ _ _ _ hlt_q]; exact hget_q,
        by rw [htr_enc]; exact isCurrentSnapshot_encTr_of_ne _ p r.alice stateIdx cLen st st_q
            stateIdx_q hqp ht_q hcur_q,
        hinit_q, hpeer_q, ?_, ?_, hrest⟩
      · simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hek ⊢
        rw [htr_enc, at?_encTr_of_lt _ _ _ _ _ hek_lt]
        exact hek
      · simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hct ⊢
        rw [htr_enc, at?_encTr_of_lt _ _ _ _ _ hct_lt]
        exact hct
  have hpost' : MovesFrom InvisibleNoEffect
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]))
      post := by
    rwa [TR.runTrace_snoc]
  have hq2 : XplQuiet.QuietExt
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]))
      (runTraceMoves r (((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post)) := by
    rw [TR.runTrace_append r _ post]
    exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost')
  have hc₃ := XplQuiet.quiet_pureCRecRel hq2 hc₂
  rwa [show ms₀ ++ (pre ++ .encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post) =
    ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post by simp]

theorem clean_sendGhost {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} (pt coins : HwBytes)
    (hc : Clean interpretation r S who ok g ms τ) :
    Clean interpretation r S who ok (sendGhost g (runTraceMoves r ms).length pt coins) ms τ := by
  have hga : CBadGammaAgree interpretation S g
      (sendGhost g (runTraceMoves r ms).length pt coins) (runTraceMoves r ms).length :=
    fun _ hb => gamma'_setSendAddr_updateFreshAt₂_of_stampsLt
      (pt := pt) (coins := coins) (addr := []) hb
  refine ⟨⟨matchedPrefix_sendGhost hc.matched pt coins, hc.1.2⟩, fun hd => ?_⟩
  exact hc.not_readCollision (cbadG2_readCollision_transfer_back hga
    (cbadG2_stamps_of_matched_take hc.matched (Nat.le_refl _)) hd)

theorem clean_sendPendingGhost {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} (pt coins : HwBytes)
    (hc : Clean interpretation r S who ok g ms τ) :
    Clean interpretation r S who ok (sendPendingGhost g (runTraceMoves r ms).length pt coins) ms τ := by
  have hga : CBadGammaAgree interpretation S g
      (sendPendingGhost g (runTraceMoves r ms).length pt coins) (runTraceMoves r ms).length :=
    fun _ hb => gamma'_setSendAddr_updateFreshAt₂_of_stampsLt
      (pt := pt) (coins := coins) (addr := pqHarnessAddrBytes) hb
  refine ⟨⟨matchedPrefix_sendPendingGhost hc.matched pt coins, hc.1.2⟩, fun hd => ?_⟩
  exact hc.not_readCollision (cbadG2_readCollision_transfer_back hga
    (cbadG2_stamps_of_matched_take hc.matched (Nat.le_refl _)) hd)

theorem snd_not_readColMove_encryptAbort {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {p : Participant} {stateIdx : Nat}
    (pre : List Move) (e : MachineEvent) :
    ¬ MoveReadsCollidingMsg interpretation r S g pre e (.encryptAbort p stateIdx) := by
  rw [MoveReadsCollidingMsg.iff_rcvMoveTerm]
  rintro ⟨_, _, _, h, _⟩
  cases h

theorem snd_not_readColMove_encrypt {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {p : Participant} {stateIdx cLen pqIdx : Nat}
    {wrap : Option (Nat × Nat)} (pre : List Move) (e : MachineEvent) :
    ¬ MoveReadsCollidingMsg interpretation r S g pre e (.encrypt p stateIdx cLen pqIdx wrap) := by
  rw [MoveReadsCollidingMsg.iff_rcvMoveTerm]
  rintro ⟨_, _, _, h, _⟩
  cases h

theorem snd_clean_snoc {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {pt : HwBytes} {τ evs : List MachineEvent}
    (hc : Clean interpretation r₀ S who ok g ms τ)
    (hrun : ModelRun r₀ (ms ++ [m]))
    (hparty : m.party? = some p)
    (hwho : who[(callStarts τ).length]? = some p)
    (hpath_none : m.prekeyPath? = none)
    (hnot_rej : ∀ ds, m ≠ .reject ds)
    (hno_alice : (eventIdx isAliceDone (runTraceMoves r₀ ms) (m.next (runTraceMoves r₀ ms))).isSome = false)
    (hcs : callStarts evs = [.pt pt])
    (hnorecv : ∀ v ∈ m.vis (runTraceMoves r₀ ms), v.kind ≠ .recv)
    (hnoAcc : ∀ e ∈ evs, ∀ q, e ≠ .accept q)
    (hnoCol : ∀ pre e, ¬ MoveReadsCollidingMsg interpretation r₀ S g pre e m)
    (hevs : List.Forall₂ (EventMatchesEntry interpretation r₀ S g) evs
      (m.vis (runTraceMoves r₀ ms))) :
    Clean interpretation r₀ S who ok g (ms ++ [m]) (τ ++ evs) := by
  refine ⟨explains_snoc_send hc.matched hc.1.2 hrun hparty hwho hpath_none hnot_rej
      hno_alice hcs hnorecv hevs,
    not_readCollision_append_noAccept hc.not_readCollision hnoAcc ?_⟩
  intro m' hm' pre e
  simp only [List.mem_singleton] at hm'
  subst hm'
  exact hnoCol pre e

end Symbolic.Swarm.CREF.CliPure.SndPure
