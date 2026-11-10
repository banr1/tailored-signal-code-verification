/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all DY.ALaCarte.Basic
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.CBad
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Sticky
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet

/-!
# Suffix Two-Cut Reduction and Collision Reselection

Proves the two-cut characterization of `ModelAcceptsTermAfterAttackerSendsMoves` on accepted
32-byte `.recv` suffixes (`acceptsViaCli_iff_two_mids`) and reselection combinators under
`¬ CollisionAfterExplainedPrefixMoves`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.P3

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg RecvChain KeyDir
  parseTrSignalMsg recvChainFor ensureReceiverChain
  consumeMessageKey verifyMacAndDecrypt logSkippedKeys logMessageKeyAndStore
  messageDecrypt messageDecryptSkipped receiveSignalMsg setRecvChain kdfCk)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF.TR.FreshSigma

section UnsealedRand
unseal DY.Bytes

private theorem gamma_updateFreshAt_randTerm_32 (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g₁ : Ghost) (idx : Nat) (coins : HwBytes) :
    gamma interp S { g₁ with σ := updateFreshAt g₁.σ idx 32 coins } (randTerm idx 32) = coins := by
  let g₂ : Ghost := { g₁ with σ := updateFreshAt g₁.σ idx 32 coins }
  change gamma interp S g₂ (randTerm idx 32) = coins
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g₂) (concretizeAll interp S g₂)]
  simp [g₂, concretizeRandom, node, updateFreshAt]

end UnsealedRand

private theorem getElem?_map_rng_accept_eq_accept {pieces : List HwBytes} {pt pt' : HwBytes} {k : Nat}
    (hk : (pieces.map MachineEvent.rng ++ [MachineEvent.accept pt])[k]? = some (.accept pt')) :
    k = pieces.length ∧ pt' = pt := by
  rcases Nat.lt_trichotomy k pieces.length with hlt | rfl | hgt
  · rw [List.getElem?_append_left (by simp [hlt]), List.getElem?_map] at hk
    rcases pieces[k]? with _ | q <;> simp at hk
  · rw [List.getElem?_append_right (by simp)] at hk
    simp at hk
    exact ⟨rfl, hk.symm⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at hk
    cases hk

private theorem forall₂_snoc_inv {α β : Type} {R : α → β → Prop} {xs : List α} {x : α}
    {ys : List β} {y : β} (h : List.Forall₂ R (xs ++ [x]) (ys ++ [y])) :
    List.Forall₂ R xs ys ∧ R x y := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      cases h with
      | cons hxy hnil => cases hnil; exact ⟨.nil, hxy⟩
    | cons _ _ =>
      cases h with
      | cons _ htl => have := htl.length_eq; simp at this
  | cons a xs ih =>
    cases ys with
    | nil =>
      cases h with
      | cons _ htl => have := htl.length_eq; simp at this
    | cons b ys =>
      cases h with
      | cons hab htl =>
        obtain ⟨h1, h2⟩ := ih htl
        exact ⟨.cons hab h1, h2⟩

private theorem snoc_of_ne_nil {α : Type} :
    ∀ (l : List α), l ≠ [] → ∃ (init : List α) (last : α), l = init ++ [last] ∧ last ∈ l
  | [], h => absurd rfl h
  | [x], _ => ⟨[], x, rfl, List.mem_singleton.mpr rfl⟩
  | a :: b :: rest, _ => by
    obtain ⟨init, last, h_eq, h_mem⟩ := snoc_of_ne_nil (b :: rest) (by simp)
    exact ⟨a :: init, last, by simp [h_eq], List.mem_cons_of_mem a h_mem⟩

private theorem p3_run_bind_pure_val {α : Type} (m : Traceful α) (tr : ExecTrace) :
    (((m >>= fun _ => (pure () : Traceful Unit))).run tr).2.val = (m.run tr).2.val := by
  rw [DY.Traceful.run_bind]; rcases m.run tr with ⟨_ | _, _⟩ <;> rfl

private theorem p3_at?_append_lt {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Trace.append, Trace.length]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem p3_at?_append_length {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.append e).length := by simp [Trace.append, Trace.length]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Trace.append, Trace.at, ↓reduceDIte]

private theorem p3_at?_ge_length {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (hi : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have hnot : ¬ i < tr.length := Nat.not_lt.mpr hi
  simp only [Trace.at?, hnot, ↓reduceDIte]

private def NoNewRand {α : Type} (x : Traceful α) : Prop :=
  ∀ tr i, ((x.run tr).2.val.at? i : Option DY.Random.ExecEntryT) =
    (tr.at? i : Option DY.Random.ExecEntryT)

private theorem noNewRand_bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoNewRand x) (hf : ∀ a, NoNewRand (f a)) : NoNewRand (x >>= f) := by
  intro tr i
  rw [run_bind_snd]
  cases (x.run tr).1 with
  | none => exact hx tr i
  | some a => exact (hf a _ i).trans (hx tr i)

private theorem noNewRand_same {α : Type} {x : Traceful α}
    (h : ∀ tr, (x.run tr).2.val = tr) : NoNewRand x := by
  intro tr i; rw [h tr]

private theorem noNewRand_append_nonRand {E : Type} [ExecTraceTypes.Has E]
    (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option DY.Random.ExecEntryT) = none)
    (tr : ExecTrace) (i : Nat) :
    ((tr.append e).at? i : Option DY.Random.ExecEntryT) =
      (tr.at? i : Option DY.Random.ExecEntryT) := by
  rcases Nat.lt_trichotomy i tr.length with hlt | rfl | hgt
  · exact p3_at?_append_lt tr e hlt
  · rw [p3_at?_append_length, hproj, p3_at?_ge_length tr (Nat.le_refl _)]
  · rw [p3_at?_ge_length (tr.append e) (by change tr.length + 1 ≤ i; omega),
        p3_at?_ge_length tr (Nat.le_of_lt hgt)]

private theorem noNewRand_sendMessage (key : DY.Bytes) : NoNewRand (DY.Network.sendMessage key) :=
  fun tr i => noNewRand_append_nonRand (⟨key⟩ : DY.Network.ExecEntryT) rfl tr i

private theorem noNewRand_logEvent (ev : TREvent) : NoNewRand (DY.ProtocolEvent.logEvent ev) :=
  fun tr i => noNewRand_append_nonRand (⟨ev⟩ : TREntry) rfl tr i

private theorem noNewRand_logSkippedKeys {s : DY.Libsignal.TripleRatchet.SessionInfo}
    {pk : DY.Bytes} {rIdx stateIdx : Nat} :
    ∀ {ck : DY.Bytes} {idx : UInt32} {cnt : Nat}, NoNewRand (logSkippedKeys s pk rIdx stateIdx ck idx cnt)
  | _, _, 0 => noNewRand_same fun _ => rfl
  | ck, idx, cnt + 1 => by
    unfold logSkippedKeys
    refine noNewRand_bind (noNewRand_logEvent _) fun _ => ?_
    exact @noNewRand_logSkippedKeys s pk rIdx stateIdx (kdfCk ck).1 (idx + 1) cnt

private theorem noNewRand_logMessageKeyAndStore {me : Participant}
    {s : DY.Libsignal.TripleRatchet.SessionInfo} {dir : KeyDir}
    {seed pqSalt : DY.Bytes} {n : UInt32} {rIdx stateIdx : Nat} {st : TRState} :
    NoNewRand (logMessageKeyAndStore me s dir seed pqSalt n rIdx stateIdx st) := by
  unfold logMessageKeyAndStore
  refine noNewRand_bind (noNewRand_logEvent _) fun _ => ?_
  exact fun tr i => noNewRand_append_nonRand (⟨⟨me, st⟩⟩ : StEntry) rfl tr i

private theorem newRandoms_eq_nil_of_noNewRand {tr tr' : ExecTrace}
    (h : ∀ i, (tr'.at? i : Option DY.Random.ExecEntryT) = (tr.at? i : Option DY.Random.ExecEntryT)) :
    newRandoms tr tr' = [] := by
  unfold newRandoms
  refine List.filterMap_eq_nil_iff.mpr fun i hi => ?_
  simp only [newIndices, List.mem_range'_1] at hi
  rw [h i, p3_at?_ge_length tr hi.1]
  rfl

private theorem getLocalState_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((DY.PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr := by
  unfold DY.PersistentLocalState.getLocalState DY.PersistentGlobalState.getGlobalState
    DY.getEntry _root_.guard
  rw [run_bind_snd, run_bind_fst, run_bind_snd, DY.Traceful.run_mk]
  rcases (tr.at? stH : Option StEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).2.val = tr
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; rfl
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; rfl

private theorem receiveMessage_snd (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  unfold DY.Network.receiveMessage DY.getEntry
  rw [run_bind_snd, DY.Traceful.run_mk]
  rcases (tr.at? idx : Option DY.Network.ExecEntryT) with _ | ⟨t⟩ <;> rfl

private theorem receiveSignalMsg_snd (msgIdx : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgIdx).run tr).2.val = tr := by
  unfold receiveSignalMsg
  rw [run_bind_snd, receiveMessage_snd]
  rcases ((DY.Network.receiveMessage msgIdx).run tr).1 with _ | raw
  · rfl
  · dsimp only
    rcases parseTrSignalMsg raw with _ | msg
    · rfl
    · dsimp only
      by_cases hv : msg.version = DY.Libsignal.TripleRatchet.messageVersion <;>
        simp only [_root_.guard, hv, ↓reduceIte] <;> rfl

private theorem verifyMacAndDecrypt_snd {st : TRState} {msg : TRSignalMsg}
    {pqSalt seed : DY.Bytes} (tr : ExecTrace) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  unfold verifyMacAndDecrypt
  by_cases hm : msg.mac = DY.Libsignal.TripleRatchet.computeMac
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, run_bind_snd, DY.Traceful.run_pure]
    rcases DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext <;> rfl
  · simp only [_root_.guard, hm, ↓reduceIte]; rfl

private theorem getEntry_snd {E : Type} [ExecTraceTypes.Has E] (idx : Nat) (tr : ExecTrace) :
    ((DY.getEntry idx : Traceful E).run tr).2.val = tr := rfl

private theorem newRandoms_decryptSkipped_eq_nil (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool) (tr : ExecTrace) :
    newRandoms tr ((Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next tr) = [] := by
  apply newRandoms_eq_nil_of_noNewRand
  intro i
  unfold Move.next Move.act
  rw [p3_run_bind_pure_val]
  refine ( ?_ : NoNewRand (messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx)) tr i
  unfold messageDecryptSkipped
  refine noNewRand_bind (noNewRand_same (getLocalState_snd me stateIdx)) fun st => ?_
  refine noNewRand_bind (noNewRand_same (receiveSignalMsg_snd msgIdx)) fun msg => ?_
  refine noNewRand_bind (noNewRand_same (getEntry_snd skIdx)) fun e => ?_
  rcases e.ev with _ | _ | _ | _ | ⟨s, pk, n, seed, rIdx, srcIdx⟩ | _ | _
  all_goals try exact noNewRand_same fun _ => rfl
  dsimp only
  refine noNewRand_bind (noNewRand_same fun tr => by simp [_root_.guard]; split <;> rfl) fun _ => ?_
  refine noNewRand_bind (noNewRand_same fun tr => by
    unfold DY.Libsignal.TripleRatchet.guardTrace; simp [DY.Traceful.run_mk]) fun _ => ?_
  rcases DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · exact noNewRand_same fun _ => rfl
  · dsimp only
    refine noNewRand_bind (noNewRand_sendMessage key) fun _ => ?_
    refine noNewRand_bind (noNewRand_same (receiveMessage_snd pqIdx)) fun _ => ?_
    refine noNewRand_bind (noNewRand_same verifyMacAndDecrypt_snd) fun _ => ?_
    refine noNewRand_bind (noNewRand_logEvent _) fun _ => ?_
    refine noNewRand_bind (noNewRand_logEvent _) fun _ => ?_
    exact noNewRand_logMessageKeyAndStore

private def OnlyRecvValid (P : DY.Bytes → Prop) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr idx me peer rk n m,
    tr.length ≤ idx →
    (x.run tr).2.val.getEventAt TREvent idx = some (.Received me peer rk n m) → P m

private theorem onlyRecvValid_same {P : DY.Bytes → Prop} {α : Type} {x : Traceful α}
    (h : ∀ tr, (x.run tr).2.val = tr) : OnlyRecvValid P x := by
  intro tr idx _ _ _ _ _ hle hev
  rw [h tr] at hev
  unfold DY.Trace.getEventAt at hev
  rw [p3_at?_ge_length tr hle] at hev
  cases hev

private theorem onlyRecvValid_bind {P : DY.Bytes → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : OnlyRecvValid P x) (hf : ∀ a, OnlyRecvValid P (f a)) :
    OnlyRecvValid P (x >>= f) := by
  intro tr idx me peer rk n m hle hev
  rw [run_bind_snd] at hev
  cases h1 : (x.run tr).1 with
  | none =>
    rw [h1] at hev
    exact hx tr idx me peer rk n m hle hev
  | some a =>
    rw [h1] at hev
    dsimp only at hev
    by_cases hlt : idx < (x.run tr).2.val.length
    · have hle2 := ((f a).run (x.run tr).2.val).2.property
      have hlt2 : idx < ((f a).run (x.run tr).2.val).2.val.length :=
        Nat.lt_of_lt_of_le hlt (DY.Trace.length_le _ _ hle2)
      have hat : ((((f a).run (x.run tr).2.val).2.val).at? idx : Option TREntry) =
          (((x.run tr).2.val).at? idx : Option TREntry) := by
        simp only [DY.Trace.at?, hlt, hlt2, ↓reduceDIte]
        exact congrArg TraceEntryHas.proj
          (DY.Trace.at_le (x.run tr).2.val ((f a).run (x.run tr).2.val).2.val idx hlt hle2).symm
      have hev₁ : (x.run tr).2.val.getEventAt TREvent idx = some (.Received me peer rk n m) := by
        unfold DY.Trace.getEventAt at hev ⊢
        rwa [hat] at hev
      exact hx tr idx me peer rk n m hle hev₁
    · exact hf a (x.run tr).2.val idx me peer rk n m (Nat.not_lt.mp hlt) hev

private theorem onlyRecvValid_append_nonTREntry {P : DY.Bytes → Prop} {α : Type}
    {E : Type} [ExecTraceTypes.Has E] (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    {x : Traceful α} (hx : ∀ tr, (x.run tr).2.val = tr.append e) :
    OnlyRecvValid P x := by
  intro tr idx _ _ _ _ _ hle hev
  rw [hx tr] at hev
  unfold DY.Trace.getEventAt at hev
  rcases Nat.eq_or_lt_of_le hle with rfl | hgt
  · rw [p3_at?_append_length, hproj] at hev; cases hev
  · rw [p3_at?_ge_length (tr.append e) (by change tr.length + 1 ≤ idx; omega)] at hev
    cases hev

private theorem onlyRecvValid_logEvent_nonRecv {P : DY.Bytes → Prop} (ev : TREvent)
    (hnot : ∀ me peer rk n m, ev ≠ .Received me peer rk n m) :
    OnlyRecvValid P (DY.ProtocolEvent.logEvent ev) := by
  intro tr idx me peer rk n m hle hev
  change (tr.append (⟨ev⟩ : TREntry)).getEventAt TREvent idx = _ at hev
  unfold DY.Trace.getEventAt at hev
  rcases Nat.eq_or_lt_of_le hle with rfl | hgt
  · rw [p3_at?_append_length] at hev
    change some ev = some (.Received me peer rk n m) at hev
    injection hev with hev_eq
    exact absurd hev_eq (hnot me peer rk n m)
  · rw [p3_at?_ge_length (tr.append (⟨ev⟩ : TREntry)) (by change tr.length + 1 ≤ idx; omega)] at hev
    cases hev

private theorem onlyRecvValid_logEvent_recv {P : DY.Bytes → Prop}
    (me peer : Participant) (rk : DY.Bytes) (n : UInt32) (pt : DY.Bytes) (hpt : P pt) :
    OnlyRecvValid P (DY.ProtocolEvent.logEvent (TREvent.Received me peer rk n pt)) := by
  intro tr idx me' peer' rk' n' m hle hev
  change (tr.append (⟨TREvent.Received me peer rk n pt⟩ : TREntry)).getEventAt TREvent idx = _ at hev
  unfold DY.Trace.getEventAt at hev
  rcases Nat.eq_or_lt_of_le hle with rfl | hgt
  · rw [p3_at?_append_length] at hev
    change some (TREvent.Received me peer rk n pt) = some (.Received me' peer' rk' n' m) at hev
    injection hev with hev_eq
    injection hev_eq with _ _ _ _ hm_eq
    subst hm_eq
    exact hpt
  · rw [p3_at?_ge_length (tr.append _) (by change tr.length + 1 ≤ idx; omega)] at hev
    cases hev

private theorem onlyRecvValid_logSkippedKeys {P : DY.Bytes → Prop}
    {s : DY.Libsignal.TripleRatchet.SessionInfo}
    {pk : DY.Bytes} {rIdx stateIdx : Nat} :
    ∀ {ck : DY.Bytes} {idx : UInt32} {cnt : Nat}, OnlyRecvValid P (logSkippedKeys s pk rIdx stateIdx ck idx cnt)
  | _, _, 0 => onlyRecvValid_same fun _ => rfl
  | ck, idx, cnt + 1 => by
    unfold logSkippedKeys
    refine onlyRecvValid_bind (onlyRecvValid_logEvent_nonRecv _ fun _ _ _ _ _ h => by cases h) fun _ => ?_
    exact @onlyRecvValid_logSkippedKeys P s pk rIdx stateIdx (kdfCk ck).1 (idx + 1) cnt

private theorem onlyRecvValid_logMessageKeyAndStore {P : DY.Bytes → Prop}
    {me : Participant} {s : DY.Libsignal.TripleRatchet.SessionInfo} {dir : KeyDir}
    {seed pqSalt : DY.Bytes} {n : UInt32} {rIdx stateIdx : Nat} {st : TRState} :
    OnlyRecvValid P (logMessageKeyAndStore me s dir seed pqSalt n rIdx stateIdx st) := by
  unfold logMessageKeyAndStore
  refine onlyRecvValid_bind (onlyRecvValid_logEvent_nonRecv _ fun _ _ _ _ _ h => by cases h) fun _ => ?_
  exact onlyRecvValid_append_nonTREntry (⟨⟨me, st⟩⟩ : StEntry) rfl fun _ => rfl

private theorem onlyRecvValid_ensureReceiverChain {P : DY.Bytes → Prop}
    (st : TRState) (pk : DY.Bytes) : OnlyRecvValid P (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases recvChainFor st.toDRState pk with _ | ⟨c, b⟩
  · exact onlyRecvValid_same fun _ => rfl
  · cases b
    · exact onlyRecvValid_same fun _ => rfl
    · dsimp only
      refine onlyRecvValid_bind ?_ fun _ => onlyRecvValid_same fun _ => rfl
      rcases hlow : DY.Libsignal.TripleRatchet.x25519LowOrder pk with _ | _
      · refine onlyRecvValid_append_nonTREntry (⟨32⟩ : DY.Random.ExecEntryT) rfl fun tr => ?_
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
        have hg1 : ((_root_.guard (!DY.Libsignal.TripleRatchet.x25519LowOrder pk) : Traceful Unit).run tr).1 = some () := by
          simp [_root_.guard, hlow, DY.Traceful.run_pure]
        have hg2 : ((_root_.guard (!DY.Libsignal.TripleRatchet.x25519LowOrder pk) : Traceful Unit).run tr).2.val = tr := by
          simp [_root_.guard, hlow, DY.Traceful.run_pure]
        rw [run_bind_snd, hg1, hg2]; dsimp only
        have hr1 : ((DY.Random.genRand 32).run tr).1 = some (randTerm tr.length 32) := rfl
        have hr2 : ((DY.Random.genRand 32).run tr).2.val = tr.append (⟨32⟩ : DY.Random.ExecEntryT) := rfl
        rw [run_bind_snd, hr1, hr2]; rfl
      · refine onlyRecvValid_same fun tr => ?_
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
        have hg1 : ((_root_.guard (!DY.Libsignal.TripleRatchet.x25519LowOrder pk) : Traceful Unit).run tr).1 = none := by
          simp [_root_.guard, hlow]; rfl
        have hg2 : ((_root_.guard (!DY.Libsignal.TripleRatchet.x25519LowOrder pk) : Traceful Unit).run tr).2.val = tr := by
          simp [_root_.guard, hlow]; rfl
        rw [run_bind_snd, hg1, hg2]

private theorem onlyRecvValid_messageDecrypt_after_rcv (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace)
    (st : TRState) (msg : TRSignalMsg)
    (hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hrcv : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    {idx : Nat} {me' peer' : Participant} {rk' : DY.Bytes} {cnt' : UInt32} {ptTerm : DY.Bytes}
    (hle : tr.length ≤ idx)
    (hev : ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val.getEventAt TREvent idx =
      some (.Received me' peer' rk' cnt' ptTerm)) :
    ∃ k iv, DY.SymEnc.symDec k iv msg.ciphertext = some ptTerm := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hev
  rw [run_bind_snd, hst, getLocalState_snd] at hev; dsimp only at hev
  rw [run_bind_snd, hrcv, receiveSignalMsg_snd] at hev; dsimp only at hev
  refine ( ?_ : OnlyRecvValid (fun m => ∃ k iv, DY.SymEnc.symDec k iv msg.ciphertext = some m) _)
    tr idx me' peer' rk' cnt' ptTerm hle hev
  refine onlyRecvValid_bind (onlyRecvValid_ensureReceiverChain st msg.ratchetKey) fun x => ?_
  rcases x with ⟨st1, c1, rat⟩
  dsimp only
  rcases consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩
  · exact onlyRecvValid_same fun _ => rfl
  · dsimp only
    rcases DY.Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact onlyRecvValid_same fun _ => rfl
    · dsimp only
      refine onlyRecvValid_bind (onlyRecvValid_append_nonTREntry (⟨key⟩ : DY.Network.ExecEntryT) rfl fun _ => rfl) fun _ => ?_
      refine onlyRecvValid_bind (onlyRecvValid_same (receiveMessage_snd pqIdx)) fun pqSalt => ?_
      intro tr₂ idx₂ me₂ peer₂ rk₂ n₂ m₂ hle₂ hev₂
      rw [run_bind_snd] at hev₂
      rcases hvmd : ((verifyMacAndDecrypt st1 msg pqSalt seed).run tr₂).1 with _ | decPt
      · rw [hvmd] at hev₂
        exact (onlyRecvValid_same (P := fun m => ∃ k iv, DY.SymEnc.symDec k iv msg.ciphertext = some m)
          verifyMacAndDecrypt_snd) tr₂ idx₂ me₂ peer₂ rk₂ n₂ m₂ hle₂ hev₂
      · rw [hvmd, verifyMacAndDecrypt_snd] at hev₂; dsimp only at hev₂
        have hdec_pt : ∃ k iv, DY.SymEnc.symDec k iv msg.ciphertext = some decPt := by
          unfold verifyMacAndDecrypt at hvmd
          by_cases hmac : msg.mac = DY.Libsignal.TripleRatchet.computeMac
              (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st1.peerIk st1.myIk msg.wire
          · simp only [_root_.guard, hmac, ↓reduceIte, run_bind_fst, DY.Traceful.run_pure] at hvmd
            rcases hdec : DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
                (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext with _ | d
            · rw [hdec] at hvmd; cases hvmd
            · rw [hdec] at hvmd
              change some d = some decPt at hvmd
              injection hvmd with h_eq; subst h_eq
              exact ⟨_, _, hdec⟩
          · simp only [_root_.guard, hmac, ↓reduceIte] at hvmd; cases hvmd
        have htail : OnlyRecvValid (fun m => ∃ k iv, DY.SymEnc.symDec k iv msg.ciphertext = some m)
            (do logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c1.rIdx stateIdx c1.chainKey c1.index
                  (msg.counter.toNat - c1.index.toNat)
                DY.ProtocolEvent.logEvent (TREvent.Received me st1.peer msg.ratchetKey msg.counter decPt)
                logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt msg.counter c1.rIdx stateIdx { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }) :=
          onlyRecvValid_bind onlyRecvValid_logSkippedKeys fun _ =>
          onlyRecvValid_bind (onlyRecvValid_logEvent_recv _ _ _ _ decPt hdec_pt) fun _ =>
          onlyRecvValid_logMessageKeyAndStore
        by_cases hrat : rat = true
        · simp only [hrat, ↓reduceIte] at hev₂
          exact (onlyRecvValid_bind (onlyRecvValid_logEvent_nonRecv _ fun _ _ _ _ _ h => by cases h) fun _ =>
            onlyRecvValid_bind (onlyRecvValid_logEvent_nonRecv _ fun _ _ _ _ _ h => by cases h) fun _ => htail)
            tr₂ idx₂ me₂ peer₂ rk₂ n₂ m₂ hle₂ hev₂
        · simp only [hrat, Bool.false_eq_true, ↓reduceIte] at hev₂
          exact htail tr₂ idx₂ me₂ peer₂ rk₂ n₂ m₂ hle₂ hev₂

private theorem decrypt_ratchet_info {m : Move} {msgIdx : Nat} {tr : ExecTrace} {t ptTerm : DY.Bytes}
    (hm : m.decryptMsgIdx? = some msgIdx)
    (hmsg : tr.getMessageSentAt msgIdx = some t)
    (hnr_ne : newRandoms tr (m.next tr) ≠ [])
    (hpt : receivedPlaintext tr (m.next tr) = some ptTerm) :
    newRandoms tr (m.next tr) = [(randTerm tr.length 32, 32)] ∧
      ∃ msg k iv, parseTrSignalMsg t = some msg ∧
        DY.SymEnc.symDec k iv msg.ciphertext = some ptTerm := by
  cases m with
  | decryptSkipped me stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped =>
    exact absurd (newRandoms_decryptSkipped_eq_nil me stateIdx msgIdx' skIdx pqIdx spqrMsgIdx wrapped tr) hnr_ne
  | decrypt me stateIdx msgIdx' pqIdx spqrMsgIdx wrapped =>
    simp only [Move.decryptMsgIdx?, Option.some.injEq] at hm
    subst msgIdx'
    have hst_some : ∃ st, ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st := by
      rcases hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
      · exfalso; apply hnr_ne; apply newRandoms_eq_nil_of_noNewRand; intro i
        unfold Move.next Move.act
        rw [p3_run_bind_pure_val]
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
        rw [run_bind_snd, hst, getLocalState_snd]
      · exact ⟨st, rfl⟩
    obtain ⟨st, hst⟩ := hst_some
    have hrcv_some : ∃ msg, ((receiveSignalMsg msgIdx).run tr).1 = some msg := by
      rcases hrcv : ((receiveSignalMsg msgIdx).run tr).1 with _ | msg
      · exfalso; apply hnr_ne; apply newRandoms_eq_nil_of_noNewRand; intro i
        unfold Move.next Move.act
        rw [p3_run_bind_pure_val]
        simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
        rw [run_bind_snd, hst, getLocalState_snd]; dsimp only
        rw [run_bind_snd, hrcv, receiveSignalMsg_snd]
      · exact ⟨msg, rfl⟩
    obtain ⟨msg, hrcv⟩ := hrcv_some
    have hparse : parseTrSignalMsg t = some msg := by
      have hrcv0 := hrcv
      unfold receiveSignalMsg at hrcv0
      rw [run_bind_fst, receiveMessage_snd] at hrcv0
      have hrm : ((DY.Network.receiveMessage msgIdx).run tr).1 = tr.getMessageSentAt msgIdx := by
        unfold DY.Network.receiveMessage DY.getEntry Trace.getMessageSentAt
        rw [run_bind_fst, DY.Traceful.run_mk]
        dsimp only
        rcases (tr.at? msgIdx : Option DY.Network.ExecEntryT) <;> rfl
      rw [hrm, hmsg] at hrcv0
      dsimp only at hrcv0
      rcases hp : parseTrSignalMsg t with _ | msg0
      · rw [hp] at hrcv0; cases hrcv0
      · rw [hp] at hrcv0; dsimp only at hrcv0
        by_cases hv : msg0.version = DY.Libsignal.TripleRatchet.messageVersion
        · simp only [_root_.guard, hv, ↓reduceIte] at hrcv0
          change some msg0 = some msg at hrcv0
          injection hrcv0 with h_eq; subst h_eq; rfl
        · simp only [_root_.guard, hv, ↓reduceIte] at hrcv0; cases hrcv0
    have hrc_true : ∃ c, recvChainFor st.toDRState msg.ratchetKey = some (c, true) := by
      rcases hrc : recvChainFor st.toDRState msg.ratchetKey with _ | ⟨c, b⟩
      · exfalso; apply hnr_ne; apply newRandoms_eq_nil_of_noNewRand; intro i
        unfold Move.next Move.act
        rw [p3_run_bind_pure_val]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
        rw [run_bind_snd, hst, getLocalState_snd]; dsimp only
        rw [run_bind_snd, hrcv, receiveSignalMsg_snd]; dsimp only
        have hens : ((ensureReceiverChain st msg.ratchetKey).run tr).1 = none ∧
            ((ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
          simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; rw [hrc]; exact ⟨rfl, rfl⟩
        rw [run_bind_snd, hens.1, hens.2]
      · cases b
        · exfalso; apply hnr_ne; apply newRandoms_eq_nil_of_noNewRand; intro i
          unfold Move.next Move.act
          rw [p3_run_bind_pure_val]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
          rw [run_bind_snd, hst, getLocalState_snd]; dsimp only
          rw [run_bind_snd, hrcv, receiveSignalMsg_snd]; dsimp only
          have hens : ((ensureReceiverChain st msg.ratchetKey).run tr).1 = some (st, c, false) ∧
              ((ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
            simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; rw [hrc]; exact ⟨rfl, rfl⟩
          rw [run_bind_snd, hens.1, hens.2]; dsimp only
          rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
          · rfl
          · dsimp only
            rcases DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
            · rfl
            · dsimp only
              refine (noNewRand_bind (noNewRand_sendMessage key) fun _ =>
                noNewRand_bind (noNewRand_same (receiveMessage_snd pqIdx)) fun _ =>
                noNewRand_bind (noNewRand_same verifyMacAndDecrypt_snd) fun _ => ?_) tr i
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact noNewRand_bind noNewRand_logSkippedKeys fun _ =>
                noNewRand_bind (noNewRand_logEvent _) fun _ =>
                noNewRand_logMessageKeyAndStore
        · exact ⟨c, rfl⟩
    obtain ⟨c, hrc⟩ := hrc_true
    have hnr_eq := Symbolic.Swarm.CREF.newRandoms_decrypt_of_recvChainFor_true
      (pqIdx := pqIdx) (spqrMsgIdx := spqrMsgIdx) (wrapped := wrapped) hst hrcv hrc
    refine ⟨hnr_eq, msg, ?_⟩
    unfold receivedPlaintext at hpt
    obtain ⟨idx, hidx, hfind⟩ := List.exists_of_findSome?_eq_some hpt
    simp only [newIndices, List.mem_range'_1] at hidx
    split at hfind
    · next me' peer' rk' cnt' pt' hev =>
      injection hfind with hpt_eq; subst pt'
      unfold Move.next Move.act at hev
      rw [p3_run_bind_pure_val] at hev
      obtain ⟨k, iv, hdec⟩ :=
        onlyRecvValid_messageDecrypt_after_rcv me stateIdx msgIdx pqIdx spqrMsgIdx tr st msg
          hst hrcv hidx.1 hev
      exact ⟨k, iv, hparse, hdec⟩
    · cases hfind
  | _ => cases hm

private theorem decrypt_vis_eq {m : Move} {msgIdx : Nat}
    (hm : m.decryptMsgIdx? = some msgIdx) (tr : ExecTrace) :
    ∃ stateIdx wrapped,
      m.vis tr = decVis tr (m.next tr) stateIdx msgIdx wrapped ++ exposures tr (m.next tr) := by
  cases m <;> simp [Move.decryptMsgIdx?] at hm
  all_goals (subst hm; exact ⟨_, _, rfl⟩)

private theorem recvRepresentations_updateFreshAt_of_stampsLt
    {interp : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {b : HwBytes} {t : DY.Bytes}
    (ht : t ∈ recvRepresentations interp r₀ S g ms b) {ts : Nat}
    (ht_lt : StampsLt interp S g ts t) (n : Nat) (coins : HwBytes) :
    t ∈ recvRepresentations interp r₀ S { g with σ := updateFreshAt g.σ ts n coins } ms b := by
  refine ⟨ht.1, ?_, ht.2.2.1, fun msg hparse => ?_⟩
  · rw [gamma_updateFreshAt_of_stampsLt interp S g ts n coins t ht_lt]
    exact ht.2.1
  · obtain ⟨hw_lt, hm_lt, hrk_lt, hct_lt, hpq_lt⟩ := stampsLt_parseTrSignalMsg ht_lt hparse
    have hmsg := ht.2.2.2 msg hparse
    refine ⟨?_, ?_, hmsg.2.2.1, fun sm hsm => ?_⟩
    · rw [gamma_updateFreshAt_of_stampsLt interp S g ts n coins msg.wire hw_lt]
      exact hmsg.1
    · rw [gamma_updateFreshAt_of_stampsLt interp S g ts n coins msg.mac hm_lt]
      exact hmsg.2.1
    · have hsm' := hmsg.2.2.2 sm hsm
      refine ⟨?_, ?_, ?_, hsm'.2.2.2⟩
      · rw [gamma_updateFreshAt_of_stampsLt interp S g ts n coins msg.ciphertext hct_lt]
        exact hsm'.1
      · rw [gamma_updateFreshAt_of_stampsLt interp S g ts n coins msg.ratchetKey hrk_lt]
        exact hsm'.2.1
      · rw [gamma_updateFreshAt_of_stampsLt interp S g ts n coins msg.pqRatchet hpq_lt]
        exact hsm'.2.2.1

private theorem p3_runTrace_take_le (r₀ : ProtocolSetup) (ms : List Move) (idx : Nat) :
    runTraceMoves r₀ (ms.take idx) ≤ runTraceMoves r₀ ms := by
  conv => rhs; rw [← List.take_append_drop idx ms]
  exact runTrace_le_append r₀ (ms.take idx) (ms.drop idx)

private theorem p3_attackerKnows_of_getMessageSentAt {tr : ExecTrace} {idx : Nat} {t : DY.Bytes}
    (hget : tr.getMessageSentAt idx = some t) : t.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr t idx
    ((Trace.MessageSentAt_eq_getMessageSentAt t idx tr).mpr hget)

private theorem acceptsVia_pieces_to_two_mids {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g' : Ghost} {ms' : List Move}
    {τ₁' : List MachineEvent} {e : MachineEvent} {pieces : List HwBytes} {coins pt : HwBytes}
    {t : DY.Bytes}
    (hacc : ModelAcceptsTermAfterCoinSplit interp r S who ok g' ms' τ₁' e (pieces.map MachineEvent.rng ++ [.accept pt]) t) :
    ModelAcceptsTermAfterCoinSplit interp r S who ok g' ms' τ₁' e [.accept pt] t ∨
      ModelAcceptsTermAfterCoinSplit interp r S who ok g' ms' τ₁' e [.rng coins, .accept pt] t := by
  cases pieces with
  | nil => exact Or.inl hacc
  | cons p qs =>
    right
    obtain ⟨ext, m, msgIdx, k, pt', g₁, hext, hm_dec, haddr, hσ_eq, hmsg, hk, _, hex⟩ := hacc
    obtain ⟨rfl, hpt_eq⟩ := getElem?_map_rng_accept_eq_accept hk
    subst pt'
    have htake : ((p :: qs).map MachineEvent.rng ++ [MachineEvent.accept pt]).take ((p :: qs).length + 1) =
        (p :: qs).map MachineEvent.rng ++ [MachineEvent.accept pt] := by
      rw [List.take_of_length_le (by simp)]
    rw [htake] at hex
    let ms_pre := ms' ++ ext.map .attackerSend
    let tr_pre := runTraceMoves r ms_pre
    let idx := tr_pre.length
    change tr_pre.getMessageSentAt msgIdx = some t at hmsg
    have hfor : List.Forall₂ (EventMatchesEntry interp r S g₁)
        (τ₁' ++ e :: ((p :: qs).map MachineEvent.rng ++ [.accept pt]))
        (runVis r ms_pre ++ m.vis tr_pre) := by
      have hf := hex.1.2.2.2.2.2
      rwa [runVis_snoc] at hf
    obtain ⟨stateIdx, wrapped, hvis_m⟩ := decrypt_vis_eq hm_dec tr_pre
    let v_recv : VisEntry :=
      ⟨.recv, [t], if wrapped then .preKeyInner (sessionBaseKeys tr_pre stateIdx) else .whisper, none⟩
    have hexp_nil : exposures tr_pre (m.next tr_pre) = [] := by
      by_contra hne
      obtain ⟨exp_init, v_last, hexp_eq, hmem_last⟩ := snoc_of_ne_nil _ hne
      have hfor' := hfor
      rw [hvis_m, hexp_eq, show τ₁' ++ e :: ((p :: qs).map MachineEvent.rng ++ [.accept pt]) =
        (τ₁' ++ (e :: (p :: qs).map MachineEvent.rng)) ++ [.accept pt] by simp,
        show runVis r ms_pre ++ (decVis tr_pre (m.next tr_pre) stateIdx msgIdx wrapped ++ (exp_init ++ [v_last])) =
        (runVis r ms_pre ++ decVis tr_pre (m.next tr_pre) stateIdx msgIdx wrapped ++ exp_init) ++ [v_last] by
          simp [List.append_assoc]] at hfor'
      have ⟨_, hlast⟩ := forall₂_snoc_inv hfor'
      have hleak := Symbolic.Swarm.CREF.exposures_kind_eq_leak hmem_last
      have hkind := hlast.1
      rw [hleak] at hkind
      cases hkind
    have hpt_some : ∃ ptTerm, receivedPlaintext tr_pre (m.next tr_pre) = some ptTerm := by
      rcases hpt_opt : receivedPlaintext tr_pre (m.next tr_pre) with _ | ptTerm
      · exfalso
        have hdec_eq : decVis tr_pre (m.next tr_pre) stateIdx msgIdx wrapped =
            v_recv :: (newRandoms tr_pre (m.next tr_pre)).map (fun r => rngEntry r.1) := by
          unfold decVis; simp [hmsg, hpt_opt, v_recv]
        obtain ⟨vis_init, v_last, hvis_eq, hmem_last⟩ :=
          snoc_of_ne_nil (v_recv :: (newRandoms tr_pre (m.next tr_pre)).map (fun r => rngEntry r.1)) (by simp)
        have hfor' := hfor
        rw [hvis_m, hexp_nil, List.append_nil, hdec_eq, hvis_eq,
          show τ₁' ++ e :: ((p :: qs).map MachineEvent.rng ++ [.accept pt]) =
            (τ₁' ++ (e :: (p :: qs).map MachineEvent.rng)) ++ [.accept pt] by simp,
          ← List.append_assoc] at hfor'
        have ⟨_, hlast⟩ := forall₂_snoc_inv hfor'
        have hkind := hlast.1
        rcases List.mem_cons.mp hmem_last with rfl | hmem_rng
        · cases hkind
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmem_rng
          cases hkind
      · exact ⟨ptTerm, rfl⟩
    obtain ⟨ptTerm, hpt_term⟩ := hpt_some
    let v_acc : VisEntry := ⟨.accept, [ptTerm], .single, none⟩
    have hvis_m' : m.vis tr_pre =
        (v_recv :: (newRandoms tr_pre (m.next tr_pre)).map (fun r => rngEntry r.1)) ++ [v_acc] := by
      rw [hvis_m, hexp_nil, List.append_nil]
      unfold decVis
      simp [hmsg, hpt_term, v_recv, v_acc]
    have hfor₁_pair : List.Forall₂ (EventMatchesEntry interp r S g₁)
        (τ₁' ++ (e :: (p :: qs).map MachineEvent.rng))
        (runVis r ms_pre ++ (v_recv :: (newRandoms tr_pre (m.next tr_pre)).map (fun r => rngEntry r.1))) ∧
        EventMatchesEntry interp r S g₁ (.accept pt) v_acc := by
      have hfor' := hfor
      rw [hvis_m',
        show τ₁' ++ e :: ((p :: qs).map MachineEvent.rng ++ [.accept pt]) =
          (τ₁' ++ (e :: (p :: qs).map MachineEvent.rng)) ++ [.accept pt] by simp,
        ← List.append_assoc (runVis r ms_pre)] at hfor'
      exact forall₂_snoc_inv hfor'
    obtain ⟨hfor₁, hm_acc⟩ := hfor₁_pair
    have hnr_ne : newRandoms tr_pre (m.next tr_pre) ≠ [] := by
      intro hnr_nil
      rw [hnr_nil, List.map_nil] at hfor₁
      obtain ⟨rng_init, rng_last, hrng_eq, hmem_rng⟩ :=
        snoc_of_ne_nil ((p :: qs).map MachineEvent.rng) (by simp)
      rw [hrng_eq, show τ₁' ++ (e :: (rng_init ++ [rng_last])) =
        (τ₁' ++ (e :: rng_init)) ++ [rng_last] by simp] at hfor₁
      have ⟨_, hlast⟩ := forall₂_snoc_inv hfor₁
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hmem_rng
      cases hlast.1
    obtain ⟨hnr_eq, msg, k_cip, iv_cip, hparse, hdec⟩ :=
      decrypt_ratchet_info hm_dec hmsg hnr_ne hpt_term
    rw [hnr_eq, List.map_singleton] at hfor₁
    have hqs_nil : qs = [] := by
      cases qs with
      | nil => rfl
      | cons q qs' =>
        exfalso
        obtain ⟨rng_init, rng_last, hrng_eq, _⟩ :=
          snoc_of_ne_nil ((q :: qs').map MachineEvent.rng) (by simp)
        have hmap_eq : (p :: q :: qs').map MachineEvent.rng = (.rng p :: rng_init) ++ [rng_last] := by
          simp [hrng_eq]
        rw [hmap_eq, show τ₁' ++ (e :: ((.rng p :: rng_init) ++ [rng_last])) =
          (τ₁' ++ (e :: .rng p :: rng_init)) ++ [rng_last] by simp,
          show runVis r ms_pre ++ [v_recv, rngEntry (randTerm idx 32)] =
          (runVis r ms_pre ++ [v_recv]) ++ [rngEntry (randTerm idx 32)] by simp] at hfor₁
        obtain ⟨hfor₂, _⟩ := forall₂_snoc_inv hfor₁
        obtain ⟨rng_init₂, rng_prev, hrng_eq₂, hmem_prev⟩ :=
          snoc_of_ne_nil (.rng p :: rng_init) (by simp)
        have hmem_all : rng_prev ∈ (p :: q :: qs').map MachineEvent.rng := by
          rw [hmap_eq, hrng_eq₂]
          simp
        rw [hrng_eq₂, show τ₁' ++ (e :: (rng_init₂ ++ [rng_prev])) =
          (τ₁' ++ (e :: rng_init₂)) ++ [rng_prev] by simp] at hfor₂
        obtain ⟨_, hprev⟩ := forall₂_snoc_inv hfor₂
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hmem_all
        cases hprev.1
    subst hqs_nil
    simp only [List.map_cons, List.map_nil] at hfor₁ hex
    have hfor_peel₁ : List.Forall₂ (EventMatchesEntry interp r S g₁) (τ₁' ++ [e])
        (runVis r ms_pre ++ [v_recv]) := by
      rw [show τ₁' ++ [e, .rng p] = (τ₁' ++ [e]) ++ [.rng p] by simp,
        show runVis r ms_pre ++ [v_recv, rngEntry (randTerm idx 32)] =
          (runVis r ms_pre ++ [v_recv]) ++ [rngEntry (randTerm idx 32)] by simp] at hfor₁
      exact (forall₂_snoc_inv hfor₁).1
    obtain ⟨hfor_pre, hm_recv⟩ := forall₂_snoc_inv hfor_peel₁
    have hvis_m_3 : m.vis tr_pre = [v_recv, rngEntry (randTerm idx 32), v_acc] := by
      rw [hvis_m', hnr_eq]; rfl
    let g₂ : Ghost := { g₁ with σ := updateFreshAt g₁.σ idx 32 coins }
    have hlen_pre : τ₁'.length = (runVis r ms_pre).length := hfor_pre.length_eq
    have hmp_pre₁ : MatchedPrefix interp r S who g₁ ms_pre τ₁' :=
      (matchedPrefix_prefix hlen_pre hex.1).1
    have htr_pre : TraceEntriesLt interp S g₁ idx tr_pre :=
      traceEntriesLt_of_reachable interp S g₁ idx hmp_pre₁.2.1.2.2.1.1 (Nat.le_refl idx)
    have hmp_pre₂ : MatchedPrefix interp r S who g₂ ms_pre τ₁' :=
      matchedPrefix_updateFreshAt hmp_pre₁ (Nat.le_refl idx) 32 coins
    have ht_lt : StampsLt interp S g₁ idx t :=
      traceEntriesLt_knows htr_pre (p3_attackerKnows_of_getMessageSentAt hmsg)
    have hpt_lt : StampsLt interp S g₁ idx ptTerm :=
      stampsLt_symDec hdec (stampsLt_parseTrSignalMsg ht_lt hparse).2.2.2.1
    have hv_recv_lt : VisStampsLt interp S g₁ idx v_recv := by
      refine ⟨fun u hu => List.mem_singleton.mp hu ▸ ht_lt, fun ek hek => ?_⟩
      dsimp only [v_recv, layoutKeys] at hek
      cases wrapped
      · simp at hek
      · simp only [↓reduceIte] at hek
        exact stampsLt_of_mem_sessionBaseKeys (DY.Trace.le_refl tr_pre) htr_pre hek
    have hv_acc_lt : VisStampsLt interp S g₁ idx v_acc :=
      visStampsLt_of_terms rfl fun u hu => List.mem_singleton.mp hu ▸ hpt_lt
    have hm_recv₂ : EventMatchesEntry interp r S g₂ e v_recv :=
      (eventMatchesEntry_updateFreshAt_of_visStampsLt interp r S g₁ idx 32 coins e v_recv hv_recv_lt).mpr hm_recv
    have hm_rng₂ : EventMatchesEntry interp r S g₂ (.rng coins) (rngEntry (randTerm idx 32)) :=
      ⟨rfl, by simp [rngEntry, eventBytes, g₂, gamma_updateFreshAt_randTerm_32]⟩
    have hm_acc₂ : EventMatchesEntry interp r S g₂ (.accept pt) v_acc :=
      (eventMatchesEntry_updateFreshAt_of_visStampsLt interp r S g₁ idx 32 coins (.accept pt) v_acc hv_acc_lt).mpr hm_acc
    have hF_blk : List.Forall₂ (EventMatchesEntry interp r S g₂)
        [e, .rng coins, .accept pt] (runMoves [m] tr_pre).2 := by
      simp only [runMoves, List.append_nil, hvis_m_3]
      exact .cons hm_recv₂ (.cons hm_rng₂ (.cons hm_acc₂ .nil))
    have hpath₂ : PathFaithful interp r S g₂ (ms_pre ++ [m]) (τ₁' ++ [e, .rng coins, .accept pt]) := by
      intro i mv promote b q hmi hpp hcs hpw
      have hcs_eq : callStarts (τ₁' ++ [e, .rng coins, .accept pt]) =
          callStarts (τ₁' ++ [e, .rng p, .accept pt]) := by
        unfold callStarts
        rw [List.filter_append, List.filter_append]
        congr 1
      rw [hcs_eq] at hcs
      rw [hex.1.2.2.2.1 i mv promote b q hmi hpp hcs hpw]
      refine exists_congr fun ek => and_congr_right fun hek => ?_
      have hi_le : i ≤ ms_pre.length := by
        have hi_lt := (List.getElem?_eq_some_iff.mp hmi).1
        simp at hi_lt; omega
      rw [List.take_append_of_le_length hi_le] at hek
      have hek_lt : StampsLt interp S g₁ idx ek :=
        stampsLt_of_mem_bobDoneBaseKeys (p3_runTrace_take_le r ms_pre i) htr_pre hek
      rw [gamma_updateFreshAt_of_stampsLt interp S g₁ idx 32 coins ek hek_lt]
    have hread_blk : ∀ ev ∈ [e, .rng coins, .accept pt].zip (runMoves [m] tr_pre).2,
        ev.2.kind = .recv →
        ReadOKWith (recvRepresentations interp r S g₂ (ms_pre ++ [m]))
          (preKeyRepresentations interp r S g₂ (ms_pre ++ [m])) ev.1 ev.2 := by
      simp only [runMoves, List.append_nil, hvis_m_3]
      intro ev hev hkind
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl | rfl
      · have hmem₁ : (e, v_recv) ∈ (τ₁' ++ [e, .rng p, .accept pt]).zip (runVis r (ms_pre ++ [m])) := by
          rw [runVis_snoc, hvis_m_3, List.zip_append hlen_pre]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        have hrd₁ := hex.1.2.2.2.2.1 (e, v_recv) hmem₁ rfl
        dsimp only [ReadOKWith, v_recv] at hrd₁ ⊢
        cases wrapped
        · simp only [Bool.false_eq_true, ↓reduceIte] at hrd₁ ⊢
          rcases heb : eventBytes e with _ | ⟨tag, body⟩
          · trivial
          · rw [heb] at hrd₁
            exact recvRepresentations_updateFreshAt_of_stampsLt hrd₁ ht_lt 32 coins
        · simp only [↓reduceIte] at hrd₁ ⊢
          intro q hpw
          exact recvRepresentations_updateFreshAt_of_stampsLt (hrd₁ q hpw) ht_lt 32 coins
      · cases hkind
      · cases hkind
    have hmp₂ : MatchedPrefix interp r S who g₂ (ms_pre ++ [m]) (τ₁' ++ [e, .rng coins, .accept pt]) :=
      matchedPrefix_append hmp_pre₂ hex.1.2.1 hex.1.2.2.1 hpath₂ hread_blk hF_blk
    have hσ₂ : ∀ i, i < (runTraceMoves r ms').length → g₂.σ i = g'.σ i := by
      intro i hi
      have hle_ext : (runTraceMoves r ms').length ≤ idx :=
        DY.Trace.length_le _ _ (runTrace_le_append r ms' (ext.map .attackerSend))
      have hne_i : i ≠ idx := by omega
      funext sz
      simp [g₂, updateFreshAt, hne_i, hσ_eq i hi]
    exact ⟨ext, m, msgIdx, 1, pt, g₂, hext, hm_dec, haddr, hσ₂, hmsg, rfl, rfl, ⟨hmp₂, hex.2⟩⟩

private theorem coinSplit_exists : ∀ (σ : List MachineEvent), ∃ τ, CoinSplit σ τ
  | [] => ⟨[], .nil⟩
  | ev :: rest => by
    obtain ⟨τ, hτ⟩ := coinSplit_exists rest
    cases ev with
    | rng _ => exact ⟨τ, CoinSplit.split (pieces := []) (by simp) List.nil_prefix hτ⟩
    | _ => exact ⟨_, CoinSplit.keep (fun _ h => by cases h) hτ⟩

/-- Two-cut characterization of `ModelAcceptsTermAfterAttackerSendsMoves` on
`σ₂ = .rng coins :: .accept pt :: σ_rest` when `coins.length = 32`: an accepting decrypt step
consumes either `0` bytes (`[.accept pt]`) or all `32` bytes (`[.rng coins, .accept pt]`). -/
theorem acceptsViaCli_iff_two_mids {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g' : Ghost} {ms' : List Move}
    {τ₁' : List MachineEvent} {e : MachineEvent} {coins pt : HwBytes}
    {σ_rest : List MachineEvent} {t : _root_.DY.Bytes}
    (hcoins : coins.length = 32) :
    ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁' e (.rng coins :: .accept pt :: σ_rest) t ↔
      ModelAcceptsTermAfterCoinSplit interp r S who ok g' ms' τ₁' e [.accept pt] t ∨
        ModelAcceptsTermAfterCoinSplit interp r S who ok g' ms' τ₁' e [.rng coins, .accept pt] t := by
  constructor
  · rintro ⟨τ₂, hcs₂, hacc⟩
    cases hcs₂ with
    | keep hne _ => exact absurd rfl (hne coins)
    | @split _ pieces _ τ_after _ _ hcs_after =>
      cases hcs_after with
      | @keep _ _ τ_rest _ hcs_rest =>
        have hf_rng : ((pieces.map MachineEvent.rng).filter fun ev => eventKind ev != .rng) = [] := by
          simp [List.filter_eq_nil_iff, eventKind]
        have hhead : (((pieces.map MachineEvent.rng ++ [MachineEvent.accept pt]).filter
            fun ev => eventKind ev != .rng)).head? = some (.accept pt) := by
          rw [List.filter_append, hf_rng]; rfl
        have hacc' : ModelAcceptsTermAfterCoinSplit interp r S who ok g' ms' τ₁' e
            ((pieces.map MachineEvent.rng ++ [.accept pt]) ++ τ_rest) t := by
          simpa [List.append_assoc] using hacc
        exact acceptsVia_pieces_to_two_mids
          ((Symbolic.Swarm.CREF.sticky_acceptsVia_append_iff ⟨pt, hhead⟩).mp hacc')
  · obtain ⟨τ_rest, hcs_rest⟩ := coinSplit_exists σ_rest
    have hkeep_pt : CoinSplit (.accept pt :: σ_rest) (.accept pt :: τ_rest) :=
      CoinSplit.keep (fun _ h => by cases h) hcs_rest
    rintro (hacc0 | hacc1)
    · refine ⟨.accept pt :: τ_rest,
        CoinSplit.split (pieces := []) (by simp) List.nil_prefix hkeep_pt, ?_⟩
      exact (Symbolic.Swarm.CREF.sticky_acceptsVia_append_iff (τ₂ := [.accept pt]) ⟨pt, rfl⟩).mpr hacc0
    · have hcoins_ne : coins ≠ [] := by intro h; simp [h] at hcoins
      refine ⟨.rng coins :: .accept pt :: τ_rest,
        CoinSplit.split (pieces := [coins]) (by simp [hcoins_ne]) (by simp) hkeep_pt, ?_⟩
      exact (Symbolic.Swarm.CREF.sticky_acceptsVia_append_iff
        (τ₂ := [.rng coins, .accept pt]) ⟨pt, rfl⟩).mpr hacc1

end Symbolic.Swarm.Coinsplit.P3
