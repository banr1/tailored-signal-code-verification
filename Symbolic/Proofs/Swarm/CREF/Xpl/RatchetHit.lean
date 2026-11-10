/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# DH-Ratcheting Decrypt Inversion

Proves `ratchet_of_rng` and `ratchet_of_matched`: an accepting `Move.decrypt` step whose matched
hardware block contains `.rng rngBytes` misses `findRecvChain`, passes `x25519LowOrder`, runs
`dhRatchetStep` with `g.σ tr.length 32 = rngBytes`, and decrypts on `trDhRatchetState`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (RecvChain recvChainFor findRecvChain consumeMessageKey computeMac
  messageVersion x25519LowOrder)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState run_bind_fst run_bind_snd run_bind_pure_val
  getLocalState_snd ensureReceiverChain_run_noRatchet ensureReceiverChain_run_ratchet
  decrypt_next_noRatchet_eq decrypt_next_ratchet_eq newRandoms_decNoRatchet newRandoms_decRatchet
  receivedPlaintext_decTailTr receivedPlaintext_decRatchetPreTr)

unseal DY.Bytes in
private instance subRandomRH (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem rh_gamma_randTerm32 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ts : Nat) :
    gamma interpretation S g (randTerm ts 32) = g.σ ts 32 := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  rfl

private theorem rh_receivedPlaintext_self (tr : ExecTrace) : receivedPlaintext tr tr = none := by
  simp [receivedPlaintext, newIndices]

private theorem rh_at?_append_lt {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) :=
  RecvDec.at?_append_of_lt tr e hi

private theorem rh_at?_append_length {E E2 : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.append e).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private def rh_receivedAt (tr : ExecTrace) (i : Nat) : Option DY.Bytes :=
  match tr.getEventAt TREvent i with
  | some (.Received _ _ _ _ m) => some m
  | _ => none

private theorem rh_findSome?_congr {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

private theorem rh_mem_newIndices {tr0 tr : ExecTrace} {i : Nat} :
    i ∈ newIndices tr0 tr ↔ tr0.length ≤ i ∧ i < tr.length := by
  simp only [newIndices, List.mem_range'_1]; omega

private theorem rh_newIndices_append {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
  simp only [newIndices, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [show tr.length + 1 - tr0.length = (tr.length - tr0.length) + 1 by omega, List.range'_concat]
  congr 2; omega

private theorem rh_receivedPlaintext_append_of_proj {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E)
    (hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    receivedPlaintext tr0 (tr.append e) = receivedPlaintext tr0 tr := by
  change (newIndices tr0 (tr.append e)).findSome? (rh_receivedAt (tr.append e)) =
    (newIndices tr0 tr).findSome? (rh_receivedAt tr)
  rw [rh_newIndices_append h, List.findSome?_append]
  have hcongr : (newIndices tr0 tr).findSome? (rh_receivedAt (tr.append e)) =
      (newIndices tr0 tr).findSome? (rh_receivedAt tr) := by
    refine rh_findSome?_congr fun i hi => ?_
    simp only [rh_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, rh_at?_append_lt tr e (rh_mem_newIndices.mp hi).2]
  have hnone : rh_receivedAt (tr.append e) tr.length = none := by
    simp only [rh_receivedAt, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, rh_at?_append_length, hproj]
  rw [hcongr, List.findSome?_singleton, hnone, Option.or_none]

private theorem rh_receiveMessage_fst (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).1 = tr.getMessageSentAt idx := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  rw [run_bind_fst, Traceful.run_mk]
  rcases (tr.at? idx : Option Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem rh_receiveMessage_snd (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_snd, Traceful.run_mk]
  rcases (tr.at? idx : Option Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem rh_receiveSignalMsg_snd (msgIdx : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgIdx).run tr).2.val = tr := by
  unfold receiveSignalMsg
  rw [run_bind_snd, rh_receiveMessage_snd]
  rcases ((DY.Network.receiveMessage msgIdx).run tr).1 with _ | raw
  · rfl
  · dsimp only
    rcases parseTrSignalMsg raw with _ | msg
    · (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
    · dsimp only
      by_cases hv : msg.version = messageVersion <;> simp only [_root_.guard, hv, ↓reduceIte] <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem rh_receiveSignalMsg_some_iff {msgIdx : Nat} {tr : ExecTrace} {msg : TRSignalMsg} :
    ((receiveSignalMsg msgIdx).run tr).1 = some msg ↔
      ∃ t, tr.getMessageSentAt msgIdx = some t ∧
        parseTrSignalMsg t = some msg ∧ msg.version = messageVersion := by
  unfold receiveSignalMsg
  rw [run_bind_fst, rh_receiveMessage_fst, rh_receiveMessage_snd]
  constructor
  · intro h
    rcases hmsg : tr.getMessageSentAt msgIdx with _ | t
    · rw [hmsg] at h; cases h
    · rw [hmsg] at h; dsimp only at h
      rcases hp : parseTrSignalMsg t with _ | m
      · rw [hp] at h; dsimp only at h; rw [Traceful.run_failure] at h; cases h
      · rw [hp] at h; dsimp only at h
        by_cases hv : m.version = messageVersion
        · simp only [_root_.guard, hv, ↓reduceIte, run_bind_fst, Traceful.run_pure] at h
          injection h with h; subst h
          exact ⟨t, rfl, hp, hv⟩
        · simp only [_root_.guard, hv, ↓reduceIte, run_bind_fst, Traceful.run_failure] at h; cases h
  · rintro ⟨t, hmsg, hp, hv⟩
    rw [hmsg]; dsimp only; rw [hp]; dsimp only
    simp only [_root_.guard, hv, ↓reduceIte, run_bind_fst, Traceful.run_pure]

private theorem rh_verifyMacAndDecrypt_snd (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) (tr : ExecTrace) :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  unfold verifyMacAndDecrypt
  by_cases hm : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, run_bind_snd, Traceful.run_pure]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    rcases DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext <;>
      simp only [Traceful.run_mk, Traceful.run_pure]
  · simp only [_root_.guard, hm, ↓reduceIte, run_bind_snd, Traceful.run_failure]

private theorem rh_verifyMacAndDecrypt_some_iff {st : TRState} {msg : TRSignalMsg}
    {pqSalt seed ptTerm : DY.Bytes} {tr : ExecTrace} :
    ((verifyMacAndDecrypt st msg pqSalt seed).run tr).1 = some ptTerm ↔
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧
        DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
          msg.ciphertext = some ptTerm := by
  unfold verifyMacAndDecrypt
  by_cases hm : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, run_bind_fst, Traceful.run_pure, true_and]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    rcases hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext with _ | pt
    · simp only [Traceful.run_mk, reduceCtorEq]
    · simp only [Traceful.run_mk]
  · simp only [_root_.guard, hm, ↓reduceIte, run_bind_fst, Traceful.run_failure,
      reduceCtorEq, false_and]

private theorem rh_forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨y, hy, hxy⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

private theorem rh_vis_rng_eq_of_newRandoms_singleton
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace} {rTerm : DY.Bytes} {n : Nat}
    (hnr : newRandoms tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
      [(rTerm, n)])
    {v : VisEntry}
    (hv : v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr)
    (hkind : v.kind = .rng) :
    v = rngEntry rTerm := by
  change v ∈ decVis tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr)
    stateIdx msgIdx wrapped ++ exposures tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) at hv
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · unfold decVis at hv
    rw [hnr] at hv
    simp only [List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hv
    rcases hv with (hv | hv) | hv
    · cases hmsg : tr.getMessageSentAt msgIdx <;> simp [hmsg] at hv
      subst hv; cases hkind
    · exact hv
    · cases hpt : receivedPlaintext tr
        ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) <;> simp [hpt] at hv
      subst hv; cases hkind
  · rw [exposures_kind_eq_leak hv] at hkind; cases hkind

/-- An accepting `Move.decrypt` with a `.rng` entry in `m.vis tr` runs `dhRatchetStep`
(`findRecvChain st.recv msg.ratchetKey = none`, `x25519LowOrder msg.ratchetKey = false`) and
succeeds through `consumeMessageKey`, `spqrRecv`, and `verifyMacAndDecrypt`. -/
theorem ratchet_of_rng
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace}
    (hrng : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .rng)
    (hacc : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept) :
    ∃ (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (c' : RecvChain)
      (seed spqr' key pqSalt ptTerm : DY.Bytes),
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st ∧
      tr.getMessageSentAt msgIdx = some t ∧
      parseTrSignalMsg t = some msg ∧
      msg.version = messageVersion ∧
      findRecvChain st.recv msg.ratchetKey = none ∧
      x25519LowOrder msg.ratchetKey = false ∧
      consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter =
        some (seed, c') ∧
      Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr
        msg.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
        Option Network.ExecEntryT) = some ⟨pqSalt⟩ ∧
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
        (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
        (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
        msg.ciphertext = some ptTerm ∧
      receivedPlaintext tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
        some ptTerm ∧
      newRandoms tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
        [(randTerm tr.length 32, 32)] := by
  have hnr_ne :
      newRandoms tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) ≠ [] := by
    intro hnil
    obtain ⟨v, hv, hvk⟩ := hrng
    exact (newRandoms_eq_nil_iff_no_rng_vis_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx
      wrapped tr).mpr hnil v hv hvk
  obtain ⟨ptTerm0, hpt0⟩ :=
    (accept_in_vis_decrypt_iff_receivedPlaintext_isSome me stateIdx msgIdx pqIdx spqrMsgIdx
      wrapped tr).mp hacc
  have hpt_eq := hpt0
  unfold Move.next Move.act at hpt0
  rw [run_bind_pure_val] at hpt0
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hpt0
  rw [run_bind_snd, getLocalState_snd] at hpt0
  rcases hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with _ | st
  · rw [hst, rh_receivedPlaintext_self] at hpt0; cases hpt0
  · rw [hst] at hpt0; dsimp only at hpt0
    rw [run_bind_snd, rh_receiveSignalMsg_snd] at hpt0
    rcases hmsg : ((receiveSignalMsg msgIdx).run tr).1 with _ | msg
    · rw [hmsg, rh_receivedPlaintext_self] at hpt0; cases hpt0
    · rw [hmsg] at hpt0; dsimp only at hpt0
      obtain ⟨t, ht_sent, hparse, hver⟩ := rh_receiveSignalMsg_some_iff.mp hmsg
      rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c0
      · rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
        · obtain ⟨hens1, hens2⟩ := ensureReceiverChain_run_ratchet tr hfind hlow
          rw [run_bind_snd, hens1, hens2] at hpt0; dsimp only at hpt0
          let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
          let c1 := (trDhRatchetState st msg.ratchetKey tr.length).2
          let tr_r := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
          have hpt_r : receivedPlaintext tr tr_r = none := by
            dsimp only [tr_r]
            rw [rh_receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, rh_receivedPlaintext_self]
          rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩
          · rw [hcons] at hpt0; dsimp only at hpt0
            rw [Traceful.run_failure, hpt_r] at hpt0; cases hpt0
          · rw [hcons] at hpt0; dsimp only at hpt0
            rcases hspqr : Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
            · rw [hspqr] at hpt0; dsimp only at hpt0
              rw [Traceful.run_failure, hpt_r] at hpt0; cases hpt0
            · rw [hspqr] at hpt0; dsimp only at hpt0
              let tr_k := tr_r.append (⟨key⟩ : Network.ExecEntryT)
              have hsm1 : ((DY.Network.sendMessage key).run tr_r).1 = some tr_r.length := by
                simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                  Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
              have hsm2 : ((DY.Network.sendMessage key).run tr_r).2.val = tr_k := by
                simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                  Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
                rfl
              have hpt_k : receivedPlaintext tr tr_k = none := by
                dsimp only [tr_k]
                rw [rh_receivedPlaintext_append_of_proj
                  (by dsimp only [tr_r]; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                        Symbolic.DYBridge.DY.Trace.length_eq_2]; omega) _ rfl, hpt_r]
              rw [run_bind_snd, hsm1, hsm2] at hpt0; dsimp only at hpt0
              rw [run_bind_snd, rh_receiveMessage_snd] at hpt0
              rcases hpq : ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
              · rw [hpq, hpt_k] at hpt0; cases hpt0
              · rw [hpq] at hpt0; dsimp only at hpt0
                have hpq_at : (tr_k.at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
                  rw [rh_receiveMessage_fst] at hpq
                  simpa only [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] using
                    (Trace.MessageSentAt_eq_getMessageSentAt pqSalt pqIdx tr_k).mpr hpq
                rw [run_bind_snd, rh_verifyMacAndDecrypt_snd] at hpt0
                rcases hv : ((verifyMacAndDecrypt st1 msg pqSalt seed).run tr_k).1 with _ | ptTerm
                · rw [hv, hpt_k] at hpt0; cases hpt0
                · obtain ⟨hmac_eq, hdec⟩ := rh_verifyMacAndDecrypt_some_iff.mp hv
                  have hnext := decrypt_next_ratchet_eq (wrapped := wrapped)
                    hst ht_sent hparse hver hfind hlow hcons hspqr hpq_at hmac_eq hdec
                  dsimp only at hnext
                  have hpt_next :
                      receivedPlaintext tr
                        ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
                        some ptTerm := by
                    rw [hnext]
                    exact receivedPlaintext_decTailTr
                      (by rw [RecvDec.decRatchetPreTr_length]; omega)
                      (receivedPlaintext_decRatchetPreTr tr me st1 msg.ratchetKey key)
                      me stateIdx st1 c1 c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter
                  have hnr_next :
                      newRandoms tr
                        ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
                        [(randTerm tr.length 32, 32)] := by
                    rw [hnext]
                    exact newRandoms_decRatchet tr me stateIdx st1 c1 c'
                      msg.ratchetKey seed key pqSalt ptTerm spqr' msg.counter
                  exact ⟨st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
                    rfl, ht_sent, hparse, hver, hfind, hlow, hcons, hspqr, hpq_at,
                    hmac_eq, hdec, hpt_next, hnr_next⟩
        · have hens_none : ((ensureReceiverChain st msg.ratchetKey).run tr).1 = none ∧
              ((ensureReceiverChain st msg.ratchetKey).run tr).2.val = tr := by
            simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor TRState.toDRState; dsimp only
            rw [hfind]; simp [hlow, Traceful.run_failure]
          rw [run_bind_snd, hens_none.1, hens_none.2, rh_receivedPlaintext_self] at hpt0
          cases hpt0
      · exfalso
        obtain ⟨hens1, hens2⟩ := ensureReceiverChain_run_noRatchet tr hfind
        rw [run_bind_snd, hens1, hens2] at hpt0; dsimp only at hpt0
        rcases hcons : consumeMessageKey c0 msg.counter with _ | ⟨seed, c'⟩
        · rw [hcons] at hpt0; dsimp only at hpt0
          rw [Traceful.run_failure, rh_receivedPlaintext_self] at hpt0; cases hpt0
        · rw [hcons] at hpt0; dsimp only at hpt0
          rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
          · rw [hspqr] at hpt0; dsimp only at hpt0
            rw [Traceful.run_failure, rh_receivedPlaintext_self] at hpt0; cases hpt0
          · rw [hspqr] at hpt0; dsimp only at hpt0
            let tr_k := tr.append (⟨key⟩ : Network.ExecEntryT)
            have hsm1 : ((DY.Network.sendMessage key).run tr).1 = some tr.length := by
              simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
            have hsm2 : ((DY.Network.sendMessage key).run tr).2.val = tr_k := by
              simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
                Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
              rfl
            have hpt_k : receivedPlaintext tr tr_k = none := by
              dsimp only [tr_k]
              rw [rh_receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, rh_receivedPlaintext_self]
            rw [run_bind_snd, hsm1, hsm2] at hpt0; dsimp only at hpt0
            rw [run_bind_snd, rh_receiveMessage_snd] at hpt0
            rcases hpq : ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
            · rw [hpq, hpt_k] at hpt0; cases hpt0
            · rw [hpq] at hpt0; dsimp only at hpt0
              have hpq_at : (tr_k.at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
                rw [rh_receiveMessage_fst] at hpq
                simpa only [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] using
                  (Trace.MessageSentAt_eq_getMessageSentAt pqSalt pqIdx tr_k).mpr hpq
              rw [run_bind_snd, rh_verifyMacAndDecrypt_snd] at hpt0
              rcases hv : ((verifyMacAndDecrypt st msg pqSalt seed).run tr_k).1 with _ | ptTerm
              · rw [hv, hpt_k] at hpt0; cases hpt0
              · obtain ⟨hmac_eq, hdec⟩ := rh_verifyMacAndDecrypt_some_iff.mp hv
                have hnext := decrypt_next_noRatchet_eq (wrapped := wrapped)
                  hst ht_sent hparse hver hfind hcons hspqr hpq_at hmac_eq hdec
                apply hnr_ne
                rw [hnext]
                exact newRandoms_decNoRatchet tr me stateIdx st c0 c'
                  msg.ratchetKey seed key pqSalt ptTerm spqr' msg.counter

/-- Hardware-block corollary of `ratchet_of_rng`: if `.rng rngBytes ∈ blk` and `blk` contains an
`.accept` event, then `g.σ tr.length 32 = rngBytes` and `Move.decrypt` takes the DH-ratchet path. -/
theorem ratchet_of_matched
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {me : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {tr : ExecTrace} {blk : List HwEvents.MachineEvent} {rngBytes : HwBytes}
    (hmatch : List.Forall₂ (EventMatchesEntry interpretation r S g) blk
      ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr))
    (hrng : .rng rngBytes ∈ blk)
    (hacc : ∃ e ∈ blk, eventKind e = .accept) :
    g.σ tr.length 32 = rngBytes ∧
    ∃ (st : TRState) (t : DY.Bytes) (msg : TRSignalMsg) (c' : RecvChain)
      (seed spqr' key pqSalt ptTerm : DY.Bytes),
      ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st ∧
      tr.getMessageSentAt msgIdx = some t ∧
      parseTrSignalMsg t = some msg ∧
      msg.version = messageVersion ∧
      findRecvChain st.recv msg.ratchetKey = none ∧
      x25519LowOrder msg.ratchetKey = false ∧
      consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter =
        some (seed, c') ∧
      Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr
        msg.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
        Option Network.ExecEntryT) = some ⟨pqSalt⟩ ∧
      msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
        (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
        (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
        msg.ciphertext = some ptTerm ∧
      receivedPlaintext tr ((Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next tr) =
        some ptTerm := by
  obtain ⟨v_rng, hv_rng, hev_rng⟩ := rh_forall₂_mem_left hmatch hrng
  have hv_rng_kind : v_rng.kind = .rng := hev_rng.1.symm
  have hrng_vis : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .rng := ⟨v_rng, hv_rng, hv_rng_kind⟩
  have hacc_vis : ∃ v ∈ (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped).vis tr,
      v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := rh_forall₂_mem_left hmatch he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
      hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, hpt, hnr⟩ :=
    ratchet_of_rng hrng_vis hacc_vis
  have hv_eq : v_rng = rngEntry (randTerm tr.length 32) :=
    rh_vis_rng_eq_of_newRandoms_singleton hnr hv_rng hv_rng_kind
  subst hv_eq
  have hgam_rng : gamma interpretation S g (randTerm tr.length 32) = rngBytes := by
    have h2 := hev_rng.2
    dsimp only [rngEntry, eventBytes] at h2
    simp only [List.map_cons, List.map_nil] at h2
    exact (List.cons.inj h2).1
  have hσ : g.σ tr.length 32 = rngBytes :=
    (rh_gamma_randTerm32 interpretation S g tr.length).symm.trans hgam_rng
  exact ⟨hσ, st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
    hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, hpt⟩

end Symbolic.Swarm.CREF
