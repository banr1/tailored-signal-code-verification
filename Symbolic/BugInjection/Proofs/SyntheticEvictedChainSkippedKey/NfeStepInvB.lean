/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Bob Send and Whisper Receive Step Transitions

Proves `BobActiveInv` transitions for Bob's post-handshake steps. A `.send` step preserves Bob's
receiver-chain list and ratchet secret (`bob_send_step`), while a Whisper `.recv` with a fresh peer
ratchet key takes the DH-ratchet branch, pushes the key onto the 5-chain bounded `recv` window
(`maxReceiverChains = 5`), and updates Bob's `dhs` secret index (`bob_whisper_recv_step`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInvB

open scoped DY.Libsignal.Composed
open DY (Participant Traceful ExecTrace)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.TripleRatchet
  (TRState TREvent findRecvChain setRecvChain maxReceiverChains receiveSignalMsg
   messageEncrypt messageDecrypt messageDecryptSkipped logMessageKeyAndStore u32Max)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma clamp randTerm rngEntry received receivedPlaintext newRandoms
   bobOpkPk bobVis decVis exposures stepView
   runSteps RunMatches ReadsFaithfully PreKeyRecvMatches PreKeyRecvOpkMatches
   GhostWF runWrapped)
open Symbolic.Swarm.COMPOSED.CompTrace
  (TRStEntry RndE NetE TREvE TRStE run_bind_fst run_bind_snd receiveMessage_snd)
open Symbolic.Swarm.CREF
  (rpkT_receiveMessage_fst rpkT_getMessageSentAt_of_at? rpkT_receiveSignalMsg_some)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Swarm.CREF.TR.RecvDec
  (getLocalState_snd at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   at?_stEntry_logSkippedKeysTr trDhRatchetState decRatchetPreTr decRatchetPreTr_length
   decTailTr decrypt_next_ratchet_eq newRandoms_decRatchet
   receivedPlaintext_decTailTr receivedPlaintext_decRatchetPreTr)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (WhisperInputSpec)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (noNewBobState_runSteps_network BobActiveInv noNewBobState_preserves_active
   bobActiveInv_pin_state bobActiveInv_of_unique_new setRecvChain_map_ratchetKey
   step_le_next preCond_messageEncrypt preCond_messageDecrypt preCond_messageDecryptSkipped
   step_ok_encrypt step_next_encrypt step_ok_encryptAbort_false
   step_ok_decrypt step_next_decrypt step_ok_decryptSkipped drawsMatch_single_pin)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
  (findRecvChain_none_of_not_mem not_decryptSkipped_of_find_none decrypt_ratchet_inv
   recv_outputs_accept split_vis_recv_rng)

theorem bob_send_step {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v : List VisEntry}
    (hinv : BobActiveInv S g recvIdxs skIdx tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (hpre : s.PreCond (runSteps pre tr))
    (hbob : e.party = "bob" ∧ ∃ peer, e.cmd = .send peer)
    (hrm : RunMatches evictedI0 r S g (runSteps pre tr) s e v initIds) :
    BobActiveInv S g recvIdxs skIdx (s.next (runSteps pre tr)) := by
  set tr₁ := runSteps pre tr
  have hinv₁ : BobActiveInv S g recvIdxs skIdx tr₁ :=
    noNewBobState_preserves_active (noNewBobState_runSteps_network pre tr hnet) hinv
  obtain ⟨_, hparty, hfits, _, hok, _⟩ := hrm
  obtain ⟨hparty_bob, peer, hcmd⟩ := hbob
  rw [hparty_bob] at hparty
  rw [hcmd] at hfits
  cases s with
  | messageEncryptAbort me stateIdx =>
    exfalso
    rw [step_ok_encryptAbort_false] at hok
    cases hok
  | messageEncrypt me stateIdx cl pq =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have hcur := preCond_messageEncrypt hpre
    have hle_next := step_le_next (.messageEncrypt "bob" stateIdx cl pq) tr₁
    rw [step_ok_encrypt] at hok
    rw [step_next_encrypt] at hle_next ⊢
    unfold messageEncrypt at hok hle_next ⊢
    rw [run_bind_fst] at hok
    rw [run_bind_snd] at hle_next ⊢
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · try rw [hst] at hok
      cases hok
    · obtain ⟨hinit, hrecv, hdhs⟩ := bobActiveInv_pin_state hinv₁ hst hcur
      try rw [hst] at hok
      try rw [hst] at hle_next
      try rw [hst]
      rw [getLocalState_snd] at hok hle_next ⊢; dsimp only at hok hle_next ⊢
      have hguard : (_root_.guard (st.ns ≠ u32Max) : Traceful Unit) = pure () := by
        unfold _root_.guard
        split
        · rfl
        · next hneg =>
          exfalso
          unfold _root_.guard at hok
          split at hok
          · next hpos => exact hneg hpos
          · rw [run_bind_fst, DY.Traceful.run_failure] at hok; cases hok
      rw [hguard] at hok hle_next ⊢
      rw [run_bind_fst, DY.Traceful.run_pure] at hok; dsimp only at hok
      rw [run_bind_snd, DY.Traceful.run_pure] at hle_next ⊢; dsimp only at hle_next ⊢
      rw [run_bind_fst] at hok; rw [run_bind_snd] at hle_next ⊢
      rw [(Runs.genRand tr₁ 32).1, (Runs.genRand tr₁ 32).2] at hok hle_next ⊢
      dsimp only at hok hle_next ⊢
      let tr_r1 := tr₁.append (RndE 32)
      rw [run_bind_fst] at hok; rw [run_bind_snd] at hle_next ⊢
      rw [(Runs.genRand tr_r1 cl).1, (Runs.genRand tr_r1 cl).2] at hok hle_next ⊢
      dsimp only at hok hle_next ⊢
      let tr_r2 := tr_r1.append (RndE cl)
      let spqrOut := DY.Spqr.spqrSend st.spqr (randTerm tr_r1.length cl)
      have hsm1 : ((DY.Network.sendMessage spqrOut.2.1).run tr_r2).1 = some tr_r2.length :=
        (Runs.sendMessage tr_r2 spqrOut.2.1).1
      have hsm2 : ((DY.Network.sendMessage spqrOut.2.1).run tr_r2).2.val =
          tr_r2.append (NetE spqrOut.2.1) :=
        (Runs.sendMessage tr_r2 spqrOut.2.1).2
      rw [run_bind_fst, hsm1, hsm2] at hok
      rw [run_bind_snd, hsm1, hsm2] at hle_next ⊢
      dsimp only at hok hle_next ⊢
      let tr_k := tr_r2.append (NetE spqrOut.2.1)
      rw [run_bind_fst, rpkT_receiveMessage_fst, receiveMessage_snd] at hok
      rw [run_bind_snd, rpkT_receiveMessage_fst, receiveMessage_snd] at hle_next ⊢
      rcases hpq : tr_k.getMessageSentAt pq with _ | pqSalt
      · try rw [hpq] at hok
        cases hok
      · try rw [hpq] at hle_next
        try rw [hpq]
        dsimp only at hle_next ⊢
        let m := randTerm tr₁.length 32
        let ck' := (DY.Libsignal.TripleRatchet.kdfCk st.cks).1
        let seed := (DY.Libsignal.TripleRatchet.kdfCk st.cks).2
        let evSent := TREvent.Sent "bob" st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m
        have hl1 : ((DY.ProtocolEvent.logEvent evSent).run tr_k).1 = some () := by
          simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
            Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
            DY.Traceful.run_mk, DY.Traceful.run_pure]
        have hl2 := logEvent_snd_eq evSent tr_k
        rw [run_bind_snd, hl1, hl2] at hle_next ⊢; dsimp only at hle_next ⊢
        let tr_s := tr_k.append (TREvE evSent)
        let st' : TRState := { st with cks := ck', ns := st.ns + 1, spqr := spqrOut.1 }
        rw [run_bind_snd] at hle_next ⊢
        unfold logMessageKeyAndStore at hle_next ⊢
        let evMk := TREvent.MessageKey (st.sessionInfo "bob") .sender
          seed pqSalt st.ns st.rIdx stateIdx
        have hmk1 : ((DY.ProtocolEvent.logEvent evMk).run tr_s).1 = some () := by
          simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
            Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
            DY.Traceful.run_mk, DY.Traceful.run_pure]
        have hmk2 := logEvent_snd_eq evMk tr_s
        rw [run_bind_snd, run_bind_fst, hmk1, hmk2] at hle_next ⊢; dsimp only at hle_next ⊢
        let tr_mk := tr_s.append (TREvE evMk)
        have hst1 : ((DY.PersistentLocalState.storeLocalState "bob" st').run tr_mk).1 =
            some tr_mk.length := by
          simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
            Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
            Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
        have hst2 := storeLocalState_tr_snd_eq "bob" st' tr_mk
        rw [hst1, hst2] at hle_next ⊢; dsimp only at hle_next ⊢
        rw [(Runs.sendMessage (tr_mk.append (TRStE "bob" st')) _).2] at hle_next ⊢
        have hge : tr₁.length ≤ tr_mk.length := by
          simp only [tr_mk, tr_s, tr_k, tr_r2, tr_r1,
            Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
          omega
        have hat_new (w : DY.Bytes) :
            (((tr_mk.append (TRStE "bob" st')).append (NetE w)).at? tr_mk.length :
            Option TRStEntry) = some ⟨⟨"bob", st'⟩⟩ := by
          rw [at?_append_non_entry _ _ rfl, Symbolic.Swarm.CREF.at?_append_length]; rfl
        have hmk_none : ∀ j, tr₁.length ≤ j → (tr_mk.at? j : Option TRStEntry) = none := by
          intro j hj
          dsimp only [tr_mk, tr_s, tr_k, tr_r2, tr_r1]
          rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_append_non_entry _ _ rfl, at?_eq_none_of_le tr₁ hj]
        refine bobActiveInv_of_unique_new hinv₁ hle_next hge (hat_new _) ?_ hinit hrecv hdhs
        intro j s0 hj hat
        rw [at?_append_non_entry _ _ rfl] at hat
        by_cases hlt : j < tr_mk.length
        · rw [at?_append_of_lt _ _ hlt, hmk_none j hj] at hat; cases hat
        · by_cases heq : j = tr_mk.length
          · subst heq
            rw [Symbolic.Swarm.CREF.at?_append_length] at hat
            injection hat with h1; injection h1 with h2; injection h2 with _ hs0
            exact ⟨rfl, hs0.symm⟩
          · rw [at?_eq_none_of_le (tr_mk.append (TRStE "bob" st'))
                (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                      Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat
            cases hat
  | _ => cases hfits

theorem bob_whisper_recv_step {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx pkIdx skIdx' : Fin 16}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v visAll : List VisEntry}
    (hgwf : GhostWF g visAll)
    (hinv : BobActiveInv S g recvIdxs skIdx tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (hpre : s.PreCond (runSteps pre tr))
    (hbob : e.party = "bob" ∧ ∃ peer, e.cmd = .recv peer)
    (hwh : WhisperInputSpec e pkIdx)
    (hcoins : evictedSecretIdx (clamp (e.coins.take 32)) = some skIdx')
    (hnotMem : pkIdx ∉ recvIdxs)
    (hrm : RunMatches evictedI0 r S g (runSteps pre tr) s e v initIds)
    (hsub : ∀ w ∈ v, w ∈ visAll) :
    BobActiveInv S g ((recvIdxs ++ [pkIdx]).drop ((recvIdxs.length + 1) - 5)) skIdx'
      (s.next (runSteps pre tr)) := by
  set tr₁ := runSteps pre tr
  have hinv₁ : BobActiveInv S g recvIdxs skIdx tr₁ :=
    noNewBobState_preserves_active (noNewBobState_runSteps_network pre tr hnet) hinv
  obtain ⟨_, hparty, hfits, _, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, hrf, _⟩ := hrm
  obtain ⟨hparty_bob, peer, hcmd⟩ := hbob
  obtain ⟨hwrap, hnpk, body, m_wire, hin_eq, htry, hm_rk, _⟩ := hwh
  rw [hparty_bob] at hparty
  rw [hcmd] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨peer, hcmd⟩ hout
  cases s with
  | bobStart b a kh regA mh pqIdx spqr =>
    exfalso
    have hinp : inp = ⟨.recv, received tr₁ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₁).toList,
        .preKeyRecv, none⟩ := by
      have hv0 := hv_split.symm.trans hvis_eq
      unfold stepView bobVis at hv0
      simp only [hok, ↓reduceIte, List.cons_append] at hv0
      injection hv0
    rw [hinp] at hbm_in
    have hpk_opk : PreKeyRecvOpkMatches evictedI0 r S g e.input
        (received tr₁ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₁).toList) := hbm_in.2
    have hpk_rec : ∃ x y z, PreKeyRecvMatches evictedI0 r S g e.input [x, y, z] := by
      unfold PreKeyRecvOpkMatches at hpk_opk
      rcases hts : received tr₁ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₁).toList with
        _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _ | _⟩⟩⟩⟩ <;> rw [hts] at hpk_opk
      · exact False.elim hpk_opk
      · exact False.elim hpk_opk
      · exact False.elim hpk_opk
      · exact ⟨x, y, z, hpk_opk.1⟩
      · exact ⟨x, y, z, hpk_opk.1⟩
      · exact False.elim hpk_opk
    obtain ⟨_, _, _, p, hp, _⟩ := hpk_rec
    rw [hnpk] at hp; cases hp
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    exfalso
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have hcur := preCond_messageDecryptSkipped hpre
    have hok_copy := hok
    rw [step_ok_decryptSkipped] at hok_copy
    unfold messageDecryptSkipped at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · try rw [hst] at hok_copy
      cases hok_copy
    · try rw [hst] at hok_copy
      rw [getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₁).1 with _ | msg
      · try rw [hmsg_run] at hok_copy
        cases hok_copy
      · obtain ⟨_, hrecv_map, _⟩ := bobActiveInv_pin_state hinv₁ hst hcur
        obtain ⟨t, hat, hparse, _⟩ := rpkT_receiveSignalMsg_some hmsg_run
        have hinp : inp = ⟨.recv, [t], .whisper, none⟩ := by
          have hv0 := hv_split.symm.trans hvis_eq
          unfold stepView decVis at hv0
          simp only [hok, ↓reduceIte, hwrap, Bool.false_eq_true,
            rpkT_getMessageSentAt_of_at? hat, Option.map_some, Option.toList_some,
            List.cons_append] at hv0
          injection hv0
        rw [hinp, hin_eq] at hrf
        dsimp only [ReadsFaithfully] at hrf
        have hrk_eq := ((hrf.2.2.2 msg hparse).2.2.2 m_wire htry).2.1.trans hm_rk
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk_eq hnotMem
        rw [not_decryptSkipped_of_find_none hst hmsg_run hfind] at hok
        cases hok
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have hcur := preCond_messageDecrypt hpre
    have hle_next := step_le_next (.messageDecrypt "bob" stateIdx msgIdx pq spqr) tr₁
    have hok_copy := hok
    rw [step_ok_decrypt] at hok_copy
    unfold messageDecrypt at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · try rw [hst] at hok_copy
      cases hok_copy
    · try rw [hst] at hok_copy
      rw [getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₁).1 with _ | msg
      · try rw [hmsg_run] at hok_copy
        cases hok_copy
      · obtain ⟨hinit, hrecv_map, _⟩ := bobActiveInv_pin_state hinv₁ hst hcur
        obtain ⟨t₀, hat₀, hparse₀, _⟩ := rpkT_receiveSignalMsg_some hmsg_run
        have hinp : inp = ⟨.recv, [t₀], .whisper, none⟩ := by
          have hv0 := hv_split.symm.trans hvis_eq
          unfold stepView decVis at hv0
          simp only [hok, ↓reduceIte, hwrap, Bool.false_eq_true,
            rpkT_getMessageSentAt_of_at? hat₀, Option.map_some, Option.toList_some,
            List.cons_append] at hv0
          injection hv0
        rw [hinp, hin_eq] at hrf
        dsimp only [ReadsFaithfully] at hrf
        have hrk_eq : gamma evictedI0 S g msg.ratchetKey = evictedPubOfIdx pkIdx :=
          ((hrf.2.2.2 msg hparse₀).2.2.2 m_wire htry).2.1.trans hm_rk
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk_eq hnotMem
        obtain ⟨w, hw_msg⟩ := decrypt_ratchet_inv hok hst hmsg_run hfind
        have hrk_w : gamma evictedI0 S g w.msg.ratchetKey = evictedPubOfIdx pkIdx := by
          rw [hw_msg]; exact hrk_eq
        have hfind_w : findRecvChain st.recv w.msg.ratchetKey = none := by
          rw [hw_msg]; exact hfind
        let st1 := (trDhRatchetState st w.msg.ratchetKey tr₁.length).1
        let c := (trDhRatchetState st w.msg.ratchetKey tr₁.length).2
        let tr_pre := decRatchetPreTr tr₁ "bob" st1 w.msg.ratchetKey w.key
        have htr' : (Step.messageDecrypt "bob" stateIdx msgIdx pq spqr).next tr₁ =
            decTailTr tr_pre "bob" stateIdx st1 c w.c' w.msg.ratchetKey w.seed
              w.pqSalt w.ptTerm w.spqr' w.msg.counter :=
          (step_next_decrypt "bob" stateIdx msgIdx pq spqr tr₁).trans
            (decrypt_next_ratchet_eq hst w.hmsg w.hparse w.hver hfind_w w.hlow
              w.hcons w.hspqr w.hpqSalt w.hmac_eq w.hdec)
        have hvis_full : v =
            ⟨.recv, [w.t], .whisper, none⟩ ::
            rngEntry (randTerm tr₁.length 32) ::
            ⟨.accept, [w.ptTerm], .single, none⟩ ::
            exposures tr₁ (decTailTr tr_pre "bob" stateIdx st1 c w.c' w.msg.ratchetKey
              w.seed w.pqSalt w.ptTerm w.spqr' w.msg.counter) := by
          rw [hvis_eq]
          unfold stepView decVis
          simp only [hok, ↓reduceIte, hwrap, Bool.false_eq_true, w.hmsg, htr']
          dsimp only [tr_pre]
          rw [newRandoms_decRatchet,
            receivedPlaintext_decTailTr
              (by rw [decRatchetPreTr_length]; omega)
              (receivedPlaintext_decRatchetPreTr ..)]
          rfl
        obtain ⟨_, drs_rest, hdrs_eq⟩ :=
          split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
        have hrng_mem : rngEntry (randTerm tr₁.length 32) ∈ visAll := by
          apply hsub
          rw [hv_split, hdrs_eq]; simp
        rw [hdrs_eq] at hdr
        have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
        have hdhs_idx : evictedSecretIdx (clamp (gamma evictedI0 S g st1.dhs)) = some skIdx' := by
          change evictedSecretIdx (clamp (gamma evictedI0 S g (randTerm tr₁.length 32))) =
            some skIdx'
          rw [hdhs_bytes]; exact hcoins
        rw [htr'] at hle_next ⊢
        unfold decTailTr at hle_next ⊢
        dsimp only at hle_next ⊢
        let tr_sk := Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr
          (st1.sessionInfo "bob") w.msg.ratchetKey c.rIdx stateIdx c.chainKey c.index
          (w.msg.counter.toNat - c.index.toNat) tr_pre
        let tr_rec := tr_sk.append
          (TREvE (TREvent.Received "bob" st1.peer w.msg.ratchetKey w.msg.counter w.ptTerm))
        let tr_mk := tr_rec.append
          (TREvE (TREvent.MessageKey (st1.sessionInfo "bob") .receiver
            w.seed w.pqSalt w.msg.counter c.rIdx stateIdx))
        let stB' : TRState := { st1 with recv := setRecvChain st1.recv w.c', spqr := w.spqr' }
        have hge : tr₁.length ≤ tr_mk.length := by
          dsimp only [tr_mk, tr_rec, tr_sk]
          rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
              Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
              Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr_length, decRatchetPreTr_length]
          omega
        have hat_new : ((tr_mk.append (⟨⟨"bob", stB'⟩⟩ : TRStEntry)).at? tr_mk.length :
            Option TRStEntry) = some ⟨⟨"bob", stB'⟩⟩ := by
          rw [Symbolic.Swarm.CREF.at?_append_length]; rfl
        have hmk_none : ∀ j, tr₁.length ≤ j → (tr_mk.at? j : Option TRStEntry) = none := by
          intro j hj
          dsimp only [tr_mk, tr_rec, tr_sk, tr_pre]
          rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_stEntry_logSkippedKeysTr]
          unfold decRatchetPreTr
          rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_eq_none_of_le tr₁ hj]
        have hrecv_new : stB'.recv.map (fun x => gamma evictedI0 S g x.ratchetKey) =
            ((recvIdxs ++ [pkIdx]).drop ((recvIdxs.length + 1) - 5)).map evictedPubOfIdx := by
          have hmap0 := congrArg (List.map (gamma evictedI0 S g))
            (setRecvChain_map_ratchetKey st1.recv w.c')
          rw [List.map_map, List.map_map] at hmap0
          refine hmap0.trans ?_
          have hlen : st.recv.length = recvIdxs.length := by
            have := congrArg List.length hrecv_map
            simpa only [List.length_map] using this
          dsimp only [st1, trDhRatchetState, maxReceiverChains]
          simp only [Function.comp_def]
          rw [List.map_drop, List.map_append, hrecv_map, hlen]
          dsimp only [List.map]
          rw [hrk_w]
          symm
          rw [List.map_drop, List.map_append]
          rfl
        refine bobActiveInv_of_unique_new hinv₁ hle_next hge hat_new ?_ hinit hrecv_new hdhs_idx
        intro j s0 hj hat
        by_cases hlt : j < tr_mk.length
        · rw [at?_append_of_lt _ _ hlt, hmk_none j hj] at hat; cases hat
        · by_cases heq : j = tr_mk.length
          · subst heq
            rw [Symbolic.Swarm.CREF.at?_append_length] at hat
            injection hat with h1; injection h1 with h2; injection h2 with _ hs0
            exact ⟨rfl, hs0.symm⟩
          · rw [at?_eq_none_of_le (tr_mk.append (⟨⟨"bob", stB'⟩⟩ : TRStEntry))
                (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                      Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat
            cases hat
  | _ => cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInvB
