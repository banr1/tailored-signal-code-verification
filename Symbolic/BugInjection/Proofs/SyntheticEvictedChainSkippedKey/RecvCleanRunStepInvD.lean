/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation

/-!
# Clean-Run Prefix Step Agreement: Whisper `.recv`

Step agreement for whisper receive calls (`5 + 2 * h` for `h < 10`) along the clean-run prefix.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvD

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.TripleRatchet
  (TRState TREvent RecvChain findRecvChain setRecvChain kdfCk maxReceiverChains
   receiveSignalMsg messageDecrypt messageDecryptSkipped)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma clamp runSteps stepView bobVis decVis bobOpkPk received
   exposures rngEntry randTerm GhostWF RunMatches ReadsFaithfully
   PreKeyRecvMatches PreKeyRecvOpkMatches)
open Symbolic.Swarm.COMPOSED.CompTrace
  (TRStEntry TREvE run_bind_fst)
open Symbolic.Swarm.CREF
  (rpkT_getMessageSentAt_of_at? rpkT_receiveSignalMsg_some)
open Symbolic.Swarm.CREF.TR
  (gamma_rand)
open Symbolic.Swarm.CREF.TR.RecvDec
  (getLocalState_snd at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   at?_stEntry_logSkippedKeysTr trDhRatchetState decRatchetPreTr decRatchetPreTr_length
   decTailTr decrypt_next_ratchet_eq newRandoms_decRatchet
   receivedPlaintext_decTailTr receivedPlaintext_decRatchetPreTr)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encMsg ratchetState recvSt recvKey)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (WhisperInputSpec)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (setRecvChain_map_ratchetKey step_le_next preCond_messageDecrypt
   preCond_messageDecryptSkipped step_ok_decrypt step_next_decrypt
   step_ok_decryptSkipped drawsMatch_single_pin)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
  (findRecvChain_none_of_not_mem not_decryptSkipped_of_find_none decrypt_ratchet_inv
   recv_outputs_accept split_vis_recv_rng)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (bytesToLiteral_spqrSendMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (gClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
  (StateBytesAgree stateBytesAgree_decrypt_ratchet)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRep
  (encMsg_tryFrom_inv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
  (PeeledCall PkiUnchanged pkiUnchanged_runSteps_network pkiUnchanged_step_party)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
  (NoNewPartyState noNewPartyState_trans noNewPartyState_runSteps_network
   noNewPartyState_step_other ActivePartySt noNewPartyState_preserves_active
   activePartySt_pin_state activePartySt_of_unique_new)

/-- Steps a whisper `.recv` call across a network prefix `c.pre`. Since `pkIdx ∉ recvIdxs` rules out
`messageDecryptSkipped` and non-prekey wire tags rule out `bobStart`, the step is a DH-ratchet
`messageDecrypt` that updates `ActivePartySt` via `stateBytesAgree_decrypt_ratchet`. -/
theorem party_whisper_recv_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {receiver otherParty : Participant} {initRole : Bool}
    {recvIdxs : List (Fin 16)} {skIdx pkIdx skIdx' : Fin 16}
    {stSendClean stRecvClean : TRState} {coinsClean pqKeyClean ptClean : Bytes}
    {tsDhsNew : Nat} {tr : ExecTrace} {c : PeeledCall} {e : RunEvent}
    (hne_other : otherParty ≠ receiver)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hAct : ActivePartySt receiver initRole S g (gClean r cls) recvIdxs skIdx stRecvClean tr)
    (he_party : e.party = receiver ∧ ∃ peer, e.cmd = .recv peer)
    (hwh : WhisperInputSpec e pkIdx)
    (hcoins : evictedSecretIdx (clamp (e.coins.take 32)) = some skIdx')
    (hnotMem : pkIdx ∉ recvIdxs)
    (hsent_wire : e.input =
      wireWhisperTag :: gamma evictedI0 S (gClean r cls)
        (encMsg stSendClean coinsClean pqKeyClean ptClean))
    (hrk_len_clean : (gamma evictedI0 S (gClean r cls) (dhPk stSendClean.dhs)).length = 32)
    (hspqr_recv : stRecvClean.spqr.view? DY.Spqr.InitState.SubF = none)
    (hdhs_clean : (gClean r cls).σ tsDhsNew 32 = e.coins.take 32)
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hpre : c.s.PreCond (runSteps c.pre tr))
    (hrm : RunMatches evictedI0 r S g (runSteps c.pre tr) c.s e c.v (some (none, 7#32, 9#32)))
    (hsub : ∀ w ∈ c.v, w ∈ visAll) :
    let tr' := c.s.next (runSteps c.pre tr)
    let pqMsgClean := (DY.Spqr.spqrSend stSendClean.spqr coinsClean).2.2
    let rsClean := ratchetState stRecvClean (dhPk stSendClean.dhs) (rnd tsDhsNew 32)
    let cClean' : RecvChain := { rsClean.2 with chainKey := (kdfCk rsClean.2.chainKey).1, index := 1 }
    let stRecvOutClean : TRState :=
      { rsClean.1 with recv := setRecvChain rsClean.1.recv cClean',
                       spqr := recvSt stRecvClean.spqr pqMsgClean }
    PkiUnchanged tr' ∧
    ActivePartySt receiver initRole S g (gClean r cls)
      ((recvIdxs ++ [pkIdx]).drop ((recvIdxs.length + 1) - 5)) skIdx' stRecvOutClean tr' ∧
    NoNewPartyState otherParty tr tr' := by
  set tr₁ := runSteps c.pre tr
  have hpki₁ : PkiUnchanged tr₁ := pkiUnchanged_runSteps_network c.pre hnet hpki
  have hAct₁ : ActivePartySt receiver initRole S g (gClean r cls) recvIdxs skIdx stRecvClean tr₁ :=
    noNewPartyState_preserves_active (noNewPartyState_runSteps_network c.pre tr hnet) hAct
  obtain ⟨_, hparty, hfits, _, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, hrf, _⟩ := hrm
  obtain ⟨hparty_rec, peer, hcmd⟩ := he_party
  obtain ⟨hwrap, hnpk, body, m_wire, hin_eq, htry, hm_rk, _⟩ := hwh
  rw [hparty_rec] at hparty
  rw [hcmd] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨peer, hcmd⟩ hout
  cases hs : c.s with
  | bobStart b a kh regA mh pqIdx spqr =>
    exfalso
    rw [hs] at hok hvis_eq
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
    rw [hs] at hparty hpre hok hvis_eq
    simp only [Step.party?, Option.some.injEq] at hparty; subst me
    have hcur := preCond_messageDecryptSkipped hpre
    have hok_copy := hok
    rw [step_ok_decryptSkipped] at hok_copy
    unfold messageDecryptSkipped at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState receiver stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · try rw [hst] at hok_copy
      cases hok_copy
    · try rw [hst] at hok_copy
      rw [getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₁).1 with _ | msg
      · try rw [hmsg_run] at hok_copy
        cases hok_copy
      · obtain ⟨_, _, hrecv_map, _⟩ := activePartySt_pin_state hAct₁ hst hcur
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
    rw [hs] at hparty hpre hok hvis_eq
    simp only [Step.party?, Option.some.injEq] at hparty; subst me
    have hpki' : PkiUnchanged ((Step.messageDecrypt receiver stateIdx msgIdx pq spqr).next tr₁) :=
      pkiUnchanged_step_party rfl hpki₁
    have hnoNewOther : NoNewPartyState otherParty tr
        ((Step.messageDecrypt receiver stateIdx msgIdx pq spqr).next tr₁) :=
      noNewPartyState_trans (noNewPartyState_runSteps_network c.pre tr hnet)
        (noNewPartyState_step_other tr₁ rfl
          (by dsimp only [Step.party?]; intro heq; injection heq with h; exact hne_other h.symm))
    have hcur := preCond_messageDecrypt hpre
    have hle_next := step_le_next (.messageDecrypt receiver stateIdx msgIdx pq spqr) tr₁
    have hok_copy := hok
    rw [step_ok_decrypt] at hok_copy
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState receiver stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · try rw [hst] at hok_copy
      cases hok_copy
    · try rw [hst] at hok_copy
      rw [getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₁).1 with _ | msg
      · try rw [hmsg_run] at hok_copy
        cases hok_copy
      · obtain ⟨hinit, hagree_st, hrecv_map, _⟩ := activePartySt_pin_state hAct₁ hst hcur
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
        have hrf_fields := (hrf.2.2.2 msg hparse₀).2.2.2 m_wire htry
        have hrk_eq : gamma evictedI0 S g msg.ratchetKey = evictedPubOfIdx pkIdx :=
          hrf_fields.2.1.trans hm_rk
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk_eq hnotMem
        obtain ⟨w, hw_msg⟩ := decrypt_ratchet_inv hok hst hmsg_run hfind
        have hrk_w : gamma evictedI0 S g w.msg.ratchetKey = evictedPubOfIdx pkIdx := by
          rw [hw_msg]; exact hrk_eq
        have hrk_w_wire : gamma evictedI0 S g w.msg.ratchetKey =
            m_wire.senderRatchetKey.bytes.toList := by
          rw [hw_msg]; exact hrf_fields.2.1
        have hpq_w_wire : gamma evictedI0 S g w.msg.pqRatchet = m_wire.pqRatchet := by
          rw [hw_msg]; exact hrf_fields.2.2.1
        have hfind_w : findRecvChain st.recv w.msg.ratchetKey = none := by
          rw [hw_msg]; exact hfind
        let st1 := (trDhRatchetState st w.msg.ratchetKey tr₁.length).1
        let cChain := (trDhRatchetState st w.msg.ratchetKey tr₁.length).2
        let tr_pre := decRatchetPreTr tr₁ receiver st1 w.msg.ratchetKey w.key
        have htr' : (Step.messageDecrypt receiver stateIdx msgIdx pq spqr).next tr₁ =
            decTailTr tr_pre receiver stateIdx st1 cChain w.c' w.msg.ratchetKey w.seed
              w.pqSalt w.ptTerm w.spqr' w.msg.counter :=
          (step_next_decrypt receiver stateIdx msgIdx pq spqr tr₁).trans
            (decrypt_next_ratchet_eq hst w.hmsg w.hparse w.hver hfind_w w.hlow
              w.hcons w.hspqr w.hpqSalt w.hmac_eq w.hdec)
        have hvis_full : c.v =
            ⟨.recv, [w.t], .whisper, none⟩ ::
            rngEntry (randTerm tr₁.length 32) ::
            ⟨.accept, [w.ptTerm], .single, none⟩ ::
            exposures tr₁ (decTailTr tr_pre receiver stateIdx st1 cChain w.c' w.msg.ratchetKey
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
        obtain ⟨_, _, hdrs_eq⟩ :=
          split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
        have hrng_mem : rngEntry (randTerm tr₁.length 32) ∈ visAll := by
          apply hsub; rw [hv_split, hdrs_eq]; simp
        rw [hdrs_eq] at hdr
        have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
        have hdhs_idx : evictedSecretIdx (clamp (gamma evictedI0 S g st1.dhs)) = some skIdx' := by
          change evictedSecretIdx (clamp (gamma evictedI0 S g (randTerm tr₁.length 32))) =
            some skIdx'
          rw [hdhs_bytes]; exact hcoins
        have hdhsNew_gam : gamma evictedI0 S g (randTerm tr₁.length 32) =
            gamma evictedI0 S (gClean r cls) (rnd tsDhsNew 32) := by
          rw [hdhs_bytes]; unfold rnd; rw [gamma_rand]; simp [hdhs_clean]
        have hb_clean : gamma evictedI0 S (gClean r cls)
            (encMsg stSendClean coinsClean pqKeyClean ptClean) = body :=
          (List.cons.inj (hsent_wire.symm.trans hin_eq)).2
        obtain ⟨_, _, _, hrk_clean_wire, hpq_clean_wire, _, _⟩ :=
          encMsg_tryFrom_inv hb_clean hrk_len_clean htry
        have hrkMsg_gam : gamma evictedI0 S g w.msg.ratchetKey =
            gamma evictedI0 S (gClean r cls) (dhPk stSendClean.dhs) :=
          hrk_w_wire.trans hrk_clean_wire.symm
        let pqMsgClean := (DY.Spqr.spqrSend stSendClean.spqr coinsClean).2.2
        have hpqMsg_gam : gamma evictedI0 S g w.msg.pqRatchet =
            gamma evictedI0 S (gClean r cls) pqMsgClean :=
          hpq_w_wire.trans hpq_clean_wire.symm
        have hspqr_clean : DY.Spqr.spqrRecv stRecvClean.spqr pqMsgClean 1 =
            some (recvSt stRecvClean.spqr pqMsgClean, recvKey stRecvClean.spqr pqMsgClean) := by
          dsimp only [pqMsgClean]
          unfold DY.Spqr.spqrRecv DY.Spqr.spqrEmptyMsg
          rw [bytesToLiteral_spqrSendMsg, hspqr_recv]; rfl
        let rsClean := ratchetState stRecvClean (dhPk stSendClean.dhs) (rnd tsDhsNew 32)
        let cClean' : RecvChain :=
          { rsClean.2 with chainKey := (kdfCk rsClean.2.chainKey).1, index := 1 }
        have hst_agree' : StateBytesAgree S g (gClean r cls)
            { st1 with recv := setRecvChain st1.recv w.c', spqr := w.spqr' }
            { rsClean.1 with recv := setRecvChain rsClean.1.recv cClean',
                             spqr := recvSt stRecvClean.spqr pqMsgClean } :=
          stateBytesAgree_decrypt_ratchet (c' := w.c') (c'' := cClean')
            hagree_st hrkMsg_gam hdhsNew_gam hpqMsg_gam w.hspqr hspqr_clean
        refine ⟨hpki', ?_, hnoNewOther⟩
        rw [htr'] at hle_next ⊢
        unfold decTailTr at hle_next ⊢
        dsimp only at hle_next ⊢
        let tr_sk := Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr
          (st1.sessionInfo receiver) w.msg.ratchetKey cChain.rIdx stateIdx cChain.chainKey
          cChain.index (w.msg.counter.toNat - cChain.index.toNat) tr_pre
        let tr_rec := tr_sk.append
          (TREvE (TREvent.Received receiver st1.peer w.msg.ratchetKey w.msg.counter w.ptTerm))
        let tr_mk := tr_rec.append
          (TREvE (TREvent.MessageKey (st1.sessionInfo receiver) .receiver
            w.seed w.pqSalt w.msg.counter cChain.rIdx stateIdx))
        let stOut : TRState := { st1 with recv := setRecvChain st1.recv w.c', spqr := w.spqr' }
        have hge : tr₁.length ≤ tr_mk.length := by
          dsimp only [tr_mk, tr_rec, tr_sk]
          rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
              Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
              Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr_length, decRatchetPreTr_length]
          omega
        have hat_new : ((tr_mk.append (⟨⟨receiver, stOut⟩⟩ : TRStEntry)).at? tr_mk.length :
            Option TRStEntry) = some ⟨⟨receiver, stOut⟩⟩ := by
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
        have hrecv_new : stOut.recv.map (fun x => gamma evictedI0 S g x.ratchetKey) =
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
        have hinit' : stOut.initiator = initRole := hinit
        refine activePartySt_of_unique_new hAct₁ hle_next hge hat_new ?_ hinit'
          hst_agree' hrecv_new hdhs_idx
        intro j s0 hj hat
        by_cases hlt : j < tr_mk.length
        · rw [at?_append_of_lt _ _ hlt, hmk_none j hj] at hat; cases hat
        · by_cases heq : j = tr_mk.length
          · subst heq
            rw [Symbolic.Swarm.CREF.at?_append_length] at hat
            injection hat with h1; injection h1 with h2; injection h2 with _ hs0
            exact ⟨rfl, hs0.symm⟩
          · rw [at?_eq_none_of_le (tr_mk.append (⟨⟨receiver, stOut⟩⟩ : TRStEntry))
                (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                      Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat
            cases hat
  | _ => rw [hs] at hfits; cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvD
