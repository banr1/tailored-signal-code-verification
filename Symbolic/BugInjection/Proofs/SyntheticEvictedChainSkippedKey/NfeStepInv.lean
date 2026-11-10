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
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Alice Step Wrappers, Decrypt Unpacking, and Bob's Call 3 Transition

Proves preservation of `NoBobState` and `BobActiveInv` across `"alice"` steps, refutes
`messageDecryptSkipped` when the message ratchet key is absent from `st.recv`, and unpacks
succeeding DH-ratchet `messageDecrypt` steps into `DecryptRatchetWitness`. Also establishes
`BobActiveInv` after Bob's `bobStart` handshake on Call 3.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv

open scoped DY.Libsignal.Composed
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg TREvent RecvChain findRecvChain consumeMessageKey
   computeMac trMsgKeys messageVersion x25519LowOrder
   receiveSignalMsg verifyMacAndDecrypt ensureReceiverChain
   messageDecrypt messageDecryptSkipped)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds Move
   gamma ecKey clamp randTerm rngEntry received receivedPlaintext newRandoms
   bobOpkPk bobVis pqExposureAt trExposureAt exposures stepView
   runSteps RunMatches OutputsMatch ReadsFaithfully GhostWF inputKind runWrapped)
open Symbolic.Swarm.COMPOSED.CompTrace
  (TRStEntry run_bind_fst receiveMessage_snd)
open Symbolic.Swarm.CREF
  (rpkT_bobStart_inv rpkT_bobDoneBaseKeys_bobStartTr
   rpkR_finalSt rpkR_bobStartTr_last rpkBH_trStateStoredAt_bobStartTr
   rpkT_receiveMessage_fst rpkT_at?_of_getMessageSentAt rpkT_getMessageSentAt_of_at?
   rpkT_receiveSignalMsg_some rpkT_verifyMacAndDecrypt_some
   bobRatchetedSt bobRatchetedChain bks_stored_of_getLocalState)
open Symbolic.Swarm.CREF.CliPure
  (newRandoms_bobStartTr receivedPlaintext_bobStartTr)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Swarm.CREF.TR.RecvDec
  (getLocalState_snd receiveSignalMsg_run ensureReceiverChain_run_ratchet trDhRatchetState)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev evictedPubOfIdx_inj ev3_preKey_fields ev3_coins_idx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (NoBobState noNewBobState_trans noNewBobState_runSteps_network noNewBobState_step_alice
   noBobState_of_noNew BobActiveInv noNewBobState_preserves_active setRecvChain_map_ratchetKey
   step_ok_decrypt step_ok_decryptSkipped step_next_bobStart drawsMatch_single_pin)

theorem alice_step_noBobState {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v : List VisEntry}
    (h0 : NoBobState tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (halice : e.party = "alice")
    (hrm : RunMatches evictedI0 r S g (runSteps pre tr) s e v initIds) :
    NoBobState (s.next (runSteps pre tr)) := by
  have hp : s.party? = some "alice" := hrm.2.1.trans (congrArg some halice)
  exact noBobState_of_noNew
    (noNewBobState_trans (noNewBobState_runSteps_network pre tr hnet)
      (noNewBobState_step_alice (runSteps pre tr) hrm.1 hp))
    h0

theorem alice_step_active {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v : List VisEntry}
    (hinv : BobActiveInv S g recvIdxs skIdx tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (halice : e.party = "alice")
    (hrm : RunMatches evictedI0 r S g (runSteps pre tr) s e v initIds) :
    BobActiveInv S g recvIdxs skIdx (s.next (runSteps pre tr)) := by
  have hp : s.party? = some "alice" := hrm.2.1.trans (congrArg some halice)
  exact noNewBobState_preserves_active
    (noNewBobState_trans (noNewBobState_runSteps_network pre tr hnet)
      (noNewBobState_step_alice (runSteps pre tr) hrm.1 hp))
    hinv

theorem findRecvChain_none_of_not_mem {S : OpaqueSymbolSemantics} {g : Ghost}
    {recv : List RecvChain} {recvIdxs : List (Fin 16)} {pk : DY.Bytes} {pkIdx : Fin 16}
    (hrecv : recv.map (fun c => gamma evictedI0 S g c.ratchetKey) = recvIdxs.map evictedPubOfIdx)
    (hpk : gamma evictedI0 S g pk = evictedPubOfIdx pkIdx)
    (hnotMem : pkIdx ∉ recvIdxs) :
    findRecvChain recv pk = none := by
  unfold findRecvChain
  cases hf : recv.find? (fun x => x.ratchetKey == pk) with
  | none => rfl
  | some c =>
    exfalso
    have hmem : c ∈ recv := List.mem_of_find?_eq_some hf
    have hp := List.find?_some (p := fun x : RecvChain => x.ratchetKey == pk) hf
    have heq : c.ratchetKey = pk := beq_iff_eq.mp hp
    have hmem_map : gamma evictedI0 S g c.ratchetKey ∈
        recv.map (fun x => gamma evictedI0 S g x.ratchetKey) :=
      List.mem_map_of_mem hmem
    rw [heq, hpk, hrecv, List.mem_map] at hmem_map
    obtain ⟨idx, hidx_mem, hidx_eq⟩ := hmem_map
    exact hnotMem (evictedPubOfIdx_inj hidx_eq ▸ hidx_mem)

theorem not_decryptSkipped_of_find_none {me : Participant} {stateIdx msgIdx sk pq : Nat}
    {spqr : UInt32} {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg}
    (hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hmsg : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    (hfind : findRecvChain st.recv msg.ratchetKey = none) :
    (Step.messageDecryptSkipped me stateIdx msgIdx sk pq spqr).ok tr = false := by
  rw [step_ok_decryptSkipped]
  obtain ⟨t, hat, hparse, hver⟩ := rpkT_receiveSignalMsg_some hmsg
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run (rpkT_getMessageSentAt_of_at? hat) hparse hver
  unfold messageDecryptSkipped
  rw [run_bind_fst, hst, getLocalState_snd]
  dsimp only
  rw [run_bind_fst, hrcv1, hrcv2]
  dsimp only
  rw [run_bind_fst]
  rcases ((DY.getEntry sk : Traceful (DY.ProtocolEvent.ExecEntryT TREvent)).run tr).1 with
    _ | ⟨⟨ev_sk⟩⟩
  · rfl
  · dsimp only
    cases ev_sk with
    | SkippedKeyStored s pk n seed rIdx src =>
      dsimp only
      have hguard_false : ¬ (s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
          (findRecvChain st.toDRState.recv pk).isSome = true) := by
        rintro ⟨_, rfl, _, his⟩
        change (findRecvChain st.recv msg.ratchetKey).isSome = true at his
        rw [hfind] at his
        cases his
      simp only [_root_.guard, hguard_false, ↓reduceIte, run_bind_fst, DY.Traceful.run_failure]
      rfl
    | _ =>
      dsimp only
      rw [DY.Traceful.run_failure]
      rfl

/-- Witnesses unpacked from a succeeding `messageDecrypt` step when `findRecvChain = none`. -/
structure DecryptRatchetWitness (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqr : UInt32) (tr : ExecTrace) (st : TRState) where
  t : DY.Bytes
  msg : TRSignalMsg
  seed : DY.Bytes
  c' : RecvChain
  spqr' : DY.Bytes
  key : DY.Bytes
  pqSalt : DY.Bytes
  ptTerm : DY.Bytes
  hmsg : tr.getMessageSentAt msgIdx = some t
  hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg
  hver : msg.version = messageVersion
  hlow : x25519LowOrder msg.ratchetKey = false
  hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter =
    some (seed, c')
  hspqr : DY.Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr
    msg.pqRatchet spqr = some (spqr', key)
  hpqSalt : (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
    (⟨key⟩ : DY.Network.ExecEntryT)).at? pqIdx : Option DY.Network.ExecEntryT) = some ⟨pqSalt⟩
  hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
    (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
    (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire
  hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
    msg.ciphertext = some ptTerm

theorem decrypt_ratchet_inv {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqr : UInt32} {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg}
    (hok : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqr).ok tr = true)
    (hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hmsg_run : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    (hfind : findRecvChain st.recv msg.ratchetKey = none) :
    ∃ w : DecryptRatchetWitness me stateIdx msgIdx pqIdx spqr tr st, w.msg = msg := by
  rw [step_ok_decrypt] at hok
  obtain ⟨t, hat, hparse, hver⟩ := rpkT_receiveSignalMsg_some hmsg_run
  have hmsg_at := rpkT_getMessageSentAt_of_at? hat
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run hmsg_at hparse hver
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hok
  rw [run_bind_fst, hst, getLocalState_snd] at hok; dsimp only at hok
  rw [run_bind_fst, hrcv1, hrcv2] at hok; dsimp only at hok
  have hlow : x25519LowOrder msg.ratchetKey = false := by
    cases hl : x25519LowOrder msg.ratchetKey with
    | false => rfl
    | true =>
      exfalso
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at hok; unfold DY.Libsignal.TripleRatchet.recvChainFor TRState.toDRState at hok
      dsimp only at hok
      rw [hfind, hl] at hok
      simp only [↓reduceIte, run_bind_fst, DY.Traceful.run_failure] at hok
      cases hok
  obtain ⟨hens1, hens2⟩ := ensureReceiverChain_run_ratchet tr hfind hlow
  rw [run_bind_fst, hens1, hens2] at hok; dsimp only at hok
  let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
  let c := (trDhRatchetState st msg.ratchetKey tr.length).2
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · rw [hcons, DY.Traceful.run_failure] at hok; cases hok
  · rw [hcons] at hok; dsimp only at hok
    rcases hspqr : DY.Spqr.spqrRecv st1.spqr msg.pqRatchet spqr with _ | ⟨spqr', key⟩
    · rw [hspqr, DY.Traceful.run_failure] at hok; cases hok
    · rw [hspqr] at hok; dsimp only at hok
      let tr_r := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
      let tr_k := tr_r.append (⟨key⟩ : DY.Network.ExecEntryT)
      have hsm1 : ((DY.Network.sendMessage key).run tr_r).1 = some tr_r.length :=
        (Runs.sendMessage tr_r key).1
      have hsm2 : ((DY.Network.sendMessage key).run tr_r).2.val = tr_k :=
        (Runs.sendMessage tr_r key).2
      rw [run_bind_fst, hsm1, hsm2] at hok; dsimp only at hok
      rw [run_bind_fst, rpkT_receiveMessage_fst, receiveMessage_snd] at hok
      rcases hpq : tr_k.getMessageSentAt pqIdx with _ | pqSalt
      · rw [hpq] at hok; cases hok
      · rw [hpq] at hok; dsimp only at hok
        rw [run_bind_fst] at hok
        rcases hv : ((verifyMacAndDecrypt st1 msg pqSalt seed).run tr_k).1 with _ | ptTerm
        · rw [hv] at hok; cases hok
        · have ⟨hmac_eq, _⟩ := rpkT_verifyMacAndDecrypt_some hv
          have hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey
              (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm := by
            unfold verifyMacAndDecrypt at hv
            simp only [_root_.guard, hmac_eq, ↓reduceIte, run_bind_fst,
              DY.Traceful.run_pure] at hv
            dsimp only [liftM, monadLift, MonadLift.monadLift] at hv
            rw [DY.Traceful.run_mk] at hv
            exact hv
          exact ⟨⟨t, msg, seed, c', spqr', key, pqSalt, ptTerm,
            hmsg_at, hparse, hver, hlow, hcons, hspqr,
            rpkT_at?_of_getMessageSentAt hpq, hmac_eq, hdec⟩, rfl⟩

theorem exposures_kind_leak {tr tr' : ExecTrace} {w : VisEntry}
    (hw : w ∈ exposures tr tr') : w.kind = .leak := by
  unfold exposures at hw
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
    unfold pqExposureAt at hj
    rcases h : tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent j with _ | ev <;> rw [h] at hj
    · cases hj
    · cases ev <;> simp at hj <;> subst hj <;> rfl
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
    unfold trExposureAt at hj
    rcases h : tr'.getEventAt TREvent j with _ | ev <;> rw [h] at hj
    · cases hj
    · cases ev <;> simp at hj <;> subst hj <;> rfl

theorem recv_outputs_accept {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {e : RunEvent} {outs : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hexit : ∃ out, e.exit = some (0, out))
    (hcmd : ∃ peer, e.cmd = .recv peer)
    (hout : OutputsMatch evictedI0 r S g e outs initIds) :
    ∃ w_out, outs = [w_out] ∧ w_out.kind = .accept := by
  obtain ⟨out, he⟩ := hexit
  obtain ⟨peer, hc⟩ := hcmd
  unfold OutputsMatch at hout
  rw [he, hc] at hout
  obtain ⟨w_out, rfl, hbm⟩ := hout
  exact ⟨w_out, rfl, hbm.1.symm⟩

theorem split_vis_recv_rng {inp v₀ v₂ w_out : VisEntry} {drs rest : List VisEntry}
    {ts : Nat}
    (hvis : inp :: (drs ++ [w_out]) = v₀ :: rngEntry (randTerm ts 32) :: v₂ :: rest)
    (hkind : w_out.kind = .accept) :
    inp = v₀ ∧ ∃ drs_rest, drs = rngEntry (randTerm ts 32) :: drs_rest := by
  injection hvis with hinp htail
  refine ⟨hinp, ?_⟩
  cases drs with
  | nil =>
    dsimp only [List.nil_append] at htail
    injection htail with hw _
    rw [hw] at hkind
    cases hkind
  | cons d drs_rest =>
    dsimp only [List.cons_append] at htail
    injection htail with hd _
    exact ⟨drs_rest, congrArg (· :: drs_rest) hd⟩

theorem bob_call3_step {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {v visAll : List VisEntry}
    (halice_r : r.alice = "alice")
    (hgwf : GhostWF g visAll)
    (hnoBob : NoBobState tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (hrm : RunMatches evictedI0 r S g (runSteps pre tr) s (ev 3) v initIds)
    (hsub : ∀ w ∈ v, w ∈ visAll) :
    BobActiveInv S g [⟨4, by decide⟩] ⟨5, by decide⟩ (s.next (runSteps pre tr)) := by
  set tr₃ := runSteps pre tr
  have hnoBob₃ : NoBobState tr₃ :=
    noBobState_of_noNew (noNewBobState_runSteps_network pre tr hnet) hnoBob
  obtain ⟨_hcls, hparty, hfits, hpeer, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, _hbm_in, hdr, hout, hrf, _hpf⟩ := hrm
  have hbob : (ev 3).party = "bob" := rfl
  have hcmd : ∃ peer, (ev 3).cmd = .recv peer := ⟨_, rfl⟩
  obtain ⟨peer₃, hcmd₃⟩ := hcmd
  rw [hbob] at hparty
  rw [hcmd₃] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨peer₃, hcmd₃⟩ hout
  cases s with
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    exfalso
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decrypt] at hok
    unfold messageDecrypt at hok
    rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₃).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₃ stateIdx st (bks_stored_of_getLocalState hst)
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    exfalso
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decryptSkipped] at hok
    unfold messageDecryptSkipped at hok
    rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₃).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₃ stateIdx st (bks_stored_of_getLocalState hst)
  | bobStart b a kh regA mh pqIdx spqr =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have ha : a = "alice" := by
      simpa [Step.MatchesSetupPeer, halice_r] using hpeer
    subst ha
    have hnext_mv := step_next_bobStart "bob" "alice" kh regA mh pqIdx spqr tr₃
    have hview : stepView (.bobStart "bob" "alice" kh regA mh pqIdx spqr) tr₃
        (runWrapped (ev 3)) =
        bobVis tr₃ ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃)
          mh (bobOpkPk "bob" kh tr₃) ++
        exposures tr₃ ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃) := by
      unfold stepView
      simp only [hok, ↓reduceIte]
      rw [hnext_mv]
    have hpt_some : ∃ pt,
        receivedPlaintext tr₃
          ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃) = some pt := by
      rcases hpt : receivedPlaintext tr₃
          ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃) with _ | pt
      · exfalso
        have hw_mem : w_out ∈ v := by rw [hv_split]; simp
        rw [hvis_eq, hview, List.mem_append] at hw_mem
        rcases hw_mem with hw_bob | hw_exp
        · simp only [bobVis, hpt, Option.map_none, Option.toList_none, List.append_nil,
            List.mem_cons, List.mem_map] at hw_bob
          rcases hw_bob with rfl | ⟨_, _, rfl⟩ <;> simp [rngEntry] at hw_accept
        · have := exposures_kind_leak hw_exp
          rw [hw_accept] at this; cases this
      · exact ⟨pt, rfl⟩
    obtain ⟨pt, hpt⟩ := hpt_some
    obtain ⟨w⟩ := rpkT_bobStart_inv hpt
    have htr' : (Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₃ =
        Symbolic.Swarm.CREF.bobStartTr tr₃ "bob" "alice" w.out w.msg w.c'
          w.spqr' w.key w.seed w.pqSalt w.m :=
      hnext_mv.trans (w.next_eq 0)
    have hrec_terms : received tr₃ [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
      simp only [received, List.filterMap_cons, List.filterMap_nil,
        rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
        rpkT_getMessageSentAt_of_at? w.hmsg]
    have hvis_full : v =
        ⟨.recv, [w.ek, w.ct, w.raw] ++ (bobOpkPk "bob" kh tr₃).toList, .preKeyRecv, none⟩ ::
        rngEntry (randTerm tr₃.length 32) ::
        ⟨.accept, [w.m], .single,
          DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone tr₃
            (Symbolic.Swarm.CREF.bobStartTr tr₃ "bob" "alice"
              w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m)⟩ ::
        exposures tr₃ (Symbolic.Swarm.CREF.bobStartTr tr₃ "bob" "alice"
          w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m) := by
      rw [hvis_eq, hview, w.next_eq 0]
      unfold bobVis
      rw [hrec_terms, newRandoms_bobStartTr, receivedPlaintext_bobStartTr]
      rfl
    obtain ⟨hinp_eq, drs_rest, hdrs_eq⟩ :=
      split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
    have hrng_mem : rngEntry (randTerm tr₃.length 32) ∈ visAll := by
      apply hsub
      rw [hv_split, hdrs_eq]; simp
    rw [hdrs_eq] at hdr
    have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
    have hdhs_idx : evictedSecretIdx
        (clamp (gamma evictedI0 S g (randTerm tr₃.length 32))) = some ⟨5, by decide⟩ := by
      rw [hdhs_bytes]; exact ev3_coins_idx
    obtain ⟨_, p₃, hp₃, hp₃_bk, hp₃_rk, _⟩ := ev3_preKey_fields
    rw [hinp_eq] at hrf
    dsimp only [ReadsFaithfully, List.cons_append] at hrf
    obtain ⟨_, _, _, hpk_matches, p₃', hp₃', msg', hparse', _, _, _, _, hrk_eq, _⟩ := hrf
    obtain ⟨p₃'', hp₃'', hbk_eq, _⟩ := hpk_matches
    rw [hp₃] at hp₃' hp₃''
    cases hp₃'; cases hp₃''
    rw [w.hparse] at hparse'
    cases hparse'
    have hek_eq : ecKey (gamma evictedI0 S g w.ek) = ecKey (evictedPubOfIdx ⟨3, by decide⟩) :=
      hbk_eq.symm.trans hp₃_bk
    have hrk4 : gamma evictedI0 S g w.msg.ratchetKey = evictedPubOfIdx ⟨4, by decide⟩ :=
      hrk_eq.trans hp₃_rk
    rw [htr']
    obtain ⟨tr₀, hlast⟩ := rpkR_bobStartTr_last w
    have hat_final : ((Symbolic.Swarm.CREF.bobStartTr tr₃ "bob" "alice"
        w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m).at? tr₀.length :
        Option TRStEntry) = some ⟨⟨"bob", rpkR_finalSt w⟩⟩ := by
      rw [hlast, Symbolic.Swarm.CREF.at?_append_length]; rfl
    have hchild_eq : tr₀.length =
        (Symbolic.Swarm.CREF.bobStartPreSkipTr tr₃ "bob" "alice" w.out w.msg w.key).length +
          (w.msg.counter.toNat -
            (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).index.toNat) + 2 := by
      rcases rpkBH_trStateStoredAt_bobStartTr w hat_final with ⟨_, h0⟩ | ⟨heq, _, _⟩
      · exact False.elim (hnoBob₃ _ _ h0)
      · exact heq
    have huniq_all : ∀ i st,
        ((Symbolic.Swarm.CREF.bobStartTr tr₃ "bob" "alice"
          w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m).at? i :
          Option TRStEntry) = some ⟨⟨"bob", st⟩⟩ →
        i = tr₀.length ∧ st = rpkR_finalSt w := by
      intro i st hat
      rcases rpkBH_trStateStoredAt_bobStartTr w hat with ⟨_, h0⟩ | ⟨hi, _, hst_eq⟩
      · exact False.elim (hnoBob₃ _ _ h0)
      · exact ⟨hi.trans hchild_eq.symm, hst_eq⟩
    refine ⟨?_, ⟨tr₀.length, rpkR_finalSt w, hat_final, ?_, ?_, ?_⟩, ?_⟩
    · intro i st hat
      obtain ⟨_, rfl⟩ := huniq_all i st hat
      rfl
    · intro j st hj hat
      obtain ⟨hj_eq, _⟩ := huniq_all j st hat
      omega
    · unfold rpkR_finalSt
      dsimp only
      have hmap0 := congrArg (List.map (gamma evictedI0 S g))
        (setRecvChain_map_ratchetKey
          (bobRatchetedSt "alice" w.out.ikB w.out.ikA w.out.keys w.out.spkSk
            w.msg.ratchetKey (randTerm tr₃.length 32)).recv w.c')
      rw [List.map_map, List.map_map] at hmap0
      refine hmap0.trans ?_
      unfold bobRatchetedSt bobRatchetedChain
      dsimp only [List.map]
      exact congrArg (· :: []) hrk4
    · unfold rpkR_finalSt bobRatchetedSt
      dsimp only
      exact hdhs_idx
    · refine ⟨w.ek, ?_, hek_eq⟩
      rw [rpkT_bobDoneBaseKeys_bobStartTr]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  | _ => cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
