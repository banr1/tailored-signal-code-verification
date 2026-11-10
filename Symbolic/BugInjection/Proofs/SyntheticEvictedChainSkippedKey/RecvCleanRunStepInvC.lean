/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvB
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRep
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTrace
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
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
# Clean-Run Prefix Step Agreement: Call 3 (`bobStart`)

Proves `bob_call3_agree`, which steps Call 3 (`bobStart`) across an arbitrary network prefix
`c3.pre`, matches all PQXDH handshake and initial message concretizations under `g` against
`gClean r cls`, initializes `"bob"` at `stB3Clean cls`, and records `ek ∈ bobDoneBaseKeys`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.PQXDH (BobKeyHandles PreKeyMsgHandles agree pqxdhIkm pqxdhKdf errToOption)
open DY.Libsignal.TripleRatchet
  (TRState TREvent RecvChain findRecvChain setRecvChain kdfCk maxReceiverChains
   isCurrentSnapshot receiveSignalMsg messageDecrypt messageDecryptSkipped spqrB2A)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Move PreKeyFields PreKeyRep
   gamma clamp ecKey kyberKey pubBytes secretBytes preKeyWire parsePreKeyWire
   setupSecret runSteps stepView bobVis decVis bobOpkPk received receivedPlaintext
   exposures rngEntry randTerm GhostAndSemMatchSetup GhostWF
   RunMatches ReadsFaithfully PreKeyRecvMatches PreKeyRecvOpkMatches
   bobDoneBaseKeys runWrapped)
open Symbolic.Swarm.COMPOSED.CompTrace
  (TRStEntry TREvE run_bind_fst)
open Symbolic.Swarm.CREF
  (StOpt BobStartOk rpkT_bobStart_inv rpkT_bobDoneBaseKeys_bobStartTr
   rpkR_finalSt rpkR_bobStartTr_last rpkBH_trStateStoredAt_bobStartTr
   rpkT_getMessageSentAt_of_at? rpkT_receiveSignalMsg_some
   bobRatchetedSt bobRatchetedChain bks_stored_of_getLocalState
   parsePreKeyWire_inner_tryFrom)
open Symbolic.Swarm.CREF.CliPure
  (newRandoms_bobStartTr receivedPlaintext_bobStartTr)
open Symbolic.Swarm.CREF.TR
  (gamma_rand gamma_dhPk setupSecret_eq gamma_kemSS_of_not_implicitReject ekBytes)
open Symbolic.Swarm.CREF.TR.RecvDec
  (getLocalState_snd at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   at?_stEntry_logSkippedKeysTr trDhRatchetState decRatchetPreTr decRatchetPreTr_length
   decTailTr decrypt_next_ratchet_eq newRandoms_decRatchet
   receivedPlaintext_decTailTr receivedPlaintext_decRatchetPreTr)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg bobSt0 ratchetState recvSt recvKey kemDecap_kemEncap)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA o1 stA0)
open Symbolic.BugInjection (hexBytes)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev hexDigit hexBytes_ofList WhisperInputSpec ev3_preKey_fields ev3_coins_idx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (r_names_of_fit setRecvChain_map_ratchetKey
   step_le_next preCond_messageDecrypt preCond_messageDecryptSkipped
   step_ok_decrypt step_next_decrypt step_ok_decryptSkipped step_next_bobStart
   drawsMatch_single_pin)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
  (findRecvChain_none_of_not_mem not_decryptSkipped_of_find_none decrypt_ratchet_inv
   exposures_kind_leak recv_outputs_accept split_vis_recv_rng)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (ev2_to_ev3 ev3_full_fields not_kyberMismatch_ev3)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (ratchetKeyTimestamps bytesToLiteral_spqrSendMsg
   coins1Clean coins2Clean pqm2Clean m2Clean stB3Clean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (gClean gClean_sigma_45 ghostAndSemMatchSetup_gClean gamma_dhPk_ratchetTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
  (o1_ct_eq StateBytesAgree stateBytesAgree_bobStart)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRep
  (encMsg_tryFrom_inv)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
  (PeeledCall PkiUnchanged pkiUnchanged_runSteps_network pkiUnchanged_step_party
   pki_pin_st pki_pin_reg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
  (NoPartyState NoNewPartyState noNewPartyState_trans noPartyState_of_noNew
   noNewPartyState_runSteps_network noNewPartyState_step_other
   ActivePartySt activePartySt_init)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvB
  (gamma_setup_rnd_eq)

private theorem hexBytes_go_len :
    ∀ cs : List Char, (hexBytes.go hexDigit cs).length = cs.length / 2
  | [] => by simp [hexBytes.go]
  | [_] => by simp [hexBytes.go]
  | _ :: _ :: rest => by simp only [hexBytes.go, List.length_cons, hexBytes_go_len rest]; omega

section
attribute [local irreducible] Symbolic.BugInjection.hexBytes

set_option maxRecDepth 16384 in
theorem ev3_input_len_lt : (ev 3).input.length < 2 ^ 63 := by
  rw [show (ev 3).input = hexBytes (nfe_str_of_hex (ev 3).input) from rfl,
      show (nfe_str_of_hex (ev 3).input) = String.ofList (nfe_chars_of_hex (ev 3).input) from rfl,
      hexBytes_ofList, hexBytes_go_len]
  decide

set_option maxRecDepth 16384 in
theorem ev24_input_len_lt : (ev 24).input.length < 2 ^ 63 := by
  rw [show (ev 24).input = hexBytes (nfe_str_of_hex (ev 24).input) from rfl,
      show (nfe_str_of_hex (ev 24).input) = String.ofList (nfe_chars_of_hex (ev 24).input) from rfl,
      hexBytes_ofList, hexBytes_go_len]
  decide
end

private theorem ev3_party_eq : (ev 3).party = "bob" := rfl

private theorem ev3_cmd_recv : ∃ peer, (ev 3).cmd = .recv peer := ⟨_, rfl⟩

private theorem kyberCt0_len : (w0.kyberCts.headD []).length = 1568 := by
  decide +kernel

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

/-- Under `PkiUnchanged tr`, `t4` stores no `.oneTimePrekey`, so `StOpt tr b opkIdx opk` forces
`opkIdx = none` and `opk = none`. -/
private theorem stOpt_opk_none_of_pkiUnchanged {tr : ExecTrace} {b : Participant}
    {opkIdx : Option Nat} {opk : Option Bytes}
    (hpki : PkiUnchanged tr)
    (hopk : StOpt tr b opkIdx opk) :
    opkIdx = none ∧ opk = none := by
  cases opkIdx with
  | none =>
    cases opk with
    | none => exact ⟨rfl, rfl⟩
    | some _ => cases hopk
  | some idx =>
    cases opk with
    | none => cases hopk
    | some k =>
      exfalso
      rcases pki_pin_st hpki hopk with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
      · injection h1 with hk _; cases hk
      · injection h2 with hk _; cases hk
      · injection h3 with hk _; cases hk
      · injection h4 with hk _; cases hk

/-- Steps Call 3 (`bobStart`) across a network prefix `c3.pre` to initialize `"bob"`'s
`ActivePartySt` at `stB3Clean cls` and record `ek ∈ bobDoneBaseKeys`. -/
theorem bob_call3_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {tr : ExecTrace} {c3 : PeeledCall}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hCompat : GhostAndSemMatchSetup evictedI0 r S g)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hnoBob : NoPartyState "bob" tr)
    (hev2_out : (ev 2).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes evictedI0 (secretBytes r 0)))
      (gamma evictedI0 S (gClean r cls) o1.ek)
      (gamma evictedI0 S (gClean r cls) o1.ct)
      (gamma evictedI0 S (gClean r cls) (m2Clean cls))))
    (hnet : ∀ x ∈ c3.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches evictedI0 r S g (runSteps c3.pre tr) c3.s (ev 3) c3.v
      (some (none, 7#32, 9#32)))
    (hsub : ∀ w ∈ c3.v, w ∈ visAll) :
    let tr' := c3.s.next (runSteps c3.pre tr)
    PkiUnchanged tr' ∧
    ActivePartySt "bob" false S g (gClean r cls) [⟨4, by decide⟩] ⟨5, by decide⟩
      (stB3Clean cls) tr' ∧
    NoNewPartyState "alice" tr tr' ∧
    (∃ ek ∈ bobDoneBaseKeys tr',
      ecKey (gamma evictedI0 S g ek) = ecKey (evictedPubOfIdx ⟨3, by decide⟩)) := by
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  set tr₃ := runSteps c3.pre tr
  have hpki₃ : PkiUnchanged tr₃ := pkiUnchanged_runSteps_network c3.pre hnet hpki
  have hnoBob₃ : NoPartyState "bob" tr₃ :=
    noPartyState_of_noNew (noNewPartyState_runSteps_network c3.pre tr hnet) hnoBob
  obtain ⟨_, hparty, hfits, hpeer, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, _, hdr, hout, hrf, _⟩ := hrm
  have hbob : (ev 3).party = "bob" := ev3_party_eq
  obtain ⟨peer₃, hcmd₃⟩ := ev3_cmd_recv
  rw [hbob] at hparty
  rw [hcmd₃] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨peer₃, hcmd₃⟩ hout
  cases hs : c3.s with
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    exfalso
    rw [hs] at hparty hok
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decrypt] at hok
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hok
    rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₃).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₃ stateIdx st (bks_stored_of_getLocalState hst)
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    exfalso
    rw [hs] at hparty hok
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decryptSkipped] at hok
    unfold messageDecryptSkipped at hok
    rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₃).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₃ stateIdx st (bks_stored_of_getLocalState hst)
  | bobStart b a kh regA mh pqIdx spqr =>
    rw [hs] at hparty hpeer hok hvis_eq
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have ha : a = "alice" := by
      simpa [Step.MatchesSetupPeer, hnames.1] using hpeer
    subst ha
    have hpki' : PkiUnchanged ((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₃) :=
      pkiUnchanged_step_party rfl hpki₃
    have hnoNewA : NoNewPartyState "alice" tr
        ((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₃) :=
      noNewPartyState_trans (noNewPartyState_runSteps_network c3.pre tr hnet)
        (noNewPartyState_step_other tr₃ rfl (by simp [Step.party?]))
    have hle_next := step_le_next (.bobStart "bob" "alice" kh regA mh pqIdx spqr) tr₃
    have hnext_mv := step_next_bobStart "bob" "alice" kh regA mh pqIdx spqr tr₃
    have hview : stepView (.bobStart "bob" "alice" kh regA mh pqIdx spqr) tr₃
        (runWrapped (ev 3)) =
        bobVis tr₃ ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃)
          mh (bobOpkPk "bob" kh tr₃) ++
        exposures tr₃ ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃) := by
      unfold stepView; simp only [hok, ↓reduceIte]; rw [hnext_mv]
    have hpt_some : ∃ pt,
        receivedPlaintext tr₃
          ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃) = some pt := by
      rcases hpt : receivedPlaintext tr₃
          ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₃) with _ | pt
      · exfalso
        have hw_mem : w_out ∈ c3.v := by rw [hv_split]; simp
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
    have hw_ikB : w.ikB = ikB := by
      rcases pki_pin_st hpki₃ w.hik with ⟨hp, _⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
      · exact absurd hp (by decide)
      · injection hk with _ hsk
      · injection hk with hkind _; cases hkind
      · injection hk with hkind _; cases hkind
    have hw_spk : w.spk = spkB := by
      rcases pki_pin_st hpki₃ w.hspk with ⟨hp, _⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
      · exact absurd hp (by decide)
      · injection hk with hkind _; cases hkind
      · injection hk with _ hsk
      · injection hk with hkind _; cases hkind
    have hw_pq : w.pqsk = pqskB := by
      rcases pki_pin_st hpki₃ w.hpq with ⟨hp, _⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
      · exact absurd hp (by decide)
      · injection hk with hkind _; cases hkind
      · injection hk with hkind _; cases hkind
      · injection hk with _ hsk
    obtain ⟨hkh_opk, hw_opk⟩ := stOpt_opk_none_of_pkiUnchanged hpki₃ w.hopk
    have hw_ikA : w.ikAPk = dhPk ikA := by
      rcases pki_pin_reg hpki₃ w.hreg with ⟨_, hikA_eq, _⟩ | ⟨hp, _, _⟩
      · exact hikA_eq
      · exact absurd hp (by decide)
    have hrec_terms : received tr₃ [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
      simp only [received, List.filterMap_cons, List.filterMap_nil,
        rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
        rpkT_getMessageSentAt_of_at? w.hmsg]
    have hvis_full : c3.v =
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
    obtain ⟨hinp_eq, _, hdrs_eq⟩ :=
      split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
    have hrng_mem : rngEntry (randTerm tr₃.length 32) ∈ visAll := by
      apply hsub; rw [hv_split, hdrs_eq]; simp
    rw [hdrs_eq] at hdr
    have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
    have hdhs_idx : evictedSecretIdx
        (clamp (gamma evictedI0 S g (randTerm tr₃.length 32))) = some ⟨5, by decide⟩ := by
      rw [hdhs_bytes]; exact ev3_coins_idx
    have hdhsB_gam : gamma evictedI0 S g (randTerm tr₃.length 32) =
        gamma evictedI0 S (gClean r cls) (rnd 45 32) := by
      rw [hdhs_bytes]; unfold rnd; rw [gamma_rand]; simp [gClean_sigma_45]
    obtain ⟨_, p₃, hp₃, hp₃_bk, hp₃_rk, _⟩ := ev3_preKey_fields
    have hfull := ev3_full_fields hp₃
    have hev3_in : (ev 3).input = preKeyWire none 7#32 9#32 r.regIdA
        (ecKey (pubBytes evictedI0 (secretBytes r 0)))
        (gamma evictedI0 S (gClean r cls) o1.ek)
        (gamma evictedI0 S (gClean r cls) o1.ct)
        (gamma evictedI0 S (gClean r cls) (m2Clean cls)) := by
      have hcomb := ev2_to_ev3.symm.trans hev2_out
      injection hcomb with hpair
      exact (Prod.mk.inj hpair).2
    obtain ⟨_, hp₃_ct_clean, hp₃_bk_clean, hp₃_msg_clean⟩ :=
      parsePreKeyWire_preKeyWire_inv hev3_in ev3_input_len_lt hp₃
    rw [hinp_eq] at hrf
    dsimp only [ReadsFaithfully, List.cons_append] at hrf
    rcases hrf with ⟨_, _, _, ⟨p₁, hp₁, hbk₁, hct₁, _⟩, p₂, hp₂, hFaith⟩
    cases hp₃.symm.trans hp₁
    cases hp₃.symm.trans hp₂
    have hek_g_ekb : gamma evictedI0 S g w.ek = ekBytes p₃ := by
      have hdrop := congrArg (List.drop 1) hbk₁
      rw [List.drop_take] at hdrop
      exact hdrop.symm
    have hct_g : gamma evictedI0 S g w.ct = w0.kyberCts.headD [] := by
      rw [hfull.2.2.2.2.1] at hct₁
      unfold kyberKey at hct₁
      injection hct₁ with hct₁
      injection hct₁ with _ heq
      exact heq.symm
    have hek_clean_val : gamma evictedI0 S (gClean r cls) o1.ek = evictedPubOfIdx ⟨3, by decide⟩ :=
      (List.cons.inj (hp₃_bk_clean.symm.trans hfull.2.2.2.2.2.1)).2
    have hekb_val : ekBytes p₃ = evictedPubOfIdx ⟨3, by decide⟩ := by
      unfold ekBytes
      rw [hfull.2.2.2.2.2.1]
      dsimp only [ecKey, List.drop]
      exact List.take_of_length_le (by decide)
    have hek_gam : gamma evictedI0 S g w.ek = gamma evictedI0 S (gClean r cls) o1.ek :=
      (hek_g_ekb.trans hekb_val).trans hek_clean_val.symm
    have hek_ec : ecKey (gamma evictedI0 S g w.ek) = ecKey (evictedPubOfIdx ⟨3, by decide⟩) := by
      rw [hek_g_ekb, hekb_val]
    have hct_clean_val : gamma evictedI0 S (gClean r cls) o1.ct = w0.kyberCts.headD [] := by
      have h := hp₃_ct_clean.symm.trans hfull.2.2.2.2.1
      injection h with hkk
      exact (List.cons.inj hkk).2
    have hnk₃ := not_kyberMismatch_ev3 hfit hp₃
    have hs4_eq : setupSecret r 4 = pqskB := (setupSecret_eq r hNe).2.2.2.1
    have hagree_w := w.hagree
    rw [hw_ikB, hw_spk, hw_pq, hw_opk, hw_ikA] at hagree_w
    obtain ⟨ss_w, hdec_w, hss_w_gam⟩ :=
      gamma_kemSS_of_not_implicitReject evictedI0 r S g p₃ ⟨w.ek, w.ct, w.raw⟩
        (w0.kyberCts.headD []) hCompat hNe hnk₃ hfull.2.2.2.2.1 kyberCt0_len hct_g
    rw [hs4_eq] at hdec_w
    have hkeys_w : w.keys = pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB)
        (agree w.ek ikB) (agree w.ek spkB) none ss_w) := by
      unfold DY.Libsignal.PQXDH.bobAgreement at hagree_w
      rw [hdec_w] at hagree_w
      injection hagree_w with hk_eq
      exact hk_eq.symm
    have hdec_clean : errToOption (DY.PQKem.kemDecap (setupSecret r 4) o1.ct) =
        some (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 := by
      rw [hs4_eq, o1_ct_eq, kemDecap_kemEncap pqskB (rnd 23 32)]
      rfl
    obtain ⟨ss_c, hdec_c, hss_c_gam⟩ :=
      gamma_kemSS_of_not_implicitReject evictedI0 r S (gClean r cls) p₃
        ⟨o1.ek, o1.ct, m2Clean cls⟩ (w0.kyberCts.headD [])
        (ghostAndSemMatchSetup_gClean cls hfit hCompat) hNe hnk₃
        hfull.2.2.2.2.1 kyberCt0_len hct_clean_val
    have hss_c_eq : ss_c = (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 := by
      rw [hdec_clean, Option.getD_some] at hdec_c
      exact hdec_c.symm
    subst hss_c_eq
    have hss_gam : gamma evictedI0 S g ss_w =
        gamma evictedI0 S (gClean r cls) (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 :=
      hss_w_gam.trans hss_c_gam.symm
    rcases hFaith with ⟨msg_f, hparse_f, _, _, _, _, hrk_w_p, hpq_w_p, _⟩
    rw [w.hparse] at hparse_f
    injection hparse_f with hmsg_eq; subst hmsg_eq
    have hrk4 : gamma evictedI0 S g w.msg.ratchetKey = evictedPubOfIdx ⟨4, by decide⟩ :=
      hrk_w_p.trans hp₃_rk
    have hrk_dhsA_len : (gamma evictedI0 S (gClean r cls) (dhPk dhsA)).length = 32 := by
      have hts24 : (24 : Nat) ∈ ratchetKeyTimestamps := by decide
      rw [gamma_dhPk_ratchetTs hfit hts24]
      decide
    have htry_p₃ := parsePreKeyWire_inner_tryFrom hp₃
    obtain ⟨_, _, _, hrk_c_p, hpq_c_p, _, _⟩ :=
      encMsg_tryFrom_inv hp₃_msg_clean.symm hrk_dhsA_len htry_p₃
    have hrkMsg_gam : gamma evictedI0 S g w.msg.ratchetKey =
        gamma evictedI0 S (gClean r cls) (dhPk dhsA) :=
      hrk_w_p.trans hrk_c_p.symm
    have hpqMsg_gam : gamma evictedI0 S g w.msg.pqRatchet =
        gamma evictedI0 S (gClean r cls) (pqm2Clean cls) :=
      hpq_w_p.trans hpq_c_p.symm
    have hikB_gam : gamma evictedI0 S g ikB = gamma evictedI0 S (gClean r cls) ikB :=
      gamma_setup_rnd_eq cls hfit hCompat (by decide) (by decide)
    have hspkB_gam : gamma evictedI0 S g spkB = gamma evictedI0 S (gClean r cls) spkB :=
      gamma_setup_rnd_eq cls hfit hCompat (by decide) (by decide)
    have hikA_gam : gamma evictedI0 S g (dhPk ikA) =
        gamma evictedI0 S (gClean r cls) (dhPk ikA) := by
      rw [gamma_dhPk, gamma_dhPk,
          gamma_setup_rnd_eq cls hfit hCompat (ts := 0) (n := 32) (by decide) (by decide)]
    have hspqr_w := w.hspqr
    rw [hw_ikB, hw_spk, hw_ikA, hkeys_w] at hspqr_w
    have hst_agree := stateBytesAgree_bobStart (cls := cls) (c' := w.c')
      hikB_gam hspkB_gam hikA_gam hek_gam hss_gam hrkMsg_gam hdhsB_gam hpqMsg_gam hspqr_w
    have hfinal_eq : rpkR_finalSt w =
        (let keys_b := pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB)
           (agree w.ek ikB) (agree w.ek spkB) none ss_w)
         let (stB_r, _) := ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys_b w.msg)
           w.msg.ratchetKey (randTerm tr₃.length 32)
         { stB_r with recv := setRecvChain stB_r.recv w.c', spqr := w.spqr' }) := by
      unfold rpkR_finalSt BobStartOk.out Symbolic.Swarm.CREF.bobOut
        bobRatchetedSt ratchetState bobSt0
      rw [hw_ikB, hw_spk, hw_ikA, hkeys_w]
      rfl
    have hst_agree' : StateBytesAgree S g (gClean r cls) (rpkR_finalSt w) (stB3Clean cls) := by
      rw [hfinal_eq]; exact hst_agree
    obtain ⟨tr_pre_last, hlast⟩ := rpkR_bobStartTr_last w
    have hat_final : (((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₃).at?
        tr_pre_last.length : Option TRStEntry) = some ⟨⟨"bob", rpkR_finalSt w⟩⟩ := by
      rw [htr', hlast, Symbolic.Swarm.CREF.at?_append_length]; rfl
    have hchild_eq : tr_pre_last.length =
        (Symbolic.Swarm.CREF.bobStartPreSkipTr tr₃ "bob" "alice" w.out w.msg w.key).length +
          (w.msg.counter.toNat -
            (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).index.toNat) + 2 := by
      have hat_raw : ((Symbolic.Swarm.CREF.bobStartTr tr₃ "bob" "alice"
          w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m).at? tr_pre_last.length :
          Option TRStEntry) = some ⟨⟨"bob", rpkR_finalSt w⟩⟩ := by
        rw [hlast, Symbolic.Swarm.CREF.at?_append_length]; rfl
      rcases rpkBH_trStateStoredAt_bobStartTr w hat_raw with ⟨_, h0⟩ | ⟨heq, _, _⟩
      · exact False.elim (hnoBob₃ _ _ h0)
      · exact heq
    have huniq_all : ∀ j st, tr₃.length ≤ j →
        (((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₃).at? j :
          Option TRStEntry) = some ⟨⟨"bob", st⟩⟩ →
        j = tr_pre_last.length ∧ st = rpkR_finalSt w := by
      intro j st _ hat
      rw [htr'] at hat
      rcases rpkBH_trStateStoredAt_bobStartTr w hat with ⟨_, h0⟩ | ⟨hj, _, hst_eq⟩
      · exact False.elim (hnoBob₃ _ _ h0)
      · exact ⟨hj.trans hchild_eq.symm, hst_eq⟩
    have hrecv_map : (rpkR_finalSt w).recv.map (fun c => gamma evictedI0 S g c.ratchetKey) =
        [evictedPubOfIdx ⟨4, by decide⟩] := by
      unfold rpkR_finalSt
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
    refine ⟨hpki',
      activePartySt_init hnoBob₃ hle_next hat_final huniq_all rfl hst_agree' hrecv_map hdhs_idx,
      hnoNewA, w.ek, ?_, hek_ec⟩
    simp only [htr', rpkT_bobDoneBaseKeys_bobStartTr, List.mem_append, List.mem_singleton]
    exact Or.inr rfl
  | _ => rw [hs] at hfits; cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvC
