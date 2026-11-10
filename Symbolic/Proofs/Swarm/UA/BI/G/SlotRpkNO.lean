/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
import Batteries.Data.UInt
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReachBob
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewTieBundle
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyOverModel
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.ExplainOKPure
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L04BridgeBQuietFail
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L10SlotRpkNewOverCli
import Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNOHelpers
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.Base -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Bob Non-Promote Pre-Key Receive Slot

Proves `uab_slot_rpk_no_of : XlateInvSpecB -> XlateExcPSpecB -> UASlotRpkNOSpecB`, showing that
Bob's non-promote pre-key `recv` slot preserves the turn simulation `PqTurnSim1A` and the trace
invariant `UAInvB` across prefixes containing break and invert steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNO

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace ReachabilityConfig)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent CliEvent StateAndMessage)
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.PQXDH (BobKeyHandles PreKeyMsgHandles)
open _root_.DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg consumeMessageKey)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.E2E (PEParams wireWhisper wirePrekey encodeRecordUnderExtras preKeyStoreEventsBytes)
open CryptoVerification.SignalSession (Inputs PqParty filesOf encodeDir pqRecvInputs
  pqRecvWhisperModel PqSessionMatches PqxdhPartyInSpecDomain partyAddress)
open Symbolic.Swarm.COMPOSED.CompTrace (NetE RndE)
open Symbolic.Swarm.CREF (BobRuns bobStartTr bobChain
  b5_bobStart_next b5_attackerSend_next b5_attackerSend_reachable bobOpkPk_eq
  bobOut bobKeysOf bobRatchetedSt OpkSel StOpt Runs.bobStart opkUsedB_append_rnd_net
  g2b_bobDoneEk_stampsLt_of_reachable CBadSigmaFrame cBadSigmaFrame_updateFreshAt
  cBadSigmaFrame_refl cbadG2_gammaAgree_of_sigmaFrame cbadG2_gamma_eq
  compSemOf SemReady compSemOf_ready
  Sanitize.clearStuckWrap Sanitize.sanitizeMoves Sanitize.getElem?_sanitizeMoves
  Sanitize.sanitizeMoves_take Sanitize.runVis_sanitizeMoves Sanitize.runTrace_sanitizeMoves
  Sanitize.modelRun_sanitizeMoves Sanitize.roleFaithful_sanitizeMoves
  Sanitize.readFaithful_sanitizeMoves Sanitize.outcomeFaithful_sanitizeMoves
  Sanitize.readCollision_sanitizeMoves_iff
  Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath?
  Sanitize.preKeyRepresentations_sanitizeMoves
  MacInv.runTrace_at?_24 MacInv.runTrace_at?_9 MacInv.runTrace_at?_13
  TR.bobSaltSeed TR.bobKeys TR.bobChain TR.StE TR.EvE
  TR.setupSecret_eq TR.setupPublic_eq TR.setupTrace_eq
  TR.setupTr5 TR.setupTr4 TR.setupTr3 TR.setupTr2 TR.setupTr1
  TR.at?_append_of_lt TR.at?_append_eq TR.at?_append_self TR.setupTrace_reachable
  TR.FreshSigma.StampsLt TR.FreshSigma.updateFreshAt TR.FreshSigma.updateFreshAt_self
  TR.FreshSigma.traceEntriesLt_of_reachable
  TR.FreshSigma.preKeyRepresentations_updateFreshAt_of_traceEntriesLt
  TR.rep_ek_ct_gamma TR.bobSaltSeed_gamma TR.ekBytes TR.gamma_setupPublic_0_2_6
  TR.gamma_computeMac TR.gamma_trMsgKeys_macKey TR.gamma_trMsgKeys_cipherKey
  TR.gamma_trMsgKeys_iv TR.gamma_serializedIk TR.computeMacBytes TR.length_hmacWith
  TR.G1.g1_rep_ptAtoms_tr)
open Symbolic.Swarm.CREF.CliPure (newRandoms_bobStartTr receivedPlaintext_bobStartTr
  vis_bobStart bobKeyHandlesOf bobAgreement_of_not_implicitReject
  rpk_at?_some_of_le rpk_getMessageSentAt_of_at?
  rpk_setupPublic_8 rpk_bobStart_of_exactRep_pqSalt_at bobSaltSeed_some_of_not_implicitReject
  x25519LowOrder_false_of_gamma_notLow RpkSeedAkHyp RpkNotSpqrMacHyp rpk_seedAkHyp
  rpk_notSpqrMacHyp rpk_reps_nonempty
  rpk_bobTrialGuard_of_contract rpk_exactRep_of_not_bobStartCollision rpk_bobStartCollision_sanitizeMoves
  preKeyRepresentations_mono_append RecvAcceptContractPure)
open Symbolic.Swarm.CREF.Cli (interpOfParams externContractsHoldCli_interpOfParams
  modelAgree_interpOfParams mlkemOf_interpOfParams hmacFnOf_interpOfParams Xof
  exited_eq_pqObserve_iff observedExcept_exited_iff
  PqDirInv PqPartyInv PqBobInv wfPq_of_pqPartyInv records_of_pqPartyInv opkUsed_of_pqPartyInv
  keyToBytes32_bytesToKey32 peerOf_eq_addrE_other inputsEquiv_pqRecvInputs
  Slots.rpkModelHookBridge_interpOfParams Slots.pqRecvPrekeyModel_none_ok_inv
  Slots.rpkNew_accept_tie_bundle Slots.wfPq_clear_session)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli explainsCli_toClean)
open Symbolic.Swarm.Coinsplit.Lift.L02 (outcomeFaithfulCli_of_goodExit0Cut)
open Symbolic.Swarm.Coinsplit.Lift.L04 (bridgeB_quiet_fail)
open Symbolic.Swarm.Coinsplit.Lift.L10 (RpkNewOverNC slot_rpk_new_over_cli_gen)
open Symbolic.Proofs.Swarm.UA.Defs (SchedFits callsOf flatEvents)
open Symbolic.Proofs.Swarm.UA.Base (runSteps_append runTrace_append)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UAInvB UASlotPostB UASlotRpkNOSpecB XlateInvSpecB
  XlateExcPSpecB)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Base (collisionAtCli_append explains_snoc_rejected)
open Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer (step_le_next runSteps_le runSteps_reachable
  stepsWF_append_iff stepsStateFaithful_append_noLoad matchesEvents_snoc_run1
  matchesEvents_visStampsLt ghostWF_transfer matchesEvents_transfer gamma_randTerm_eq)
open Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNOHelpers (schedFits_recv_call
  preKeyRepresentations_iff_on knownBaseKey_iff_on bobStartCollision_iff_on
  not_readCollisionCli_snoc_noDecrypt_any aliceRecordPendingInSession_bob_recv)

/-! ## Step Execution and View Bridges -/

section StepInstances
open scoped _root_.DY.Libsignal.Composed

private theorem step_network_next (msg : _root_.DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).next tr = tr.append (NetE msg) := by
  let inst : ReachabilityConfig.HasStep _root_.DY.Network.reachability reachability := inferInstance
  have hstep : reachability.step (Step.network msg).toInput =
      _root_.DY.Network.reachability.step msg := inst.pf_step msg
  unfold Step.next
  rw [hstep]
  simp only [_root_.DY.Network.reachability, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_mk]

private theorem step_network_preCond {msg : _root_.DY.Bytes} {tr : ExecTrace}
    (h : msg.AttackerKnows tr) : (Step.network msg).PreCond tr := by
  let inst : ReachabilityConfig.HasStep _root_.DY.Network.reachability reachability := inferInstance
  exact (inst.pf_pre msg tr).mp h

private theorem step_bobStart_preCond (b a : Participant) (kh : BobKeyHandles)
    (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) :
    (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).PreCond tr := by
  let inst : ReachabilityConfig.HasStep _root_.DY.Libsignal.Composed.bobStart.reachability reachability :=
    inferInstance
  exact (inst.pf_pre (b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx) tr).mp trivial

private theorem step_bobStart_run {b a : Participant} {kh : BobKeyHandles}
    {regIdxA : Nat} {mh : PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    {ret : Nat} {tr tr' : ExecTrace}
    (h : BobRuns (_root_.DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) tr ret tr') :
    (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).ok tr = true ∧
      (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).next tr = tr' := by
  let inst : ReachabilityConfig.HasStep _root_.DY.Libsignal.Composed.bobStart.reachability reachability :=
    inferInstance
  have hstep : reachability.step (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).toInput =
      _root_.DY.Libsignal.Composed.bobStart.reachability.step (b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx) :=
    inst.pf_step (b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx)
  refine ⟨?_, ?_⟩
  · unfold Step.ok
    rw [hstep]
    change ((_root_.DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).1.isSome = true
    rw [h.1]; rfl
  · unfold Step.next
    rw [hstep]
    change ((_root_.DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val = tr'
    exact h.2

end StepInstances

cref_hide_foreign_instances

private theorem stepView_bobStart_eq_move_vis {b a : Participant} {kh : BobKeyHandles}
    {regIdxA : Nat} {mh : PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    {tr : ExecTrace} {wrapped : Bool}
    {o : _root_.DY.Libsignal.PQXDH.BobHandshakeOut} {msg : TRSignalMsg}
    {c' : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    {spqr' key seed pqSalt m : _root_.DY.Bytes}
    (hok : (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).ok tr = true)
    (hnext_s : (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).next tr =
      bobStartTr tr b a o msg c' spqr' key seed pqSalt m)
    (hnext_m : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 3).next tr =
      bobStartTr tr b a o msg c' spqr' key seed pqSalt m) :
    stepView (Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) tr wrapped =
      (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 3).vis tr := by
  unfold stepView Move.vis
  dsimp only
  simp only [hok, ↓reduceIte, hnext_s, hnext_m]
  have hlen : (bobVis tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) mh
      (bobOpkPk b kh tr)).length = 3 := by
    unfold bobVis rngEntry
    rw [newRandoms_bobStartTr, receivedPlaintext_bobStartTr]
    rfl
  rw [List.take_of_length_le (Nat.le_of_eq hlen)]

/-! ## Pure Accept Contract Extraction -/

private theorem rpk_no_accept_contract (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hkind : c.stdin.head? ≠ some wireWhisperTag ∨ t.records r r.bob = none)
    (hno_prom : ∀ rec_ q, t.records r r.bob = some rec_ → parsePreKeyWire c.stdin = some q →
      ¬ EligibleForSessionPromotion rec_ c.stdin)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited 0 out files))) :
    let interp' := interpOfParams interp P
    ∃ (body : HwBytes) (pf : PreKeyFields) (sm : StateAndMessage) (ct_wire : HwBytes),
      c.stdin = wirePrekey :: body ∧
      parsePreKeyWire c.stdin = some pf ∧
      HonestIdentity interp' r c.stdin ∧
      (∀ q, parsePreKeyWire c.stdin = some q → q.baseKey.take 33 ∉ accepted) ∧
      RecvAcceptContractPure interp' r (t_clean.opkUsed r) c.stdin sm pf c.coins ct_wire out := by
  let interp' := interpOfParams interp P
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hBridge := Slots.rpkModelHookBridge_interpOfParams hagree
  have hmlkem := mlkemOf_interpOfParams interp P
  have hhmac := hmacFnOf_interpOfParams interp P
  have hoff : t.bobOff = false := by
    cases hbo : t.bobOff with | false => rfl | true => exact absurd hbob (hbca hbo)
  have htc_eq : t_clean = t := hsim.bobOff_false_eq hoff; subst t_clean
  have hDir : PqDirInv interp' P r t accepted := hsim.dirInv
  have hfb_bob : FilesBounded (t.dirs r.bob) := hbob ▸ hfb
  obtain ⟨stB, hBobInv⟩ := hDir.2.1
  have hinvB : PqPartyInv interp' P r accepted r.bob stB (t.dirs r.bob) := by
    unfold PqBobInv at hBobInv; rwa [hoff] at hBobInv
  have hwfB : PqxdhPartyInSpecDomain P stB := wfPq_of_pqPartyInv hinvB hfb_bob
  let c1 := toCliCallNone c
  have hin1 : InputsFor c1 (t.dirs c1.party) i := inputsFor_toCliCallNone hbun hin
  have hi_enc : InputsFor c1 (filesOf (encodeDir P stB)) i := by
    rwa [show c1.party = r.bob from hbob, hinvB.dir_eq] at hin1
  let rc := _root_.CryptoGames.HKDF.bytesToKey32 c.coins
  have hcoins_rc : c1.coins = _root_.CryptoGames.HMAC.keyToBytes32 rc :=
    (keyToBytes32_bytesToKey32 hcoins).symm
  have hcmd_stB : c1.cmd = .recv (partyAddress stB.party.other) := by
    change c.cmd = .recv (partyAddress stB.party.other)
    rw [hcmd, peerOf_eq_addrE_other, ← hinvB.party_eq]
  have heq_recv : InputsEquiv i (pqRecvInputs P stB c.stdin rc) :=
    inputsEquiv_pqRecvInputs (c := c1) hi_enc hcmd_stB rfl hcoins_rc
  have hp : PqModelPost interp P i (.exited 0 out files) := PqModelRel.exited_iff.mp hRel
  unfold StdinBounded at hsb; rw [hcmd] at hsb
  by_cases hw : ∃ body, c.stdin = wireWhisperTag :: body
  · obtain ⟨body, hstdin⟩ := hw
    have hrec_none : t.records r r.bob = none := hkind.resolve_left (by simp [hstdin])
    have hsess_none : stB.session = none := by
      rw [records_of_pqPartyInv hinvB] at hrec_none
      cases hs : stB.session with | none => rfl | some _ => rw [hs] at hrec_none; cases hrec_none
    have hstdin_w : c.stdin = wireWhisper :: body := by rwa [wireWhisper_eq_wireWhisperTag]
    have hobs := hp.recvWhisper stB body rc hwfB (hsb.1 body hstdin) (hstdin_w ▸ heq_recv)
    simp only [pqRecvWhisperModel, hsess_none] at hobs
    cases hobs
  · have hnw_tag : c.stdin.head? ≠ some wireWhisperTag := by
      intro hh; cases hcs : c.stdin with
      | nil => simp [hcs] at hh
      | cons b tl => simp only [hcs, List.head?_cons, Option.some.injEq] at hh; exact hw ⟨tl, hh ▸ hcs⟩
    have hlen_lt : c.stdin.length < 2 ^ 32 := hsb.2.1 hnw_tag
    by_cases hpk : ∃ body, c.stdin = wirePrekey :: body
    · obtain ⟨body, hstdin⟩ := hpk
      have hbody_lt : body.length < 2 ^ 32 := by rw [hstdin, List.length_cons] at hlen_lt; omega
      have heq_body : InputsEquiv i (pqRecvInputs P stB (wirePrekey :: body) rc) := hstdin ▸ heq_recv
      cases hq : parsePreKey body with
      | none =>
        have hobs := hp.recvPrekeyReject stB body rc hwfB hbody_lt hq heq_body
        cases hobs
      | some q =>
        have hno_fm : ∀ x g, stB.session = some (x, g) → ¬ PqFieldsMatch x g q := by
          intro x g hsess hfm
          have hrec_bob : t.records r r.bob = some (encodeRecordUnderExtras (fun _ => x) g) := by
            rw [records_of_pqPartyInv hinvB, hsess]; rfl
          exact hno_prom _ q hrec_bob (by rw [hstdin]; simpa using hq)
            (hstdin.symm ▸ promoteMatch_of_pqFieldsMatch hwfB hsess hq hfm)
        cases hm : preKeyOfBody? body with
        | none =>
          have hobs := hp.recvPrekeyUntyped stB body q rc hwfB hbody_lt hq hm hno_fm heq_body
          cases hobs
        | some m =>
          obtain ⟨q₁, hq₁, _, hminner, _, _, _, _, _, _, _⟩ := preKeyOfBody?_some_inv hm
          cases Option.some.inj (hq.symm.trans hq₁)
          have hp_b : parsePreKeyWire (wirePrekey :: body) = some q := by simpa using hq
          have hmlt : m.inner.length + 2048 < 2 ^ 32 := hminner ▸ hsb.2.2.1 q (hstdin ▸ hp_b)
          cases hsess : stB.session with
          | none =>
            have hvac : ∀ x g, stB.session = some (x, g) → PqSessionMatches x g m :=
              fun _ _ hs => by rw [hsess] at hs; cases hs
            have hobs := hp.recvPrekeyParsed (Xof interp' P) stB body m rc hwfB hbody_lt hm hmlt hvac heq_body
            rcases exited_eq_pqObserve_iff.mp hobs with ⟨_, h01, _, _⟩ | ⟨st', out', hmod, _, hout_eq, _⟩
            · cases h01
            · subst hout_eq
              obtain ⟨inner, k, x', g', _, htf, htrust, hk, hdec, hmk, _⟩ :=
                Slots.pqRecvPrekeyModel_none_ok_inv hsess hmod
              obtain ⟨_, hhon_m, hfresh_m, _, _, hcontract_m, _, _⟩ :=
                Slots.rpkNew_accept_tie_bundle hr hext' hagree' hBridge hmlkem hhmac hwfB hinvB
                  hcoins hmlt htf htrust hk hdec hmk
              have heq_pf := preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? hm hq htf
              have hcontract := heq_pf.recvAcceptContractPure hp_b hcontract_m
              have hhon := heq_pf.honestIdentity hcontract_m.parse hp_b hhon_m
              have hfresh := heq_pf.fresh hcontract_m.parse hp_b hfresh_m
              refine ⟨body, q, ⟨encodeRecordUnderExtras (fun _ => x') g', preKeyStoreEventsBytes m ++ out⟩,
                _, hstdin, hstdin ▸ hp_b, hstdin ▸ hhon, fun q' hq' => hfresh q' (hstdin ▸ hq'),
                hstdin ▸ hcontract⟩
          | some xg =>
            rcases xg with ⟨x, g⟩
            have hnomatch : ¬ PqSessionMatches x g m :=
              fun hsm => hno_fm x g hsess ((pqFieldsMatch_iff_pqSessionMatches x g hq hm).mpr hsm)
            obtain ⟨hob_ex, _⟩ := hp.recvPrekeyParsedNoMatch (Xof interp' P) stB x g body m rc
              hwfB hsess hbody_lt hm hmlt hnomatch heq_body
            rcases observedExcept_exited_iff.mp hob_ex with ⟨_, h01, _, _⟩ | ⟨st', out', hmod, _, hout_eq, _⟩
            · cases h01
            · subst hout_eq
              let stB₀ : PqParty := { stB with session := none }
              let t₀ : CliTurn :=
                { dirs := fun p => if p = r.bob then filesOf (encodeDir P stB₀) else t.dirs p
                  sent := t.sent, bobOff := false }
              have hwfB₀ : PqxdhPartyInSpecDomain P stB₀ := Slots.wfPq_clear_session P hwfB
              have hB₀_dir : PqPartyInv interp' P r accepted r.bob stB₀
                  (filesOf (encodeDir P stB₀)) :=
                { party_eq := hinvB.party_eq, me_eq := hinvB.me_eq, peerId_eq := hinvB.peerId_eq,
                  alice_stores := fun h => absurd h.symm hr.1, bob_stores := hinvB.bob_stores,
                  session_reach := (fun _ _ hs => nomatch hs), dir_eq := rfl }
              have hB₀ : PqPartyInv interp' P r accepted r.bob stB₀ (t₀.dirs r.bob) := by
                simpa [t₀] using hB₀_dir
              have hopk₀ : t₀.opkUsed r = t.opkUsed r := by
                have ho₀ := opkUsed_of_pqPartyInv hr.1 hB₀
                have hoB := opkUsed_of_pqPartyInv hr.1 hinvB
                obtain ⟨_, _, ho_cases, _⟩ := hinvB.bob_stores hr.1.symm
                cases hw_opk : r.withOpk
                · rw [ho₀.1 hw_opk, hoB.1 hw_opk]
                · rcases ho_cases with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
                  · cases hno_w.symm.trans hw_opk
                  · rw [(ho₀.2 hw_opk).1.mpr hot_s, (hoB.2 hw_opk).1.mpr hot_s]
                  · rw [(ho₀.2 hw_opk).2.mpr hot_n, (hoB.2 hw_opk).2.mpr hot_n]
              obtain ⟨inner, k, x', g', _, htf, htrust, hk, hdec, hmk, _⟩ :=
                Slots.pqRecvPrekeyModel_none_ok_inv (rfl : stB₀.session = none) hmod
              obtain ⟨_, hhon_m, hfresh_m, _, _, hcontract₀, _, _⟩ :=
                Slots.rpkNew_accept_tie_bundle hr hext' hagree' hBridge hmlkem hhmac hwfB₀ hB₀
                  hcoins hmlt htf htrust hk hdec hmk
              rw [hopk₀] at hcontract₀
              have heq_pf := preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? hm hq htf
              have hcontract := heq_pf.recvAcceptContractPure hp_b hcontract₀
              have hhon := heq_pf.honestIdentity hcontract₀.parse hp_b hhon_m
              have hfresh := heq_pf.fresh hcontract₀.parse hp_b hfresh_m
              refine ⟨body, q, ⟨encodeRecordUnderExtras (fun _ => x') g', preKeyStoreEventsBytes m ++ out⟩,
                _, hstdin, hstdin ▸ hp_b, hstdin ▸ hhon, fun q' hq' => hfresh q' (hstdin ▸ hq'),
                hstdin ▸ hcontract⟩
    · have hnw : c.stdin.head? ≠ some wireWhisper := by rwa [wireWhisper_eq_wireWhisperTag]
      have hnp : c.stdin.head? ≠ some wirePrekey := by
        intro hh; cases hcs : c.stdin with
        | nil => simp [hcs] at hh
        | cons b tl => simp only [hcs, List.head?_cons, Option.some.injEq] at hh; exact hpk ⟨tl, hh ▸ hcs⟩
      have hobs := hp.recvOther stB c.stdin rc hwfB hlen_lt hnw hnp heq_recv
      cases hobs

/-! ## Constructive `Step.bobStart` Explanation Lift -/

private theorem bobSaltSeed_unpack_local (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep)
    (msg : TRSignalMsg) (salt seed : _root_.DY.Bytes)
    (hparse : parseTrSignalMsg x.msg = some msg) (hss : TR.bobSaltSeed r p x = some (salt, seed)) :
    ∃ opk c' st', OpkSel r p opk ∧
      consumeMessageKey (bobChain r (bobKeysOf r x opk) msg) msg.counter = some (seed, c') ∧
      _root_.DY.Spqr.spqrRecv (_root_.DY.Spqr.spqrInit (bobKeysOf r x opk).pqr
          _root_.DY.Libsignal.TripleRatchet.spqrB2A)
        msg.pqRatchet (preKeySpqrIndex p) = some (st', salt) := by
  unfold TR.bobSaltSeed at hss
  have hbk_eq : TR.bobKeys r p x = Swarm.CREF.bobKeys r p x := by
    unfold TR.bobKeys Swarm.CREF.bobKeys Swarm.Stage1Trials.bobOpk? bobKeysOf
    rcases p.preKeyId with _ | id
    · rfl
    · by_cases h : (r.withOpk && id == r.opkId) = true <;> simp [h, Bind.bind, Option.bind, Pure.pure]
  rw [hbk_eq] at hss
  rcases hbk : Swarm.CREF.bobKeys r p x with _ | keys
  · simp [hbk, Bind.bind, Option.bind] at hss
  obtain ⟨opk, hsel, rfl⟩ := Swarm.CREF.bobKeys_unpack r p x keys hbk
  have hbc_eq : TR.bobChain r (bobKeysOf r x opk) msg = bobChain r (bobKeysOf r x opk) msg := rfl
  simp only [hbk, hparse, hbc_eq, Bind.bind, Option.bind, Pure.pure] at hss
  rcases hcmk : consumeMessageKey (bobChain r (bobKeysOf r x opk) msg) msg.counter with _ | ⟨seed', c'⟩
  · simp [hcmk] at hss
  · simp only [hcmk] at hss
    rcases hspqr : _root_.DY.Spqr.spqrRecv
        (_root_.DY.Spqr.spqrInit (bobKeysOf r x opk).pqr _root_.DY.Libsignal.TripleRatchet.spqrB2A)
        msg.pqRatchet (preKeySpqrIndex p) with _ | ⟨st', salt'⟩
    · simp [hspqr] at hss
    · simp only [hspqr, Option.some.injEq, Prod.mk.injEq] at hss
      rcases hss with ⟨rfl, rfl⟩
      exact ⟨opk, c', st', hsel, hcmk, hspqr⟩

private theorem rpk_runTrace_at?_19_local (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 19 =
      some (TR.StE r.bob { kind := .pqPrekey, sk := setupSecret r 4 }) := by
  refine rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.setupTrace_le_runTrace r ms) ?_
  rw [(TR.setupSecret_eq r hne).2.2.2.1, TR.setupTrace_eq r hne]
  cases r.withOpk <;>
    simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5,
      TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1] <;>
    repeat (first
      | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
      | (refine TR.at?_append_eq _ _ ?_; simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]))

private theorem rpk_runTrace_at?_1_local (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 1 =
      some (TR.EvE (.IdentityRegistered r.alice (setupPublic r 0)
        (Signature.vk (randTerm 0 32)) true)) := by
  have h0 : setupPublic r 0 = DiffieHellman.dhPk (randTerm 0 32) := by
    rw [(TR.setupPublic_eq r hne).1, (TR.setupSecret_eq r hne).1]
  rw [h0]
  refine rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.setupTrace_le_runTrace r ms) ?_
  rw [TR.setupTrace_eq r hne]
  cases r.withOpk <;>
    simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5,
      TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1] <;>
    repeat (first
      | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
      | (refine TR.at?_append_eq _ _ ?_; simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]))

private theorem bobDoneBaseKeys_stampsLt {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr : ExecTrace} (hReach : tr.Reachable reachability) (hlen : tr.length ≤ ts)
    {ek : _root_.DY.Bytes} (hek : ek ∈ bobDoneBaseKeys tr) :
    TR.FreshSigma.StampsLt interp S g ts ek := by
  unfold bobDoneBaseKeys at hek
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hek
  split at hi
  · rename_i b a ikB ikA spk pqpk opk ek' ct keys hget
    cases hi
    exact g2b_bobDoneEk_stampsLt_of_reachable interp S g ts hReach hlen i b a ikB ikA spk pqpk opk
      ek ct keys hget
  · cases hi

private theorem callStarts_cons_length (e : MachineEvent) (τ : List MachineEvent) :
    (callStarts (e :: τ)).length = (callStarts [e]).length + (callStarts τ).length := by
  simpa only [List.singleton_append] using
    _root_.DY.Libsignal.Composed.Refinement.callStarts_length_append [e] τ

private theorem callStarts_length_rng_prefix (ds : List HwBytes) (τ : List MachineEvent) :
    (callStarts ((ds.map .rng) ++ τ)).length = (callStarts τ).length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have h0 : (callStarts [MachineEvent.rng d]).length = 0 := rfl
    rw [List.map_cons, List.cons_append, callStarts_cons_length, h0, Nat.zero_add, ih]

private theorem callStarts_length_of_coinSplit_local {σ τ : List MachineEvent}
    (h : CoinSplit σ τ) : (callStarts τ).length = (callStarts σ).length := by
  induction h with
  | nil => rfl
  | @keep x σ' τ' _ _ ih =>
    rw [callStarts_cons_length x τ', callStarts_cons_length x σ', ih]
  | @split b ds σ' τ' _ _ _ ih =>
    have h0 : (callStarts [MachineEvent.rng b]).length = 0 := rfl
    rw [callStarts_length_rng_prefix, callStarts_cons_length (MachineEvent.rng b) σ',
      h0, Nat.zero_add, ih]

private theorem eventMatchesEntry_to_bytesMatchEntry {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {e : MachineEvent} {v : VisEntry}
    (hv : v.layout ≠ .preKeySend) (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks)
    (h : EventMatchesEntry interp r S g e v) :
    BytesMatchEntry interp r S g (eventKind e) (eventBytes e) v := by
  unfold EventMatchesEntry at h
  unfold BytesMatchEntry
  refine ⟨h.1, ?_⟩
  have hm := h.2
  cases hl : v.layout <;> simp only [hl] at hm ⊢
  case preKeySend => exact absurd hl hv
  case preKeyInner eks => exact absurd hl (hv2 eks)
  all_goals exact hm

private theorem randTerm_inj {i₁ n₁ i₂ n₂ : Nat} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (h : randTerm i₁ n₁ = randTerm i₂ n₂) : i₁ = i₂ ∧ n₁ = n₂ := by
  let gA : Ghost := ⟨fun i n => if i = i₁ ∧ n = n₁ then [1#8] else [], fun _ => []⟩
  let interp₀ : ExternInterpretation := fun _ _ => none
  let S₀ : OpaqueSymbolSemantics := ⟨fun _ _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ _ => [],
    fun _ _ => [], fun _ _ => [], fun _ => [], fun _ _ => [], fun _ => [],
    fun _ _ _ => []⟩
  have heq := congrArg (gamma interp₀ S₀ gA) h
  rw [gamma_randTerm_eq interp₀ S₀ gA i₁ n₁ hn₁,
    gamma_randTerm_eq interp₀ S₀ gA i₂ n₂ hn₂] at heq
  dsimp only [gA] at heq
  have h₁ : (if i₁ = i₁ ∧ n₁ = n₁ then ([1#8] : HwBytes) else []) = [1#8] := by simp
  rw [h₁] at heq
  split at heq
  · next h₂ => exact ⟨h₂.1.symm, h₂.2.symm⟩
  · cases heq

private theorem rpk_bobStart_step_explains {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {evs_pre : List CliEvent} {c : CliCall} {out : HwBytes}
    {pf : PreKeyFields}
    {g' g_out : Ghost} {ss' : List Step} {vis' : List VisEntry}
    {τ' : List MachineEvent} {ms_s ms₁ ms₂ ms₃ ms₄ : List Move}
    {x : PreKeyRep} {msg : TRSignalMsg} {c'_ch : _root_.DY.Libsignal.TripleRatchet.RecvChain}
    {spqr' salt seed pqSalt m : _root_.DY.Bytes} {opk : Option _root_.DY.Bytes}
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hcoins : c.coins.length = 32)
    (hex' : Explains interp' r S g' ss' vis' evs_pre)
    (hnrc' : ¬ ReadCollisionCli interp' r S g' ss' evs_pre)
    (htr_ms_s : runTraceMoves r ms_s = runTrace r ss')
    (hms₁ : ms₁ = ms_s ++ [Move.attackerSend x.ek])
    (hms₂ : ms₂ = ms₁ ++ [Move.attackerSend x.ct])
    (hms₃ : ms₃ = ms₂ ++ [Move.attackerSend x.msg])
    (hms₄ : ms₄ = ms₃ ++ [Move.attackerSend pqSalt])
    (hg_out : g_out = { g' with σ := TR.FreshSigma.updateFreshAt g'.σ (runTraceMoves r ms₄).length 32 c.coins })
    (hx_s : x ∈ preKeyRepresentations interp' r S g' ms_s c.stdin)
    (hx₁ : x ∈ preKeyRepresentations interp' r S g' ms₁ c.stdin)
    (hx₂ : x ∈ preKeyRepresentations interp' r S g' ms₂ c.stdin)
    (hx₄ : x ∈ preKeyRepresentations interp' r S g' ms₄ c.stdin)
    (hpq₃ : pqSalt.AttackerKnows (runTraceMoves r ms₃))
    (hc₄ : Clean interp' r S who ok g' ms₄ τ')
    (hno_done : ∀ q, parsePreKeyWire c.stdin = some q →
      ¬ ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms₄),
        ecKey (gamma interp' S g' ek) = q.baseKey.take 33)
    (hopk_st : StOpt (runTraceMoves r ms₄) r.bob (bobKeyHandlesOf opk).opk opk)
    (hek₄ : (runTraceMoves r ms₄).at? (runTraceMoves r ms_s).length = some (NetE x.ek))
    (hct₄ : (runTraceMoves r ms₄).at? (runTraceMoves r ms₁).length = some (NetE x.ct))
    (hmsg₄ : (runTraceMoves r ms₄).at? (runTraceMoves r ms₂).length = some (NetE x.msg))
    (hok_s : (Step.bobStart r.bob r.alice (bobKeyHandlesOf opk) 1
        ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
        (runTraceMoves r ms₃).length (preKeySpqrIndex pf)).ok (runTraceMoves r ms₄) = true)
    (hnext_s : (Step.bobStart r.bob r.alice (bobKeyHandlesOf opk) 1
        ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
        (runTraceMoves r ms₃).length (preKeySpqrIndex pf)).next (runTraceMoves r ms₄) =
      bobStartTr (runTraceMoves r ms₄) r.bob r.alice
        (bobOut (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk (setupPublic r 0)
          x.ek x.ct (bobKeysOf r x opk)) msg c'_ch spqr' salt seed pqSalt m)
    (hnext_m : (Move.bobStart r.bob r.alice (bobKeyHandlesOf opk) 1
        ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
        (runTraceMoves r ms₃).length (preKeySpqrIndex pf) 3).next (runTraceMoves r ms₄) =
      bobStartTr (runTraceMoves r ms₄) r.bob r.alice
        (bobOut (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk (setupPublic r 0)
          x.ek x.ct (bobKeysOf r x opk)) msg c'_ch spqr' salt seed pqSalt m)
    (hmp_out : MatchedPrefix interp' r S who g_out
      (ms₄ ++ [Move.bobStart r.bob r.alice (bobKeyHandlesOf opk) 1
        ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
        (runTraceMoves r ms₃).length (preKeySpqrIndex pf) 3])
      (τ' ++ [.recv c.stdin, .rng c.coins, .accept out])) :
    let ev := runEventOf c (some (0, out))
    ∃ g ss vis,
      Explains interp' r S g ss vis (evs_pre ++ [.run ev]) ∧
        ¬ ReadCollisionCli interp' r S g ss (evs_pre ++ [.run ev]) := by
  intro ev
  let kh := bobKeyHandlesOf opk
  let mh : PreKeyMsgHandles :=
    ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
  let pqIdx : Nat := (runTraceMoves r ms₃).length
  let tr₄ := runTraceMoves r ms₄
  let sBob : Step := Step.bobStart r.bob r.alice kh 1 mh pqIdx (preKeySpqrIndex pf)
  let mBob : Move := Move.bobStart r.bob r.alice kh 1 mh pqIdx (preKeySpqrIndex pf) 3
  let pre : List Step := [.network x.ek, .network x.ct, .network x.msg, .network pqSalt]
  have htr_ms₁ : runTraceMoves r ms₁ = (Step.network x.ek).next (runTrace r ss') := by
    rw [hms₁, _root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next, step_network_next, htr_ms_s]
  have htr_ms₂ : runTraceMoves r ms₂ = (Step.network x.ct).next (runTraceMoves r ms₁) := by
    rw [hms₂, _root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next, step_network_next]
  have htr_ms₃ : runTraceMoves r ms₃ = (Step.network x.msg).next (runTraceMoves r ms₂) := by
    rw [hms₃, _root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next, step_network_next]
  have htr_ms₄ : tr₄ = (Step.network pqSalt).next (runTraceMoves r ms₃) := by
    dsimp only [tr₄]
    rw [hms₄, _root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next, step_network_next]
  have htr₄_eq : tr₄ = runSteps pre (runTrace r ss') := by
    simp only [pre, runSteps, ← htr_ms₁, ← htr_ms₂, ← htr_ms₃, ← htr_ms₄]
  have hfr : CBadSigmaFrame g' g_out tr₄.length := by
    rw [hg_out]
    exact cBadSigmaFrame_updateFreshAt g' (Nat.le_refl _) 32 c.coins
  have hlen_ss'_le : (runTrace r ss').length ≤ tr₄.length := by
    rw [htr₄_eq]
    exact _root_.DY.Trace.length_le _ _ (runSteps_le pre (runTrace r ss'))
  let vBob := stepView sBob tr₄ (runWrapped ev)
  have hvBob_eq_mvis : vBob = mBob.vis tr₄ :=
    stepView_bobStart_eq_move_vis hok_s hnext_s hnext_m
  have hopk_pk : bobOpkPk r.bob kh tr₄ = opk.map DiffieHellman.dhPk :=
    bobOpkPk_eq tr₄ r.bob kh opk hopk_st
  have hvis_list := vis_bobStart hnext_m hopk_pk
    (rpk_getMessageSentAt_of_at? hek₄) (rpk_getMessageSentAt_of_at? hct₄)
    (rpk_getMessageSentAt_of_at? hmsg₄)
  have hF_all : List.Forall₂ (EventMatchesEntry interp' r S g_out)
      (τ' ++ [.recv c.stdin, .rng c.coins, .accept out])
      (runVis r (ms₄ ++ [mBob])) := hmp_out.2.2.2.2.2
  have hrm_len : τ'.length = (runVis r ms₄).length :=
    matchedPrefix_length_eq hc₄.matched
  have hrunVis_split : runVis r (ms₄ ++ [mBob]) = runVis r ms₄ ++ mBob.vis tr₄ := by
    unfold runVis
    rw [← List.cons_append, _root_.DY.Libsignal.Composed.Refinement.runMoves_append]
    simp [runMoves, runTraceMoves, tr₄]
  rw [hrunVis_split] at hF_all
  have hF_blk : List.Forall₂ (EventMatchesEntry interp' r S g_out)
      [.recv c.stdin, .rng c.coins, .accept out] (mBob.vis tr₄) := by
    have hdrop := (Swarm.CREF.forall₂_append_split hF_all).2
    rw [← hrm_len, List.drop_left] at hdrop
    exact hdrop
  rw [hvis_list] at hF_blk hvBob_eq_mvis
  cases hF_blk with
  | cons hE_recv hF_1 =>
    cases hF_1 with
    | cons hE_rng hF_2 =>
      cases hF_2 with
      | cons hE_acc _ =>
        have hReach_setup : (setupTrace r).Reachable reachability := TR.setupTrace_reachable r
        have hReach_ss' : (runTrace r ss').Reachable reachability :=
          runSteps_reachable ss' hReach_setup hex'.2.2.1.2.2.1
        have htr_entries_ss' :=
          TR.FreshSigma.traceEntriesLt_of_reachable interp' S g' tr₄.length hReach_ss' hlen_ss'_le
        have hvis'_lt := matchesEvents_visStampsLt hex'.2.2.2 hReach_setup hex'.2.2.1.2.2.1
          hlen_ss'_le htr_entries_ss'
        have hghost_vis' : GhostWF g_out vis' := ghostWF_transfer hfr hvis'_lt hex'.2.1
        have hghost_out : GhostWF g_out (vis' ++ vBob) := by
          refine ⟨?_, hghost_vis'.2.1, ?_⟩
          · intro v hv hk ts n hn hmem
            rcases List.mem_append.mp hv with hv' | hvB
            · exact hghost_vis'.1 v hv' hk ts n hn hmem
            · rw [hvBob_eq_mvis] at hvB
              rcases List.mem_cons.mp hvB with rfl | hvB
              · cases hk
              · rcases List.mem_cons.mp hvB with rfl | hvB
                · simp only [List.mem_singleton] at hmem
                  obtain ⟨rfl, rfl⟩ := randTerm_inj hn (by decide) hmem
                  rw [hg_out]
                  simp [TR.FreshSigma.updateFreshAt_self, hcoins]
                · simp only [List.mem_singleton] at hvB; subst hvB; cases hk
          · intro v hv hk
            rcases List.mem_append.mp hv with hv' | hvB
            · exact hghost_vis'.2.2 v hv' hk
            · rw [hvBob_eq_mvis] at hvB
              rcases List.mem_cons.mp hvB with rfl | hvB
              · cases hk
              · rcases List.mem_cons.mp hvB with rfl | hvB
                · cases hk
                · simp only [List.mem_singleton] at hvB; subst hvB; cases hk
        have hwf_pre : StepsWF (pre ++ [sBob]) (runTrace r ss') := by
          dsimp only [pre, List.cons_append, List.nil_append, StepsWF]
          refine ⟨step_network_preCond (htr_ms_s ▸ hx_s.1), trivial, ?_⟩
          rw [← htr_ms₁]
          refine ⟨step_network_preCond hx₁.2.1, trivial, ?_⟩
          rw [← htr_ms₂]
          refine ⟨step_network_preCond hx₂.2.2.1, trivial, ?_⟩
          rw [← htr_ms₃]
          refine ⟨step_network_preCond hpq₃, trivial, ?_⟩
          rw [← htr_ms₄]
          exact ⟨step_bobStart_preCond _ _ _ _ _ _ _ _, trivial, trivial⟩
        have hwf_steps : StepsWF (ss' ++ pre ++ [sBob]) (setupTrace r) := by
          rw [List.append_assoc]
          exact (stepsWF_append_iff ss' (pre ++ [sBob]) (setupTrace r)).mpr
            ⟨hex'.2.2.1.2.2.1, hwf_pre⟩
        have hsf_steps : StepsStateFaithful r (ss' ++ pre ++ [sBob]) := by
          rw [List.append_assoc]
          refine stepsStateFaithful_append_noLoad hex'.2.2.1.2.2.2 ?_
          intro u hu
          simp only [pre, sBob, List.cons_append, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl <;> rfl
        have hmwf_out : ModelRunWF r (ss' ++ pre ++ [sBob]) :=
          ⟨hex'.2.2.1.1, hex'.2.2.1.2.1, hwf_steps, hsf_steps⟩
        have hme_pre_out : MatchesEvents interp' r S g_out (setupTrace r) ss' evs_pre vis' :=
          matchesEvents_transfer hfr hex'.2.2.2 hReach_setup hex'.2.2.1.2.2.1 hlen_ss'_le
        have hev_party : ev.party = r.bob := hbob
        have hev_cmd : ev.cmd = .recv (peerOf r r.bob) := hcmd
        have hev_input : ev.input = c.stdin := by simp [ev, runEventOf, runInput, hcmd]
        have hev_kind : inputKind ev = .recv := by simp [inputKind, ev, runEventOf, hcmd]
        have hev_coins : ev.coins = c.coins := rfl
        have hev_exit : ev.exit = some (0, out) := rfl
        have hpeer_ok : sBob.MatchesSetupPeer r := by
          simp [Step.MatchesSetupPeer, sBob]
        have hfits_cmd : sBob.FitsCmd ev.cmd := by
          simp [Step.FitsCmd, sBob, hev_cmd]
        have hx₄_out : x ∈ preKeyRepresentationsOn interp' r S g_out tr₄ c.stdin := by
          have htr₄_lt := TR.FreshSigma.traceEntriesLt_of_reachable interp' S g' tr₄.length
            hc₄.matched.2.1.2.2.1.1 (Nat.le_refl tr₄.length)
          rw [hg_out]
          exact TR.FreshSigma.preKeyRepresentations_updateFreshAt_of_traceEntriesLt
            hx₄ htr₄_lt 32 c.coins
        have hrf_out : ReadsFaithfully interp' r S g_out tr₄
            ⟨.recv, [x.ek, x.ct, x.msg] ++ (opk.map DiffieHellman.dhPk).toList,
              .preKeyRecv, none⟩
            ev.input := by
          rw [hev_input]
          dsimp only [ReadsFaithfully, List.cons_append]
          exact hx₄_out
        have hpf_out : PathFaithfulAt interp' S g_out tr₄ sBob ev.input := by
          intro q hq
          rw [hev_input] at hq
          dsimp only [sBob]
          rintro ⟨ek, hek_mem, heq⟩
          have hga := cbadG2_gammaAgree_of_sigmaFrame interp' S hfr
          have hek_lt := bobDoneBaseKeys_stampsLt (interp := interp') (S := S) (g := g')
            hc₄.matched.2.1.2.2.1.1 (Nat.le_refl tr₄.length) hek_mem
          rw [cbadG2_gamma_eq hga hek_lt] at heq
          exact hno_done q hq ⟨ek, hek_mem, heq⟩
        have hcoins_ne : c.coins ≠ [] := by intro hnil; rw [hnil] at hcoins; cases hcoins
        have hB_rng := eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hE_rng
        have hB_acc := eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hE_acc
        have hB_recv := eventMatchesEntry_to_bytesMatchEntry (fun h => by cases h) (fun _ h => by cases h) hE_recv
        have hdrs_out : DrawsMatch interp' r S g_out
            [⟨.rng, [randTerm tr₄.length 32], .single, none⟩] ev.coins :=
          ⟨[c.coins], fun p hp => by simp only [List.mem_singleton] at hp; exact hp ▸ hcoins_ne,
            by simp [hev_coins], .cons hB_rng .nil⟩
        have hinp_out : BytesMatchEntry interp' r S g_out (inputKind ev) ev.input
            ⟨.recv, [x.ek, x.ct, x.msg] ++ (opk.map DiffieHellman.dhPk).toList,
              .preKeyRecv, none⟩ := by
          rw [hev_kind, hev_input]
          exact hB_recv
        have hrm_out : RunMatches interp' r S g_out (runSteps pre (runTrace r ss')) sBob ev vBob
            (activeBundleIds evs_pre) := by
          rw [← htr₄_eq]
          refine ⟨rfl, hev_party.symm ▸ rfl, hfits_cmd, hpeer_ok, hok_s, ⟨out, hev_exit⟩, rfl,
            _, [_], [_], hvBob_eq_mvis, hinp_out, hdrs_out, ?_, hrf_out, hpf_out⟩
          simp only [OutputsMatch, hev_exit, hev_cmd]
          exact ⟨_, rfl, hB_acc⟩
        have hpre_inv : ∀ u ∈ pre, u.cls = .invisible := by
          intro u hu
          simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl <;> rfl
        have hme_out : MatchesEvents interp' r S g_out (setupTrace r)
            (ss' ++ pre ++ [sBob]) (evs_pre ++ [.run ev]) (vis' ++ vBob) :=
          matchesEvents_snoc_run1 hme_pre_out hpre_inv hrm_out
        have hex_out : Explains interp' r S g_out (ss' ++ pre ++ [sBob]) (vis' ++ vBob)
            (evs_pre ++ [.run ev]) :=
          ⟨hmp_out.1, hghost_out, hmwf_out, hme_out⟩
        have hnrc_out : ¬ ReadCollisionCli interp' r S g_out (ss' ++ pre ++ [sBob])
            (evs_pre ++ [.run ev]) := by
          rw [List.append_assoc]
          refine not_readCollisionCli_snoc_noDecrypt_any hfr hex'.2.2.1 hex'.2.2.2 hlen_ss'_le ?_ hnrc'
          intro u hu
          simp only [pre, sBob, List.cons_append, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl <;> rfl
        exact ⟨g_out, ss' ++ pre ++ [sBob], vis' ++ vBob, hex_out, hnrc_out⟩

private theorem rpk_clearStuckWrap_prekeyPath?_imp_local {tr : ExecTrace} {m : Move} {promote : Bool}
    (hp : (Sanitize.clearStuckWrap tr m).prekeyPath? = some promote) :
    m.prekeyPath? = some promote := by
  cases m <;> simp only [Sanitize.clearStuckWrap, Move.prekeyPath?] at hp ⊢
  case bobStart => exact hp
  case decrypt me si mi pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  case decryptSkipped me si mi k pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  all_goals cases hp

private theorem rpk_sanitize_clean_local {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (hc : Clean interpretation r S who ok g ms acc) :
    Clean interpretation r S who ok g (Sanitize.sanitizeMoves (setupTrace r) ms) acc := by
  let ms_s := Sanitize.sanitizeMoves (setupTrace r) ms
  have hpath_s : PathFaithful interpretation r S g ms_s acc := by
    intro i m' promote b' p hi hpath hcall hparse
    rw [Sanitize.getElem?_sanitizeMoves] at hi
    rcases hmi : ms[i]? with _ | m
    · simp [hmi] at hi
    · simp only [hmi, Option.map_some, Option.some.injEq] at hi
      subst hi
      simp only [ms_s, Sanitize.sanitizeMoves_take, Sanitize.runVis_sanitizeMoves,
        Sanitize.runTrace_sanitizeMoves] at hcall ⊢
      exact hc.matched.2.2.2.1 i m promote b' p hmi
        (rpk_clearStuckWrap_prekeyPath?_imp_local hpath) hcall hparse
  exact ⟨⟨⟨hc.matched.1, Sanitize.modelRun_sanitizeMoves hc.matched.2.1,
    Sanitize.roleFaithful_sanitizeMoves hc.matched.2.2.1, hpath_s,
    Sanitize.readFaithful_sanitizeMoves hc.matched.2.2.2.2.1,
    by simpa [ms_s] using hc.matched.2.2.2.2.2⟩,
    Sanitize.outcomeFaithful_sanitizeMoves hc.1.2⟩,
    mt Sanitize.readCollision_sanitizeMoves_iff.mp hc.2⟩

private theorem rpk_clean_snoc_attackerSend_local {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} {t : _root_.DY.Bytes}
    (hc : Clean interpretation r S who ok g ms acc)
    (ht : t.AttackerKnows (runTraceMoves r ms)) :
    Clean interpretation r S who ok g (ms ++ [.attackerSend t]) acc :=
  _root_.DY.Libsignal.Composed.Refinement.clean_attackerSend hc
    (by rw [_root_.DY.Libsignal.Composed.Refinement.runTrace_snoc]; exact b5_attackerSend_reachable hc.matched.2.1.2.2.1.1 t ht)

private theorem rpk_callCount_lt_snoc_attackerSend_local {r : ProtocolSetup} {ms : List Move}
    {acc : List MachineEvent} {t : _root_.DY.Bytes}
    (hlt : ∀ i (m : Move) promote, ms[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < (callStarts acc).length) :
    ∀ i (m : Move) promote, (ms ++ [Move.attackerSend t])[i]? = some m →
      m.prekeyPath? = some promote →
      callCount (runVis r ((ms ++ [Move.attackerSend t]).take i)) < (callStarts acc).length := by
  intro i m promote hi hpath
  rcases Nat.lt_or_ge i ms.length with hlt_i | hge_i
  · rw [List.getElem?_append_left hlt_i] at hi
    rw [List.take_append_of_le_length hlt_i.le]
    exact hlt i m promote hi hpath
  · rcases Nat.eq_or_lt_of_le hge_i with rfl | hgt_i
    · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; cases hpath
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

private theorem rpk_no_live_accept {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {t_clean : CliTurn} {accepted : List HwBytes}
    {evs_pre : List CliEvent} {c : CliCall} {out : HwBytes}
    {body : HwBytes} {pf : PreKeyFields} {sm : StateAndMessage} {ct_wire : HwBytes}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {x' : PreKeyRep}
    (hext' : ExternContractsHoldCli interp')
    (hr : ProtocolSetupWF r)
    (hSem : SemReady interp' r S)
    (hSeq : S = compSemOf interp' r)
    (hXlate : XlateInvSpecB)
    (hsched_pre : SchedFits (callsOf evs_pre) who ok)
    (hwho_k : who[(callStarts (flatEvents evs_pre)).length]? = some r.bob)
    (hlive_pre : CliLiveAtCli interp' r S who ok t_clean accepted (flatEvents evs_pre))
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hcoins : c.coins.length = 32)
    (_hstdin : c.stdin = wirePrekey :: body)
    (hp : parsePreKeyWire c.stdin = some pf)
    (hfresh : ∀ q, parsePreKeyWire c.stdin = some q → q.baseKey.take 33 ∉ accepted)
    (hC : RecvAcceptContractPure interp' r (t_clean.opkUsed r) c.stdin sm pf c.coins ct_wire out)
    (hnkm : ¬ KyberMismatch interp' r pf)
    (hex' : Explains interp' r S g' ss' vis' evs_pre)
    (hnrc' : ¬ ReadCollisionCli interp' r S g' ss' evs_pre)
    (hx'_on : x' ∈ preKeyRepresentationsOn interp' r S g' (runTrace r ss') c.stdin)
    (hnbsc_on : ¬ BobSessionStartCollidesOrImplicitRejectsOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') pf x') :
    let ev := runEventOf c (some (0, out))
    ∃ g ss vis,
      Explains interp' r S g ss vis (evs_pre ++ [.run ev]) ∧
        ¬ ReadCollisionCli interp' r S g ss (evs_pre ++ [.run ev]) := by
  obtain ⟨τ', ms', hex'_cli, hnrc'_cli, htr', hsalts', hpref', hpt'⟩ :=
    hXlate hr hSem hsched_pre hex' hnrc'
  have hc' : Clean interp' r S who ok g' ms' τ' := explainsCli_toClean hex'_cli hnrc'_cli
  have hlive_τ' := hlive_pre.cliLiveAt_of_cut ⟨g', ms', hex'_cli, hnrc'_cli⟩
  have hx'_ms : x' ∈ preKeyRepresentations interp' r S g' ms' c.stdin :=
    (preKeyRepresentations_iff_on htr').mpr hx'_on
  have hnbsc_ms : ¬ BobSessionStartCollidesOrImplicitRejects interp' r S g' ms' pf x' :=
    fun h => hnbsc_on ((bobStartCollision_iff_on htr' hsalts' hpref' hpt').mp h)
  set ms_s := Sanitize.sanitizeMoves (setupTrace r) ms'
  have hc_s : Clean interp' r S who ok g' ms_s τ' := rpk_sanitize_clean_local hc'
  have hlt_s : ∀ i (m : Move) promote, ms_s[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms_s.take i)) < (callStarts τ').length :=
    fun _ _ _ hi hpath => Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hc'.matched hi hpath
  have hx_s : x' ∈ preKeyRepresentations interp' r S g' ms_s c.stdin := by
    rwa [Sanitize.preKeyRepresentations_sanitizeMoves]
  have hnbsc_s : ¬ BobSessionStartCollidesOrImplicitRejects interp' r S g' ms_s pf x' := by
    rwa [rpk_bobStartCollision_sanitizeMoves]
  have hSeedAk : RpkSeedAkHyp interp' r S := rpk_seedAkHyp hext' hr hSeq
  have hNotSpqrMac : RpkNotSpqrMacHyp interp' r S := rpk_notSpqrMacHyp interp' r S
  have hS_ck : S.chainKey = Swarm.SHARED.SpqrBytes.spqrChainKeyOf interp' := by
    rw [hSeq]; rfl
  obtain ⟨hek'_gamma, _, msg', hparse', hwire'_gamma, hmac'_gamma, _, hcipher'_gamma, hrk'_gamma,
      hpq'_gamma, hctr'_eq, _⟩ :=
    TR.rep_ek_ct_gamma interp' r S g' ms_s c.stdin pf ct_wire x' hp hC.kyber_ct hx_s
  have hctr'_le : msg'.counter.toNat ≤ _root_.DY.Libsignal.TripleRatchet.maxForwardJumps :=
    hctr'_eq ▸ hC.counter_le
  have hpq'_ne : gamma interp' S g' msg'.pqRatchet ≠ [] := hpq'_gamma ▸ hC.pqRatchet_ne_nil
  obtain ⟨_, _, _, salt', seed', hbk', hcmk', hspqr', hbss', _⟩ :=
    bobSaltSeed_some_of_not_implicitReject hC.opk_ok hparse' hctr'_le hpq'_ne
  obtain ⟨hsalt'_gamma, hseed'_gamma, _⟩ :=
    TR.bobSaltSeed_gamma interp' hext'.1 r hr S g' hc_s.matched.1 (t_clean.opkUsed r) c.stdin pf
      hp hnkm ct_wire hC.kyber_ct hC.ct_len hC.opk_ok hC.counter_le hC.pqRatchet_ne_nil
      ms_s x' hx_s msg' salt' seed' hparse' hbss'
  have hlow' := x25519LowOrder_false_of_gamma_notLow interp' hext'.1 S g'
    (hrk'_gamma ▸ hC.ratchetKey_ok)
  have hek_eq : TR.ekBytes pf = (pf.baseKey.take 33).drop 1 := by simp [TR.ekBytes, List.drop_take]
  have hek'_rw : gamma interp' S g' x'.ek = (pf.baseKey.take 33).drop 1 := hek'_gamma.trans hek_eq
  obtain ⟨hp0, hp2, _⟩ := TR.gamma_setupPublic_0_2_6 interp' r S g' hc_s.matched.1 hr.1
  have hmac_T_gamma :
      gamma interp' S g'
        (_root_.DY.Libsignal.TripleRatchet.computeMac
          (_root_.DY.Libsignal.TripleRatchet.trMsgKeys salt' seed').macKey
          (_root_.DY.Libsignal.PQXDH.serializedIk (setupPublic r 0))
          (_root_.DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
        gamma interp' S g' msg'.mac := by
    rw [TR.gamma_computeMac, TR.gamma_trMsgKeys_macKey, hsalt'_gamma, hseed'_gamma,
      TR.gamma_serializedIk, TR.gamma_serializedIk, hp0, hp2, hwire'_gamma]
    exact (hC.mac_eq S hS_ck).trans hmac'_gamma.symm
  have hguard :=
    rpk_bobTrialGuard_of_contract hext'.1 hr.1 hC hlive_τ'.2.2 hc_s hx_s hparse'
  have hdec_salt'_seed' :
      interp' _root_.DY.Libsignal.Refinement.aesCbcDecryptSymbol
        [gamma interp' S g' msg'.ciphertext,
         gamma interp' S g' (_root_.DY.Libsignal.TripleRatchet.trMsgKeys salt' seed').cipherKey,
         (gamma interp' S g' (_root_.DY.Libsignal.TripleRatchet.trMsgKeys salt' seed').iv).take 16] =
        some out := by
    rw [hcipher'_gamma, TR.gamma_trMsgKeys_cipherKey, TR.gamma_trMsgKeys_iv,
      hsalt'_gamma, hseed'_gamma]
    exact hC.dec_eq S hS_ck
  have hcmac_len : (gamma interp' S g' msg'.mac).length = 8 := by
    rw [← hmac_T_gamma, TR.gamma_computeMac]; unfold TR.computeMacBytes
    rw [List.length_take, TR.length_hmacWith]; decide
  have hpt_mac : msg'.mac ∉ plaintextTerms (runVis r ms_s) := by
    simpa using TR.G1.g1_rep_ptAtoms_tr r ms_s [] (fun _ h => nomatch h) hparse'
  obtain ⟨x, msg, salt, seed, pqSalt, m, hx, hcan, hparse, hlow, hbss, hpq_ak, hmac, hdec, hpt⟩ :=
    rpk_exactRep_of_not_bobStartCollision hr hext'.1 hext'.2 hNotSpqrMac hSeedAk
      hc_s.matched hp hnkm hC.kyber_ct hC.ct_len
      (hC.opk_ok.imp id fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩) hx_s hnbsc_s hbk' hguard hparse' hcmk' hspqr'
      hbss' (hek'_rw ▸ hC.baseKey_ok.1) (hek'_rw ▸ hC.baseKey_ok.2.1) (hek'_rw ▸ hC.baseKey_ok.2.2)
      hlow' hctr'_le hcmac_len hmac_T_gamma hdec_salt'_seed' hpq'_ne hpt_mac
  let ms₁ := ms_s ++ [Move.attackerSend x.ek]
  let ms₂ := ms₁ ++ [Move.attackerSend x.ct]
  let ms₃ := ms₂ ++ [Move.attackerSend x.msg]
  let ms₄ := ms₃ ++ [Move.attackerSend pqSalt]
  have hx₁ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.ek]) hx
  have hx₂ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.ct]) hx₁
  have hx₃ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.msg]) hx₂
  have hx₄ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend pqSalt]) hx₃
  have hpq₃ : pqSalt.AttackerKnows (runTraceMoves r ms₃) :=
    _root_.DY.Bytes.AttackerKnows_le _ _ _ (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₂ _)
      (_root_.DY.Bytes.AttackerKnows_le _ _ _ (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₁ _)
        (_root_.DY.Bytes.AttackerKnows_le _ _ _ (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms_s _) hpq_ak))
  have hc₁ := rpk_clean_snoc_attackerSend_local hc_s hx.1
  have hc₂ := rpk_clean_snoc_attackerSend_local hc₁ hx₁.2.1
  have hc₃ := rpk_clean_snoc_attackerSend_local hc₂ hx₂.2.2.1
  have hc₄ := rpk_clean_snoc_attackerSend_local hc₃ hpq₃
  have hlt₄ := rpk_callCount_lt_snoc_attackerSend_local
    (rpk_callCount_lt_snoc_attackerSend_local
      (rpk_callCount_lt_snoc_attackerSend_local
        (rpk_callCount_lt_snoc_attackerSend_local hlt_s (t := x.ek)) (t := x.ct)) (t := x.msg))
    (t := pqSalt)
  let mh : PreKeyMsgHandles :=
    ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
  let pqIdx : Nat := (runTraceMoves r ms₃).length
  have hek₄ : (runTraceMoves r ms₄).at? mh.ek = some (NetE x.ek) :=
    rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₃ _)
      (rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₂ _)
        (rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₁ _)
          (by rw [_root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _)))
  have hct₄ : (runTraceMoves r ms₄).at? mh.ct = some (NetE x.ct) :=
    rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₃ _)
      (rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₂ _)
        (by rw [_root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _))
  have hmsg₄ : (runTraceMoves r ms₄).at? mh.msg = some (NetE x.msg) :=
    rpk_at?_some_of_le (_root_.DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₃ _)
      (by rw [_root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _)
  have hpqSalt : (((runTraceMoves r ms₄).append (RndE 32)).append (NetE salt)).at? pqIdx =
      some (NetE pqSalt) :=
    rpk_at?_some_of_le (_root_.DY.Trace.append_le _ _)
      (rpk_at?_some_of_le (_root_.DY.Trace.append_le _ _)
        (by rw [_root_.DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _))
  have hcs_eq : (callStarts τ').length = (callStarts (flatEvents evs_pre)).length :=
    callStarts_length_of_coinSplit_local hex'_cli.1
  have hwho_τ' : who[(callStarts τ').length]? = some r.bob := hcs_eq ▸ hwho_k
  have hno_done : ∀ q, parsePreKeyWire c.stdin = some q →
      ¬ ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms₄),
        ecKey (gamma interp' S g' ek) = q.baseKey.take 33 := by
    intro q hq ⟨ek, hek, heq⟩
    exact hfresh q hq (heq ▸ (hlive_τ'.2.1.clean g' ms₄ hc₄).1.2.1.2.2.2 ek hek)
  have hopk_unused : r.withOpk = true → pf.preKeyId = some r.opkId →
      PQXDH.opkUsedB (runTraceMoves r ms₄) r.bob (DiffieHellman.dhPk (setupSecret r 6)) = false := by
    intro hw hpk
    rcases hC.opk_ok with hnone | ⟨_, hu, _⟩
    · rw [hnone] at hpk; cases hpk
    · simpa only [← rpk_setupPublic_8 r hr.1 hw] using hlive_τ'.2.2 hw hu g' ms₄ hc₄
  obtain ⟨opk, hsel, hmp_out⟩ :=
    rpk_bobStart_of_exactRep_pqSalt_at hr.1 hc₄.matched hlt₄ hwho_τ' hno_done hp hC.version hx₄
      hcan hparse hlow hbss hpqSalt hmac hdec hpt hopk_unused hek₄ hct₄ hmsg₄
  obtain ⟨opk₂, c'_ch, spqr', hsel₂, hcmk₂, hspqr₂⟩ :=
    bobSaltSeed_unpack_local r pf x msg salt seed hparse hbss
  have hopk_eq_opk₂ : opk₂ = opk := by
    rcases hsel with ⟨hn1, rfl⟩ | ⟨_, hp1, rfl⟩ <;> rcases hsel₂ with ⟨hn2, rfl⟩ | ⟨_, hp2, rfl⟩
    · rfl
    · rw [hn1] at hp2; cases hp2
    · rw [hn2] at hp1; cases hp1
    · rfl
  subst opk₂
  let kh := bobKeyHandlesOf opk
  let tr₄ := runTraceMoves r ms₄
  have hopk_st : StOpt tr₄ r.bob kh.opk opk := by
    rcases hsel with ⟨_, hopk_eq⟩ | ⟨hwith, _, hopk_eq⟩
    · dsimp only [kh]; rw [hopk_eq]; trivial
    · dsimp only [kh]; rw [hopk_eq]; exact MacInv.runTrace_at?_24 r hr.1 ms₄ hwith
  have hmac_eq_st : msg.mac = _root_.DY.Libsignal.TripleRatchet.computeMac
      (_root_.DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
      (bobRatchetedSt r.alice (DiffieHellman.dhPk (setupSecret r 1)) (setupPublic r 0)
        (bobKeysOf r x opk) (setupSecret r 2) msg.ratchetKey (randTerm tr₄.length 32)).peerIk
      (bobRatchetedSt r.alice (DiffieHellman.dhPk (setupSecret r 1)) (setupPublic r 0)
        (bobKeysOf r x opk) (setupSecret r 2) msg.ratchetKey (randTerm tr₄.length 32)).myIk
      msg.wire := by
    have hm0 := hmac
    have hp2' : setupPublic r 2 = DiffieHellman.dhPk (setupSecret r 1) := by
      rw [(TR.setupPublic_eq r hr.1).2.1, (TR.setupSecret_eq r hr.1).2.1]
    rw [hp2'] at hm0
    exact hm0
  have hused : ∀ o, opk = some o →
      PQXDH.opkUsedB ((tr₄.append (RndE 32)).append (NetE salt)) r.bob
        (DiffieHellman.dhPk o) = false := by
    intro o ho; rw [opkUsedB_append_rnd_net]
    rcases hsel with ⟨_, hopk_eq⟩ | ⟨hw, hpk, hopk_eq⟩
    · rw [hopk_eq] at ho; cases ho
    · rw [hopk_eq] at ho; rw [← Option.some.inj ho]; exact hopk_unused hw hpk
  have hver_msg : msg.version = _root_.DY.Libsignal.TripleRatchet.messageVersion := by
    obtain ⟨p₂, hp₂, msg₁, hparse₁, _, _, _, _, _, _, _, hver₁⟩ := hx.2.2.2.2
    cases hp.symm.trans hp₂; cases hparse.symm.trans hparse₁
    apply UInt8.ext; rw [hver₁, hC.version]; decide
  have hruns := Runs.bobStart (MacInv.runTrace_at?_9 r hr.1 ms₄) (MacInv.runTrace_at?_13 r hr.1 ms₄)
    (rpk_runTrace_at?_19_local r hr.1 ms₄) hopk_st (rpk_runTrace_at?_1_local r hr.1 ms₄)
    hek₄ hct₄ hcan (bobAgreement_of_not_implicitReject r x opk) hmsg₄ hparse hver_msg
    hlow hcmk₂ hspqr₂ hpqSalt hmac_eq_st hdec hused
  obtain ⟨hok_s, hnext_s⟩ := step_bobStart_run hruns
  have hnext_m : (Move.bobStart r.bob r.alice kh 1 mh pqIdx (preKeySpqrIndex pf) 3).next tr₄ =
      bobStartTr tr₄ r.bob r.alice
        (bobOut (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk (setupPublic r 0)
          x.ek x.ct (bobKeysOf r x opk)) msg c'_ch spqr' salt seed pqSalt m :=
    (b5_bobStart_next _ _ _ _ _ _ _ _ tr₄).trans hruns.2
  have htr_ms_s : runTraceMoves r ms_s = runTrace r ss' := by
    rw [Sanitize.runTrace_sanitizeMoves, htr']
  exact rpk_bobStart_step_explains hbob hcmd hcoins hex' hnrc' htr_ms_s rfl rfl rfl rfl rfl
    hx hx₁ hx₂ hx₄ hpq₃ hc₄ hno_done hopk_st hek₄ hct₄ hmsg₄ hok_s hnext_s hnext_m hmp_out

/-! ## Non-Promote Pre-Key Receive Slot Theorem -/

/-- Bob's non-promote pre-key `recv` slot preserves `PqTurnSim1A` and `UAInvB`, given
`XlateInvSpecB` and `XlateExcPSpecB`. -/
theorem uab_slot_rpk_no_of (hXI : XlateInvSpecB) (hXP : XlateExcPSpecB) :
    UASlotRpkNOSpecB := by
  intro interp P r hext hagree hr t t_clean c i code out files accepted evs_pre
    hsim hbob hcmd hbun hcoins hsb hfb hbca hkind hpqh hno_prom hin hRel
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hSem : SemReady interp' r S := compSemOf_ready interp' r hr
  obtain ⟨t_clean', accepted', hsim', hstep_cli⟩ :=
    slot_rpk_new_over_cli_gen outcomeFaithfulCli_of_goodExit0Cut bridgeB_quiet_fail
      interp P r hext hagree hr hsim hbob hcmd hbun hcoins hsb hfb hbca hkind hpqh hno_prom hin hRel
      (σ_pre := flatEvents evs_pre)
  refine ⟨t_clean', accepted', hsim', fun who ok hsched hua => ?_⟩
  let ev := runEventOf c (some (code, out))
  obtain ⟨hsched_pre, hwho_k, hok_k, hflat_eq⟩ := schedFits_recv_call hcmd hsched
  rcases hua with hcol_pre | ⟨hlive_pre, hpend_pre, ⟨g₀, ss₀, vis₀, hex₀, hnrc₀⟩⟩
  · exact Or.inl (collisionAtCli_append [.run ev] hcol_pre)
  · by_cases hcol : CollisionAfterExplainedPrefix interp' r S (evs_pre ++ [.run ev])
    · exact Or.inl hcol
    · refine Or.inr ⟨?_,
        aliceRecordPendingInSession_bob_recv hr hbob hcmd hsim hsim' hpend_pre, ?_⟩
      ·
        rw [hflat_eq]
        refine hstep_cli who ok hwho_k hlive_pre ?_ hok_k
        intro hcode0 pf₁ hp₁ hfresh₁ hrep_all τ₁ g ms hex₁ hnrc₁ _
        subst hcode0
        obtain ⟨τ₀, ms₀, hex₀_cli, hnrc₀_cli, htr₀, _, _, _⟩ :=
          hXI hr hSem hsched_pre hex₀ hnrc₀
        have hc₀ : Clean interp' r S who ok g₀ ms₀ τ₀ := explainsCli_toClean hex₀_cli hnrc₀_cli
        have hlive_τ₀ := hlive_pre.cliLiveAt_of_cut ⟨g₀, ms₀, hex₀_cli, hnrc₀_cli⟩
        have hnk₀_ms : ¬ KnownBaseKey interp' r S g₀ ms₀ pf₁ := by
          rintro ⟨ek, hek, heq⟩
          exact hfresh₁ (heq ▸ (hlive_τ₀.2.1.clean g₀ ms₀ hc₀).1.2.1.2.2.2 ek hek)
        have hnk₀_on : ¬ KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) pf₁ :=
          fun h => hnk₀_ms ((knownBaseKey_iff_on htr₀).mpr h)
        have hev_input : ev.input = c.stdin := by simp [ev, runEventOf, runInput, hcmd]
        have hrep₀_on : ∃ x, x ∈ preKeyRepresentationsOn interp' r S g₀ (runTrace r ss₀) ev.input := by
          rw [hev_input]
          obtain ⟨x, hx⟩ := hrep_all g₀ ms₀
          exact ⟨x, (preKeyRepresentations_iff_on htr₀).mp hx⟩
        have hp₁_ev : parsePreKeyWire ev.input = some pf₁ := hev_input.symm ▸ hp₁
        have hexcp := hXP hr hSem hsched hlive_pre hex₀ hnrc₀ hcmd rfl hp₁_ev hnk₀_on hrep₀_on
          hcol τ₁ g ms hex₁ hnrc₁
        dsimp only [ev] at hev_input
        rwa [hev_input] at hexcp
      ·
        by_cases hcode0 : code = 0
        · subst hcode0
          obtain ⟨body, pf, sm, ct_wire, hstdin, hp, hhon, hfresh, hC⟩ :=
            rpk_no_accept_contract interp P r hext hagree hr hsim hbob hcmd hbun hcoins
              hsb hfb hbca hkind hno_prom hin hRel
          obtain ⟨τ₀, ms₀, hex₀_cli, hnrc₀_cli, htr₀, _, _, _⟩ :=
            hXI hr hSem hsched_pre hex₀ hnrc₀
          have hc₀ : Clean interp' r S who ok g₀ ms₀ τ₀ := explainsCli_toClean hex₀_cli hnrc₀_cli
          have hlive_τ₀ := hlive_pre.cliLiveAt_of_cut ⟨g₀, ms₀, hex₀_cli, hnrc₀_cli⟩
          have hnk₀_on : ¬ KnownBaseKeyOn interp' S g₀ (runTrace r ss₀) pf := by
            rintro ⟨ek, hek, heq⟩
            rw [← htr₀] at hek
            exact hfresh pf hp (heq ▸ (hlive_τ₀.2.1.clean g₀ ms₀ hc₀).1.2.1.2.2.2 ek hek)
          have hrep₀_ms : ∃ x, x ∈ preKeyRepresentations interp' r S g₀ ms₀ c.stdin :=
            rpk_reps_nonempty interp' r S g₀ ms₀ c.stdin pf ct_wire hp hC.outer_ver hC.spkId_eq
              hC.kpkId_eq hC.kyber_ct hhon (hC.opk_ok.imp id fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩)
          have hrep₀_on : ∃ x, x ∈ preKeyRepresentationsOn interp' r S g₀ (runTrace r ss₀) c.stdin := by
            obtain ⟨x, hx⟩ := hrep₀_ms
            exact ⟨x, (preKeyRepresentations_iff_on htr₀).mp hx⟩
          have hnexc : ¬ PreKeyStartCollidesOrRejects interp' r S g₀ ss₀ evs_pre c.stdin pf := by
            intro hexc
            apply hcol
            refine ⟨evs_pre, ev, [], g₀, ss₀, vis₀, rfl, hex₀, ?_⟩
            have hev_cmd : ev.cmd = .recv (peerOf r r.bob) := hcmd
            have hev_input : ev.input = wirePrekey :: body := by
              simp [ev, runEventOf, runInput, hcmd, hstdin]
            dsimp only [_root_.DY.Libsignal.Composed.Refinement.Cli.NextEventCollides]
            rw [hev_cmd, hev_input]
            exact ⟨⟨out, rfl⟩, Or.inr ⟨pf, hstdin ▸ hp, Or.inr ⟨hnk₀_on, hstdin ▸ hexc⟩⟩⟩
          have hnot_or : ¬ (KyberMismatch interp' r pf ∨
              ∀ g' ss' vis', Explains interp' r S g' ss' vis' evs_pre →
                ¬ ReadCollisionCli interp' r S g' ss' evs_pre →
                ∀ x ∈ preKeyRepresentationsOn interp' r S g' (runTrace r ss') c.stdin,
                  BobSessionStartCollidesOrImplicitRejectsOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') pf x) :=
            fun hor => hnexc ⟨hrep₀_on, hor⟩
          have hnkm : ¬ KyberMismatch interp' r pf := fun hkm => hnot_or (Or.inl hkm)
          have hnot_all : ¬ (∀ g' ss' vis', Explains interp' r S g' ss' vis' evs_pre →
              ¬ ReadCollisionCli interp' r S g' ss' evs_pre →
              ∀ x ∈ preKeyRepresentationsOn interp' r S g' (runTrace r ss') c.stdin,
                BobSessionStartCollidesOrImplicitRejectsOn interp' r S g' (runTrace r ss') vis' (honestSaltsOf r ss') pf x) :=
            fun hall => hnot_or (Or.inr hall)
          obtain ⟨g', ss', vis', hex', hnrc', x', hx'_on, hnbsc_on⟩ :
              ∃ g' ss' vis', Explains interp' r S g' ss' vis' evs_pre ∧
                ¬ ReadCollisionCli interp' r S g' ss' evs_pre ∧
                ∃ x' ∈ preKeyRepresentationsOn interp' r S g' (runTrace r ss') c.stdin,
                  ¬ BobSessionStartCollidesOrImplicitRejectsOn interp' r S g' (runTrace r ss') vis'
                      (honestSaltsOf r ss') pf x' := by
            by_contra hnone
            apply hnot_all
            intro g' ss' vis' hex' hnrc' x' hx'
            by_contra hnbsc
            exact hnone ⟨g', ss', vis', hex', hnrc', x', hx', hnbsc⟩
          exact rpk_no_live_accept hext' hr hSem rfl hXI hsched_pre (hbob ▸ hwho_k) hlive_pre
            hbob hcmd hcoins hstdin hp hfresh hC hnkm hex' hnrc' hx'_on hnbsc_on
        · have hrej : RunRejected ev := by
            intro out' hexit
            change some (code, out) = some (0, out') at hexit
            injection hexit with h1
            injection h1 with hc0 _
            exact hcode0 hc0
          have hex_rej : Explains interp' r S g₀ ss₀ vis₀ (evs_pre ++ [.run ev]) :=
            explains_snoc_rejected hrej hex₀
          have hnrc_rej : ¬ ReadCollisionCli interp' r S g₀ ss₀ (evs_pre ++ [.run ev]) := by
            simpa only [List.append_nil] using
              not_readCollisionCli_snoc_noDecrypt_any (δ := [])
                (cBadSigmaFrame_refl g₀ (runTrace r ss₀).length)
                hex₀.2.2.1 hex₀.2.2.2 (Nat.le_refl _) (by simp) hnrc₀
          exact ⟨g₀, ss₀, vis₀, hex_rej, hnrc_rej⟩

end Symbolic.Proofs.Swarm.UA.BI.G.SlotRpkNO
