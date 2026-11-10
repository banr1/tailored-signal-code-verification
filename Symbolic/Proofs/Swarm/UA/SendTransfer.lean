/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredClassical
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.CBadG2.MacGuess
import Symbolic.Proofs.Swarm.CREF.CBadG2.Stamps
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReach
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReachBob
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.SendWire.GhostInvariance
import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.SlotInitTransfer
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Step and Ghost Transfer for the `send` Slot

Establishes `CBadGammaAgree` transfer across `setSendAddr`, trace evaluation and `GhostWF`
extension for `Step.messageEncrypt`, and step-level clean-explanation extensions for rejected,
Whisper, and pending-pre-key `send` runs.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.SendTransfer

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace Traceful)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (EnvEvent RunEvent CliEvent)
open _root_.DY.Libsignal.PQXDH (PQXDHEvent)
open _root_.DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed (ComposedEvent reachability)
open _root_.DY.Libsignal.Composed.Refinement
  (Step VisEntry VisEventKind ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost GhostWF
   GhostAndSemMatchSetup ExplainsClassical MatchesEventsClassical MatchesEventsClassicalAt
   EnvMatchesClassical BundlePreKeyIds activeBundleIds
   sessionHasDecrypted
   RunMatches RunRejected DrawsMatch OutputsMatch BytesMatchEntry ReadsFaithfully PathFaithfulAt
   StepsWF StepsStateFaithful ModelRunWF stepView encDraws encSendEntry pendingPreKey lastSent
   rngEntry randTerm runWrapped inputKind setupTrace runSteps runTrace
   SendMatches PreKeyRep recvRepresentationsOn preKeyRepresentationsOn
   ecKey kyberKey secretBytes
   gamma ConcretizedTerm concretizeAll allFuns concretizeTrWire concretizeSym concretizeRandom
   RecvCollisionOn honestSaltsOf honestKeysOf availableStates bobDoneBaseKeys
   whisperTrials trialTerms Move StateFaithful runTraceMoves runMoves)
open _root_.DY.Libsignal.Composed.Refinement.Cli
  (ReadCollisionCliClassical aliceUuid bobUuid serializeAddresses)
open _root_.DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot parseTrSignalMsg trMsgKeys computeMac)
open CryptoVerification.SignalSession (Address)
open Symbolic.Proofs.Swarm.UA.Base (runSteps_append runTrace_append)
open Symbolic.Proofs.Swarm.UA.SlotInitTransfer
  (step_le_next runSteps_le step_next_reachable runSteps_reachable stepsWF_append_iff
   matchesEvents_snoc_run1 visStampsLt_of_stepView
   bytesMatchEntry_transfer matchesEvents_visStampsLt ghostWF_transfer matchesEvents_transfer)
open Symbolic.Swarm.CREF
  (RoleStE SemReady CBadSigmaFrame CBadGammaAgree
   cBadSigmaFrame_updateFreshAt cbadG2_fst_lt_of_mem_setupRandomsAt
   cbadG2_gamma_eq cbadG2_stampsLt_getMessageSentAt_of_entries cbadG2_getMessageSentAt_le
   g2b_bobDoneEk_stampsLt_of_reachable cbadG2_memoCollisionOn_iff
   cbadG2_stampsLt_prefixTerms cbadG2_stateStampsLt_availableStates
   cbadG2_stampsLt_skippedLogged_of_entries cbadG2_stampsLt_whisperTrials cbadG2_stampsLt_saltTerms
   stampsLt_wire_of_computeMac)
open Symbolic.Swarm.CREF.CliPure (cbadG2_preKeyRecvMatches_transfer)
open Symbolic.Swarm.CREF.TR.FreshSigma
  (MemoRel MemoStampsLt memoStampsLt_of_mem
   gConcat0_pp2 gDhPk_pp2 gDh_pp2 gKdf0_pp2 gSym0_pp2 gTrunc0_pp2 gVariant0_pp2
   gKemPk_pp2 gKemEncap_pp2 gKemSS_pp2 gKemRej_pp2 gVk_pp2 gSign_pp2
   gSpqrInit_pp2 gSpqrSendState_pp2 gSpqrSendKey_pp2 gSpqrSendMsg_pp2
   gSpqrRecvState_pp2 gSpqrRecvKey_pp2 gSpqrChainKey_pp2)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength
  _root_.DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes _root_.DY.Libsignal.Composed.toTripleRatchet
  _root_.DY.Libsignal.Composed.toPQXDHSpqr

/-! ## `setSendAddr` Stamp and Explanation Transfer -/

private def sendSigGhost (g : Ghost) (ts : Nat) (pt coins : HwBytes) : Ghost :=
  { g with
    σ := Symbolic.Swarm.CREF.TR.FreshSigma.updateFreshAt
      (Symbolic.Swarm.CREF.TR.FreshSigma.updateFreshAt g.σ ts 32 pt)
      (ts + 1) coins.length coins }

private theorem cBadSigmaFrame_sendSigGhost (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    CBadSigmaFrame g (sendSigGhost g ts pt coins) ts := by
  have h1 : CBadSigmaFrame g
      { g with σ := Symbolic.Swarm.CREF.TR.FreshSigma.updateFreshAt g.σ ts 32 pt } ts :=
    cBadSigmaFrame_updateFreshAt g (Nat.le_refl ts) 32 pt
  have h2 : CBadSigmaFrame
      { g with σ := Symbolic.Swarm.CREF.TR.FreshSigma.updateFreshAt g.σ ts 32 pt }
      (sendSigGhost g ts pt coins) ts :=
    cBadSigmaFrame_updateFreshAt _ (Nat.le_succ ts) coins.length coins
  exact ⟨fun i hi n => (h2.1 i hi n).trans (h1.1 i hi n), h2.2.trans h1.2⟩

private theorem sendGhost_eq_setSendAddr (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    Symbolic.Swarm.CREF.SendWire.sendGhost g ts pt coins =
      Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g ts pt coins) ts [] :=
  rfl

private theorem sendPendingGhost_eq_setSendAddr (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    Symbolic.Swarm.CREF.SendWire.sendPendingGhost g ts pt coins =
      Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g ts pt coins) ts
        Symbolic.Swarm.CREF.SendWire.pqHarnessAddrBytes :=
  rfl

section SetSendAddrRev

unseal _root_.DY.Bytes

private theorem isFreshSendWire_eq_false_of_memoStampsLt
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (x : _root_.DY.TrWire.TrWireMsg.SubF _root_.DY.Bytes)
    (h : MemoStampsLt ts (concretizeTrWire g x (fun y _ => _root_.DY.Bytes.rec (concretizeAll i S g) y))) :
    Symbolic.Swarm.CREF.SendWire.isFreshSendWire ts x.pack = false := by
  cases htrue' : Symbolic.Swarm.CREF.SendWire.isFreshSendWire ts x.pack with
  | false => rfl
  | true =>
    unfold Symbolic.Swarm.CREF.SendWire.isFreshSendWire at htrue'
    rw [_root_.DY.BytesView.view_pack] at htrue'
    dsimp only at htrue'
    split at htrue'
    · next e he =>
      split at htrue'
      · next r hr =>
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at htrue'
        obtain ⟨hts_eq, hsz_eq⟩ := htrue'
        rcases x with ⟨v, rk, c, pc, ct, pq, ev⟩
        dsimp only [concretizeTrWire] at he h
        have hct : MemoStampsLt ts (_root_.DY.Bytes.rec (concretizeAll i S g) ct) :=
          Symbolic.Swarm.CREF.TR.FreshSigma.memoStampsLt_of_mem h (by simp)
        have hpv_e := _root_.DY.Bytes.pack_view? _root_.DY.SymEnc.Enc.SubF ct
        rw [he] at hpv_e
        rw [← hpv_e, _root_.DY.Bytes.rec_eq (concretizeSym i) (concretizeAll i S g)] at hct
        rcases e with ⟨k, iv, msg⟩
        dsimp only [concretizeSym] at hr hct
        have hmsg : MemoStampsLt ts (_root_.DY.Bytes.rec (concretizeAll i S g) msg) :=
          Symbolic.Swarm.CREF.TR.FreshSigma.memoStampsLt_of_mem hct (by simp)
        have hpv_r := _root_.DY.Bytes.pack_view? _root_.DY.Random.Random msg
        rw [hr] at hpv_r
        rw [← hpv_r, _root_.DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)] at hmsg
        dsimp only [concretizeRandom] at hmsg
        have hsz0 : r.size ≠ 0 := by omega
        simp only [hsz0, ↓reduceIte] at hmsg
        have hlt : r.timestamp < ts :=
          hmsg r.pack r.pack (g.σ r.timestamp r.size) r (List.mem_cons_self ..)
            (_root_.DY.BytesView.view_pack r)
        omega
      · cases htrue'
    · cases htrue'

private theorem isFreshSendWire_eq_false_of_stampsLt
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (w : _root_.DY.Bytes)
    (hw : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt i S g ts w) :
    Symbolic.Swarm.CREF.SendWire.isFreshSendWire ts w = false := by
  cases hvw : w.view? _root_.DY.TrWire.TrWireMsg.SubF with
  | none => simp [Symbolic.Swarm.CREF.SendWire.isFreshSendWire, hvw]
  | some x =>
    have hpv := _root_.DY.Bytes.pack_view? _root_.DY.TrWire.TrWireMsg.SubF w
    rw [hvw] at hpv
    rw [← hpv]
    refine isFreshSendWire_eq_false_of_memoStampsLt i S g ts x ?_
    change MemoStampsLt ts (_root_.DY.Bytes.rec (concretizeAll i S g) w) at hw
    rwa [← hpv, _root_.DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll i S g)] at hw

private theorem gTrWire0_setSendAddr_rev_pp2
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (rec2 : _root_.DY.Bytes → ConcretizedTerm) :
    _root_.DY.Bytes.PartialProof2
      (concretizeTrWire (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)) (concretizeTrWire g)
      (_root_.DY.Bytes.rec (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)))
      rec2 (MemoRel ts) := by
  intro x ih h
  have hfalse : Symbolic.Swarm.CREF.SendWire.isFreshSendWire ts x.pack = false :=
    isFreshSendWire_eq_false_of_memoStampsLt i S
      (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr) ts x h
  rcases x with ⟨v, rk, c, pc, ct, pq, ev⟩
  dsimp only [concretizeTrWire, MemoRel] at h hfalse ⊢
  have hrk : rec2 rk = _root_.DY.Bytes.rec
      (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)) rk :=
    ih rk (by simp +arith [_root_.DY.ALaCarte.FunctorSizeOf.sizeOf])
      (memoStampsLt_of_mem h (by simp))
  have hct : rec2 ct = _root_.DY.Bytes.rec
      (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)) ct :=
    ih ct (by simp +arith [_root_.DY.ALaCarte.FunctorSizeOf.sizeOf])
      (memoStampsLt_of_mem h (by simp))
  have hpq : rec2 pq = _root_.DY.Bytes.rec
      (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)) pq :=
    ih pq (by simp +arith [_root_.DY.ALaCarte.FunctorSizeOf.sizeOf])
      (memoStampsLt_of_mem h (by simp))
  rw [hrk, hct, hpq]
  dsimp only [Symbolic.Swarm.CREF.SendWire.setSendAddr]
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte]

private theorem allFuns_setSendAddr_rev_pp2
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (rec2 : _root_.DY.Bytes → ConcretizedTerm) (id : Fin 12) :
    _root_.DY.Bytes.PartialProof2
      (allFuns i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr) id) (allFuns i S g id)
      (_root_.DY.Bytes.rec (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)))
      rec2 (MemoRel ts) := by
  let rec1 := _root_.DY.Bytes.rec (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr))
  match id with
  | ⟨0, _⟩ =>
    dsimp only [allFuns, _root_.DY.Libsignal.Composed.SubF.internal]
    intro _ _ _; rfl
  | ⟨1, _⟩ => dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩ _ _ _; rfl
  | ⟨2, _⟩ => dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gConcat0_pp2 ts rec1 rec2
  | ⟨3, _⟩ =>
    dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro id2
    match id2 with | ⟨0, _⟩ => exact gDhPk_pp2 i ts rec1 rec2 | ⟨1, _⟩ => exact gDh_pp2 i ts rec1 rec2
  | ⟨4, _⟩ => dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gKdf0_pp2 i ts rec1 rec2
  | ⟨5, _⟩ => dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gSym0_pp2 i ts rec1 rec2
  | ⟨6, _⟩ => dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gTrunc0_pp2 ts rec1 rec2
  | ⟨7, _⟩ => dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gVariant0_pp2 ts rec1 rec2
  | ⟨8, _⟩ =>
    dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gKemPk_pp2 S ts rec1 rec2
    | ⟨1, _⟩ => exact gKemEncap_pp2 i ts rec1 rec2
    | ⟨2, _⟩ => exact gKemSS_pp2 i S ts rec1 rec2
    | ⟨3, _⟩ => exact gKemRej_pp2 S ts rec1 rec2
  | ⟨9, _⟩ =>
    dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro id2
    match id2 with | ⟨0, _⟩ => exact gVk_pp2 S ts rec1 rec2 | ⟨1, _⟩ => exact gSign_pp2 S ts rec1 rec2
  | ⟨10, _⟩ =>
    dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gSpqrInit_pp2 S ts rec1 rec2
    | ⟨1, _⟩ => exact gSpqrSendState_pp2 S ts rec1 rec2
    | ⟨2, _⟩ => exact gSpqrSendKey_pp2 S ts rec1 rec2
    | ⟨3, _⟩ => exact gSpqrSendMsg_pp2 S ts rec1 rec2
    | ⟨4, _⟩ => exact gSpqrRecvState_pp2 S ts rec1 rec2
    | ⟨5, _⟩ => exact gSpqrRecvKey_pp2 S ts rec1 rec2
    | ⟨6, _⟩ => exact gSpqrChainKey_pp2 S ts rec1 rec2
  | ⟨11, _⟩ =>
    dsimp only [allFuns]; apply _root_.DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gTrWire0_setSendAddr_rev_pp2 i S g ts addr rec2

private theorem gammaAgree_setSendAddr_rev
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes) :
    CBadGammaAgree i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr) g ts := by
  have hpf : _root_.DY.Bytes.Proof2
      (concretizeAll i S (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr)) (concretizeAll i S g) (MemoRel ts) :=
    _root_.DY.Bytes.PartialProof2.combine (allFuns_setSendAddr_rev_pp2 i S g ts addr _)
  exact hpf.prove

end SetSendAddrRev

private theorem gammaAgree_setSendAddr_fwd
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes) :
    CBadGammaAgree i S g (Symbolic.Swarm.CREF.SendWire.setSendAddr g ts addr) ts :=
  Symbolic.Swarm.CREF.SendWire.gamma'_setSendAddr_of_stampsLt i S g ts addr

private theorem recvRepOn_of_gammaAgree {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts) {tr : ExecTrace}
    (htr : Symbolic.Swarm.CREF.TR.FreshSigma.TraceEntriesLt interp S g₁ ts tr)
    {b : HwBytes} {t : _root_.DY.Bytes}
    (ht : t ∈ recvRepresentationsOn interp S g₁ tr b) :
    t ∈ recvRepresentationsOn interp S g₂ tr b := by
  obtain ⟨hk, hb, hp, hf⟩ := ht
  have hts := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr hk
  refine ⟨hk, (cbadG2_gamma_eq hga hts).trans hb, hp, fun msg hmsg => ?_⟩
  obtain ⟨hw, hm, hrk, hct, hpq⟩ :=
    Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_parseTrSignalMsg hts hmsg
  obtain ⟨h1, h2, h3, h4⟩ := hf msg hmsg
  refine ⟨(cbadG2_gamma_eq hga hw).trans h1, (cbadG2_gamma_eq hga hm).trans h2, h3,
    fun m hm' => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := h4 m hm'
  exact ⟨(cbadG2_gamma_eq hga hct).trans e1, (cbadG2_gamma_eq hga hrk).trans e2,
    (cbadG2_gamma_eq hga hpq).trans e3, e4, e5⟩

private theorem preKeyRepOn_of_gammaAgree {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts) {tr : ExecTrace}
    (htr : Symbolic.Swarm.CREF.TR.FreshSigma.TraceEntriesLt interp S g₁ ts tr)
    {b : HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentationsOn interp r S g₁ tr b) :
    x ∈ preKeyRepresentationsOn interp r S g₂ tr b := by
  obtain ⟨hek, hct, hmsg, hm, p, hp, hfi⟩ := hx
  have h1 := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr hek
  have h2 := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr hct
  have h3 := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr hmsg
  refine ⟨hek, hct, hmsg, ?_, p, hp, ?_⟩
  · have hγ : ∀ t ∈ [x.ek, x.ct, x.msg], gamma interp S g₂ t = gamma interp S g₁ t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact cbadG2_gamma_eq hga h1
      · exact cbadG2_gamma_eq hga h2
      · exact cbadG2_gamma_eq hga h3
    exact (cbadG2_preKeyRecvMatches_transfer hγ).mpr hm
  · obtain ⟨msg, hpm, e1, e2, e8, e3, e4, e7, e5, e6⟩ := hfi
    obtain ⟨hw, hmac, hrk, hct', hpq⟩ :=
      Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_parseTrSignalMsg h3 hpm
    exact ⟨msg, hpm, (cbadG2_gamma_eq hga hw).trans e1, (cbadG2_gamma_eq hga hmac).trans e2, e8,
      (cbadG2_gamma_eq hga hct').trans e3, (cbadG2_gamma_eq hga hrk).trans e4,
      (cbadG2_gamma_eq hga hpq).trans e7, e5, e6⟩

private theorem bobDoneBaseKeys_stampsLt_loc {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr : ExecTrace} (hReach : tr.Reachable reachability) (hlen : tr.length ≤ ts)
    {ek : _root_.DY.Bytes} (hek : ek ∈ bobDoneBaseKeys tr) :
    Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g ts ek := by
  unfold bobDoneBaseKeys at hek
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hek
  split at hi
  · rename_i b a ikB ikA spk pqpk opk ek' ct keys hget
    cases hi
    exact g2b_bobDoneEk_stampsLt_of_reachable interp S g ts hReach hlen i b a ikB ikA spk pqpk opk
      ek ct keys hget
  · cases hi

private theorem matchesEvents_of_gammaAgree {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ g₂ : Ghost} {initIds : Option BundlePreKeyIds} {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts)
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g₁ initIds tr ss evs vis)
    (hReach : tr.Reachable reachability)
    (hwf : StepsWF ss tr)
    (hlen : (runSteps ss tr).length ≤ ts) :
    MatchesEventsClassicalAt interp r S g₂ initIds tr ss evs vis := by
  induction hme with
  | nil hinv => exact .nil hinv
  | @run0 _ tr₀ pre ss' ev evs' vs hpre hrej _ ih =>
    obtain ⟨hwf_pre, hwf_ss⟩ := (stepsWF_append_iff pre ss' tr₀).mp hwf
    rw [runSteps_append] at hlen
    exact .run0 hpre hrej (ih (runSteps_reachable pre hReach hwf_pre) hwf_ss hlen)
  | @env _ tr₀ pre s ss' ev evs' v vs hpre hem _ ih =>
    obtain ⟨hwf_pre, hpre_s, _, hwf_ss⟩ := (stepsWF_append_iff pre (s :: ss') tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    have hReach₂ := step_next_reachable hReach₁ hpre_s
    have hrun_eq : runSteps (pre ++ s :: ss') tr₀ = runSteps ss' (s.next (runSteps pre tr₀)) := by
      rw [runSteps_append]; rfl
    rw [hrun_eq] at hlen
    have hlen₂ : (s.next (runSteps pre tr₀)).length ≤ ts :=
      Nat.le_trans (_root_.DY.Trace.length_le _ _ (runSteps_le ss' _)) hlen
    have htr₂ :=
      Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₂ hlen₂
    cases ev with
    | leak p k =>
      obtain ⟨hcls, hleak, hp, hv_eq, v₀, rfl, hbme⟩ := hem
      have hv₀_st : Symbolic.Swarm.CREF.TR.FreshSigma.VisStampsLt interp S g₁ ts v₀ := by
        have hmem : v₀ ∈ stepView s (runSteps pre tr₀) false := by rw [← hv_eq]; simp
        exact visStampsLt_of_stepView hReach₁ (_root_.DY.Trace.le_refl _) hlen₂ htr₂ hmem
      have hem' : EnvMatchesClassical interp r S g₂ (runSteps pre tr₀) s (.leak p k) [v₀] :=
        ⟨hcls, hleak, hp, hv_eq, v₀, rfl, (bytesMatchEntry_transfer hga hv₀_st).mpr hbme⟩
      exact .env hpre hem' (ih hReach₂ hwf_ss hlen)
    | breakDH | breakKEM | invertDH _ | invertKEM _ | registerCorrupt _ _ => cases hem
  | @run1 initIds₀ tr₀ pre s ss' ev evs' v vs hpre hrm _ ih =>
    obtain ⟨hwf_pre, hpre_s, _, hwf_ss⟩ := (stepsWF_append_iff pre (s :: ss') tr₀).mp hwf
    have hReach₁ := runSteps_reachable pre hReach hwf_pre
    have hReach₂ := step_next_reachable hReach₁ hpre_s
    have hrun_eq : runSteps (pre ++ s :: ss') tr₀ = runSteps ss' (s.next (runSteps pre tr₀)) := by
      rw [runSteps_append]; rfl
    rw [hrun_eq] at hlen
    have hlen₂ : (s.next (runSteps pre tr₀)).length ≤ ts :=
      Nat.le_trans (_root_.DY.Trace.length_le _ _ (runSteps_le ss' _)) hlen
    have hlen₁ : (runSteps pre tr₀).length ≤ ts :=
      Nat.le_trans (_root_.DY.Trace.length_le _ _ (step_le_next s _)) hlen₂
    have htr₁ :=
      Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₁ hlen₁
    have htr₂ :=
      Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₂ hlen₂
    obtain ⟨hcls, hparty, hfits, hpeer, hok, hexit, hv_eq,
      inp, drs, outs, hv_split, hinp, hdrs, houts, hrf, hpf⟩ := hrm
    have hv_st : ∀ u ∈ v, Symbolic.Swarm.CREF.TR.FreshSigma.VisStampsLt interp S g₁ ts u :=
      fun u hu => by
        rw [hv_eq] at hu
        exact visStampsLt_of_stepView hReach₁ (_root_.DY.Trace.le_refl _) hlen₂ htr₂ hu
    have hinp_st := hv_st inp (by rw [hv_split]; simp)
    have hinp' := (bytesMatchEntry_transfer hga hinp_st).mpr hinp
    have hdrs' : DrawsMatch interp r S g₂ drs ev.coins := by
      obtain ⟨pieces, hne, hpref, hrel⟩ := hdrs
      refine ⟨pieces, hne, hpref, ?_⟩
      have hsub : ∀ d ∈ drs, Symbolic.Swarm.CREF.TR.FreshSigma.VisStampsLt interp S g₁ ts d :=
        fun d hd => hv_st d (by rw [hv_split]; simp [hd])
      clear hv_split hv_eq hne hpref
      revert pieces
      induction drs with
      | nil => intro pieces hrel; cases hrel; exact .nil
      | cons d ds ih_rel =>
        intro pieces hrel
        cases hrel with
        | cons hp htl =>
          exact .cons ((bytesMatchEntry_transfer hga (hsub d (by simp))).mpr hp)
            (ih_rel (fun d' hd' => hsub d' (by simp [hd'])) _ htl)
    have houts' : OutputsMatch interp r S g₂ ev outs initIds₀ := by
      unfold OutputsMatch at houts ⊢
      split at houts
      · obtain ⟨o, rfl, ho⟩ := houts
        exact ⟨o, rfl, (bytesMatchEntry_transfer hga (hv_st o (by rw [hv_split]; simp))).mpr ho⟩
      · obtain ⟨o, rfl, ho⟩ := houts
        exact ⟨o, rfl, (bytesMatchEntry_transfer hga (hv_st o (by rw [hv_split]; simp))).mpr ho⟩
      · exact houts
    have hrf' : ReadsFaithfully interp r S g₂ (runSteps pre tr₀) inp ev.input := by
      unfold ReadsFaithfully at hrf ⊢
      split at hrf
      · exact recvRepOn_of_gammaAgree hga htr₁ hrf
      · exact fun p hp => recvRepOn_of_gammaAgree hga htr₁ (hrf p hp)
      · exact preKeyRepOn_of_gammaAgree hga htr₁ hrf
      · trivial
    have hpf' : PathFaithfulAt interp S g₂ (runSteps pre tr₀) s ev.input := by
      intro p hp
      have hpf0 := hpf p hp
      have hknown_iff :
          (∃ ek ∈ bobDoneBaseKeys (runSteps pre tr₀),
              ecKey (gamma interp S g₂ ek) = p.baseKey.take 33) ↔
            (∃ ek ∈ bobDoneBaseKeys (runSteps pre tr₀),
              ecKey (gamma interp S g₁ ek) = p.baseKey.take 33) := by
        refine exists_congr fun ek => and_congr_right fun hek => ?_
        rw [cbadG2_gamma_eq hga (bobDoneBaseKeys_stampsLt_loc hReach₁ hlen₁ hek)]
      dsimp only at hpf0 ⊢
      cases s <;> simp_all
    exact .run1 hpre ⟨hcls, hparty, hfits, hpeer, hok, hexit, hv_eq,
      inp, drs, outs, hv_split, hinp', hdrs', houts', hrf', hpf'⟩ (ih hReach₂ hwf_ss hlen)

private theorem honestKeysOf_sent_loc :
    ∀ (ss : List Step) (tr : ExecTrace) (u : _root_.DY.Bytes),
      u ∈ honestKeysOf tr ss → ∃ k, (runSteps ss tr).getMessageSentAt k = some u
  | [], _, _, hu => by simp [honestKeysOf] at hu
  | s :: ss, tr, u, hu => by
    unfold honestKeysOf Step.publishedSpqrKey? at hu
    rcases List.mem_append.mp hu with hu | hu
    · refine ⟨DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx tr,
        cbadG2_getMessageSentAt_le (runSteps_le ss (s.next tr)) ?_⟩
      cases s with
      | messageEncrypt me stateIdx coinsLen pqIdx =>
        by_cases hpq : pqIdx = DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx tr
        · simp [hpq] at hu
        · simp only [hpq, ↓reduceIte] at hu
          rcases hm :
              (Step.next (.messageEncrypt me stateIdx coinsLen pqIdx) tr).getMessageSentAt
                (DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx tr)
            with _ | m <;> simp [hm] at hu
          subst hu; rfl
      | _ => simp at hu
    · exact honestKeysOf_sent_loc ss (s.next tr) u hu

private theorem honestSaltsOf_stampsLt_loc {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {ss : List Step}
    (htr : Symbolic.Swarm.CREF.TR.FreshSigma.TraceEntriesLt interp S g ts (runTrace r ss)) :
    ∀ s ∈ honestSaltsOf r ss, Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g ts s := by
  intro s hs
  unfold honestSaltsOf at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_zeroKey interp S g ts
  · obtain ⟨k, hk⟩ := honestKeysOf_sent_loc ss (setupTrace r) s hs
    exact cbadG2_stampsLt_getMessageSentAt_of_entries htr hk

private theorem recvCollisionOn_of_gammaAgree {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} {ts : Nat} (hga : CBadGammaAgree interp S g₁ g₂ ts)
    {ss₁ : List Step} {vis₁ : List VisEntry} {t : _root_.DY.Bytes}
    (hReach₁ : (runTrace r ss₁).Reachable reachability)
    (hlen₁ : (runTrace r ss₁).length ≤ ts)
    (hvis₁ : ∀ v ∈ vis₁, Symbolic.Swarm.CREF.TR.FreshSigma.VisStampsLt interp S g₁ ts v)
    (ht : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts t)
    (hcol : RecvCollisionOn interp r S g₁ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t) :
    RecvCollisionOn interp r S g₂ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t := by
  let tr₁ := runTrace r ss₁
  have htr₁ :=
    Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g₁ ts hReach₁ hlen₁
  have hpre := cbadG2_stampsLt_prefixTerms interp S g₁ r hReach₁ hlen₁ hvis₁
  have hstates := fun st (hst : st ∈ availableStates r tr₁) =>
    cbadG2_stateStampsLt_availableStates (S := S) (g := g₁) (n := ts) htr₁ hst
  have hsalts := honestSaltsOf_stampsLt_loc (r := r) (ss := ss₁) htr₁
  have hsk := cbadG2_stampsLt_skippedLogged_of_entries htr₁
  unfold RecvCollisionOn at hcol ⊢
  cases hp : parseTrSignalMsg t with
  | none =>
    simp only [hp] at hcol ⊢
    exact (cbadG2_memoCollisionOn_iff hga hpre (fun u hu => List.mem_singleton.mp hu ▸ ht)).mpr hcol
  | some msg =>
    simp only [hp] at hcol ⊢
    have hmsg := Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_parseTrSignalMsg ht hp
    have htrials := cbadG2_stampsLt_whisperTrials (r := r) htr₁ hstates hmsg
    have hwt_eq : whisperTrials interp r S g₂ tr₁ msg = whisperTrials interp r S g₁ tr₁ msg :=
      Symbolic.Swarm.CREF.Stage1Trials.whisperTrials_congr_gamma
        (cbadG2_gamma_eq hga hmsg.2.2.1)
        (fun st hst_mem c hc => cbadG2_gamma_eq hga ((hstates st hst_mem).2.2.2.2.2.2 c hc).1)
        (fun idx hlt s pk ctr seed rIdx src hget =>
          cbadG2_gamma_eq hga (hsk idx s pk ctr seed rIdx src hlt hget).2)
    rw [hwt_eq]
    have hnew : ∀ u ∈ t :: (whisperTrials interp r S g₁ tr₁ msg).flatMap
        (trialTerms (honestSaltsOf r ss₁) msg),
        Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts u := by
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · obtain ⟨ctx, hctx, hu_ctx⟩ := List.mem_flatMap.mp hu
        have htr_ctx := htrials ctx hctx
        unfold trialTerms at hu_ctx
        rcases List.mem_append.mp hu_ctx with hu_ex | hu_rest
        · exact htr_ctx.2.2.1 u hu_ex
        · revert hu_rest
          cases hseed_eq : ctx.seed? with
          | none => intro h; cases h
          | some seed =>
            dsimp only; intro hu_flat
            obtain ⟨salt, hsalt, hu_salt⟩ := List.mem_flatMap.mp hu_flat
            exact cbadG2_stampsLt_saltTerms htr_ctx.1 htr_ctx.2.1 hmsg
              (htr_ctx.2.2.2.2 seed hseed_eq) (hsalts salt hsalt) u hu_salt
    rcases hcol with hmemo | hmac
    · exact Or.inl ((cbadG2_memoCollisionOn_iff hga hpre hnew).mpr hmemo)
    · refine Or.inr ?_
      have hkeys_lt : ∀ ctx ∈ whisperTrials interp r S g₁ tr₁ msg,
          ∀ seed, ctx.seed? = some seed → ∀ s ∈ ctx.ownSalts ++ honestSaltsOf r ss₁,
            let mk := trMsgKeys s seed
            Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts mk.cipherKey ∧
            Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts mk.macKey ∧
            Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts mk.iv ∧
            Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts
              (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) := by
        intro ctx hctx seed hseed s hs
        have htr_ctx := htrials ctx hctx
        have hs_lt : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₁ ts s := by
          rcases List.mem_append.mp hs with hs_own | hs_hon
          · exact htr_ctx.2.2.2.1 s hs_own
          · exact hsalts s hs_hon
        obtain ⟨hc_lt, hm_lt, hi_lt⟩ :=
          Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_trMsgKeys hs_lt
            (htr_ctx.2.2.2.2 seed hseed)
        exact ⟨hc_lt, hm_lt, hi_lt,
          Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_computeMac hm_lt htr_ctx.1 htr_ctx.2.1 hmsg.1⟩
      exact Symbolic.Swarm.CREF.Stage1Trials.MacTagForgeryOrCollision.congr_gamma
        (cbadG2_gamma_eq hga hmsg.2.1).symm
        (cbadG2_gamma_eq hga hmsg.1).symm
        (fun ctx hctx seed hseed =>
          (cbadG2_gamma_eq hga ((htrials ctx hctx).2.2.2.2 seed hseed)).symm)
        (fun ctx hctx seed hseed s hs =>
          let ⟨hc, hm, hi, hcm⟩ := hkeys_lt ctx hctx seed hseed s hs
          ⟨(cbadG2_gamma_eq hga hc).symm, (cbadG2_gamma_eq hga hm).symm,
           (cbadG2_gamma_eq hga hi).symm, (cbadG2_gamma_eq hga hcm).symm⟩)
        (fun peerIk₀ myIk₀ salt₀ seed₀ w hterm => by
          have hmac_lt := hmsg.2.1
          rw [hterm] at hmac_lt
          exact (cbadG2_gamma_eq hga (stampsLt_wire_of_computeMac hmac_lt)).symm)
        hmac

private theorem explains_prefix_setSendAddr {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hNe : r.alice ≠ r.bob) (hReady : SemReady interp r S)
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {evs_pre : List CliEvent}
    (pt coins addr : HwBytes)
    (haddr : addr = [] ∨ addr = serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩)
    (hex₀ : ExplainsClassical interp r S g₀ ss₀ vis₀ evs_pre) :
    let ts := (runTrace r ss₀).length
    let g' := Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g₀ ts pt coins) ts addr
    ExplainsClassical interp r S g' ss₀ vis₀ evs_pre := by
  intro ts g'
  obtain ⟨hcompat₀, hgwf₀, hwf₀, hme₀⟩ := hex₀
  let g₁ := sendSigGhost g₀ ts pt coins
  have hfr : CBadSigmaFrame g₀ g₁ ts := cBadSigmaFrame_sendSigGhost g₀ ts pt coins
  have hReach_setup : (setupTrace r).Reachable reachability := hwf₀.2.1
  have hReach₀ : (runTrace r ss₀).Reachable reachability :=
    runSteps_reachable ss₀ hReach_setup hwf₀.2.2.1
  have htr₀ :=
    Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g₀ ts hReach₀ (Nat.le_refl _)
  have hvis₀ := matchesEvents_visStampsLt hme₀ hReach_setup hwf₀.2.2.1 (Nat.le_refl _) htr₀
  have hsetup_le : (setupTrace r).length ≤ ts :=
    _root_.DY.Trace.length_le _ _ (runSteps_le ss₀ (setupTrace r))
  have hcompat' : GhostAndSemMatchSetup interp r S g' :=
    hReady g' fun p hp =>
      (hfr.1 p.1 (Nat.lt_of_lt_of_le (cbadG2_fst_lt_of_mem_setupRandomsAt hNe hp) hsetup_le)
        p.2).trans (hcompat₀.1 p hp)
  have hgwf₁ : GhostWF g₁ vis₀ := ghostWF_transfer hfr hvis₀ hgwf₀
  have hgwf' : GhostWF g' vis₀ := by
    refine ⟨hgwf₁.1, fun w => ?_,
      fun v hv hk => ⟨fun hlay ek ct msg pm hterms hpm => ?_, fun hlay msg pm hterms hpm => ?_⟩⟩
    · dsimp only [g', Symbolic.Swarm.CREF.SendWire.setSendAddr]
      split
      · exact haddr
      · exact hgwf₁.2.1 w
    · have hmsg_lt₀ : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₀ ts msg :=
        (hvis₀ v hv).1 msg (by simp [hterms])
      have hw_lt₀ : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₀ ts pm.wire :=
        (Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_parseTrSignalMsg hmsg_lt₀ hpm).1
      have hfalse : Symbolic.Swarm.CREF.SendWire.isFreshSendWire ts pm.wire = false :=
        isFreshSendWire_eq_false_of_stampsLt interp S g₀ ts pm.wire hw_lt₀
      have haddr_eq : g'.addr pm.wire = g₁.addr pm.wire := by
        dsimp only [g', Symbolic.Swarm.CREF.SendWire.setSendAddr]
        rw [hfalse]
        rfl
      rw [haddr_eq]
      exact (hgwf₁.2.2 v hv hk).1 hlay ek ct msg pm hterms hpm
    · have hmsg_lt₀ : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₀ ts msg :=
        (hvis₀ v hv).1 msg (by simp [hterms])
      have hw_lt₀ : Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g₀ ts pm.wire :=
        (Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_parseTrSignalMsg hmsg_lt₀ hpm).1
      have hfalse : Symbolic.Swarm.CREF.SendWire.isFreshSendWire ts pm.wire = false :=
        isFreshSendWire_eq_false_of_stampsLt interp S g₀ ts pm.wire hw_lt₀
      have haddr_eq : g'.addr pm.wire = g₁.addr pm.wire := by
        dsimp only [g', Symbolic.Swarm.CREF.SendWire.setSendAddr]
        rw [hfalse]
        rfl
      rw [haddr_eq]
      exact (hgwf₁.2.2 v hv hk).2 hlay msg pm hterms hpm
  have hme₁ : MatchesEventsClassical interp r S g₁ (setupTrace r) ss₀ evs_pre vis₀ :=
    matchesEvents_transfer hfr hme₀ hReach_setup hwf₀.2.2.1 (Nat.le_refl _)
  have hme' : MatchesEventsClassical interp r S g' (setupTrace r) ss₀ evs_pre vis₀ :=
    matchesEvents_of_gammaAgree (gammaAgree_setSendAddr_fwd interp S g₁ ts addr)
      hme₁ hReach_setup hwf₀.2.2.1 (Nat.le_refl _)
  exact ⟨hcompat', hgwf', hwf₀, hme'⟩

private theorem not_readCollisionCli_snoc_setSendAddr {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g₀ : Ghost} {ss₀ δ : List Step} {evs_pre : List CliEvent} {ev₀ : RunEvent}
    (pt coins addr : HwBytes)
    (hwf₀ : ModelRunWF r ss₀)
    (hδ : ∀ x ∈ δ, x.decryptMsgIdx? = none)
    (hnoAccRecv : ∀ peer out, ev₀.cmd = .recv peer → ev₀.exit ≠ some (0, out))
    (hnrc₀ : ¬ ReadCollisionCliClassical interp r S g₀ ss₀ evs_pre) :
    let ts := (runTrace r ss₀).length
    let g' := Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g₀ ts pt coins) ts addr
    ¬ ReadCollisionCliClassical interp r S g' (ss₀ ++ δ) (evs_pre ++ [.run ev₀]) := by
  intro ts g'
  let g₁ := sendSigGhost g₀ ts pt coins
  have hfr : CBadSigmaFrame g₀ g₁ ts := cBadSigmaFrame_sendSigGhost g₀ ts pt coins
  have hnrc₁ : ¬ ReadCollisionCliClassical interp r S g₁ (ss₀ ++ δ) (evs_pre ++ [.run ev₀]) :=
    Symbolic.Proofs.Swarm.UA.SlotInitTransfer.not_readCollisionCli_snoc_noDecrypt
      hfr hwf₀ (Nat.le_refl _) hδ hnoAccRecv hnrc₀
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, ⟨peer, hcmd⟩, hexit, hbody, hme₁, hdec, hsent, hcol⟩
  have hilt : ss₁.length < ss₀.length := by
    by_contra hge
    have hle : ss₀.length ≤ ss₁.length := Nat.le_of_not_lt hge
    have hget : (ss₀ ++ δ)[ss₁.length]? = (ss₁ ++ m :: ss₂)[ss₁.length]? :=
      congrArg (·[ss₁.length]?) hss
    rw [List.getElem?_append_right hle, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self] at hget
    have hm_in : m ∈ δ := List.mem_of_getElem? hget
    rw [hδ m hm_in] at hdec
    cases hdec
  obtain ⟨k, hk⟩ : ∃ k, ss₀.length - ss₁.length = k + 1 := ⟨ss₀.length - ss₁.length - 1, by omega⟩
  have hss₀ : ss₀ = ss₁ ++ m :: ss₂.take k := by
    have htake := congrArg (List.take ss₀.length) hss
    rw [List.take_left, List.take_append,
      List.take_of_length_le (Nat.le_of_lt hilt), hk, List.take_succ_cons] at htake
    exact htake
  have hReach_setup : (setupTrace r).Reachable reachability := hwf₀.2.1
  have hwf₁ : StepsWF ss₁ (setupTrace r) := by
    have hwf_all := hwf₀.2.2.1
    rw [hss₀] at hwf_all
    exact ((stepsWF_append_iff ss₁ (m :: ss₂.take k) (setupTrace r)).mp hwf_all).1
  have hReach₁ : (runTrace r ss₁).Reachable reachability :=
    runSteps_reachable ss₁ hReach_setup hwf₁
  have hle_tr : runTrace r ss₁ ≤ runTrace r ss₀ := by
    rw [hss₀, runTrace_append]
    exact runSteps_le (m :: ss₂.take k) (runTrace r ss₁)
  have hlen₁ : (runTrace r ss₁).length ≤ ts := _root_.DY.Trace.length_le _ _ hle_tr
  have hga_rev : CBadGammaAgree interp S g' g₁ ts :=
    gammaAgree_setSendAddr_rev interp S g₁ ts addr
  have hme₁_1 : MatchesEventsClassical interp r S g₁ (setupTrace r) ss₁ evs₁ vis₁ :=
    matchesEvents_of_gammaAgree hga_rev hme₁ hReach_setup hwf₁ hlen₁
  have htr₁' :=
    Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g' ts hReach₁ hlen₁
  have hvis₁' := matchesEvents_visStampsLt hme₁ hReach_setup hwf₁ hlen₁ htr₁'
  have ht' := cbadG2_stampsLt_getMessageSentAt_of_entries htr₁' hsent
  have hcol_1 : RecvCollisionOn interp r S g₁ (runTrace r ss₁) vis₁ (honestSaltsOf r ss₁) t :=
    recvCollisionOn_of_gammaAgree hga_rev hReach₁ hlen₁ hvis₁' ht' hcol
  exact hnrc₁ ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, ⟨peer, hcmd⟩, hexit, hbody, hme₁_1, hdec, hsent, hcol_1⟩

/-! ## `Step.messageEncrypt` Faithfulness, `GhostWF`, and `stepView` -/

private theorem run_bind_pure_isSome {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).1.isSome = (x.run tr).1.isSome := by
  rcases hx : x.run tr with ⟨o, t, ht⟩
  cases o <;> simp [_root_.DY.Traceful.run_bind, _root_.DY.Traceful.run_pure, hx]

private def ValidLoadStep : Step → Prop
  | .network .. | .aliceStart .. | .bobStart ..
  | .messageEncrypt .. | .messageEncryptAbort ..
  | .messageDecrypt .. | .messageDecryptSkipped ..
  | .compromiseIK .. | .compromiseSPK .. | .compromisePQSPK .. | .compromiseOPK ..
  | .exposeKey .. | .exposeSpqr .. | .exposeSkipped .. => True
  | _ => False

private def stepToLoadMove : Step → Move
  | .network msg => .attackerSend msg
  | .aliceStart a b idIdx regIdx h => .aliceStart a b idIdx regIdx h 35
  | .bobStart b a kh regIdx mh pqIdx spqrIdx => .bobStart b a kh regIdx mh pqIdx spqrIdx 3
  | .messageEncrypt me stateIdx coinsLen pqIdx => .encrypt me stateIdx coinsLen pqIdx none
  | .messageEncryptAbort me stateIdx => .encryptAbort me stateIdx
  | .messageDecrypt me stateIdx msgIdx pqIdx spqrIdx => .decrypt me stateIdx msgIdx pqIdx spqrIdx false
  | .messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrIdx =>
      .decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrIdx false
  | .compromiseIK p idx => .compromiseIK p idx
  | .compromiseSPK b idx => .compromiseSPK b idx
  | .compromisePQSPK b idx => .compromisePQSPK b idx
  | .compromiseOPK b idx => .compromiseOPK b idx
  | .exposeKey me idx k => .exposeKey me idx k
  | .exposeSpqr me idx => .exposeSpqr me idx
  | .exposeSkipped idx => .exposeSkipped idx
  | _ => .reject []

private theorem validLoadStep_of_matchesEvents {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hme : MatchesEventsClassicalAt interp r S g initIds tr ss evs vis) :
    ∀ x ∈ ss, ValidLoadStep x := by
  induction hme with
  | nil hinv =>
    intro x hx; have hx' := hinv x hx; cases x <;> simp [Step.cls, ValidLoadStep] at hx' ⊢
  | run0 hpre _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hxp | hxs
    · have hc := hpre x hxp; cases x <;> simp [Step.cls, ValidLoadStep] at hc ⊢
    · exact ih x hxs
  | @env _ _ _ s _ ev _ _ _ hpre hem _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hxp | hx'
    · have hc := hpre x hxp; cases x <;> simp [Step.cls, ValidLoadStep] at hc ⊢
    · rcases List.mem_cons.mp hx' with rfl | hxs
      · cases ev with
        | leak p k =>
          rcases hem with ⟨_, hleak, _⟩
          cases x <;> simp [Step.IsLeak, ValidLoadStep] at hleak ⊢
        | breakDH | breakKEM | invertDH _ | invertKEM _ | registerCorrupt _ _ => cases hem
      · exact ih x hxs
  | run1 hpre hrm _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hxp | hx'
    · have hc := hpre x hxp; cases x <;> simp [Step.cls, ValidLoadStep] at hc ⊢
    · rcases List.mem_cons.mp hx' with rfl | hxs
      · have hc := hrm.1; cases x <;> simp [Step.cls, ValidLoadStep] at hc ⊢
      · exact ih x hxs

private theorem stepToLoadMove_next {s : Step} (hv : ValidLoadStep s) (tr : ExecTrace) :
    (stepToLoadMove s).next tr = s.next tr := by
  cases s <;> first | exact Symbolic.Swarm.CREF.SendWire.run_bind_pure_val _ tr | rfl | cases hv

private theorem stepToLoadMove_stateLoad {s : Step} (_hv : ValidLoadStep s) :
    (stepToLoadMove s).stateLoad? = s.stateLoad? := by
  cases s <;> rfl

private theorem stepToLoadMove_ok {s : Step} (hv : ValidLoadStep s) (tr : ExecTrace) :
    ((stepToLoadMove s).act.run tr).1.isSome = s.ok tr := by
  cases s <;> first | exact run_bind_pure_isSome _ tr | rfl | cases hv

private theorem runMoves_map_stepToLoadMove :
    ∀ (ss : List Step) (tr : ExecTrace), (∀ x ∈ ss, ValidLoadStep x) →
      (runMoves (ss.map stepToLoadMove) tr).1 = runSteps ss tr
  | [], _, _ => rfl
  | s :: ss, tr, hv => by
    have hvs : ValidLoadStep s := hv s (List.mem_cons_self ..)
    simp only [List.map_cons, runMoves, runSteps, stepToLoadMove_next hvs tr]
    exact runMoves_map_stepToLoadMove ss (s.next tr) fun x hx => hv x (List.mem_cons_of_mem s hx)

private theorem runTraceMoves_map_stepToLoadMove (r : ProtocolSetup) {ss : List Step}
    (hv : ∀ x ∈ ss, ValidLoadStep x) :
    runTraceMoves r (ss.map stepToLoadMove) = runTrace r ss := by
  unfold runTraceMoves runTrace
  exact runMoves_map_stepToLoadMove ss (setupTrace r) hv

private theorem stepsStateFaithful_iff_map {r : ProtocolSetup} {ss : List Step}
    (hv : ∀ x ∈ ss, ValidLoadStep x) :
    StepsStateFaithful r ss ↔ StateFaithful r (ss.map stepToLoadMove) := by
  constructor
  · intro hsf i j mi mj p k b hij hi hj hmi hok hmj
    rw [List.getElem?_map] at hi hj
    rcases hsi : ss[i]? with _ | si <;> simp [hsi] at hi; subst hi
    rcases hsj : ss[j]? with _ | sj <;> simp [hsj] at hj; subst hj
    have hv_si : ValidLoadStep si := hv si (List.mem_of_getElem? hsi)
    have hv_sj : ValidLoadStep sj := hv sj (List.mem_of_getElem? hsj)
    rw [stepToLoadMove_stateLoad hv_si] at hmi
    rw [stepToLoadMove_stateLoad hv_sj] at hmj
    rw [← List.map_take, runTraceMoves_map_stepToLoadMove r
      (fun x hx => hv x (List.mem_of_mem_take hx)), stepToLoadMove_ok hv_si] at hok
    exact hsf i j si sj p k b hij hsi hsj hmi hok hmj
  · intro hsf i j si sj p k b hij hsi hsj hsi_ld hok hsj_ld
    have hv_si : ValidLoadStep si := hv si (List.mem_of_getElem? hsi)
    have hv_sj : ValidLoadStep sj := hv sj (List.mem_of_getElem? hsj)
    have hi : (ss.map stepToLoadMove)[i]? = some (stepToLoadMove si) := by
      rw [List.getElem?_map, hsi]; rfl
    have hj : (ss.map stepToLoadMove)[j]? = some (stepToLoadMove sj) := by
      rw [List.getElem?_map, hsj]; rfl
    have hmi : (stepToLoadMove si).stateLoad? = some (p, k, true) := by
      rwa [stepToLoadMove_stateLoad hv_si]
    have hmj : (stepToLoadMove sj).stateLoad? = some (p, k, b) := by
      rwa [stepToLoadMove_stateLoad hv_sj]
    have hok' :
        ((stepToLoadMove si).act.run (runTraceMoves r ((ss.map stepToLoadMove).take i))).1.isSome =
          true := by
      rwa [← List.map_take, runTraceMoves_map_stepToLoadMove r
        (fun x hx => hv x (List.mem_of_mem_take hx)), stepToLoadMove_ok hv_si]
    exact hsf i j _ _ p k b hij hi hj hmi hok' hmj

private theorem stepsStateFaithful_snoc_messageEncrypt {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    {me : Participant} {stateIdx coinsLen pqIdx : Nat}
    (hme : MatchesEventsClassical interp r S g (setupTrace r) ss evs vis)
    (hsf : StepsStateFaithful r ss)
    (hcur : isCurrentSnapshot (runTrace r ss) stateIdx = true) :
    StepsStateFaithful r (ss ++ [.messageEncrypt me stateIdx coinsLen pqIdx]) := by
  have hv_ss := validLoadStep_of_matchesEvents hme
  have hv_all : ∀ x ∈ ss ++ [.messageEncrypt me stateIdx coinsLen pqIdx], ValidLoadStep x := by
    intro x hx
    rcases List.mem_append.mp hx with hxs | hxe
    · exact hv_ss x hxs
    · simp only [List.mem_singleton] at hxe; subst hxe; trivial
  rw [stepsStateFaithful_iff_map hv_all, List.map_append, List.map_singleton]
  refine Symbolic.Swarm.CREF.Stage1Wire.stateFaithful_snoc_of_isCurrentSnapshot
    ((stepsStateFaithful_iff_map hv_ss).mp hsf) ?_
  intro p k b hld
  simp only [stepToLoadMove, Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hld
  rcases hld with ⟨_, rfl, _⟩
  rwa [runTraceMoves_map_stepToLoadMove r hv_ss]

private def RunsLoc {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private theorem RunsLoc.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} {b : β}
    (h1 : RunsLoc x tr a tr1) (h2 : RunsLoc (f a) tr1 b tr2) :
    RunsLoc (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [_root_.DY.Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem RunsLoc.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    RunsLoc (_root_.guard p : Traceful Unit) tr () tr := by
  show ((if p then pure () else failure : Traceful Unit).run tr).1 = some () ∧
    ((if p then pure () else failure : Traceful Unit).run tr).2.val = tr
  rw [ite_eq_left_iff.mpr fun hc => absurd h hc, _root_.DY.Traceful.run_pure]
  exact ⟨rfl, rfl⟩

private theorem RunsLoc.genRand (n : Nat) (tr : ExecTrace) :
    RunsLoc (_root_.DY.Random.genRand n : Traceful _root_.DY.Bytes) tr (randTerm tr.length n)
      (tr.append (⟨n⟩ : _root_.DY.Random.ExecEntryT)) := by
  unfold RunsLoc
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    _root_.DY.Traceful.run_bind, _root_.DY.Traceful.run_mk]
  dsimp only
  rw [_root_.DY.Traceful.run_pure]
  exact ⟨rfl, rfl⟩

private theorem RunsLoc.sendMessage (m : _root_.DY.Bytes) (tr : ExecTrace) :
    RunsLoc (_root_.DY.Network.sendMessage m : Traceful Nat) tr tr.length
      (tr.append (⟨m⟩ : _root_.DY.Network.ExecEntryT)) := by
  unfold RunsLoc
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_mk]
  exact ⟨rfl, rfl⟩

private theorem RunsLoc.receiveMessage {idx : Nat} {tr : ExecTrace} {m : _root_.DY.Bytes}
    (h : (tr.at? idx : Option _root_.DY.Network.ExecEntryT) = some ⟨m⟩) :
    RunsLoc (_root_.DY.Network.receiveMessage idx : Traceful _root_.DY.Bytes) tr m tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  constructor
  · rw [_root_.DY.Traceful.run_bind, _root_.DY.Traceful.run_mk, h]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
  · rw [_root_.DY.Traceful.run_bind, _root_.DY.Traceful.run_mk, h]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

private theorem RunsLoc.logEvent (ev : _root_.DY.Libsignal.TripleRatchet.TREvent) (tr : ExecTrace) :
    RunsLoc (_root_.DY.ProtocolEvent.logEvent ev : Traceful Unit) tr ()
      (tr.append (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.TripleRatchet.TREvent)) := by
  unfold RunsLoc
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_bind,
    _root_.DY.Traceful.run_mk]
  dsimp only
  rw [_root_.DY.Traceful.run_pure]
  exact ⟨rfl, rfl⟩

private theorem RunsLoc.storeLocalState (me : Participant) (st : TRState) (tr : ExecTrace) :
    RunsLoc (_root_.DY.PersistentLocalState.storeLocalState me st : Traceful Nat) tr tr.length
      (tr.append (⟨⟨me, st⟩⟩ : RoleStE)) := by
  unfold RunsLoc
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, _root_.DY.Traceful.run_mk]
  exact ⟨rfl, rfl⟩

private theorem RunsLoc.traceLength (tr : ExecTrace) :
    RunsLoc _root_.DY.Libsignal.TripleRatchet.traceLength tr tr.length tr := by
  unfold RunsLoc _root_.DY.Libsignal.TripleRatchet.traceLength
  rw [_root_.DY.Traceful.run_mk]
  exact ⟨rfl, rfl⟩

private theorem messageEncrypt_ok_of_some {me : Participant} {stateIdx coinsLen : Nat}
    {tr : ExecTrace} {st : TRState}
    (hst : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hns : st.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max) :
    (Step.messageEncrypt me stateIdx coinsLen (tr.length + 2)).ok tr = true := by
  have of_eq : ∀ {α : Type} {f : Traceful α} {tr₀ tr₁ tr₂ : ExecTrace} {v₁ v₂ : α},
      RunsLoc f tr₀ v₁ tr₁ → v₁ = v₂ → tr₁ = tr₂ → RunsLoc f tr₀ v₂ tr₂ := by
    rintro _ _ _ _ _ _ _ h rfl rfl; exact h
  have hlen : ∀ {α E : Type} [_root_.DY.TraceEntryHas E α] (t : _root_.DY.Trace α) (e : E),
      (t.append e).length = t.length + 1 := fun _ _ => by
    rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hkey :
      ((((tr.append (⟨32⟩ : _root_.DY.Random.ExecEntryT)).append
        (⟨coinsLen⟩ : _root_.DY.Random.ExecEntryT)).append
        (⟨(_root_.DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ :
          _root_.DY.Network.ExecEntryT)).at? (tr.length + 2) :
        Option _root_.DY.Network.ExecEntryT) =
      some ⟨(_root_.DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1⟩ :=
    Symbolic.Swarm.CREF.SendWire.at?_append_eq_some _ _ (by simp only [hlen])
  have hruns : RunsLoc (_root_.DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen
      (tr.length + 2)) tr (tr.length + 6)
      (Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st) := by
    unfold _root_.DY.Libsignal.TripleRatchet.messageEncrypt
      _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      Symbolic.Swarm.CREF.SendWire.encTr
      Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encSt
      Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg
      Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMac
      Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encWire
    dsimp only
    refine RunsLoc.bind ⟨hst, Symbolic.Swarm.CREF.SendWire.getLocalState_run_eq_self me stateIdx tr⟩ ?_
    refine RunsLoc.bind (RunsLoc.guard tr hns) ?_
    refine RunsLoc.bind (RunsLoc.genRand 32 _) ?_
    refine RunsLoc.bind (of_eq (RunsLoc.genRand coinsLen _) (by simp only [hlen]; rfl) rfl) ?_
    refine RunsLoc.bind (RunsLoc.sendMessage _ _) ?_
    refine RunsLoc.bind (RunsLoc.receiveMessage hkey) ?_
    refine RunsLoc.bind (RunsLoc.logEvent _ _) ?_
    refine RunsLoc.bind (RunsLoc.bind (RunsLoc.logEvent _ _)
      (RunsLoc.storeLocalState _ _ _)) ?_
    exact of_eq (RunsLoc.sendMessage _ _) (by simp only [hlen]) rfl
  change ((_root_.DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen
      (tr.length + 2)).run tr).1.isSome = true
  rw [hruns.1]
  rfl

private theorem lastSent_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) :
    lastSent tr (Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st) =
      some (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st coinsLen tr.length) := by
  have hlt : tr.length < (Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st).length := by
    rw [Symbolic.Swarm.CREF.SendWire.encTr_length]; omega
  have hsub : (Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st).length - 1 =
      tr.length + 6 := by
    rw [Symbolic.Swarm.CREF.SendWire.encTr_length]; omega
  have hm :
      ((Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st).at? (tr.length + 6) :
        Option _root_.DY.Network.ExecEntryT) =
      some ⟨Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st coinsLen tr.length⟩ :=
    Symbolic.Swarm.CREF.SendWire.at?_append_eq_some _ _
      (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
  (unfold lastSent; simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1])
  rw [ite_eq_left_iff.mpr fun h => absurd hlt h, hsub, hm]

private theorem stepView_messageEncrypt_whisper {me : Participant} {stateIdx coinsLen : Nat}
    {tr : ExecTrace} {st : TRState}
    (hst : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hns : st.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max)
    (hppk : pendingPreKey tr stateIdx = none) :
    stepView (.messageEncrypt me stateIdx coinsLen (tr.length + 2)) tr false =
      (⟨.pt, [randTerm tr.length 32], .single, none⟩ : VisEntry) ::
        ((if coinsLen = 0 then [] else [rngEntry (randTerm (tr.length + 1) coinsLen)]) ++
          [⟨.send, [Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st coinsLen tr.length],
            .whisper, none⟩]) := by
  have hok := messageEncrypt_ok_of_some (coinsLen := coinsLen) hst hns
  have hnext : (Step.messageEncrypt me stateIdx coinsLen (tr.length + 2)).next tr =
      Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st :=
    (stepToLoadMove_next (s := .messageEncrypt me stateIdx coinsLen (tr.length + 2)) trivial tr).symm.trans
      (Symbolic.Swarm.CREF.SendWire.encrypt_next_of_some hst hns)
  dsimp only [stepView]
  rw [hok, ite_eq_left_iff.mpr fun h => absurd rfl h, hnext,
    Symbolic.Swarm.CREF.SendWire.exposures_encTr, List.append_nil,
    Symbolic.Swarm.CREF.SendWire.newRandoms_encTr]
  unfold encSendEntry
  rw [lastSent_encTr, hppk]
  by_cases hc : coinsLen = 0 <;> simp [encDraws, hc, rngEntry]

private theorem stepView_messageEncrypt_pending {me : Participant} {stateIdx coinsLen : Nat}
    {tr : ExecTrace} {st : TRState} {ek ct : _root_.DY.Bytes}
    (hst : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hns : st.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max)
    (hppk : pendingPreKey tr stateIdx = some (ek, ct)) :
    stepView (.messageEncrypt me stateIdx coinsLen (tr.length + 2)) tr true =
      (⟨.pt, [randTerm tr.length 32], .single, none⟩ : VisEntry) ::
        ((if coinsLen = 0 then [] else [rngEntry (randTerm (tr.length + 1) coinsLen)]) ++
          [⟨.send,
            [ek, ct, Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st coinsLen tr.length],
            .preKeySend, none⟩]) := by
  have hok := messageEncrypt_ok_of_some (coinsLen := coinsLen) hst hns
  have hnext : (Step.messageEncrypt me stateIdx coinsLen (tr.length + 2)).next tr =
      Symbolic.Swarm.CREF.SendWire.encTr tr me stateIdx coinsLen st :=
    (stepToLoadMove_next (s := .messageEncrypt me stateIdx coinsLen (tr.length + 2)) trivial tr).symm.trans
      (Symbolic.Swarm.CREF.SendWire.encrypt_next_of_some hst hns)
  dsimp only [stepView]
  rw [hok, ite_eq_left_iff.mpr fun h => absurd rfl h, hnext,
    Symbolic.Swarm.CREF.SendWire.exposures_encTr, List.append_nil,
    Symbolic.Swarm.CREF.SendWire.newRandoms_encTr]
  unfold encSendEntry
  rw [lastSent_encTr, hppk]
  by_cases hc : coinsLen = 0 <;> simp [encDraws, hc, rngEntry]

private theorem parseTrSignalMsg_encMsg_wire {st : TRState} {coinsLen ts : Nat}
    {pm : _root_.DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hpm : parseTrSignalMsg (Symbolic.Swarm.CREF.SendWire.encMsg st coinsLen ts) = some pm) :
    pm.wire = Symbolic.Swarm.CREF.SendWire.encWire st coinsLen ts := by
  unfold parseTrSignalMsg Symbolic.Swarm.CREF.SendWire.encMsg at hpm
  dsimp only [_root_.DY.Concat.CanConcat.split, _root_.DY.Concat.CanConcat.concat] at hpm
  rw [_root_.DY.BytesView.view_pack] at hpm
  dsimp only at hpm
  split at hpm
  · simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hpm
    obtain ⟨w, hw, _, _, hpm_eq⟩ := hpm
    subst hw
    subst hpm_eq
    rfl
  · cases hpm

private theorem ghostWF_snoc_enc {g₀ : Ghost} {ts : Nat} {pt coins addr : HwBytes}
    {vis₀ : List VisEntry} {v_send : VisEntry}
    (hgwf₀ : GhostWF
      (Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g₀ ts pt coins) ts addr) vis₀)
    (hv_send :
      (v_send.layout = .preKeySend →
        ∀ (ek ct msg : _root_.DY.Bytes) pm,
          v_send.terms = [ek, ct, msg] → parseTrSignalMsg msg = some pm →
          (Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g₀ ts pt coins) ts addr).addr pm.wire =
            serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩) ∧
      (v_send.layout = .whisper →
        ∀ (msg : _root_.DY.Bytes) pm,
          v_send.terms = [msg] → parseTrSignalMsg msg = some pm →
          (Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g₀ ts pt coins) ts addr).addr pm.wire =
            []))
    (hs_kind : v_send.kind = .send) :
    GhostWF
      (Symbolic.Swarm.CREF.SendWire.setSendAddr (sendSigGhost g₀ ts pt coins) ts addr)
      (vis₀ ++ ((⟨.pt, [randTerm ts 32], .single, none⟩ : VisEntry) ::
        ((if coins.length = 0 then [] else [rngEntry (randTerm (ts + 1) coins.length)]) ++
          [v_send]))) := by
  refine ⟨?_, hgwf₀.2.1, ?_⟩
  · intro v hv hk ts' n' hn' hmem
    rcases List.mem_append.mp hv with hv₀ | hv₁
    · exact hgwf₀.1 v hv₀ hk ts' n' hn' hmem
    · rcases List.mem_cons.mp hv₁ with rfl | hv₂
      · cases hk
      · rcases List.mem_append.mp hv₂ with hvd | hvs
        · by_cases hc : coins.length = 0
          · simp [hc] at hvd
          · simp only [hc, ↓reduceIte, List.mem_singleton] at hvd
            subst hvd
            simp only [rngEntry, List.mem_singleton] at hmem
            obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem
            simp [Symbolic.Swarm.CREF.SendWire.setSendAddr, sendSigGhost,
              Symbolic.Swarm.CREF.TR.FreshSigma.updateFreshAt_self]
        · simp only [List.mem_singleton] at hvs
          subst hvs
          rw [hs_kind] at hk
          cases hk
  · intro v hv hk
    rcases List.mem_append.mp hv with hv₀ | hv₁
    · exact hgwf₀.2.2 v hv₀ hk
    · rcases List.mem_cons.mp hv₁ with rfl | hv₂
      · cases hk
      · rcases List.mem_append.mp hv₂ with hvd | hvs
        · by_cases hc : coins.length = 0
          · simp [hc] at hvd
          · simp only [hc, ↓reduceIte, List.mem_singleton] at hvd
            subst hvd
            cases hk
        · simp only [List.mem_singleton] at hvs
          subst hvs
          exact hv_send

private theorem drawsMatch_enc {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g' : Ghost} {ts : Nat} {coins ev_coins : HwBytes}
    (hpref : coins <+: ev_coins)
    (hgamma : coins.length ≠ 0 → gamma interp S g' (randTerm (ts + 1) coins.length) = coins) :
    DrawsMatch interp r S g'
      (if coins.length = 0 then [] else [rngEntry (randTerm (ts + 1) coins.length)])
      ev_coins := by
  by_cases hc : coins = []
  · subst hc
    simp only [List.length_nil, ↓reduceIte]
    exact ⟨[], by simp, List.nil_prefix, .nil⟩
  · have hcl : coins.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    simp only [hcl, ↓reduceIte]
    refine ⟨[coins], by simp [hc], by simpa using hpref, .cons ⟨rfl, ?_⟩ .nil⟩
    dsimp only [rngEntry]
    simp [hgamma hcl]

/-! ## Step-Extension and `StampsLt` Theorems -/

private theorem eventLoggedAt_of_getEventAt_pq {tr : ExecTrace} {idx : Nat} {ev : PQXDHEvent}
    (h : tr.getEventAt PQXDHEvent idx = some ev) :
    (tr.at? idx : Option (_root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = some ⟨ev⟩ := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
  rcases hat : (tr.at? idx : Option (_root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with _ | e
  · simp [hat] at h
  · simp only [hat, Option.some.injEq] at h
    rcases e with ⟨ev'⟩
    subst h
    rfl

/-- `StampsLt` bound for `pendingPreKey` items `(ek, ct)` on a reachable trace `tr` with
`tr.length ≤ ts`. -/
theorem pendingPreKey_stampsLt_send {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr : ExecTrace} (hReach : tr.Reachable reachability) (hlen : tr.length ≤ ts)
    {stateIdx : Nat} {ek ct : _root_.DY.Bytes} (h : pendingPreKey tr stateIdx = some (ek, ct)) :
    Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g ts ek ∧
    Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp S g ts ct := by
  have htr :=
    Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp S g ts hReach hlen
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at h
  rcases hls : (tr.at? stateIdx : Option RoleStE) with _ | e
  · simp [hls] at h
  · simp only [hls, Option.map_some] at h
    by_cases hdec : sessionHasDecrypted tr (e.st.state.sessionInfo e.st.participant) stateIdx
    · simp [hdec] at h
    · simp only [hdec, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨pqev₀, hpq_mem, hi⟩ := List.exists_of_findSome?_eq_some h
      obtain ⟨i, _, hce_get⟩ := List.mem_filterMap.mp hpq_mem
      rcases hce : (tr.getEventAt ComposedEvent i) with _ | cev
      · simp [hce] at hce_get
      · simp only [hce] at hce_get
        cases cev with
        | HandshakeSession s d =>
          by_cases hs : s = e.st.state.sessionInfo e.st.participant
          · simp only [hs, ↓reduceIte] at hce_get
            rcases hpq : (tr.getEventAt PQXDHEvent d) with _ | pqev
            · simp [hpq] at hce_get
            · simp only [hpq, Option.some.injEq] at hce_get
              subst pqev₀
              cases pqev with
              | AliceDone a b ikA ikB spk pqpk opk ek' ct' keys =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hi
                rcases hi with ⟨rfl, rfl⟩
                have hLog := eventLoggedAt_of_getEventAt_pq hpq
                obtain ⟨t, _, rfl, hSlot, _⟩ :=
                  (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr hReach).aliceDone
                    a b ikA ikB spk pqpk opk ek' ct' keys d
                    ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ d tr).mpr hLog)
                obtain ⟨_, _, _, a', b', ikA', ikB', spk', pqpk', opk', ek'', ct'', keys',
                  hNetEk, hNetCt, hLog'⟩ := hSlot
                have hEq : (some ⟨.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek'' ct'' keys'⟩ :
                    Option (_root_.DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
                    some ⟨.AliceDone a b ikA ikB spk pqpk opk ek' ct' keys⟩ :=
                  ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ (t + 5) tr).mp hLog').symm.trans hLog
                injection hEq with hEntry
                injection hEntry with hEvEq
                injection hEvEq with _ _ _ _ _ _ _ hEk hCt _
                subst hEk; subst hCt
                exact ⟨Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr
                    (Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt.attackerKnows hNetEk),
                  Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_knows htr
                    (Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt.attackerKnows hNetCt)⟩
              | _ => cases hi
          · simp [hs] at hce_get

/-- Appending a `send` run event without extending `ss₀` preserves `¬ ReadCollisionCliClassical`. -/
theorem not_readCollisionCli_snoc_send_rejected {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g₀ : Ghost} {ss₀ : List Step} {evs_pre : List CliEvent} {ev₀ : RunEvent}
    {peer : Address} (hcmd₀ : ev₀.cmd = .send peer)
    (hnrc₀ : ¬ ReadCollisionCliClassical interp r S g₀ ss₀ evs_pre) :
    ¬ ReadCollisionCliClassical interp r S g₀ ss₀ (evs_pre ++ [.run ev₀]) := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, ⟨peer', hcmd⟩, hexit, hbody, hme₁, hdec, hsent, hcol⟩
  have hlen_tot : evs_pre.length + 1 = evs₁.length + 1 + evs₂.length := by
    have h := congrArg List.length hevs
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  by_cases heq : evs₁.length = evs_pre.length
  · have hget := congrArg (·[evs₁.length]?) hevs
    rw [heq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, ← heq,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hget
    simp only [List.getElem?_cons_zero, Option.some.injEq, CliEvent.run.injEq] at hget
    rw [← hget, hcmd₀] at hcmd
    cases hcmd
  · have hlt : evs₁.length < evs_pre.length := by omega
    obtain ⟨k, hk⟩ : ∃ k, evs_pre.length - evs₁.length = k + 1 :=
      ⟨evs_pre.length - evs₁.length - 1, by omega⟩
    have hevs₀ : evs_pre = evs₁ ++ .run ev :: evs₂.take k := by
      have htake := congrArg (List.take evs_pre.length) hevs
      rw [List.take_left, List.take_append,
        List.take_of_length_le (Nat.le_of_lt hlt), hk, List.take_succ_cons] at htake
      exact htake
    exact hnrc₀ ⟨evs₁, ev, evs₂.take k, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
      hevs₀, hss, ⟨peer', hcmd⟩, hexit, hbody, hme₁, hdec, hsent, hcol⟩

/-- Step-level clean-explanation extension for an exit-`0` Whisper `send` run. -/
theorem explains_and_clean_snoc_whisper {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {evs_pre : List CliEvent}
    {ev : RunEvent} {p : Participant} {peer : Address} {out coins : HwBytes}
    {stateIdx₀ : Nat} {st₀ : TRState}
    (hwf : ProtocolSetupWF r) (hReady : SemReady interp' r S)
    (hex₀ : ExplainsClassical interp' r S g₀ ss₀ vis₀ evs_pre)
    (hnrc₀ : ¬ ReadCollisionCliClassical interp' r S g₀ ss₀ evs_pre)
    (hp_ev : ev.party = p)
    (hcmd_ev : ev.cmd = .send peer)
    (hexit_ev : ev.exit = some (0, out))
    (hst₀ : ((_root_.DY.PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run
      (runTrace r ss₀)).1 = some st₀)
    (hcur₀ : isCurrentSnapshot (runTrace r ss₀) stateIdx₀ = true)
    (hns₀ : st₀.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max)
    (hppk₀ : pendingPreKey (runTrace r ss₀) stateIdx₀ = none)
    (hpref : coins <+: ev.coins)
    (hcoins_len : coins.length = 0 ∨ coins.length = 32 ∨ coins.length = 64)
    (hout : out = wireWhisperTag :: gamma interp' S
      (Symbolic.Swarm.CREF.SendWire.sendGhost g₀ (runTrace r ss₀).length ev.input coins)
      (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st₀ coins.length
        (runTrace r ss₀).length)) :
    ∃ g' ss' vis',
      ExplainsClassical interp' r S g' ss' vis' (evs_pre ++ [.run ev]) ∧
      ¬ ReadCollisionCliClassical interp' r S g' ss' (evs_pre ++ [.run ev]) := by
  let ts := (runTrace r ss₀).length
  let g' := Symbolic.Swarm.CREF.SendWire.sendGhost g₀ ts ev.input coins
  have hg'_eq : g' = Symbolic.Swarm.CREF.SendWire.setSendAddr
      (sendSigGhost g₀ ts ev.input coins) ts [] :=
    sendGhost_eq_setSendAddr g₀ ts ev.input coins
  have hex_pre : ExplainsClassical interp' r S g' ss₀ vis₀ evs_pre := by
    rw [hg'_eq]
    exact explains_prefix_setSendAddr hwf.1 hReady ev.input coins [] (Or.inl rfl) hex₀
  let s : Step := .messageEncrypt p stateIdx₀ coins.length (ts + 2)
  let v_inp : VisEntry := ⟨.pt, [randTerm ts 32], .single, none⟩
  let drs : List VisEntry :=
    if coins.length = 0 then [] else [rngEntry (randTerm (ts + 1) coins.length)]
  let v_send : VisEntry :=
    ⟨.send, [Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st₀ coins.length ts],
      .whisper, none⟩
  let v : List VisEntry := v_inp :: (drs ++ [v_send])
  have hgwf' : GhostWF g' (vis₀ ++ v) := by
    rw [hg'_eq]
    refine ghostWF_snoc_enc (hg'_eq ▸ hex_pre.2.1)
      ⟨(fun h => nomatch h), fun _ msg pm hterms hpm => ?_⟩ rfl
    simp only [v_send, List.cons.injEq, and_true] at hterms
    subst hterms
    rw [parseTrSignalMsg_encMsg_wire hpm, ← hg'_eq]
    exact Symbolic.Swarm.CREF.SendWire.sendGhost_addr_encWire g₀ st₀ coins.length ts ev.input coins
  have hwf_steps : StepsWF (ss₀ ++ [s]) (setupTrace r) :=
    (stepsWF_append_iff ss₀ [s] (setupTrace r)).mpr
      ⟨hex₀.2.2.1.2.2.1, hcur₀, ⟨hcoins_len, Or.inl rfl⟩, trivial⟩
  have hsf' : StepsStateFaithful r (ss₀ ++ [s]) :=
    stepsStateFaithful_snoc_messageEncrypt hex₀.2.2.2 hex₀.2.2.1.2.2.2 hcur₀
  have hmrwf' : ModelRunWF r (ss₀ ++ [s]) :=
    ⟨hex₀.2.2.1.1, hex₀.2.2.1.2.1, hwf_steps, hsf'⟩
  have hrw : runWrapped ev = false := by
    unfold runWrapped
    rw [hcmd_ev, hexit_ev, hout]
    rfl
  have hv_eq : v = stepView s (runTrace r ss₀) (runWrapped ev) := by
    rw [hrw]
    exact (stepView_messageEncrypt_whisper (coinsLen := coins.length) hst₀ hns₀ hppk₀).symm
  have hinp_bme : BytesMatchEntry interp' r S g' (inputKind ev) ev.input v_inp := by
    refine ⟨by simp [inputKind, hcmd_ev, v_inp], ?_⟩
    dsimp only [v_inp, List.map]
    exact congrArg (· :: [])
      (Symbolic.Swarm.CREF.SendWire.gamma_sendGhost_pt interp' S g₀ ts ev.input coins)
  have hdrs_bme : DrawsMatch interp' r S g' drs ev.coins :=
    drawsMatch_enc hpref fun hcl =>
      Symbolic.Swarm.CREF.SendWire.gamma_sendGhost_coins interp' S g₀ ts ev.input coins hcl
  have houts_bme : OutputsMatch interp' r S g' ev [v_send] (activeBundleIds evs_pre) := by
    unfold OutputsMatch
    rw [hexit_ev, hcmd_ev]
    exact ⟨v_send, rfl, rfl, _, rfl, hout⟩
  have hrm : RunMatches interp' r S g' (runTrace r ss₀) s ev v (activeBundleIds evs_pre) :=
    ⟨rfl, congrArg some hp_ev.symm, by rw [hcmd_ev]; trivial, trivial,
      messageEncrypt_ok_of_some hst₀ hns₀, ⟨out, hexit_ev⟩, hv_eq,
      v_inp, drs, [v_send], rfl, hinp_bme, hdrs_bme, houts_bme, trivial, fun _ _ => trivial⟩
  have hme' : MatchesEventsClassical interp' r S g' (setupTrace r) (ss₀ ++ [s]) (evs_pre ++ [.run ev])
      (vis₀ ++ v) := by
    simpa only [List.append_nil] using
      matchesEvents_snoc_run1 (pre := []) hex_pre.2.2.2 (fun _ h => nomatch h) hrm
  have hnrc' : ¬ ReadCollisionCliClassical interp' r S g' (ss₀ ++ [s]) (evs_pre ++ [.run ev]) := by
    rw [hg'_eq]
    exact not_readCollisionCli_snoc_setSendAddr ev.input coins [] hex₀.2.2.1
      (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl)
      (by rw [hcmd_ev]; intro _ _ h; cases h)
      hnrc₀
  exact ⟨g', ss₀ ++ [s], vis₀ ++ v, ⟨hex_pre.1, hgwf', hmrwf', hme'⟩, hnrc'⟩

/-- Step-level clean-explanation extension for an exit-`0` pending-pre-key `send` run. -/
theorem explains_and_clean_snoc_pending {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {evs_pre : List CliEvent}
    {ev : RunEvent} {p : Participant} {peer : Address} {out coins : HwBytes}
    {stateIdx₀ : Nat} {st₀ : TRState} {ek ct : _root_.DY.Bytes}
    (hwf : ProtocolSetupWF r) (hReady : SemReady interp' r S)
    (hex₀ : ExplainsClassical interp' r S g₀ ss₀ vis₀ evs_pre)
    (hnrc₀ : ¬ ReadCollisionCliClassical interp' r S g₀ ss₀ evs_pre)
    (hp_ev : ev.party = p)
    (hcmd_ev : ev.cmd = .send peer)
    (hexit_ev : ev.exit = some (0, out))
    (hst₀ : ((_root_.DY.PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run
      (runTrace r ss₀)).1 = some st₀)
    (hcur₀ : isCurrentSnapshot (runTrace r ss₀) stateIdx₀ = true)
    (hns₀ : st₀.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max)
    (hppk₀ : pendingPreKey (runTrace r ss₀) stateIdx₀ = some (ek, ct))
    (hpref : coins <+: ev.coins)
    (hcoins_len : coins.length = 0 ∨ coins.length = 32 ∨ coins.length = 64)
    (hsend : SendMatches interp' r S
      (Symbolic.Swarm.CREF.SendWire.sendPendingGhost g₀ (runTrace r ss₀).length ev.input coins)
      (activeBundleIds evs_pre)
      out
      [ek, ct,
        Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st₀ coins.length
          (runTrace r ss₀).length]) :
    ∃ g' ss' vis',
      ExplainsClassical interp' r S g' ss' vis' (evs_pre ++ [.run ev]) ∧
      ¬ ReadCollisionCliClassical interp' r S g' ss' (evs_pre ++ [.run ev]) := by
  let ts := (runTrace r ss₀).length
  let g' := Symbolic.Swarm.CREF.SendWire.sendPendingGhost g₀ ts ev.input coins
  have hg'_eq : g' = Symbolic.Swarm.CREF.SendWire.setSendAddr
      (sendSigGhost g₀ ts ev.input coins) ts
      Symbolic.Swarm.CREF.SendWire.pqHarnessAddrBytes :=
    sendPendingGhost_eq_setSendAddr g₀ ts ev.input coins
  have haddr_eq : Symbolic.Swarm.CREF.SendWire.pqHarnessAddrBytes =
      serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ := by
    have ha : aliceUuid.toList = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b".toList := rfl
    have hb : bobUuid.toList = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6".toList := rfl
    unfold serializeAddresses _root_.DY.Libsignal.Composed.Refinement.Cli.serializeAddress
      _root_.DY.Libsignal.Composed.Refinement.Cli.parseUuidBytes
    dsimp only
    rw [ha, hb]
    simp only [String.toList]
    decide +kernel
  have hex_pre : ExplainsClassical interp' r S g' ss₀ vis₀ evs_pre := by
    rw [hg'_eq]
    exact explains_prefix_setSendAddr hwf.1 hReady ev.input coins
      Symbolic.Swarm.CREF.SendWire.pqHarnessAddrBytes (Or.inr haddr_eq) hex₀
  let s : Step := .messageEncrypt p stateIdx₀ coins.length (ts + 2)
  let v_inp : VisEntry := ⟨.pt, [randTerm ts 32], .single, none⟩
  let drs : List VisEntry :=
    if coins.length = 0 then [] else [rngEntry (randTerm (ts + 1) coins.length)]
  let v_send : VisEntry :=
    ⟨.send,
      [ek, ct, Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st₀ coins.length ts],
      .preKeySend, none⟩
  let v : List VisEntry := v_inp :: (drs ++ [v_send])
  have hgwf' : GhostWF g' (vis₀ ++ v) := by
    rw [hg'_eq]
    refine ghostWF_snoc_enc (hg'_eq ▸ hex_pre.2.1)
      ⟨fun _ ek' ct' msg pm hterms hpm => ?_, (fun h => nomatch h)⟩ rfl
    simp only [v_send, List.cons.injEq, and_true] at hterms
    rcases hterms with ⟨_, _, rfl⟩
    rw [parseTrSignalMsg_encMsg_wire hpm, ← hg'_eq]
    exact (Symbolic.Swarm.CREF.SendWire.sendPendingGhost_addr_encWire
      g₀ st₀ coins.length ts ev.input coins).trans haddr_eq
  have hwf_steps : StepsWF (ss₀ ++ [s]) (setupTrace r) :=
    (stepsWF_append_iff ss₀ [s] (setupTrace r)).mpr
      ⟨hex₀.2.2.1.2.2.1, hcur₀, ⟨hcoins_len, Or.inl rfl⟩, trivial⟩
  have hsf' : StepsStateFaithful r (ss₀ ++ [s]) :=
    stepsStateFaithful_snoc_messageEncrypt hex₀.2.2.2 hex₀.2.2.1.2.2.2 hcur₀
  have hmrwf' : ModelRunWF r (ss₀ ++ [s]) :=
    ⟨hex₀.2.2.1.1, hex₀.2.2.1.2.1, hwf_steps, hsf'⟩
  have hrw : runWrapped ev = true := by
    obtain ⟨preKeyId, spkId, kpkId, _, hout⟩ := hsend
    unfold runWrapped
    rw [hcmd_ev, hexit_ev, hout]
    rfl
  have hv_eq : v = stepView s (runTrace r ss₀) (runWrapped ev) := by
    rw [hrw]
    exact (stepView_messageEncrypt_pending (coinsLen := coins.length) hst₀ hns₀ hppk₀).symm
  have hinp_bme : BytesMatchEntry interp' r S g' (inputKind ev) ev.input v_inp := by
    refine ⟨by simp [inputKind, hcmd_ev, v_inp], ?_⟩
    dsimp only [v_inp, List.map]
    exact congrArg (· :: [])
      (Symbolic.Swarm.CREF.SendWire.gamma_sendPendingGhost_pt interp' S g₀ ts ev.input coins)
  have hdrs_bme : DrawsMatch interp' r S g' drs ev.coins :=
    drawsMatch_enc hpref fun hcl =>
      Symbolic.Swarm.CREF.SendWire.gamma_sendPendingGhost_coins interp' S g₀ ts ev.input coins hcl
  have houts_bme : OutputsMatch interp' r S g' ev [v_send] (activeBundleIds evs_pre) := by
    unfold OutputsMatch
    rw [hexit_ev, hcmd_ev]
    exact ⟨v_send, rfl, rfl, hsend⟩
  have hrm : RunMatches interp' r S g' (runTrace r ss₀) s ev v (activeBundleIds evs_pre) :=
    ⟨rfl, congrArg some hp_ev.symm, by rw [hcmd_ev]; trivial, trivial,
      messageEncrypt_ok_of_some hst₀ hns₀, ⟨out, hexit_ev⟩, hv_eq,
      v_inp, drs, [v_send], rfl, hinp_bme, hdrs_bme, houts_bme, trivial, fun _ _ => trivial⟩
  have hme' : MatchesEventsClassical interp' r S g' (setupTrace r) (ss₀ ++ [s]) (evs_pre ++ [.run ev])
      (vis₀ ++ v) := by
    simpa only [List.append_nil] using
      matchesEvents_snoc_run1 (pre := []) hex_pre.2.2.2 (fun _ h => nomatch h) hrm
  have hnrc' : ¬ ReadCollisionCliClassical interp' r S g' (ss₀ ++ [s]) (evs_pre ++ [.run ev]) := by
    rw [hg'_eq]
    exact not_readCollisionCli_snoc_setSendAddr ev.input coins
      Symbolic.Swarm.CREF.SendWire.pqHarnessAddrBytes hex₀.2.2.1
      (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl)
      (by rw [hcmd_ev]; intro _ _ h; cases h)
      hnrc₀
  exact ⟨g', ss₀ ++ [s], vis₀ ++ v, ⟨hex_pre.1, hgwf', hmrwf', hme'⟩, hnrc'⟩

end Symbolic.Proofs.Swarm.UA.SendTransfer
