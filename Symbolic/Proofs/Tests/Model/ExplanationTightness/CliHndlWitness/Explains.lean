/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Witness
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.EquationalTheory.DiffieHellman
import DY.Trace.Basic
import DY.Actions.Network
import DY.Actions.ProtocolEvent
public import Symbolic.Specifications.Security.Model
import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Symbolic Model Explanation for `cli_hndl_witness`

Executes the 3-step symbolic model trace `[aliceStart, breakDH, invertDH 2]` over the concrete
machine-free witness in `Witness.lean` and proves `Explains`, `BrokenDH`, `AliceDone` at index 27,
and `HNDLPremise`, assembling `cli_hndl_witness_aux`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Explains

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E (PEParams initiateTapeLen)
open CryptoVerification.SignalSession (publicBundleOf)
open DY (ExecTrace)
open DY.Comparse
open DY.Libsignal.HwEvents (EnvEvent CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent BundleHandles AliceHandshakeOut HNDLPremise brokenDHB anyEventOnTrace)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost ProtocolSetupWF Step VisEntry GhostWF ModelRunWF
  StepsStateFaithful BytesMatchEntry RunMatches EnvMatches nextBundleIds MatchesEventsAt MatchesEvents Explains
  runWrapped stepView aliceVis rngEntry kyberCoinEntries invertEntry lastSent runSteps runTrace
  setupTrace setupPublic gamma randTerm received eventIdx isAliceDone exposures newRandoms stepIn le32 leBytes)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli ModelAgree CliTraces PqModelRel
  CliTurn initDirs InvertsGuarded runInput runEventOf bundleBlob)
open Symbolic.Swarm.COMPOSED.CompTrace (at?_le_some eventLoggedAt_mono eventLogged_mono
  eventLogged_here eventLoggedAt_append_same eventLoggedAt_append_other
  eventLogged_append_same_iff eventLogged_append_other_iff)
open Symbolic.Swarm.CREF.Cli.Slots (initiateDrawsOfCoins initiateDrawsOfCoins_lengths
  initiateDrawsOfCoins_nonempty initiateDrawsOfCoins_flatten initiateDrawsOfCoins_getD_0
  initiateDrawsOfCoins_getD_33 entropyBytes_initiateDrawsOfCoins bundleBlob_publicBundleOf_length)
open Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Witness (hndlInterp
  hndlInterp_contracts hndlP hndlP_modelAgree hndlFresh_length hndlSem hndlGhost hndlRecords
  hndlRecords_ne hndlRecords_wf hndlCompat hndlBundleB hndlTape hndlBundleB_honest hndlCall
  hndlCall_runInput hndlSkA hndlPkA hndlInitEv hndlEvs hndl_cliTraces hndl_invertsGuarded
  hndl_has_invertDH)

def hndlBh : BundleHandles :=
  { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := none }

def hndlStepInit : Step :=
  .aliceStart hndlRecords.alice hndlRecords.bob 4 6 hndlBh

def hndlSteps : List Step :=
  [hndlStepInit, .breakDH, .invertDH 2]

def hndlAliceOut : AliceHandshakeOut :=
  Symbolic.Swarm.CREF.iniAliceOut (setupTrace hndlRecords)
    (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32))
    (DY.DiffieHellman.dhPk (randTerm 10 32)) (DY.PQKem.kemPk (randTerm 16 64)) none

def hndlTr1 : ExecTrace :=
  Symbolic.Swarm.CREF.iniAliceStartTr (setupTrace hndlRecords)
    hndlRecords.alice hndlRecords.bob hndlAliceOut

def hndlTr2 : ExecTrace :=
  hndlTr1.append (⟨PQXDHEvent.BrokenDH⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)

def hndlTr3 : ExecTrace :=
  hndlTr2.append (⟨randTerm 0 32⟩ : DY.Network.ExecEntryT)

def hndlInpVis : VisEntry :=
  ⟨.recv,
   [setupPublic hndlRecords 4, setupPublic hndlRecords 5,
    setupPublic hndlRecords 6, setupPublic hndlRecords 7],
   .bundle, none⟩

def hndlDrsVis : List VisEntry :=
  rngEntry (randTerm 22 32) :: kyberCoinEntries (randTerm 23 32) ++
    [{ rngEntry (randTerm 24 32) with anchor := some 27 }]

def hndlLeakVis : VisEntry :=
  ⟨.leak, [randTerm 0 32], .leakRecord, none⟩

def hndlVis : List VisEntry :=
  (hndlInpVis :: hndlDrsVis) ++ [hndlLeakVis]

private theorem stepIn_next (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (i.pf_step x).symm

private theorem stepIn_isSome (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (i.pf_step x).symm

private theorem view_variant_dhPk (sk : DY.Bytes) :
    (DY.DiffieHellman.dhPk sk).view? DY.X25519.Variant.SubF = none := by
  simp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
    ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)

private theorem dhSkOf_x25519Key_dhPk (sk : DY.Bytes) :
    DY.Libsignal.PQXDH.extractDhSecretKey (DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk sk)) = some sk := by
  unfold DY.X25519.normalizeX25519Key
  rw [view_variant_dhPk]
  simp only [DY.Libsignal.PQXDH.extractDhSecretKey, DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk,
    DY.BytesView.view_pack]

private theorem hndl_tr0_eq :
    setupTrace hndlRecords = Symbolic.Swarm.CREF.TR.setupTr4 "alice" "bob" := by
  rw [Symbolic.Swarm.CREF.TR.setupTrace_eq hndlRecords hndlRecords_ne]; rfl

private theorem hndl_tr0_len : (setupTrace hndlRecords).length = 22 := by
  rw [hndl_tr0_eq]
  simp [Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3,
    Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1,
    Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem hndl_tr0_at2 :
    ((setupTrace hndlRecords).at? 2 : Option DY.Network.ExecEntryT) =
      some ⟨DY.DiffieHellman.dhPk (randTerm 0 32)⟩ := by
  rw [hndl_tr0_eq]
  dsimp only [Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3,
    Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1]
  iterate 19 refine at?_le_some (DY.Trace.append_le _ _) ?_
  have hlen := DY.Trace.at?_append
    (((DY.Trace.nil : ExecTrace).append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)).append
      (Symbolic.Swarm.COMPOSED.CompTrace.PQEvE
        (.IdentityRegistered "alice" (DY.DiffieHellman.dhPk (randTerm 0 32))
          (DY.Signature.vk (randTerm 0 32)) true)))
    (⟨DY.DiffieHellman.dhPk (randTerm 0 32)⟩ : DY.Network.ExecEntryT)
  simpa [Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1] using hlen

private theorem hndl_le01 : setupTrace hndlRecords ≤ hndlTr1 := by
  dsimp only [hndlTr1, Symbolic.Swarm.CREF.iniAliceStartTr]
  iterate 9 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
  exact DY.Trace.le_refl _

private theorem hndlStepInit_exec :
    hndlStepInit.ok (setupTrace hndlRecords) = true ∧
    hndlStepInit.next (setupTrace hndlRecords) = hndlTr1 ∧
    stepView hndlStepInit (setupTrace hndlRecords) (runWrapped hndlInitEv) =
      hndlInpVis :: hndlDrsVis := by
  have h14 := Symbolic.Swarm.CREF.setupTrace_at?_14 hndlRecords hndlRecords_ne
  rw [Symbolic.Swarm.CREF.setupPublic_4 hndlRecords hndlRecords_ne] at h14
  have h15 := Symbolic.Swarm.CREF.setupTrace_at?_15 hndlRecords hndlRecords_ne
  rw [Symbolic.Swarm.CREF.setupPublic_5 hndlRecords hndlRecords_ne] at h15
  have h20 := Symbolic.Swarm.CREF.setupTrace_at?_20 hndlRecords hndlRecords_ne
  rw [Symbolic.Swarm.CREF.setupPublic_6 hndlRecords hndlRecords_ne] at h20
  have h21 := Symbolic.Swarm.CREF.setupTrace_at?_21 hndlRecords hndlRecords_ne
  rw [Symbolic.Swarm.CREF.setupPublic_7 hndlRecords hndlRecords_ne] at h21
  have hlow : DY.Libsignal.TripleRatchet.x25519LowOrder (DY.DiffieHellman.dhPk (randTerm 10 32)) = false := by
    have hv_lit : (DY.DiffieHellman.dhPk (randTerm 10 32)).view? DY.Literal.Literal.SubF = none := by
      simp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]
      exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
        ({ sk := randTerm 10 32 } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    simp only [DY.Libsignal.TripleRatchet.x25519LowOrder, DY.X25519.normalizeX25519Key,
      view_variant_dhPk, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have hruns := Symbolic.Swarm.CREF.Runs.aliceStart
    (h := hndlBh)
    (Symbolic.Swarm.CREF.setupTrace_at?_4 hndlRecords hndlRecords_ne)
    (Symbolic.Swarm.CREF.setupTrace_at?_6 hndlRecords hndlRecords_ne)
    h14 h15 h20 h21
    (DY.Signature.verify_sign _ _ _) (DY.Signature.verify_sign _ _ _)
    (hopk := trivial) (opk := none) hlow rfl
  have hok : hndlStepInit.ok (setupTrace hndlRecords) = true := by
    unfold Step.ok
    dsimp only [hndlStepInit, Step.toInput]
    refine (stepIn_isSome _ _ _).trans ?_
    exact congrArg Option.isSome hruns.1
  have hnext : hndlStepInit.next (setupTrace hndlRecords) = hndlTr1 := by
    unfold Step.next
    dsimp only [hndlStepInit, Step.toInput]
    refine (stepIn_next _ _ _).trans ?_
    exact hruns.2
  refine ⟨hok, hnext, ?_⟩
  unfold stepView
  simp only [hok, ↓reduceIte]
  rw [hnext]
  dsimp only [hndlStepInit, hndlBh, Option.toList, List.append_nil]
  have hrecv : received (setupTrace hndlRecords) [14, 15, 20, 21] =
      [setupPublic hndlRecords 4, setupPublic hndlRecords 5,
       setupPublic hndlRecords 6, setupPublic hndlRecords 7] :=
    Symbolic.Swarm.CREF.received_setupHandles hndlRecords [] hndlRecords_ne
  dsimp only [hndlTr1]
  rw [Symbolic.Swarm.CREF.exposures_iniAliceStartTr, List.append_nil]
  unfold aliceVis
  dsimp only [Option.toList]
  rw [List.append_nil, hrecv, Symbolic.Swarm.CREF.newRandoms_iniAliceStartTr,
    Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr, hndl_tr0_len]
  rfl

private theorem hndl_runMatches_init :
    RunMatches hndlInterp hndlRecords hndlSem hndlGhost (setupTrace hndlRecords)
      hndlStepInit hndlInitEv (hndlInpVis :: hndlDrsVis) := by
  obtain ⟨hok, _, hview⟩ := hndlStepInit_exec
  refine ⟨rfl, rfl,
    by simp [hndlStepInit, hndlInitEv, runEventOf, hndlCall, Step.FitsCmd],
    by simp [hndlStepInit, Step.MatchesSetupPeer],
    hok, ⟨[], rfl⟩, hview.symm,
    hndlInpVis, hndlDrsVis, [],
    congrArg (hndlInpVis :: ·) (List.append_nil hndlDrsVis).symm,
    ?_, ?_, rfl, trivial, fun _ _ => trivial⟩
  · have hinp : hndlInitEv.input = bundleBlob (publicBundleOf hndlBundleB) := by
      dsimp only [hndlInitEv, runEventOf]
      exact hndlCall_runInput
    have hb4 : (bundleBlob (publicBundleOf hndlBundleB))[4]? = some 0#8 := by
      dsimp only [bundleBlob, publicBundleOf]
      rw [show hndlBundleB.opk = none from rfl, show hndlBundleB.regId = 20#32 from rfl]
      dsimp only [Option.map]
      simp only [List.append_assoc]
      rw [List.getElem?_append_right (by simp [le32]),
        List.getElem?_append_left (by simp [le32])]
      simp [le32]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hinp]
      exact Symbolic.Swarm.CREF.bundleCore_of_honestBundle hndlInterp hndlRecords hndlRecords_ne
        hndlSem hndlGhost hndlCompat _ hndlBundleB_honest
        (bundleBlob_publicBundleOf_length hndlBundleB)
    · rw [hinp]; exact hb4
  · let ds := initiateDrawsOfCoins hndlTape.toList
    have hcoins : hndlTape.toList.length = initiateTapeLen := hndlTape.2
    have hne := initiateDrawsOfCoins_nonempty hcoins
    have hflat : ds.flatten = hndlInitEv.coins := initiateDrawsOfCoins_flatten hcoins
    have hlens := initiateDrawsOfCoins_lengths hcoins
    have hσ0 : hndlGhost.σ 22 32 = ds.getD 0 [] := by
      rw [initiateDrawsOfCoins_getD_0]; rfl
    have hσ1 : hndlGhost.σ 23 32 = Symbolic.Swarm.CREF.entropyBytes ds := by
      rw [entropyBytes_initiateDrawsOfCoins]; rfl
    have hσ2 : hndlGhost.σ 24 32 = ds.getD 33 [] := by
      rw [initiateDrawsOfCoins_getD_33]; rfl
    have hfor := Symbolic.Swarm.CREF.ini_forall₂_initiate_rng_34
      hndlInterp hndlRecords hndlSem hndlGhost 22 ds hlens hσ0 hσ1 hσ2
    rw [List.forall₂_map_left_iff] at hfor
    have hnoPks : ∀ v ∈ hndlDrsVis, v.layout ≠ .preKeySend := by
      intro v hv
      dsimp only [hndlDrsVis, rngEntry, kyberCoinEntries] at hv
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | ⟨_, _, rfl⟩ | rfl <;> nofun
    have hnoPki : ∀ v ∈ hndlDrsVis, ∀ eks, v.layout ≠ .preKeyInner eks := by
      intro v hv eks
      dsimp only [hndlDrsVis, rngEntry, kyberCoinEntries] at hv
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | ⟨_, _, rfl⟩ | rfl <;> nofun
    have hconv : ∀ {c : DY.Libsignal.HwBytes} {v : VisEntry},
        v.layout ≠ .preKeySend →
        (∀ eks, v.layout ≠ .preKeyInner eks) →
        DY.Libsignal.Composed.Refinement.EventMatchesEntry
          hndlInterp hndlRecords hndlSem hndlGhost (.rng c) v →
        BytesMatchEntry hndlInterp hndlRecords hndlSem hndlGhost .rng c v := by
      intro c v hlay hlay2 ⟨hk, hl⟩
      refine ⟨hk, ?_⟩
      dsimp only [DY.Libsignal.Composed.Refinement.eventBytes] at hl ⊢
      cases hv : v.layout <;> simp only [hv] at hl ⊢
      all_goals first | exact hl | exact absurd hv hlay | exact absurd hv (hlay2 _)
    have hfor' : List.Forall₂
        (fun p v => BytesMatchEntry hndlInterp hndlRecords hndlSem hndlGhost .rng p v)
        ds hndlDrsVis := by
      change List.Forall₂ _ ds hndlDrsVis at hfor
      rw [List.forall₂_iff_get] at hfor ⊢
      exact ⟨hfor.1, fun i hi₁ hi₂ =>
        hconv (hnoPks _ (List.get_mem hndlDrsVis ⟨i, hi₂⟩))
          (hnoPki _ (List.get_mem hndlDrsVis ⟨i, hi₂⟩)) (hfor.2 i hi₁ hi₂)⟩
    exact ⟨ds, hne, ⟨[], by rw [List.append_nil, hflat]⟩, hfor'⟩

private theorem hndlBreakDH_next : Step.breakDH.next hndlTr1 = hndlTr2 := by
  unfold Step.next
  dsimp only [Step.toInput]
  refine (stepIn_next _ _ _).trans ?_
  exact (Symbolic.Swarm.CREF.TR.Runs.logEvent hndlTr1 .BrokenDH).2

private theorem hndlInvertDH_exec :
    (Step.invertDH 2).ok hndlTr2 = true ∧
    (Step.invertDH 2).next hndlTr2 = hndlTr3 ∧
    invertEntry (.invertDH 2) hndlTr2 .leakRecord = [hndlLeakVis] := by
  have hbrk : brokenDHB hndlTr2 = true := by
    unfold brokenDHB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    rw [List.any_eq_true]
    refine ⟨hndlTr1.length, List.mem_range.mpr (by simp [hndlTr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]), ?_⟩
    have hat : (hndlTr2.at? hndlTr1.length : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
        some ⟨PQXDHEvent.BrokenDH⟩ :=
      Symbolic.Swarm.CREF.TR.at?_append_self hndlTr1
        (⟨PQXDHEvent.BrokenDH⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)
    rw [hat]
  have hat2 : (hndlTr2.at? 2 : Option DY.Network.ExecEntryT) =
      some ⟨DY.DiffieHellman.dhPk (randTerm 0 32)⟩ :=
    at?_le_some (DY.Trace.le_trans _ _ _ hndl_le01 (DY.Trace.append_le _ _)) hndl_tr0_at2
  have hruns : Symbolic.Swarm.CREF.TR.Runs (DY.Libsignal.PQXDH.invertDH 2)
      hndlTr2 hndlTr2.length hndlTr3 := by
    (unfold DY.Libsignal.PQXDH.invertDH; simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1])
    refine Symbolic.Swarm.CREF.TR.Runs.bind
      (Symbolic.Swarm.CREF.TR.Runs.requireTracePredicate hbrk) ?_
    refine Symbolic.Swarm.CREF.TR.Runs.bind
      (Symbolic.Swarm.CREF.TR.Runs.bind
        (Symbolic.Swarm.CREF.TR.Runs.getEntry hat2)
        (Symbolic.Swarm.CREF.TR.Runs.pure _ _)) ?_
    rw [dhSkOf_x25519Key_dhPk]
    exact Symbolic.Swarm.CREF.TR.Runs.sendMessage _ _
  have hok : (Step.invertDH 2).ok hndlTr2 = true := by
    unfold Step.ok
    dsimp only [Step.toInput]
    refine (stepIn_isSome _ _ _).trans ?_
    exact congrArg Option.isSome hruns.1
  have hnext : (Step.invertDH 2).next hndlTr2 = hndlTr3 := by
    unfold Step.next
    dsimp only [Step.toInput]
    refine (stepIn_next _ _ _).trans ?_
    exact hruns.2
  refine ⟨hok, hnext, ?_⟩
  unfold invertEntry lastSent
  rw [hnext]
  have hlen3 : hndlTr3.length = hndlTr2.length + 1 := by
    simp [hndlTr3, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : hndlTr2.length < hndlTr3.length := by omega
  have hsub : hndlTr3.length - 1 = hndlTr2.length := by omega
  simp only [hlt, ↓reduceIte, hsub]
  have hat_last : (hndlTr3.at? hndlTr2.length : Option DY.Network.ExecEntryT) =
      some ⟨randTerm 0 32⟩ :=
    Symbolic.Swarm.CREF.TR.at?_append_self hndlTr2 _
  rw [Symbolic.Swarm.CREF.getMessageSentAt_of_at? hat_last]
  rfl

private theorem hndl_runTrace_eq : runTrace hndlRecords hndlSteps = hndlTr3 := by
  dsimp only [runTrace, hndlSteps, runSteps]
  rw [hndlStepInit_exec.2.1, hndlBreakDH_next, hndlInvertDH_exec.2.1]

theorem hndl_explains :
    Explains hndlInterp hndlRecords hndlSem hndlGhost hndlSteps hndlVis hndlEvs := by
  have hgwf : GhostWF hndlGhost hndlVis := by
    refine ⟨fun _ _ _ ts n hn _ => hndlFresh_length ts n hn, fun _ => Or.inl rfl, ?_⟩
    intro v hv hsend
    dsimp only [hndlVis, hndlInpVis, hndlDrsVis, hndlLeakVis, rngEntry, kyberCoinEntries] at hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | (⟨_, _, rfl⟩ | rfl) | rfl <;> nomatch hsend
  have hsf : StepsStateFaithful hndlRecords hndlSteps := by
    intro i _ si _ _ _ _ _ hi _ hload _ _
    have hmem : si ∈ hndlSteps := List.mem_of_getElem? hi
    simp only [hndlSteps, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> cases hload
  have hmrun : ModelRunWF hndlRecords hndlSteps :=
    ⟨Symbolic.Swarm.CREF.TR.setupRandoms_length hndlRecords hndlRecords_ne,
     Symbolic.Swarm.CREF.TR.setupTrace_reachable hndlRecords,
     ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩,
     hsf⟩
  let ids1 := nextBundleIds none hndlInitEv
  have hme_nil : MatchesEventsAt hndlInterp hndlRecords hndlSem hndlGhost ids1 hndlTr3 [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have hme_inv : MatchesEventsAt hndlInterp hndlRecords hndlSem hndlGhost ids1 hndlTr2
      [.invertDH 2] [.env (.invertDH hndlPkA hndlSkA)] [hndlLeakVis] := by
    obtain ⟨hok, hnext, hentry⟩ := hndlInvertDH_exec
    have hat2 : (hndlTr2.at? 2 : Option DY.Network.ExecEntryT) =
        some ⟨DY.DiffieHellman.dhPk (randTerm 0 32)⟩ :=
      at?_le_some (DY.Trace.le_trans _ _ _ hndl_le01 (DY.Trace.append_le _ _)) hndl_tr0_at2
    have hmsg2 : hndlTr2.getMessageSentAt 2 = some (DY.DiffieHellman.dhPk (randTerm 0 32)) :=
      Symbolic.Swarm.CREF.getMessageSentAt_of_at? hat2
    have hγ0 : gamma hndlInterp hndlSem hndlGhost (randTerm 0 32) = hndlSkA := by
      rw [← Symbolic.Swarm.CREF.setupSecret_0 hndlRecords hndlRecords_ne]
      exact (Symbolic.Swarm.CREF.gamma_setupSecret hndlInterp hndlRecords hndlRecords_ne
        hndlSem hndlGhost hndlCompat).1
    have hγ_pk : gamma hndlInterp hndlSem hndlGhost (DY.DiffieHellman.dhPk (randTerm 0 32)) =
        hndlPkA := by
      rw [Symbolic.Swarm.CREF.ini_gamma_dhPk, hγ0]; rfl
    have henv : EnvMatches hndlInterp hndlRecords hndlSem hndlGhost hndlTr2
        (.invertDH 2) (.invertDH hndlPkA hndlSkA) [hndlLeakVis] :=
      ⟨2, rfl, hok, by rw [hmsg2]; exact congrArg some hγ_pk, hentry.symm,
        hndlLeakVis, rfl, rfl, randTerm 0 32, rfl, Or.inl hγ0.symm⟩
    exact MatchesEventsAt.env (pre := []) (fun _ h => nomatch h) henv
      (by change MatchesEventsAt _ _ _ _ ids1 ((Step.invertDH 2).next hndlTr2) _ _ _; rw [hnext]; exact hme_nil)
  have hme_brk : MatchesEventsAt hndlInterp hndlRecords hndlSem hndlGhost ids1 hndlTr1
      [.breakDH, .invertDH 2] [.env .breakDH, .env (.invertDH hndlPkA hndlSkA)] [hndlLeakVis] := by
    have henv : EnvMatches hndlInterp hndlRecords hndlSem hndlGhost hndlTr1 .breakDH .breakDH [] :=
      ⟨rfl, rfl⟩
    exact MatchesEventsAt.env (pre := []) (fun _ h => nomatch h) henv
      (by change MatchesEventsAt _ _ _ _ ids1 (Step.breakDH.next hndlTr1) _ _ _; rw [hndlBreakDH_next]; exact hme_inv)
  have hme : MatchesEvents hndlInterp hndlRecords hndlSem hndlGhost (setupTrace hndlRecords)
      hndlSteps hndlEvs hndlVis :=
    MatchesEventsAt.run1 (pre := []) (fun _ h => nomatch h) hndl_runMatches_init
      (by change MatchesEventsAt _ _ _ _ ids1 (hndlStepInit.next (setupTrace hndlRecords)) _ _ _; rw [hndlStepInit_exec.2.1]; exact hme_brk)
  exact ⟨hndlCompat, hgwf, hmrun, hme⟩

private def isSetupOrAliceDone : PQXDHEvent → Bool
  | .IdentityRegistered .. => true
  | .SignedPrekeyPublished .. => true
  | .PQPrekeyPublished .. => true
  | .OneTimePrekeyPublished .. => true
  | .AliceDone .. => true
  | _ => false

private theorem onlySetupOrAliceDone_nil :
    ∀ ev, (DY.Trace.nil : ExecTrace).EventLogged ev → isSetupOrAliceDone ev = true := by
  intro _ ⟨_, h⟩
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
    Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h

private theorem onlySetupOrAliceDone_other {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (ih : ∀ ev, tr.EventLogged ev → isSetupOrAliceDone ev = true) :
    ∀ ev, (tr.append e).EventLogged ev → isSetupOrAliceDone ev = true :=
  fun ev h => ih ev ((eventLogged_append_other_iff hnone).mp h)

private theorem onlySetupOrAliceDone_pq {tr : ExecTrace} {ev₀ : PQXDHEvent}
    (hok : isSetupOrAliceDone ev₀ = true)
    (ih : ∀ ev, tr.EventLogged ev → isSetupOrAliceDone ev = true) :
    ∀ ev, (tr.append (⟨ev₀⟩ : DY.ProtocolEvent.ExecEntryT PQXDHEvent)).EventLogged ev →
      isSetupOrAliceDone ev = true := by
  intro ev h
  rcases eventLogged_append_same_iff.mp h with h' | rfl
  · exact ih ev h'
  · exact hok

private theorem hndlTr1_events :
    ∀ ev, hndlTr1.EventLogged ev → isSetupOrAliceDone ev = true := by
  have h0 : ∀ ev, (setupTrace hndlRecords).EventLogged ev → isSetupOrAliceDone ev = true := by
    rw [hndl_tr0_eq]
    unfold Symbolic.Swarm.CREF.TR.setupTr4 Symbolic.Swarm.CREF.TR.setupTr3
      Symbolic.Swarm.CREF.TR.setupTr2 Symbolic.Swarm.CREF.TR.setupTr1
    exact onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_pq rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_pq rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_pq rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
      (onlySetupOrAliceDone_pq rfl (onlySetupOrAliceDone_other rfl
        onlySetupOrAliceDone_nil)))))))))))))))))))))
  dsimp only [hndlTr1, Symbolic.Swarm.CREF.iniAliceStartTr]
  exact onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
    (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_pq rfl
    (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
    (onlySetupOrAliceDone_other rfl (onlySetupOrAliceDone_other rfl
    (onlySetupOrAliceDone_other rfl h0))))))))

private theorem hndlTr3_not_logged {ev : PQXDHEvent}
    (h1 : isSetupOrAliceDone ev = false) (h2 : PQXDHEvent.BrokenDH ≠ ev) :
    ¬ hndlTr3.EventLogged ev := by
  intro h
  have h' : hndlTr2.EventLogged ev := (eventLogged_append_other_iff rfl).mp h
  rcases eventLogged_append_same_iff.mp h' with h'' | heq
  · have := hndlTr1_events ev h''
    rw [h1] at this
    cases this
  · exact h2 heq

theorem hndl_brokenDH : (runTrace hndlRecords hndlSteps).EventLogged PQXDHEvent.BrokenDH := by
  rw [hndl_runTrace_eq]
  exact eventLogged_mono (DY.Trace.append_le _ _) (eventLogged_here hndlTr1 PQXDHEvent.BrokenDH)

theorem hndl_aliceDone_and_premise :
    (runTrace hndlRecords hndlSteps).EventLoggedAt
      (PQXDHEvent.AliceDone hndlRecords.alice hndlRecords.bob hndlAliceOut.ikA hndlAliceOut.ikB
        hndlAliceOut.spk hndlAliceOut.pqpk hndlAliceOut.opk hndlAliceOut.ek
        hndlAliceOut.ct hndlAliceOut.keys) 27 ∧
    HNDLPremise hndlRecords.alice hndlRecords.bob hndlAliceOut.ikA hndlAliceOut.ikB
      hndlAliceOut.spk hndlAliceOut.pqpk 27 (runTrace hndlRecords hndlSteps) := by
  rw [hndl_runTrace_eq]
  refine ⟨?_, ?_,
    hndlTr3_not_logged rfl (fun h => nomatch h),
    hndlTr3_not_logged rfl (fun h => nomatch h),
    hndlTr3_not_logged rfl (fun h => nomatch h),
    hndlTr3_not_logged rfl (fun h => nomatch h),
    hndlTr3_not_logged rfl (fun h => nomatch h)⟩
  · have hget := (Symbolic.Swarm.CREF.getEventAt_pq_iniAliceStartTr
      (setupTrace hndlRecords) hndlRecords.alice hndlRecords.bob hndlAliceOut).2.2.2.2.2.1
    rw [hndl_tr0_len, ← DY.Trace.EventLoggedAt_eq_getEventAt] at hget
    exact eventLoggedAt_mono
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _)) hget
  · intro j hj
    have hj2 : hndlTr2.EventLoggedAt PQXDHEvent.BrokenDH j := eventLoggedAt_append_other rfl hj
    rcases eventLoggedAt_append_same hj2 with ⟨_, hj1⟩ | ⟨rfl, _⟩
    · exact absurd (hndlTr1_events PQXDHEvent.BrokenDH ⟨j, hj1⟩) (by decide)
    · have hlen1 : hndlTr1.length = 31 := by
        dsimp only [hndlTr1]
        rw [Symbolic.Swarm.CREF.length_iniAliceStartTr, hndl_tr0_len]
      omega

theorem cli_hndl_witness_aux :
    ∃ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
      (evs : List CliEvent) (S : OpaqueSymbolSemantics) (g : Ghost) (ss : List Step) (vis : List VisEntry),
      ExternContractsHoldCli interp ∧ ModelAgree interp P ∧ ProtocolSetupWF r ∧
      CliTraces (PqModelRel interp P) interp r (CliTurn.init (initDirs interp r)) evs ∧
      InvertsGuarded interp r evs ∧
      (∃ pk sk, CliEvent.env (EnvEvent.invertDH pk sk) ∈ evs) ∧
      Explains interp r S g ss vis evs ∧
      (runTrace r ss).EventLogged PQXDHEvent.BrokenDH ∧
      ∃ a b ikA ikB spk pqpk opk ek ct keys i,
        (runTrace r ss).EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i ∧
        HNDLPremise a b ikA ikB spk pqpk i (runTrace r ss) :=
  ⟨hndlInterp, hndlP, hndlRecords, hndlEvs, hndlSem, hndlGhost, hndlSteps, hndlVis,
   hndlInterp_contracts, hndlP_modelAgree, hndlRecords_wf,
   hndl_cliTraces, hndl_invertsGuarded, hndl_has_invertDH,
   hndl_explains, hndl_brokenDH,
   _, _, _, _, _, _, _, _, _, _, 27, hndl_aliceDone_and_premise⟩

end Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Explains
