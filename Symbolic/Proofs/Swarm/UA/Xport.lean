/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs

/-!
# Invariance Under `interpOfParams`

Proves `xport : UAXportSpec`: `ExplainsClassical` and `CollisionAfterExplainedPrefixClassical` are
invariant under `interpOfParams`, which overrides only SPQR and HMAC symbols not consulted by
`gamma`, `gamma'`, `pubBytes`, `kyberDecapsBytes`, or `kyberEncapsBytes`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.Xport

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY.Libsignal.HwEvents (CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.E2E (PEParams)
open Symbolic.Swarm.CREF.Cli (interpOfParams gamma_interpOfParams gamma'_interpOfParams
  pubBytes_interpOfParams kyberDecapsBytes_interpOfParams kyberEncapsBytes_interpOfParams)
open Symbolic.Proofs.Swarm.UA.Defs (UAXportSpec)

private theorem matchesEventsAt_imp {i₁ i₂ : ExternInterpretation}
    (hrm : @RunMatches i₁ = @RunMatches i₂) (hem : EnvMatchesClassical i₁ = EnvMatchesClassical i₂)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : _root_.DY.ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : MatchesEventsClassicalAt i₁ r S g initIds tr ss evs vis) :
    MatchesEventsClassicalAt i₂ r S g initIds tr ss evs vis := by
  induction hm with
  | nil hpre => exact .nil hpre
  | run1 hpre hrun _ ih => exact .run1 hpre (hrm ▸ hrun) ih
  | run0 hpre hrej _ ih => exact .run0 hpre hrej ih
  | env hpre henv _ ih => exact .env hpre (hem ▸ henv) ih

theorem explains_interpOfParams_eq (interp : ExternInterpretation) (P : PEParams) :
    ExplainsClassical (interpOfParams interp P) = ExplainsClassical interp := by
  have hcompat : GhostAndSemMatchSetup (interpOfParams interp P) = GhostAndSemMatchSetup interp := by
    funext r S g
    simp only [GhostAndSemMatchSetup, gamma_interpOfParams, kyberDecapsBytes_interpOfParams]
  have hbme : @BytesMatchEntry (interpOfParams interp P) = @BytesMatchEntry interp := by
    funext r S g k b v initIds
    simp only [BytesMatchEntry, PreKeyBundleLayoutMatches, BundleSignedKeysMatch, SendMatches,
      PreKeyRecvOpkMatches, PreKeyRecvMatches, gamma_interpOfParams, pubBytes_interpOfParams]
  have hrr : recvRepresentationsOn (interpOfParams interp P) = recvRepresentationsOn interp := by
    funext S g tr b; simp only [recvRepresentationsOn, gamma_interpOfParams]
  have hpkr :
      preKeyRepresentationsOn (interpOfParams interp P) = preKeyRepresentationsOn interp := by
    funext r S g tr b
    simp only [preKeyRepresentationsOn, PreKeyRecvMatches, FaithfulInner,
      gamma_interpOfParams, pubBytes_interpOfParams]
  have hrf : ReadsFaithfully (interpOfParams interp P) = ReadsFaithfully interp := by
    funext r S g tr v b; simp only [ReadsFaithfully, hrr, hpkr]
  have hpf : PathFaithfulAt (interpOfParams interp P) = PathFaithfulAt interp := by
    funext S g tr s b; simp only [PathFaithfulAt, gamma_interpOfParams]
  have hdm : DrawsMatch (interpOfParams interp P) = DrawsMatch interp := by
    funext r S g drs coins; simp only [DrawsMatch, hbme]
  have hom : @OutputsMatch (interpOfParams interp P) = @OutputsMatch interp := by
    funext r S g ev outs initIds; simp only [OutputsMatch, hbme]
  have hrm : @RunMatches (interpOfParams interp P) = @RunMatches interp := by
    funext r S g tr s ev vis initIds; simp only [RunMatches, hbme, hdm, hom, hrf, hpf]
  have hem : EnvMatchesClassical (interpOfParams interp P) = EnvMatchesClassical interp := by
    funext r S g tr s ev vis; simp only [EnvMatchesClassical, hbme]
  have hme : MatchesEventsClassicalAt (interpOfParams interp P) = MatchesEventsClassicalAt interp := by
    funext r S g initIds tr ss evs vis
    exact propext ⟨matchesEventsAt_imp hrm hem, matchesEventsAt_imp hrm.symm hem.symm⟩
  funext r S g ss vis evs
  simp only [ExplainsClassical, MatchesEventsClassical, hcompat, hme]

theorem collisionAtCli_interpOfParams_eq (interp : ExternInterpretation) (P : PEParams) :
    CollisionAfterExplainedPrefixClassical (interpOfParams interp P) = CollisionAfterExplainedPrefixClassical interp := by
  have hex := explains_interpOfParams_eq interp P
  have hbme : @BytesMatchEntry (interpOfParams interp P) = @BytesMatchEntry interp := by
    funext r S g k b v initIds
    simp only [BytesMatchEntry, PreKeyBundleLayoutMatches, BundleSignedKeysMatch, SendMatches,
      PreKeyRecvOpkMatches, PreKeyRecvMatches, gamma_interpOfParams, pubBytes_interpOfParams]
  have hrr : recvRepresentationsOn (interpOfParams interp P) = recvRepresentationsOn interp := by
    funext S g tr b; simp only [recvRepresentationsOn, gamma_interpOfParams]
  have hpkr :
      preKeyRepresentationsOn (interpOfParams interp P) = preKeyRepresentationsOn interp := by
    funext r S g tr b
    simp only [preKeyRepresentationsOn, PreKeyRecvMatches, FaithfulInner,
      gamma_interpOfParams, pubBytes_interpOfParams]
  have hrm : @RunMatches (interpOfParams interp P) = @RunMatches interp := by
    have hrf : ReadsFaithfully (interpOfParams interp P) = ReadsFaithfully interp := by
      funext r S g tr v b; simp only [ReadsFaithfully, hrr, hpkr]
    have hpf : PathFaithfulAt (interpOfParams interp P) = PathFaithfulAt interp := by
      funext S g tr s b; simp only [PathFaithfulAt, gamma_interpOfParams]
    have hdm : DrawsMatch (interpOfParams interp P) = DrawsMatch interp := by
      funext r S g drs coins; simp only [DrawsMatch, hbme]
    have hom : @OutputsMatch (interpOfParams interp P) = @OutputsMatch interp := by
      funext r S g ev outs initIds; simp only [OutputsMatch, hbme]
    funext r S g tr s ev vis initIds; simp only [RunMatches, hbme, hdm, hom, hrf, hpf]
  have hem : EnvMatchesClassical (interpOfParams interp P) = EnvMatchesClassical interp := by
    funext r S g tr s ev vis; simp only [EnvMatchesClassical, hbme]
  have hme : MatchesEventsClassicalAt (interpOfParams interp P) = MatchesEventsClassicalAt interp := by
    funext r S g initIds tr ss evs vis
    exact propext ⟨matchesEventsAt_imp hrm hem, matchesEventsAt_imp hrm.symm hem.symm⟩
  have hmc : MemoCollisionOn (interpOfParams interp P) = MemoCollisionOn interp := by
    funext r S g known tr vis nt np; simp only [MemoCollisionOn, gamma'_interpOfParams]
  have hwt : whisperTrials (interpOfParams interp P) = whisperTrials interp := by
    funext r S g tr msg; simp only [whisperTrials, gamma_interpOfParams]
  have hos : MacTagForgeryOrCollision (interpOfParams interp P) = MacTagForgeryOrCollision interp := by
    funext S g known honest msg ctxs
    simp only [MacTagForgeryOrCollision, UnknownSeedMacGuess, TruncatedMacSeedCollision,
      gamma_interpOfParams]
  have hrc : RecvCollisionOn (interpOfParams interp P) = RecvCollisionOn interp := by
    funext r S g tr vis salts t; simp only [RecvCollisionOn, hmc, hwt, hos]
  have hrsc : ReselectCollisionOn (interpOfParams interp P) = ReselectCollisionOn interp := by
    funext r S g tr vis salts t; simp only [ReselectCollisionOn, gamma_interpOfParams, hrr, hrc]
  have hbsc : BobSessionStartCollidesOrImplicitRejectsOn (interpOfParams interp P) = BobSessionStartCollidesOrImplicitRejectsOn interp := by
    funext r S g tr vis salts p x
    simp only [BobSessionStartCollidesOrImplicitRejectsOn, hmc, hos]
  have hrdc : ReadCollisionCliClassical (interpOfParams interp P) = ReadCollisionCliClassical interp := by
    funext r S g ss evs; simp only [ReadCollisionCliClassical, MatchesEventsClassical, hme, hrc]
  have hac : ModelAcceptsTermAfterAttackerSendsClassical (interpOfParams interp P) = ModelAcceptsTermAfterAttackerSendsClassical interp := by
    funext r S g ss evs₁ ev t; simp only [ModelAcceptsTermAfterAttackerSendsClassical, hex]
  have hwe : SignalMsgAcceptedOnlyViaCollisionClassical (interpOfParams interp P) = SignalMsgAcceptedOnlyViaCollisionClassical interp := by
    funext r S g ss evs₁ ev b
    simp only [SignalMsgAcceptedOnlyViaCollisionClassical, RepresentationsCollideOrAcceptedCollideClassical, hrr, hex,
      hrdc, hac, hrc, hrsc]
  have hpke : PreKeyStartCollidesOrRejectsClassical (interpOfParams interp P) = PreKeyStartCollidesOrRejectsClassical interp := by
    funext r S g ss evs₁ b p
    simp only [PreKeyStartCollidesOrRejectsClassical, hpkr, KyberMismatch,
      kyberEncapsBytes_interpOfParams, kyberDecapsBytes_interpOfParams, hex, hrdc, hbsc]
  have hkbk : KnownBaseKeyOn (interpOfParams interp P) = KnownBaseKeyOn interp := by
    funext S g tr p; simp only [KnownBaseKeyOn, gamma_interpOfParams]
  have hpg : PrefixExplainingGhostsClassical (interpOfParams interp P) = PrefixExplainingGhostsClassical interp := by
    funext r S g ss evs₁; simp only [PrefixExplainingGhostsClassical, hex]
  funext r S evs
  simp only [CollisionAfterExplainedPrefixClassical, NextEventCollidesClassical,
    pubBytes_interpOfParams, hex, hwe, hpke, hkbk, hpg, hbme, hmc]

/-- `ExplainsClassical` and `CollisionAfterExplainedPrefixClassical` are invariant under
`interpOfParams`. -/
theorem xport : UAXportSpec := by
  intro interp P r S
  refine ⟨fun g ss vis evs => ?_, fun evs => ?_⟩
  · rw [explains_interpOfParams_eq interp P]
  · rw [collisionAtCli_interpOfParams_eq interp P]

end Symbolic.Proofs.Swarm.UA.Xport
