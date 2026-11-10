/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs

/-!
# Parameter-Override Invariance of Explanations and Collisions

Proves `xport : UAXportSpecB`, showing that `Explains` and `CollisionAfterExplainedPrefix` are
unchanged when `interp` is replaced by `interpOfParams interp P`, because both predicates read
`ExternInterpretation` only through fields preserved by `interpOfParams`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.RAB.Xport

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY.Libsignal.HwEvents (CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.E2E (PEParams)
open Symbolic.Swarm.CREF.Cli (interpOfParams gamma_interpOfParams gamma'_interpOfParams
  pubBytes_interpOfParams kyberDecapsBytes_interpOfParams kyberEncapsBytes_interpOfParams)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs (UAXportSpecB)

private theorem matchesEventsAt_imp {i₁ i₂ : ExternInterpretation}
    (hrm : @RunMatches i₁ = @RunMatches i₂) (hem : EnvMatches i₁ = EnvMatches i₂)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : _root_.DY.ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : MatchesEventsAt i₁ r S g initIds tr ss evs vis) :
    MatchesEventsAt i₂ r S g initIds tr ss evs vis := by
  induction hm with
  | nil hpre => exact .nil hpre
  | run1 hpre hrun _ ih => exact .run1 hpre (hrm ▸ hrun) ih
  | run0 hpre hrej _ ih => exact .run0 hpre hrej ih
  | env hpre henv _ ih => exact .env hpre (hem ▸ henv) ih

private theorem bytesMatchEntry_interpOfParams_eq (interp : ExternInterpretation) (P : PEParams) :
    @BytesMatchEntry (interpOfParams interp P) = @BytesMatchEntry interp := by
  funext r S g k b v initIds
  simp only [BytesMatchEntry, PreKeyBundleLayoutMatches, BundleSignedKeysMatch, SendMatches,
    PreKeyRecvOpkMatches, PreKeyRecvMatches, gamma_interpOfParams, pubBytes_interpOfParams]

private theorem recvRepresentationsOn_interpOfParams_eq
    (interp : ExternInterpretation) (P : PEParams) :
    recvRepresentationsOn (interpOfParams interp P) = recvRepresentationsOn interp := by
  funext S g tr b
  simp only [recvRepresentationsOn, gamma_interpOfParams]

private theorem preKeyRepresentationsOn_interpOfParams_eq
    (interp : ExternInterpretation) (P : PEParams) :
    preKeyRepresentationsOn (interpOfParams interp P) = preKeyRepresentationsOn interp := by
  funext r S g tr b
  simp only [preKeyRepresentationsOn, PreKeyRecvMatches, FaithfulInner,
    gamma_interpOfParams, pubBytes_interpOfParams]

private theorem matchesEventsAt_interpOfParams_eq (interp : ExternInterpretation) (P : PEParams) :
    MatchesEventsAt (interpOfParams interp P) = MatchesEventsAt interp := by
  have hbme := bytesMatchEntry_interpOfParams_eq interp P
  have hrr := recvRepresentationsOn_interpOfParams_eq interp P
  have hpkr := preKeyRepresentationsOn_interpOfParams_eq interp P
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
  have hem : EnvMatches (interpOfParams interp P) = EnvMatches interp := by
    funext r S g tr s ev vis
    cases ev <;> simp only [EnvMatches, gamma_interpOfParams, hbme]
  funext r S g initIds tr ss evs vis
  exact propext ⟨matchesEventsAt_imp hrm hem, matchesEventsAt_imp hrm.symm hem.symm⟩

theorem explains_interpOfParams_eq (interp : ExternInterpretation) (P : PEParams) :
    Explains (interpOfParams interp P) = Explains interp := by
  have hcompat : GhostAndSemMatchSetup (interpOfParams interp P) = GhostAndSemMatchSetup interp := by
    funext r S g
    simp only [GhostAndSemMatchSetup, gamma_interpOfParams, kyberDecapsBytes_interpOfParams]
  have hme := matchesEventsAt_interpOfParams_eq interp P
  funext r S g ss vis evs
  simp only [Explains, MatchesEvents, hcompat, hme]

theorem collisionAtCli_interpOfParams_eq (interp : ExternInterpretation) (P : PEParams) :
    CollisionAfterExplainedPrefix (interpOfParams interp P) = CollisionAfterExplainedPrefix interp := by
  have hex := explains_interpOfParams_eq interp P
  have hbme := bytesMatchEntry_interpOfParams_eq interp P
  have hrr := recvRepresentationsOn_interpOfParams_eq interp P
  have hpkr := preKeyRepresentationsOn_interpOfParams_eq interp P
  have hme := matchesEventsAt_interpOfParams_eq interp P
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
  have hrdc : ReadCollisionCli (interpOfParams interp P) = ReadCollisionCli interp := by
    funext r S g ss evs; simp only [ReadCollisionCli, MatchesEvents, hme, hrc]
  have hac : ModelAcceptsTermAfterAttackerSends (interpOfParams interp P) = ModelAcceptsTermAfterAttackerSends interp := by
    funext r S g ss evs₁ ev t; simp only [ModelAcceptsTermAfterAttackerSends, hex]
  have hwe : SignalMsgAcceptedOnlyViaCollision (interpOfParams interp P) = SignalMsgAcceptedOnlyViaCollision interp := by
    funext r S g ss evs₁ ev b
    simp only [SignalMsgAcceptedOnlyViaCollision, _root_.DY.Libsignal.Composed.Refinement.Cli.RepresentationsCollideOrAcceptedCollide, hrr, hex,
      hrdc, hac, hrc, hrsc]
  have hpke : PreKeyStartCollidesOrRejects (interpOfParams interp P) = PreKeyStartCollidesOrRejects interp := by
    funext r S g ss evs₁ b p
    simp only [PreKeyStartCollidesOrRejects, hpkr, KyberMismatch,
      kyberEncapsBytes_interpOfParams, kyberDecapsBytes_interpOfParams, hex, hrdc, hbsc]
  have hkbk : KnownBaseKeyOn (interpOfParams interp P) = KnownBaseKeyOn interp := by
    funext S g tr p; simp only [KnownBaseKeyOn, gamma_interpOfParams]
  have hpg : PrefixExplainingGhosts (interpOfParams interp P) = PrefixExplainingGhosts interp := by
    funext r S g ss evs₁; simp only [PrefixExplainingGhosts, hex]
  funext r S evs
  simp only [CollisionAfterExplainedPrefix, _root_.DY.Libsignal.Composed.Refinement.Cli.NextEventCollides,
    pubBytes_interpOfParams, hex, hwe, hpke, hkbk, hpg, hbme, hmc]

/-- `Explains` and `CollisionAfterExplainedPrefix` are invariant under `interpOfParams`. -/
theorem xport : UAXportSpecB := by
  intro interp P r S
  refine ⟨fun g ss vis evs => ?_, fun evs => ?_⟩
  · rw [explains_interpOfParams_eq interp P]
  · rw [collisionAtCli_interpOfParams_eq interp P]

end Symbolic.Proofs.Swarm.UA.BI.RAB.Xport
