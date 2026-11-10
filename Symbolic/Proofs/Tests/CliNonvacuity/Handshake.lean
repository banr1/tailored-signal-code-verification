/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCliTraces
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
import all DY.ALaCarte.Basic
import all DY.ALaCarte.DecidableEq
import all DY.ALaCarte.Ordering
import all DY.Misc.Instances
import all DY.Bytes.Basic
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.Concat
import all DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.KdfExtract
import all DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.Instance
import Symbolic.Specifications.Model.PQXDH
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import all Init.Data.Array.Attach
import all Init.Data.Array.DecidableEq
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Handshake

/-!
# CLI-Level Reachability of `honestHandshakeWithoutOpkTrace` and `honestHandshakeWithOpkTrace`

Combines `cliTraces_handshake` (`HandshakeCliTraces`), `explains_handshake`, and the
collision-excuses dischargers (`PtNoCollision`, `RecvNoCollision`, `HandshakeCollisionsFalse`,
`HandshakeCollisionsTrue`) to close `CliTraceReachableProof` for both PQXDH + Triple Ratchet
handshake traces.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Handshake

set_option maxRecDepth 200000

open CryptoProofLib.Refinement (ExternInterpretation)
open scoped DY.Libsignal.Composed
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open CryptoVerification.SignalSession (publicBundleOf)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry VisEventKind
   BundlePreKeyIds OpkNamed nextBundleIds
   setupTrace runSteps runTrace stepView runWrapped inputKind
   secretBytes pubBytes ecKey kyberKey slice preKeyWire
   bobDoneBaseKeys PreKeyRep parsePreKeyWire
   BytesMatchEntry DrawsMatch OutputsMatch
   ReadsFaithfully PathFaithfulAt RunMatches MatchesEventsAt MatchesEvents Explains
   getMessageSentAt_attackerKnows
   preKeyRepresentationsOn honestSaltsOf
   BobSessionStartCollidesOrImplicitRejectsOn gamma)
open DY.Libsignal.Composed.Refinement.Cli
  (peerOf bundleBlob runEventOf ReadCollisionCli CollisionAfterExplainedPrefix)
open Symbolic.Tests.Nonvacuity
  (honestHandshakeWithoutOpkTrace honestHandshakeWithOpkTrace)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (opkB o1 stA0 coins0 key0 m0 oOpk stA0Opk coins0Opk key0Opk m0Opk
   t4 t5 t6 t4Opk t5Opk t6Opk t7Opk)
open Symbolic.Proofs.Tests.Nonvacuity (tHandshakeNoOpk)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encMsg parse_encMsg)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (CliTraceReachableProof invertsGuarded_of_noInverts matchesEvents_run1)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp myHooks myInterp_total myInterp_contracts myHooks_agree
   freshBytes pt0 mkRecords mkRecords_wf mySem)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision (not_nextEventCollides_pt)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (not_collisionAfterExplainedPrefix_of_from not_collision_nil
   not_collision_step_run not_collision_step_irrelevant
   not_nextEventCollides_accepted_prekey_no_recv)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel
  (tsEk tsDhsA entByte tapeInitBytes cSend0 rcBytes bE_cli wire0 pkMsg0 wire0_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCliTraces
  (call0 call1 call2 ev0 ev1 ev2 evsOf call0_runInput cliTraces_handshake)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of m1Of m2Of msPrefix2 msOf
   ghostOf ghostOf_compat mySem_eq_comp
   vis1Comp vis2Comp vis3Comp visPrefix2Comp visOfComp
   setupTrace_false_eq setupTrace_true_eq
   m0_next_false m0_next_true m1_next_false m1_next_true m2_next_false m2_next_true
   m0_ok_false m0_ok_true m1_ok_false m1_ok_true m2_ok_false m2_ok_true
   runTrace_msPrefix2_false runTrace_msPrefix2_true
   runTrace_msOf_false runTrace_msOf_true
   vis_m0_false vis_m0_true vis_m1_false vis_m1_true vis_m2_false vis_m2_true
   modelRunWF_msOf modelRunWF_msPrefix2 ghostWF_msOf ghostWF_msPrefix2)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
  (mkRecordsComp mkRecords_eq_comp p0Fields parsePreKeyWire_wire0 honestPreKeyRep)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (not_bobStartCollides_false)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue (not_bobStartCollides_true)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Handshake
  (hsGamma gamma_comp_eq_hsGamma gamma_eq_hsGamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (preKeyHdrBool preKeyRepTableBool preKeyRep_of_tableBool)

/-! ## Table-Evaluated `PreKeyRep` and `BytesMatchEntry` Checkers -/

private def initIdsOf (r : ProtocolSetup) : BundlePreKeyIds :=
  (if r.withOpk then some r.opkId else none, r.spkId, r.kpkId)

theorem honestPreKeyRep_mem_prefix2 (withOpk : Bool) :
    honestPreKeyRep withOpk ∈
      preKeyRepresentationsOn myInterp (mkRecords withOpk) (mySem withOpk)
        (ghostOf withOpk) (runTrace (mkRecords withOpk) (msPrefix2 withOpk)) (wire0 withOpk) := by
  cases withOpk
  · refine preKeyRep_of_tableBool (gamma_eq_hsGamma false)
      (congrArg (fun r => pubBytes myInterp (secretBytes r 0)) (mkRecords_eq_comp false)) ?_ ?_ ?_
      (parse_encMsg stA0 coins0 key0 m0)
      (by rw [mkRecords_eq_comp]; decide +kernel) ?_
    · rw [runTrace_msPrefix2_false]; exact getMessageSentAt_attackerKnows (i := 25) rfl
    · rw [runTrace_msPrefix2_false]; exact getMessageSentAt_attackerKnows (i := 26) rfl
    · rw [runTrace_msPrefix2_false]; exact getMessageSentAt_attackerKnows (i := 37) rfl
    · decide +kernel
  · refine preKeyRep_of_tableBool (gamma_eq_hsGamma true)
      (congrArg (fun r => pubBytes myInterp (secretBytes r 0)) (mkRecords_eq_comp true)) ?_ ?_ ?_
      (parse_encMsg stA0Opk coins0Opk key0Opk m0Opk)
      (by rw [mkRecords_eq_comp]; decide +kernel) ?_
    · rw [runTrace_msPrefix2_true]; exact getMessageSentAt_attackerKnows (i := 29) rfl
    · rw [runTrace_msPrefix2_true]; exact getMessageSentAt_attackerKnows (i := 30) rfl
    · rw [runTrace_msPrefix2_true]; exact getMessageSentAt_attackerKnows (i := 41) rfl
    · decide +kernel

private def bundleSignedMatchAtBool (γ : DY.Bytes → HwBytes) (b : HwBytes)
    (spk spkSig pqpk pqpkSig : DY.Bytes) : Bool :=
  (b.length == preKeyBundleByteLength) &&
    (slice b 46 33 == ecKey (γ spk)) &&
    (slice b 79 64 == γ spkSig) &&
    (slice b 147 1569 == kyberKey (γ pqpk)) &&
    (slice b 1716 64 == γ pqpkSig)

private def bytesMatchEntryAtBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (γ : DY.Bytes → HwBytes) (kb : VisEventKind × HwBytes) (v : VisEntry) : Bool :=
  (kb.1 == v.kind) &&
  let b := kb.2
  match v.layout with
  | .single => v.terms.map γ == [b]
  | .bundle =>
    match v.terms with
    | [spk, spkSig, pqpk, pqpkSig] =>
      bundleSignedMatchAtBool γ b spk spkSig pqpk pqpkSig && (b[4]? == some 0#8)
    | [spk, spkSig, pqpk, pqpkSig, opk] =>
      bundleSignedMatchAtBool γ b spk spkSig pqpk pqpkSig && (b[4]? == some 1#8) &&
        (slice b 9 33 == ecKey (γ opk))
    | _ => false
  | .preKeySend =>
    (kb.1 == .send) &&
    match v.terms with
    | [ek, ct, msg] =>
      b == preKeyWire (if r.withOpk then some r.opkId else none) r.spkId r.kpkId r.regIdA
        (ecKey (pubBytes interp (secretBytes r 0))) (γ ek) (γ ct) (γ msg)
    | _ => false
  | .preKeyRecv =>
    let ikAPub := ecKey (pubBytes interp (secretBytes r 0))
    match v.terms, parsePreKeyWire b with
    | [ek, ct, msg], some p =>
      (p.baseKey.take 33 == ecKey (γ ek)) && (p.kyberCiphertext == some (kyberKey (γ ct))) &&
        (p.message == γ msg) && (p.version == 4) && (p.signedPreKeyId == r.spkId) &&
        (p.kyberPreKeyId == some r.kpkId) && (p.identityKey.take 33 == ikAPub) &&
        p.preKeyId.isNone
    | [ek, ct, msg, _], some p =>
      (p.baseKey.take 33 == ecKey (γ ek)) && (p.kyberCiphertext == some (kyberKey (γ ct))) &&
        (p.message == γ msg) && (p.version == 4) && (p.signedPreKeyId == r.spkId) &&
        (p.kyberPreKeyId == some r.kpkId) && (p.identityKey.take 33 == ikAPub) &&
        (p.preKeyId == some r.opkId) && r.withOpk
    | _, _ => false
  | .fresh n => b.length == n
  | .kyberCoin j =>
    match v.terms with
    | [t] => (b.length == 4) && ((γ t).length == 32) && (b.head? == (γ t)[j]?)
    | _ => false
  | _ => false

private theorem bytesMatchEntry_of_atBool {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {kb : VisEventKind × HwBytes} {v : VisEntry}
    (h : bytesMatchEntryAtBool interp r (gamma interp S g) kb v = true) :
    BytesMatchEntry interp r S g kb.1 kb.2 v
      (if kb.1 == .send then some (initIdsOf r) else none) := by
  unfold bytesMatchEntryAtBool at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hk, hl⟩ := h
  refine ⟨beq_iff_eq.mp hk, ?_⟩
  cases hlay : v.layout with
  | single => rw [hlay] at hl; exact beq_iff_eq.mp hl
  | bundle =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨spk, _ | ⟨spkSig, _ | ⟨pqpk, _ | ⟨pqpkSig, _ | ⟨opk, _ | _⟩⟩⟩⟩⟩ <;>
      rw [hts] at hl <;> try cases hl
    · unfold bundleSignedMatchAtBool at hl; simp only [Bool.and_eq_true, beq_iff_eq] at hl
      exact ⟨⟨hl.1.1.1.1.1, hl.1.1.1.1.2, hl.1.1.1.2, hl.1.1.2, hl.1.2⟩, hl.2⟩
    · unfold bundleSignedMatchAtBool at hl; simp only [Bool.and_eq_true, beq_iff_eq] at hl
      exact ⟨⟨hl.1.1.1.1.1.1, hl.1.1.1.1.1.2, hl.1.1.1.1.2, hl.1.1.1.2, hl.1.1.2⟩, hl.1.2, hl.2⟩
  | preKeySend =>
    rw [hlay] at hl
    simp only [Bool.and_eq_true] at hl
    obtain ⟨hks, hl⟩ := hl
    rw [hks]
    dsimp only [↓reduceIte, initIdsOf]
    rcases hts : v.terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | _⟩⟩⟩ <;> rw [hts] at hl <;> try cases hl
    exact ⟨if r.withOpk then some r.opkId else none, r.spkId, r.kpkId, rfl, beq_iff_eq.mp hl⟩
  | preKeyRecv =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | ⟨opk, _ | _⟩⟩⟩⟩ <;>
      rw [hts] at hl <;> try cases hl
    · cases hp : parsePreKeyWire kb.2 with
      | none => rw [hp] at hl; cases hl
      | some p =>
        rw [hp] at hl
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hl
        obtain ⟨⟨⟨⟨⟨⟨⟨hbk, hct⟩, hmsg⟩, hv⟩, hspk⟩, hkpk⟩, hidA⟩, hopk⟩ := hl
        have hopkF : OpkNamed r kb.2 false := ⟨p, hp, hopk⟩
        exact ⟨⟨p, hp, hbk, hct, hmsg, hv, hspk, hkpk, hidA, false, hopkF⟩, hopkF⟩
    · cases hp : parsePreKeyWire kb.2 with
      | none => rw [hp] at hl; cases hl
      | some p =>
        rw [hp] at hl
        simp only [Bool.and_eq_true, beq_iff_eq] at hl
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨hbk, hct⟩, hmsg⟩, hv⟩, hspk⟩, hkpk⟩, hidA⟩, hopk⟩, hwopk⟩ := hl
        have hopkT : OpkNamed r kb.2 true := ⟨p, hp, hopk, hwopk⟩
        exact ⟨⟨p, hp, hbk, hct, hmsg, hv, hspk, hkpk, hidA, true, hopkT⟩, hopkT⟩
  | fresh n => rw [hlay] at hl; exact beq_iff_eq.mp hl
  | kyberCoin j =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨t, _ | _⟩ <;> rw [hts] at hl <;> try cases hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    exact ⟨hl.1.1, t, rfl, hl.1.2, hl.2⟩
  | _ => rw [hlay] at hl; cases hl

private def forall₂BytesMatchAtBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (γ : DY.Bytes → HwBytes) (kbs : List (VisEventKind × HwBytes)) (vs : List VisEntry) : Bool :=
  (kbs.length == vs.length) && (kbs.zip vs).all fun p => bytesMatchEntryAtBool interp r γ p.1 p.2

private theorem forall₂_bytesMatchEntry_of_atBool {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ {kbs : List (VisEventKind × HwBytes)} {vs : List VisEntry},
      forall₂BytesMatchAtBool interp r (gamma interp S g) kbs vs = true →
      List.Forall₂ (fun kb v =>
        BytesMatchEntry interp r S g kb.1 kb.2 v
          (if kb.1 == .send then some (initIdsOf r) else none)) kbs vs
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [forall₂BytesMatchAtBool] at h
  | _ :: _, [], h => by simp [forall₂BytesMatchAtBool] at h
  | _ :: es, _ :: vs, h => by
    simp only [forall₂BytesMatchAtBool, List.length_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, beq_iff_eq] at h
    exact .cons (bytesMatchEntry_of_atBool h.2.1)
      (forall₂_bytesMatchEntry_of_atBool (by
        simp [forall₂BytesMatchAtBool, Nat.succ.inj h.1, h.2.2]))

private theorem forall₂_split_append {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      xs₁.length = ys₁.length →
      List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) →
      List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | _ :: xs₁, _, _ :: ys₁, _, hlen, .cons hr hrest => by
    obtain ⟨h1, h2⟩ := forall₂_split_append (Nat.succ.inj hlen) hrest
    exact ⟨.cons hr h1, h2⟩

private theorem forall₂_cons_left {α β : Type} {R : α → β → Prop} {a : α} {as : List α}
    {bs : List β} (h : List.Forall₂ R (a :: as) bs) :
    ∃ b bs', bs = b :: bs' ∧ R a b ∧ List.Forall₂ R as bs' := by
  cases h with
  | cons hab hrest => exact ⟨_, _, rfl, hab, hrest⟩

private theorem forall₂_nil_left {α β : Type} {R : α → β → Prop} {bs : List β}
    (h : List.Forall₂ R [] bs) : bs = [] := by
  cases h; rfl

private theorem forall₂_map_left {α α' β : Type} {R : α' → β → Prop} {f : α → α'} :
    ∀ {as : List α} {bs : List β},
      List.Forall₂ R (as.map f) bs → List.Forall₂ (fun a b => R (f a) b) as bs
  | [], _, .nil => .nil
  | _ :: _, _, .cons hab hrest => .cons hab (forall₂_map_left hrest)

private def initRngPieces (withOpk : Bool) : List HwBytes :=
  [freshBytes (tsEk withOpk) 32] ++
    List.replicate 32 (List.replicate 4 (entByte withOpk)) ++
    [freshBytes (tsDhsA withOpk) 32]

private def kbs1 (withOpk : Bool) : List (VisEventKind × HwBytes) :=
  (.recv, bundleBlob (publicBundleOf (bE_cli withOpk))) ::
    (initRngPieces withOpk).map (.rng, ·)

private def kbs2 (withOpk : Bool) : List (VisEventKind × HwBytes) :=
  [(.pt, pt0), (.rng, cSend0.take 32), (.send, wire0 withOpk)]

private def kbs3 (withOpk : Bool) : List (VisEventKind × HwBytes) :=
  [(.recv, wire0 withOpk), (.rng, rcBytes withOpk), (.accept, pt0)]

private def kbsAll (withOpk : Bool) : List (VisEventKind × HwBytes) :=
  (kbs1 withOpk ++ kbs2 withOpk) ++ kbs3 withOpk

private noncomputable def allBytesMatchBool (withOpk : Bool) : Bool :=
  forall₂BytesMatchAtBool myInterp (mkRecordsComp withOpk) (hsGamma withOpk)
    (kbsAll withOpk) (visOfComp withOpk)

private theorem bytesMatch_handshake (withOpk : Bool) :
    List.Forall₂ (fun kb v =>
        BytesMatchEntry myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk) kb.1 kb.2 v
          (if kb.1 == .send then some (initIdsOf (mkRecords withOpk)) else none))
      (kbsAll withOpk) (visOfComp withOpk) := by
  rw [mySem_eq_comp, mkRecords_eq_comp]
  have hb : allBytesMatchBool withOpk = true := by cases withOpk <;> decide +kernel
  unfold allBytesMatchBool at hb
  rw [← gamma_comp_eq_hsGamma withOpk] at hb
  exact forall₂_bytesMatchEntry_of_atBool hb

/-! ## `RunMatches` and `Explains` Proofs -/

private theorem bytesMatch_steps (withOpk : Bool) :
    List.Forall₂ (fun kb v =>
        BytesMatchEntry myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk) kb.1 kb.2 v
          (if kb.1 == .send then some (initIdsOf (mkRecords withOpk)) else none))
      (kbs1 withOpk) (vis1Comp withOpk) ∧
    List.Forall₂ (fun kb v =>
        BytesMatchEntry myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk) kb.1 kb.2 v
          (if kb.1 == .send then some (initIdsOf (mkRecords withOpk)) else none))
      (kbs2 withOpk) (vis2Comp withOpk) ∧
    List.Forall₂ (fun kb v =>
        BytesMatchEntry myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk) kb.1 kb.2 v
          (if kb.1 == .send then some (initIdsOf (mkRecords withOpk)) else none))
      (kbs3 withOpk) (vis3Comp withOpk) := by
  have h12 : (kbs1 withOpk ++ kbs2 withOpk).length = (visPrefix2Comp withOpk).length := by
    cases withOpk <;> decide +kernel
  have h1 : (kbs1 withOpk).length = (vis1Comp withOpk).length := by
    cases withOpk <;> decide +kernel
  obtain ⟨hpre, h3⟩ := forall₂_split_append h12 (bytesMatch_handshake withOpk)
  obtain ⟨h1', h2⟩ := forall₂_split_append h1 hpre
  exact ⟨h1', h2, h3⟩

private theorem runMatches_ev0 (withOpk : Bool) :
    RunMatches myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (setupTrace (mkRecords withOpk)) (m0Of withOpk) (ev0 withOpk) (vis1Comp withOpk) := by
  have hbm1 := (bytesMatch_steps withOpk).1
  unfold kbs1 at hbm1
  obtain ⟨inp0, drs0, hvis1, hinp0, hdrs0⟩ := forall₂_cons_left hbm1
  have hlay : inp0.layout = .bundle := by
    have hh : (vis1Comp withOpk).head? = some inp0 := by simp [hvis1]
    have hb : ((vis1Comp withOpk).head?.map (·.layout)) = some .bundle := by
      cases withOpk <;> decide +kernel
    rw [hh] at hb; injection hb
  refine ⟨by cases withOpk <;> rfl,
    by cases withOpk <;> rfl,
    by cases withOpk <;> trivial,
    by cases withOpk <;> rfl,
    by cases withOpk
       · rw [setupTrace_false_eq]; exact m0_ok_false
       · rw [setupTrace_true_eq]; exact m0_ok_true,
    ⟨[], rfl⟩,
    by cases withOpk
       · rw [setupTrace_false_eq, vis_m0_false]; rfl
       · rw [setupTrace_true_eq, vis_m0_true]; rfl,
    inp0, drs0, [],
    by rw [hvis1, List.append_nil],
    ?_, ?_, rfl,
    by unfold ReadsFaithfully; rw [hlay]; trivial,
    fun _ _ => trivial⟩
  · have hin : (ev0 withOpk).input = bundleBlob (publicBundleOf (bE_cli withOpk)) :=
      call0_runInput withOpk
    have hk : inputKind (ev0 withOpk) = .recv := rfl
    rw [hin, hk]; exact hinp0
  · have hdrs0' := forall₂_map_left (f := (VisEventKind.rng, ·)) hdrs0
    refine ⟨initRngPieces withOpk, by cases withOpk <;> decide, ?_, hdrs0'⟩
    have heq : (initRngPieces withOpk).flatten = tapeInitBytes withOpk := by
      cases withOpk <;> decide
    exact ⟨[], by rw [List.append_nil, heq]; rfl⟩

private theorem runMatches_ev1 (withOpk : Bool) :
    RunMatches myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      ((m0Of withOpk).next (setupTrace (mkRecords withOpk)))
      (m1Of withOpk) (ev1 withOpk) (vis2Comp withOpk)
      (some (initIdsOf (mkRecords withOpk))) := by
  have hbm2 := (bytesMatch_steps withOpk).2.1
  unfold kbs2 at hbm2
  obtain ⟨inp1, r1, hv0, hinp1, hr1⟩ := forall₂_cons_left hbm2
  obtain ⟨dr1, r2, hv1, hdr1, hr2⟩ := forall₂_cons_left hr1
  obtain ⟨out1, r3, hv2, hout1, hr3⟩ := forall₂_cons_left hr2
  have hv3 := forall₂_nil_left hr3
  have hvis2 : vis2Comp withOpk = [inp1, dr1, out1] := by rw [hv0, hv1, hv2, hv3]
  have hlay : inp1.layout = .single := by
    have hh : (vis2Comp withOpk).head? = some inp1 := by simp [hvis2]
    have hb : ((vis2Comp withOpk).head?.map (·.layout)) = some .single := by
      cases withOpk <;> decide +kernel
    rw [hh] at hb; injection hb
  have hw : runWrapped (ev1 withOpk) = true := by
    dsimp only [ev1, runEventOf, call1, runWrapped]
    rw [wire0_eq]; rfl
  refine ⟨by cases withOpk <;> rfl,
    by cases withOpk <;> rfl,
    by cases withOpk <;> trivial,
    by cases withOpk <;> trivial,
    by cases withOpk
       · rw [setupTrace_false_eq, m0_next_false]; exact m1_ok_false
       · rw [setupTrace_true_eq, m0_next_true]; exact m1_ok_true,
    ⟨wire0 withOpk, rfl⟩,
    by rw [hw]
       cases withOpk
       · rw [setupTrace_false_eq, m0_next_false, vis_m1_false]; rfl
       · rw [setupTrace_true_eq, m0_next_true, vis_m1_true]; rfl,
    inp1, [dr1], [out1], hvis2,
    hinp1,
    ⟨[cSend0.take 32], by decide, ⟨cSend0.drop 32, by cases withOpk <;> decide⟩, .cons hdr1 .nil⟩,
    ⟨out1, rfl, hout1⟩,
    by unfold ReadsFaithfully; rw [hlay]; trivial,
    by cases withOpk <;> exact fun _ _ => trivial⟩

private theorem runMatches_ev2 (withOpk : Bool) :
    RunMatches myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (runTrace (mkRecords withOpk) (msPrefix2 withOpk))
      (m2Of withOpk) (ev2 withOpk) (vis3Comp withOpk)
      (some (initIdsOf (mkRecords withOpk))) := by
  have hbm3 := (bytesMatch_steps withOpk).2.2
  unfold kbs3 at hbm3
  obtain ⟨inp2, r1, hv0, hinp2, hr1⟩ := forall₂_cons_left hbm3
  obtain ⟨dr2, r2, hv1, hdr2, hr2⟩ := forall₂_cons_left hr1
  obtain ⟨out2, r3, hv2, hout2, hr3⟩ := forall₂_cons_left hr2
  have hv3 := forall₂_nil_left hr3
  have hvis3 : vis3Comp withOpk = [inp2, dr2, out2] := by rw [hv0, hv1, hv2, hv3]
  have hrf : ReadsFaithfully myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (runTrace (mkRecords withOpk) (msPrefix2 withOpk)) inp2 (ev2 withOpk).input := by
    have hinp2_eq : (vis3Comp withOpk).head? = some inp2 := by simp [hvis3]
    cases withOpk
    · have hh : (vis3Comp false).head? =
          some ⟨.recv, [o1.ek, o1.ct, encMsg stA0 coins0 key0 m0], .preKeyRecv, none⟩ := rfl
      rw [hh, Option.some.injEq] at hinp2_eq
      rw [← hinp2_eq]
      exact honestPreKeyRep_mem_prefix2 false
    · have hh : (vis3Comp true).head? =
          some ⟨.recv, [oOpk.ek, oOpk.ct, encMsg stA0Opk coins0Opk key0Opk m0Opk, dhPk opkB],
            .preKeyRecv, none⟩ := rfl
      rw [hh, Option.some.injEq] at hinp2_eq
      rw [← hinp2_eq]
      exact honestPreKeyRep_mem_prefix2 true
  have hpf : PathFaithfulAt myInterp (mySem withOpk) (ghostOf withOpk)
      (runTrace (mkRecords withOpk) (msPrefix2 withOpk)) (m2Of withOpk) (ev2 withOpk).input := by
    unfold PathFaithfulAt
    intro p _
    cases withOpk
    · have hnil : bobDoneBaseKeys (runTrace (mkRecords false) (msPrefix2 false)) = [] := by
        rw [runTrace_msPrefix2_false]; decide +kernel
      simp only [m2Of, Bool.false_eq_true, ↓reduceIte, hnil]
      rintro ⟨_, h, _⟩; cases h
    · have hnil : bobDoneBaseKeys (runTrace (mkRecords true) (msPrefix2 true)) = [] := by
        rw [runTrace_msPrefix2_true]; decide +kernel
      simp only [m2Of, ↓reduceIte, hnil]
      rintro ⟨_, h, _⟩; cases h
  refine ⟨by cases withOpk <;> rfl,
    by cases withOpk <;> rfl,
    by cases withOpk <;> trivial,
    by cases withOpk <;> rfl,
    by cases withOpk
       · rw [runTrace_msPrefix2_false]; exact m2_ok_false
       · rw [runTrace_msPrefix2_true]; exact m2_ok_true,
    ⟨pt0, rfl⟩,
    by cases withOpk
       · rw [runTrace_msPrefix2_false, vis_m2_false]; rfl
       · rw [runTrace_msPrefix2_true, vis_m2_true]; rfl,
    inp2, [dr2], [out2], hvis3,
    hinp2,
    ⟨[rcBytes withOpk], by cases withOpk <;> decide, ⟨[], by simp [ev2, runEventOf, call2]⟩,
      .cons hdr2 .nil⟩,
    ⟨out2, rfl, hout2⟩,
    hrf, hpf⟩

private theorem nextBundleIds_ev0 (withOpk : Bool) :
    nextBundleIds none (ev0 withOpk) = some (initIdsOf (mkRecords withOpk)) := by
  have hin : (ev0 withOpk).input = bundleBlob (publicBundleOf (bE_cli withOpk)) :=
    call0_runInput withOpk
  have hcmd : ∃ peer spk, (ev0 withOpk).cmd = .init peer spk := by
    cases withOpk <;> exact ⟨_, _, rfl⟩
  obtain ⟨peer, spk, hcmd⟩ := hcmd
  simp only [nextBundleIds, hcmd, hin, mkRecords_eq_comp, initIdsOf]
  cases withOpk <;> decide +kernel

private theorem nextBundleIds_ev1 (withOpk : Bool) (ids : Option BundlePreKeyIds) :
    nextBundleIds ids (ev1 withOpk) = ids := by
  cases withOpk <;> rfl

private theorem nextBundleIds_ev2 (withOpk : Bool) (ids : Option BundlePreKeyIds) :
    nextBundleIds ids (ev2 withOpk) = ids := by
  cases withOpk <;> rfl

theorem explains_prefix2 (withOpk : Bool) :
    Explains myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (msPrefix2 withOpk) (visPrefix2Comp withOpk)
      [.run (ev0 withOpk), .run (ev1 withOpk)] := by
  refine ⟨ghostOf_compat withOpk, ghostWF_msPrefix2 withOpk, modelRunWF_msPrefix2 withOpk, ?_⟩
  have hnil : MatchesEventsAt myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (nextBundleIds (some (initIdsOf (mkRecords withOpk))) (ev1 withOpk))
      ((m1Of withOpk).next ((m0Of withOpk).next (setupTrace (mkRecords withOpk)))) [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have h1 := matchesEvents_run1 (runMatches_ev1 withOpk) hnil
  rw [List.append_nil, ← nextBundleIds_ev0 withOpk] at h1
  exact matchesEvents_run1 (runMatches_ev0 withOpk) h1

theorem explains_handshake (withOpk : Bool) :
    Explains myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (msOf withOpk) (visOfComp withOpk) (evsOf withOpk) := by
  refine ⟨ghostOf_compat withOpk, ghostWF_msOf withOpk, modelRunWF_msOf withOpk, ?_⟩
  have hnil : MatchesEventsAt myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk)
      (nextBundleIds (some (initIdsOf (mkRecords withOpk))) (ev2 withOpk))
      ((m2Of withOpk).next (runTrace (mkRecords withOpk) (msPrefix2 withOpk))) [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have h2 := matchesEvents_run1 (runMatches_ev2 withOpk) hnil
  rw [List.append_nil] at h2
  have htr : runTrace (mkRecords withOpk) (msPrefix2 withOpk) =
      (m1Of withOpk).next ((m0Of withOpk).next (setupTrace (mkRecords withOpk))) := rfl
  rw [htr, ← nextBundleIds_ev1 withOpk (some (initIdsOf (mkRecords withOpk)))] at h2
  have h1 := matchesEvents_run1 (runMatches_ev1 withOpk) h2
  rw [← nextBundleIds_ev0 withOpk] at h1
  have h0 := matchesEvents_run1 (runMatches_ev0 withOpk) h1
  unfold visOfComp visPrefix2Comp
  rw [List.append_assoc]
  exact h0

/-! ## Non-Collision Proof and Top-Level `CliTraceReachableProof` Theorems -/

private theorem not_readCollisionCli_prefix2 (withOpk : Bool) :
    ¬ ReadCollisionCli myInterp (mkRecords withOpk) (mySem withOpk)
        (ghostOf withOpk) (msPrefix2 withOpk) [.run (ev0 withOpk), .run (ev1 withOpk)] := by
  rintro ⟨_, _, _, ss₁, ss₂, m, _, _, _, _, _, _, hss, _, _, _, _, hdec, _⟩
  have hm : m ∈ msPrefix2 withOpk := by rw [hss]; simp
  simp only [msPrefix2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> cases withOpk <;> cases hdec

private theorem not_bobStartCollides_handshake (withOpk : Bool) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn myInterp (mkRecords withOpk) (mySem withOpk)
        (ghostOf withOpk) (runTrace (mkRecords withOpk) (msPrefix2 withOpk))
        (visPrefix2Comp withOpk) (honestSaltsOf (mkRecords withOpk) (msPrefix2 withOpk))
        (p0Fields withOpk) (honestPreKeyRep withOpk) := by
  cases withOpk
  · exact not_bobStartCollides_false
  · exact not_bobStartCollides_true

theorem not_collisionAfterExplainedPrefix_handshake (withOpk : Bool) :
    ¬ CollisionAfterExplainedPrefix myInterp (mkRecords withOpk) (mySem withOpk)
        (evsOf withOpk) := by
  apply not_collisionAfterExplainedPrefix_of_from
  unfold evsOf
  apply not_collision_step_irrelevant (by cases withOpk <;> rfl)
  apply not_collision_step_run
  · intro g ss vis hExp
    dsimp only [List.nil_append] at hExp ⊢
    exact not_nextEventCollides_pt
      (by cases withOpk <;> rfl)
      (by cases withOpk <;> decide)
      (by cases withOpk <;> decide)
      (by cases withOpk <;> decide)
      hExp
  apply not_collision_step_run
  · intro g ss vis hOuterExp
    dsimp only [List.nil_append, List.cons_append] at hOuterExp ⊢
    exact not_nextEventCollides_accepted_prekey_no_recv
      (peer := peerOf (mkRecords withOpk) "bob")
      (body := (pkMsg0 withOpk).bytes)
      (p := p0Fields withOpk)
      rfl
      (wire0_eq withOpk)
      hOuterExp
      (by cases withOpk <;> rfl)
      (wire0_eq withOpk ▸ parsePreKeyWire_wire0 withOpk)
      (explains_prefix2 withOpk)
      (not_readCollisionCli_prefix2 withOpk)
      (wire0_eq withOpk ▸ honestPreKeyRep_mem_prefix2 withOpk)
      (not_bobStartCollides_handshake withOpk)
  exact not_collision_nil

private theorem evsOf_exit_zero (withOpk : Bool) :
    ∀ ev : RunEvent, .run ev ∈ evsOf withOpk → ∃ out, ev.exit = some (0, out) := by
  intro ev h
  simp only [evsOf, List.mem_cons, List.not_mem_nil, or_false, CliEvent.run.injEq] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨[], rfl⟩
  · exact ⟨wire0 withOpk, rfl⟩
  · exact ⟨pt0, rfl⟩

theorem cliReachable_honestHandshakeWithoutOpkTrace :
    CliTraceReachableProof honestHandshakeWithoutOpkTrace :=
  ⟨myInterp, myHooks, mkRecords false, mySem false,
    evsOf false, ghostOf false, msOf false, visOfComp false,
    cliTraces_handshake false,
    evsOf_exit_zero false,
    explains_handshake false,
    runTrace_msOf_false,
    myInterp_total, myInterp_contracts, myHooks_agree, mkRecords_wf false,
    invertsGuarded_of_noInverts rfl,
    by decide +kernel,
    not_collisionAfterExplainedPrefix_handshake false⟩

theorem cliReachable_honestHandshakeWithOpkTrace :
    CliTraceReachableProof honestHandshakeWithOpkTrace :=
  ⟨myInterp, myHooks, mkRecords true, mySem true,
    evsOf true, ghostOf true, msOf true, visOfComp true,
    cliTraces_handshake true,
    evsOf_exit_zero true,
    explains_handshake true,
    runTrace_msOf_true,
    myInterp_total, myInterp_contracts, myHooks_agree, mkRecords_wf true,
    invertsGuarded_of_noInverts rfl,
    by decide +kernel,
    not_collisionAfterExplainedPrefix_handshake true⟩

end Symbolic.Proofs.Tests.CliNonvacuity.Handshake
