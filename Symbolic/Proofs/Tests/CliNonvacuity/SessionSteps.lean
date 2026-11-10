/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
import all DY.Bytes.Basic
import all DY.ALaCarte.Basic
import all DY.ALaCarte.DecidableEq
import all DY.ALaCarte.Ordering
import all DY.Misc.Instances
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
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
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli

/-!
# `Explains` and Representation Witnesses Across Session Prefixes

Provides a table-backed `Bool` checker for `BytesMatchEntry` across all 60 `VisEntry`s of
`visAt 11`, symbolic message/pre-key representation witnesses, and step-by-step `RunMatches`,
`EnvMatches`, `MatchesEvents`, and `Explains` proofs for every prefix of
`(msExposed, visAt 11, evsExposed)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps

set_option maxRecDepth 200000

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEventKind VisEntry
   BundlePreKeyIds OpkNamed nextBundleIds sessionHasDecrypted
   setupTrace secretBytes pubBytes ecKey kyberKey slice clamp randTerm
   runSteps runTrace stepView encDraws encSendEntry pendingPreKey decVis exposures
   bobDoneBaseKeys sessionBaseKeys
   PreKeyFields PreKeyRep parsePreKeyWire preKeyWire
   BytesMatchEntry ReadsFaithfully PathFaithfulAt DrawsMatch OutputsMatch
   RunMatches EnvMatches MatchesEventsAt MatchesEvents Explains
   recvRepresentationsOn preKeyRepresentationsOn gamma)
open DY.Libsignal.Composed.Refinement.Cli (bundleBlob)
open CryptoVerification.SignalSession (publicBundleOf)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (matchesEvents_run1 matchesEvents_env)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
  (beqBareOptFast beqBareOptFast_true decEqBytesFast
   instDecidableEqBytes_eq_fast instDecidableEqBytes_pq instDecidableEqBytes_composed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (r0Comp r0_eq_comp S0Comp S0_eq_comp myGhostComp myGhost_eq_comp
   attackerKnows_of_getMessageSentAt)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli
  (cliGamma gamma_comp_eq_cliGamma gamma_eq_cliGamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (recvRepTableBool recvRep_of_tableBool preKeyHdrBool preKeyRepTableBool preKeyRep_of_tableBool)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (decide_nvVec3168_self decide_nvEk1152_self decide_nvDk2400_self
   decide_nvEk1152_nvDk2400 decide_nvDk2400_nvEk1152)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encSig parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
   stA0 coins0 key0 m0 stA1 coins1 key1 m1 stB2 coins2 key2 m2 stA4 coins3 key3 m3)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 S0 myGhost myGhost_compat setupTrace_r0_eq
   cSend0 cSend1 cSendReply0 cSend2 rc3Bytes rc6Bytes rc8Bytes
   move0_init move1_enc0 move2_enc1 move3_bobStart move4_dec1 move5_encReply0
   move6_decReply0 move7_leakCkr move8_leakCks move9_enc2 move10_dec2
   msHonest msLeaks msTail msExposed
   move0_next move1_next move2_next move3_next move4_next
   move5_next move6_next move7_next move8_next move9_next move10_next
   move0_ok move1_ok move2_ok move3_ok move4_ok
   move5_ok move6_ok move7_ok move8_ok move9_ok move10_ok)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04 (bE_cli pkMsg0 pkMsg1 wire0 wire1)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel58 (bodyReply0 body2 wireReply0 wire2)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces
  (ckrBytes cksBytes
   runEv0 runEv1 runEv2 runEv3 runEv4 runEv5 runEv6 runEv7 runEv8
   runEv0_input leakEvCkr leakEvCks evsHonest evsExposed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (initPieces msPre3 msPre4 msPre5 msPre6 msPre8
   evsPre3 evsPre4 evsPre5 evsPre6 evsPre8
   trAt visBetween encSendBetween visSteps visAt
   runTrace_take_eq modelRunWF_take ghostWF_visAt)

/-! ## Table-Backed `BytesMatchEntry` `Bool` Checker -/

private def initIds0 (r : ProtocolSetup) : BundlePreKeyIds :=
  (none, r.spkId, r.kpkId)

private def bundleSignedKeysMatchGamma (γ : DY.Bytes → HwBytes) (b : HwBytes)
    (spk spkSig pqpk pqpkSig : DY.Bytes) : Bool :=
  (b.length == preKeyBundleByteLength) &&
  (slice b 46 33 == ecKey (γ spk)) &&
  (slice b 79 64 == γ spkSig) &&
  (slice b 147 1569 == kyberKey (γ pqpk)) &&
  (slice b 1716 64 == γ pqpkSig)

private def bytesMatchEntryGamma (interp : ExternInterpretation) (r : ProtocolSetup)
    (γ : DY.Bytes → HwBytes) (k : VisEventKind) (b : HwBytes) (v : VisEntry) : Bool :=
  (k == v.kind) &&
  match v.layout with
  | .single => v.terms.map γ == [b]
  | .whisper =>
    match v.terms with
    | [t] => b == wireWhisperTag :: γ t
    | _ => false
  | .bundle =>
    match v.terms with
    | [spk, spkSig, pqpk, pqpkSig] =>
      bundleSignedKeysMatchGamma γ b spk spkSig pqpk pqpkSig && (b[4]? == some 0#8)
    | _ => false
  | .preKeySend =>
    (k == .send) &&
    match v.terms with
    | [ek, ct, msg] =>
      b == preKeyWire none r.spkId r.kpkId r.regIdA
        (ecKey (pubBytes interp (secretBytes r 0))) (γ ek) (γ ct) (γ msg)
    | _ => false
  | .preKeyRecv =>
    let ikAPub := ecKey (pubBytes interp (secretBytes r 0))
    match v.terms, parsePreKeyWire b with
    | [ek, ct, msg], some p =>
      (p.baseKey.take 33 == ecKey (γ ek)) &&
      (p.kyberCiphertext == some (kyberKey (γ ct))) &&
      (p.message == γ msg) &&
      (p.version == 4) &&
      (p.signedPreKeyId == r.spkId) &&
      (p.kyberPreKeyId == some r.kpkId) &&
      (p.identityKey.take 33 == ikAPub) &&
      p.preKeyId.isNone
    | _, _ => false
  | .preKeyInner eks =>
    let ikAPub := ecKey (pubBytes interp (secretBytes r 0))
    match v.terms, parsePreKeyWire b with
    | [t], some p =>
      (p.version == 4) &&
      (p.identityKey.take 33 == ikAPub) &&
      (eks.any fun ek => p.baseKey.take 33 == ecKey (γ ek)) &&
      (p.message == γ t)
    | _, _ => false
  | .fresh n => b.length == n
  | .kyberCoin j =>
    match v.terms with
    | [t] => (b.length == 4) && ((γ t).length == 32) && (b.head? == (γ t)[j]?)
    | _ => false
  | .unconstrained => true
  | .leakPq pq => if pq then b == r.kyberSecB else v.terms.map γ == [b]
  | .leakRecord =>
    match v.terms with
    | [t] => (b == γ t) || (b == clamp (γ t))
    | _ => false

private theorem bytesMatchEntry_of_bool {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {γ : DY.Bytes → HwBytes}
    {k : VisEventKind} {b : HwBytes} {v : VisEntry}
    (hγ : gamma interp S g = γ)
    (h : bytesMatchEntryGamma interp r γ k b v = true) :
    BytesMatchEntry interp r S g k b v (if k == .send then some (initIds0 r) else none) := by
  rw [← hγ] at h
  unfold bytesMatchEntryGamma at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hk, hl⟩ := h
  refine ⟨beq_iff_eq.mp hk, ?_⟩
  cases hlay : v.layout with
  | single =>
    rw [hlay] at hl
    exact beq_iff_eq.mp hl
  | whisper =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨t, _ | _⟩ <;> rw [hts] at hl <;> try cases hl
    exact ⟨t, rfl, beq_iff_eq.mp hl⟩
  | bundle =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨spk, _ | ⟨spkSig, _ | ⟨pqpk, _ | ⟨pqpkSig, _ | _⟩⟩⟩⟩ <;>
      rw [hts] at hl <;> try cases hl
    unfold bundleSignedKeysMatchGamma at hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    exact ⟨⟨hl.1.1.1.1.1, hl.1.1.1.1.2, hl.1.1.1.2, hl.1.1.2, hl.1.2⟩, hl.2⟩
  | preKeySend =>
    rw [hlay] at hl
    simp only [Bool.and_eq_true] at hl
    obtain ⟨hks, hl⟩ := hl
    rw [hks]
    dsimp only [↓reduceIte, initIds0]
    rcases hts : v.terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | _⟩⟩⟩ <;>
      rw [hts] at hl <;> try cases hl
    exact ⟨none, r.spkId, r.kpkId, rfl, beq_iff_eq.mp hl⟩
  | preKeyRecv =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | _⟩⟩⟩ <;>
      rw [hts] at hl <;> try cases hl
    cases hp : parsePreKeyWire b with
    | none => rw [hp] at hl; cases hl
    | some p =>
      rw [hp] at hl
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hl
      obtain ⟨⟨⟨⟨⟨⟨⟨hbk, hct⟩, hmsg⟩, hv⟩, hspk⟩, hkpk⟩, hidA⟩, hopk⟩ := hl
      have hopkF : OpkNamed r b false := ⟨p, hp, hopk⟩
      exact ⟨⟨p, hp, hbk, hct, hmsg, hv, hspk, hkpk, hidA, false, hopkF⟩, hopkF⟩
  | preKeyInner eks =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨t, _ | _⟩ <;> rw [hts] at hl <;> try cases hl
    cases hp : parsePreKeyWire b with
    | none => rw [hp] at hl; cases hl
    | some p =>
      rw [hp] at hl
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hl
      obtain ⟨⟨⟨hv, hidA⟩, hex⟩, hmsg⟩ := hl
      exact ⟨t, p, rfl, rfl, hv, hidA, hex, hmsg⟩
  | fresh n =>
    rw [hlay] at hl
    exact beq_iff_eq.mp hl
  | kyberCoin j =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨t, _ | _⟩ <;> rw [hts] at hl <;> try cases hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    exact ⟨hl.1.1, t, rfl, hl.1.2, hl.2⟩
  | unconstrained => trivial
  | leakPq pq =>
    rw [hlay] at hl
    cases pq <;> exact beq_iff_eq.mp hl
  | leakRecord =>
    rw [hlay] at hl
    rcases hts : v.terms with _ | ⟨t, _ | _⟩ <;> rw [hts] at hl <;> try cases hl
    simp only [Bool.or_eq_true, beq_iff_eq] at hl
    exact ⟨t, rfl, hl⟩

private def forall₂BytesMatchAtBool (interp : ExternInterpretation) (r : ProtocolSetup)
    (γ : DY.Bytes → HwBytes)
    (kbs : List (VisEventKind × HwBytes)) (vs : List VisEntry) : Bool :=
  (kbs.length == vs.length) &&
    (kbs.zip vs).all fun p => bytesMatchEntryGamma interp r γ p.1.1 p.1.2 p.2

private theorem forall₂_bytesMatchEntry_of_bool {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {γ : DY.Bytes → HwBytes}
    (hγ : gamma interp S g = γ) :
    ∀ {kbs : List (VisEventKind × HwBytes)} {vs : List VisEntry},
      forall₂BytesMatchAtBool interp r γ kbs vs = true →
      List.Forall₂ (fun (kb : VisEventKind × HwBytes) v =>
        BytesMatchEntry interp r S g kb.1 kb.2 v
          (if kb.1 == .send then some (initIds0 r) else none)) kbs vs
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [forall₂BytesMatchAtBool] at h
  | _ :: _, [], h => by simp [forall₂BytesMatchAtBool] at h
  | _ :: kbs, _ :: vs, h => by
    simp only [forall₂BytesMatchAtBool, List.length_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, beq_iff_eq] at h
    exact .cons (bytesMatchEntry_of_bool hγ h.2.1)
      (forall₂_bytesMatchEntry_of_bool hγ (by
        simp only [forall₂BytesMatchAtBool, Nat.succ.inj h.1, beq_self_eq_true, Bool.true_and]
        exact h.2.2))

/-! ## Symbolic Terms, Fast Evaluators, and Representation Witnesses -/

def ekTerm : DY.Bytes := (t5.getMessageSentAt 25).getD (randTerm 0 0)
def ctTerm : DY.Bytes := (t5.getMessageSentAt 26).getD (randTerm 0 0)
def msg0Term : DY.Bytes := (t6.getMessageSentAt 37).getD (randTerm 0 0)
def msg1Term : DY.Bytes := (t7.getMessageSentAt 44).getD (randTerm 0 0)
def msgReply0Term : DY.Bytes := (t10.getMessageSentAt 64).getD (randTerm 0 0)
def msg2Term : DY.Bytes := (t14.getMessageSentAt 82).getD (randTerm 0 0)
def x3Rep : PreKeyRep := ⟨ekTerm, ctTerm, msg0Term⟩
def x4Rep : PreKeyRep := ⟨ekTerm, ctTerm, msg1Term⟩

def msg0Sig : TRSignalMsg := encSig stA0 coins0 key0 m0
def msg1Sig : TRSignalMsg := encSig stA1 coins1 key1 m1
def msgReply0Sig : TRSignalMsg := encSig stB2 coins2 key2 m2
def msg2Sig : TRSignalMsg := encSig stA4 coins3 key3 m3

theorem parse_msg0Term : parseTrSignalMsg msg0Term = some msg0Sig :=
  parse_encMsg stA0 coins0 key0 m0
theorem parse_msg1Term : parseTrSignalMsg msg1Term = some msg1Sig :=
  parse_encMsg stA1 coins1 key1 m1
theorem parse_msgReply0Term : parseTrSignalMsg msgReply0Term = some msgReply0Sig :=
  parse_encMsg stB2 coins2 key2 m2
theorem parse_msg2Term : parseTrSignalMsg msg2Term = some msg2Sig :=
  parse_encMsg stA4 coins3 key3 m3

unseal DY.Bytes in
noncomputable def kemDecapFast (sk cipher : DY.Bytes) : Option DY.Bytes :=
  match cipher.view? DY.PQKem.Encap.SubF with
  | some { pk, entropy } =>
    match pk.view? DY.PQKem.Pk.SubF with
    | some { sk := sk' } =>
      if @decide (sk = sk') (decEqBytesFast sk sk') then
        some ({ pk, entropy } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack
      else none
    | none => none
  | none => none

unseal DY.Bytes in
theorem kemDecap_eq_fast : (@DY.PQKem.kemDecap DY.Bytes _) = kemDecapFast := by
  funext sk cipher
  dsimp only [DY.PQKem.kemDecap, DY.PQKem.instCanPQKemBytes, kemDecapFast]
  rcases cipher.view? DY.PQKem.Encap.SubF with _ | ⟨⟨pk, entropy⟩⟩
  · rfl
  · dsimp only
    rcases pk.view? DY.PQKem.Pk.SubF with _ | ⟨⟨sk'⟩⟩
    · rfl
    · dsimp only
      cases decEqBytesFast sk sk' with
      | isFalse h => simp [h]
      | isTrue h => simp [h]

unseal DY.Bytes in
noncomputable def symDecFast (key iv ct : DY.Bytes) : Option DY.Bytes :=
  match ct.view? DY.SymEnc.Enc.SubF with
  | some { key := key', iv := iv', msg } =>
    if @decide (key = key') (decEqBytesFast key key') &&
       @decide (iv = iv') (decEqBytesFast iv iv') then some msg else none
  | none => none

unseal DY.Bytes in
theorem symDec_eq_fast : (@DY.SymEnc.symDec DY.Bytes _) = symDecFast := by
  funext key iv ct
  dsimp only [DY.SymEnc.symDec, DY.SymEnc.instCanSymEncBytes, symDecFast]
  rcases ct.view? DY.SymEnc.Enc.SubF with _ | ⟨⟨key', iv', msg⟩⟩
  · rfl
  · dsimp only
    cases decEqBytesFast key key' with
    | isFalse hk => simp [hk]
    | isTrue hk =>
      cases decEqBytesFast iv iv' with
      | isFalse hiv => simp [hk, hiv]
      | isTrue hiv => simp [hk, hiv]

noncomputable def decEqSessionInfoFast :
    DecidableEq (@DY.Libsignal.TripleRatchet.SessionInfo
      (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes)) :=
  fun a b =>
    match decEqBytesFast a.sid b.sid,
        (inferInstance : Decidable (a.initiator = b.initiator ∧ a.me = b.me ∧ a.peer = b.peer)) with
    | isTrue h1, isTrue ⟨h2, h3, h4⟩ =>
      isTrue (by cases a; cases b; dsimp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl)
    | isFalse h1, _ => isFalse (fun h => h1 (congrArg (·.sid) h))
    | _, isFalse h2 =>
      isFalse (fun h => h2 ⟨congrArg (·.initiator) h, congrArg (·.me) h, congrArg (·.peer) h⟩)

theorem ite_sessionInfo_eq_fast {α : Sort _}
    (a b : @DY.Libsignal.TripleRatchet.SessionInfo
      (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes))
    (t e : α) :
    @ite α (a = b)
      (@DY.Libsignal.TripleRatchet.instDecidableEqSessionInfo
        (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes) a b)
      t e =
    if (@decide (a = b) (decEqSessionInfoFast a b)) = true then t else e := by
  cases decEqSessionInfoFast a b with
  | isFalse hf => simp [hf]
  | isTrue ht => simp [ht]

theorem decide_sessionInfo_eq_fast
    (a b : @DY.Libsignal.TripleRatchet.SessionInfo
      (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes)) :
    @decide (a = b)
      (@DY.Libsignal.TripleRatchet.instDecidableEqSessionInfo
        (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes) a b) =
    @decide (a = b) (decEqSessionInfoFast a b) := by
  cases decEqSessionInfoFast a b with
  | isFalse hf => simp [hf]
  | isTrue ht => simp [ht]

theorem ite_bytes_composed_eq_fast {α : Sort _} (a b : DY.Bytes) (t e : α) :
    @ite α (a = b)
      (@DY.instDecidableEqBytes DY.Libsignal.Composed.instBytesFunctor_symbolic a b) t e =
    if (@decide (a = b) (decEqBytesFast a b)) = true then t else e := by
  cases decEqBytesFast a b with
  | isFalse hf => simp [hf]
  | isTrue ht => simp [ht]

theorem ite_bytes_tr_eq_fast {α : Sort _} (a b : DY.Bytes) (t e : α) :
    @ite α (a = b)
      (@DY.instDecidableEqBytes
        (@DY.Libsignal.TripleRatchet.HasExecBytes.bytesFunc
          (@DY.Libsignal.Composed.HasExecBytes.toTRExecBytes DY.Libsignal.Composed.instHasExecBytes))
        a b) t e =
    if (@decide (a = b) (decEqBytesFast a b)) = true then t else e := by
  cases decEqBytesFast a b with
  | isFalse hf => simp [hf]
  | isTrue ht => simp [ht]

theorem setupTrace_r0Comp : setupTrace r0Comp = t4 := by
  rw [← r0_eq_comp]
  exact setupTrace_r0_eq

local macro "close_eval" : tactic =>
  `(tactic| (
    try simp (config := { zeta := false }) only [S0_eq_comp]
    try simp (config := { zeta := false }) only [r0_eq_comp]
    try simp (config := { zeta := false }) only [myGhost_eq_comp]
    try simp (config := { zeta := false }) only [gamma_comp_eq_cliGamma]
    try simp (config := { zeta := false }) only [gamma_eq_cliGamma]
    try simp (config := { zeta := false }) only [setupTrace_r0Comp]
    try dsimp (config := { zeta := false }) only [
      r0Comp, S0Comp, myGhostComp, DY.PQKem.instCanPQKemBytes,
      DY.Spqr.spqrRecv, DY.Spqr.spqrEmptyMsg, DY.Spqr.spqrParamsDir?,
      DY.SymEnc.instCanSymEncBytes,
      List.contains, List.elem, instBEqOfDecidableEq, Option.instBEq]
    try simp (config := { zeta := false }) only [kemDecap_eq_fast]
    try simp (config := { zeta := false }) only [symDec_eq_fast]
    try simp (config := { zeta := false }) only [instDecidableEqBytes_composed]
    try simp (config := { zeta := false }) only [instDecidableEqBytes_eq_fast]
    try simp (config := { zeta := false }) only [instDecidableEqBytes_pq]
    try simp (config := { zeta := false }) only [decide_nvVec3168_self]
    try simp (config := { zeta := false }) only [decide_nvEk1152_self]
    try simp (config := { zeta := false }) only [decide_nvDk2400_self]
    try simp (config := { zeta := false }) only [decide_nvEk1152_nvDk2400]
    try simp (config := { zeta := false }) only [decide_nvDk2400_nvEk1152]))

private theorem x3Rep_ok :
    preKeyRepTableBool cliGamma (wirePrekeyTag :: pkMsg0.bytes) x3Rep msg0Sig = true := by
  decide +kernel

private theorem x4Rep_ok :
    preKeyRepTableBool cliGamma (wirePrekeyTag :: pkMsg1.bytes) x4Rep msg1Sig = true := by
  decide +kernel

private theorem msg1_ok :
    recvRepTableBool cliGamma pkMsg1.inner msg1Term msg1Sig = true := by
  decide +kernel

private theorem msgReply0_ok :
    recvRepTableBool cliGamma bodyReply0 msgReply0Term msgReply0Sig = true := by
  decide +kernel

private theorem msg2_ok :
    recvRepTableBool cliGamma body2 msg2Term msg2Sig = true := by
  decide +kernel

theorem x3Rep_mem_pre3 :
    x3Rep ∈ preKeyRepresentationsOn myInterp r0 S0 myGhost (runTrace r0 msPre3)
      (wirePrekeyTag :: pkMsg0.bytes) := by
  have htr : runTrace r0 msPre3 = trAt 3 := runTrace_take_eq 3
  refine preKeyRep_of_tableBool gamma_eq_cliGamma
    (congrArg (fun r => pubBytes myInterp (secretBytes r 0)) r0_eq_comp)
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 25) rfl)
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 26) rfl)
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 37) rfl)
    parse_msg0Term (by rw [r0_eq_comp]; decide +kernel) x3Rep_ok

theorem x4Rep_mem_pre4 :
    x4Rep ∈ preKeyRepresentationsOn myInterp r0 S0 myGhost (runTrace r0 msPre4)
      (wirePrekeyTag :: pkMsg1.bytes) := by
  have htr : runTrace r0 msPre4 = trAt 4 := runTrace_take_eq 4
  refine preKeyRep_of_tableBool gamma_eq_cliGamma
    (congrArg (fun r => pubBytes myInterp (secretBytes r 0)) r0_eq_comp)
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 25) rfl)
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 26) rfl)
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 44) rfl)
    parse_msg1Term (by rw [r0_eq_comp]; decide +kernel) x4Rep_ok

private theorem parse_pkMsg1_message :
    (parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes)).map (·.message) = some pkMsg1.inner := by
  decide +kernel

theorem msg1Term_mem_pre4 {p : PreKeyFields}
    (hp : parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes) = some p) :
    msg1Term ∈ recvRepresentationsOn myInterp S0 myGhost (runTrace r0 msPre4) p.message := by
  have hmsg := parse_pkMsg1_message
  rw [hp] at hmsg; dsimp only [Option.map] at hmsg; rw [Option.some.inj hmsg]
  have htr : runTrace r0 msPre4 = trAt 4 := runTrace_take_eq 4
  exact recvRep_of_tableBool gamma_eq_cliGamma
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 44) rfl)
    parse_msg1Term msg1_ok

theorem msgReply0Term_mem_pre6 :
    msgReply0Term ∈ recvRepresentationsOn myInterp S0 myGhost (runTrace r0 msPre6) bodyReply0 := by
  have htr : runTrace r0 msPre6 = trAt 6 := runTrace_take_eq 6
  exact recvRep_of_tableBool gamma_eq_cliGamma
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 64) rfl)
    parse_msgReply0Term msgReply0_ok

theorem msg2Term_mem_pre8 :
    msg2Term ∈ recvRepresentationsOn myInterp S0 myGhost (runTrace r0 msPre8) body2 := by
  have htr : runTrace r0 msPre8 = trAt 10 := runTrace_take_eq 10
  exact recvRep_of_tableBool gamma_eq_cliGamma
    (htr ▸ attackerKnows_of_getMessageSentAt (idx := 82) rfl)
    parse_msg2Term msg2_ok

/-! ## `RunMatches`, `EnvMatches`, `MatchesEvents`, and `Explains` Across Prefixes -/

private abbrev BMatch (kb : VisEventKind × HwBytes) (v : VisEntry) : Prop :=
  BytesMatchEntry myInterp r0 S0 myGhost kb.1 kb.2 v
    (if kb.1 == .send then some (initIds0 r0) else none)

private def kb0 : List (VisEventKind × HwBytes) :=
  (.recv, bundleBlob (publicBundleOf bE_cli)) :: initPieces.map (.rng, ·)
private def kb1 : List (VisEventKind × HwBytes) :=
  [(.pt, pt0), (.rng, cSend0.take 32), (.send, wire0)]
private def kb2 : List (VisEventKind × HwBytes) := [(.pt, pt1), (.rng, cSend1.take 32), (.send, wire1)]
private def kb3 : List (VisEventKind × HwBytes) := [(.recv, wire0), (.rng, rc3Bytes), (.accept, pt0)]
private def kb4 : List (VisEventKind × HwBytes) := [(.recv, wire1), (.accept, pt1)]
private def kb5 : List (VisEventKind × HwBytes) := [(.pt, ptReply0), (.rng, cSendReply0.take 32), (.send, wireReply0)]
private def kb6 : List (VisEventKind × HwBytes) := [(.recv, wireReply0), (.rng, rc6Bytes), (.accept, ptReply0)]
private def kb7 : List (VisEventKind × HwBytes) := [(.leak, ckrBytes)]
private def kb8 : List (VisEventKind × HwBytes) := [(.leak, cksBytes)]
private def kb9 : List (VisEventKind × HwBytes) := [(.pt, pt2), (.rng, cSend2.take 32), (.send, wire2)]
private def kb10 : List (VisEventKind × HwBytes) := [(.recv, wire2), (.rng, rc8Bytes), (.accept, pt2)]
private def kbAll : List (VisEventKind × HwBytes) :=
  [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, kb8, kb9, kb10].flatten

private theorem bytesMatch_all : List.Forall₂ BMatch kbAll (visAt 11) := by
  unfold BMatch
  rw [r0_eq_comp]
  refine forall₂_bytesMatchEntry_of_bool gamma_eq_cliGamma ?_
  generalize h1 : kbAll = kbs
  generalize h2 : visAt 11 = vs
  dsimp (config := { zeta := false }) only [visAt, visSteps, visBetween, move4_dec1,
    decVis, sessionBaseKeys, DY.ExecTrace.getLocalStateAt,
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents] at h2
  simp (config := { zeta := false }) only [ite_sessionInfo_eq_fast] at h2
  close_eval
  subst h1 h2
  decide +kernel

private theorem forall₂_append_inv {α β : Type} {R : α → β → Prop} :
    ∀ {a₁ a₂ : List α} {b₁ b₂ : List β},
      a₁.length = b₁.length →
      List.Forall₂ R (a₁ ++ a₂) (b₁ ++ b₂) →
      List.Forall₂ R a₁ b₁ ∧ List.Forall₂ R a₂ b₂
  | [], _, [], _, _, h => ⟨.nil, h⟩
  | [], _, _ :: _, _, hlen, _ => by cases hlen
  | _ :: _, _, [], _, hlen, _ => by cases hlen
  | _ :: _, _, _ :: _, _, hlen, .cons hr hrest =>
    let ⟨h1, h2⟩ := forall₂_append_inv (Nat.succ.inj hlen) hrest
    ⟨.cons hr h1, h2⟩

private abbrev PeelAt (k : Nat) (kb : List (VisEventKind × HwBytes)) (vis : List VisEntry)
    (rest : List (List (VisEventKind × HwBytes))) : Prop :=
  List.Forall₂ BMatch kb vis ∧ List.Forall₂ BMatch rest.flatten (visSteps.drop (k + 1)).flatten

private theorem peel_step0 : PeelAt 0 kb0 (visBetween move0_init t4 t5 none false)
    [kb1, kb2, kb3, kb4, kb5, kb6, kb7, kb8, kb9, kb10] := forall₂_append_inv rfl bytesMatch_all
private theorem peel_step1 : PeelAt 1 kb1 (visBetween move1_enc0 t5 t6 (some (25, 26)) false)
    [kb2, kb3, kb4, kb5, kb6, kb7, kb8, kb9, kb10] := forall₂_append_inv rfl peel_step0.2
private theorem peel_step2 : PeelAt 2 kb2 (visBetween move2_enc1 t6 t7 (some (25, 26)) false)
    [kb3, kb4, kb5, kb6, kb7, kb8, kb9, kb10] := forall₂_append_inv rfl peel_step1.2
private theorem peel_step3 : PeelAt 3 kb3 (visBetween move3_bobStart t7 t8 none false)
    [kb4, kb5, kb6, kb7, kb8, kb9, kb10] := forall₂_append_inv rfl peel_step2.2
private theorem peel_step4 : PeelAt 4 kb4 (visBetween move4_dec1 t8 t9 none true)
    [kb5, kb6, kb7, kb8, kb9, kb10] := forall₂_append_inv rfl peel_step3.2
private theorem peel_step5 : PeelAt 5 kb5 (visBetween move5_encReply0 t9 t10 none false)
    [kb6, kb7, kb8, kb9, kb10] := forall₂_append_inv rfl peel_step4.2
private theorem peel_step6 : PeelAt 6 kb6 (visBetween move6_decReply0 t10 t11 none false)
    [kb7, kb8, kb9, kb10] := forall₂_append_inv rfl peel_step5.2
private theorem peel_step7 : PeelAt 7 kb7 (visBetween move7_leakCkr t11 t12 none false)
    [kb8, kb9, kb10] := forall₂_append_inv rfl peel_step6.2
private theorem peel_step8 : PeelAt 8 kb8 (visBetween move8_leakCks t12 t13 none false)
    [kb9, kb10] := forall₂_append_inv rfl peel_step7.2
private theorem peel_step9 : PeelAt 9 kb9 (visBetween move9_enc2 t13 t14 none false)
    [kb10] := forall₂_append_inv rfl peel_step8.2
private theorem peel_step10 : PeelAt 10 kb10 (visBetween move10_dec2 t14 t15 none false)
    [] := forall₂_append_inv rfl peel_step9.2

unseal DY.Bytes in
private theorem encSendEntry_eq_between {tr tr' : ExecTrace} {stateIdx : Nat}
    (h : (match pendingPreKey tr stateIdx, tr.getMessageSentAt 25, tr.getMessageSentAt 26 with
          | some (ek, ct), some ek', some ct' =>
            (beqBareOptFast 256 ek.val ek'.val == some true) &&
            (beqBareOptFast 256 ct.val ct'.val == some true)
          | _, _, _ => false) = true) :
    encSendBetween tr tr' (some (25, 26)) = encSendEntry tr tr' stateIdx true := by
  unfold encSendEntry encSendBetween
  cases DY.Libsignal.Composed.Refinement.lastSent tr tr' with
  | none => rfl
  | some w =>
    dsimp only [↓reduceIte]
    rcases hp : pendingPreKey tr stateIdx with _ | ⟨⟨ek, ct⟩⟩ <;> rw [hp] at h
    · cases h
    · rcases hek : tr.getMessageSentAt 25 with _ | ek' <;> rw [hek] at h
      · cases h
      · rcases hct : tr.getMessageSentAt 26 with _ | ct' <;> rw [hct] at h
        · cases h
        · simp only [Bool.and_eq_true, beq_iff_eq] at h
          rw [Subtype.ext (beqBareOptFast_true 256 _ _ h.1),
              Subtype.ext (beqBareOptFast_true 256 _ _ h.2)]

private theorem encSendEntry_eq_between_none {tr tr' : ExecTrace} {stateIdx : Nat}
    (h : pendingPreKey tr stateIdx = none) :
    encSendBetween tr tr' none = encSendEntry tr tr' stateIdx false := by
  unfold encSendEntry encSendBetween
  rw [h]
  cases DY.Libsignal.Composed.Refinement.lastSent tr tr' <;> rfl

private theorem stepView_move0 :
    visBetween move0_init t4 t5 none false =
      stepView move0_init t4 (DY.Libsignal.Composed.Refinement.runWrapped runEv0) := by
  unfold stepView visBetween; rw [move0_next, move0_ok]; rfl

unseal DY.Bytes in
private theorem stepView_move1 :
    visBetween move1_enc0 t5 t6 (some (25, 26)) false =
      stepView move1_enc0 t5 (DY.Libsignal.Composed.Refinement.runWrapped runEv1) := by
  have hw : DY.Libsignal.Composed.Refinement.runWrapped runEv1 = true := by decide +kernel
  unfold stepView visBetween
  rw [move1_next, move1_ok, hw]
  dsimp only [move1_enc0]
  simp only [↓reduceIte]
  rw [encSendEntry_eq_between (tr := t5) (tr' := t6) (stateIdx := 30)]
  generalize h1 : pendingPreKey t5 30 = ppk
  dsimp (config := { zeta := false }) only [pendingPreKey, DY.ExecTrace.getLocalStateAt,
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents, sessionHasDecrypted] at h1
  simp (config := { zeta := false }) only [ite_sessionInfo_eq_fast, decide_sessionInfo_eq_fast] at h1
  subst h1; decide +kernel

unseal DY.Bytes in
private theorem stepView_move2 :
    visBetween move2_enc1 t6 t7 (some (25, 26)) false =
      stepView move2_enc1 t6 (DY.Libsignal.Composed.Refinement.runWrapped runEv2) := by
  have hw : DY.Libsignal.Composed.Refinement.runWrapped runEv2 = true := by decide +kernel
  unfold stepView visBetween
  rw [move2_next, move2_ok, hw]
  dsimp only [move2_enc1]
  simp only [↓reduceIte]
  rw [encSendEntry_eq_between (tr := t6) (tr' := t7) (stateIdx := 36)]
  generalize h1 : pendingPreKey t6 36 = ppk
  dsimp (config := { zeta := false }) only [pendingPreKey, DY.ExecTrace.getLocalStateAt,
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents, sessionHasDecrypted] at h1
  simp (config := { zeta := false }) only [ite_sessionInfo_eq_fast, decide_sessionInfo_eq_fast] at h1
  subst h1; decide +kernel

private theorem stepView_move3 :
    visBetween move3_bobStart t7 t8 none false =
      stepView move3_bobStart t7 (DY.Libsignal.Composed.Refinement.runWrapped runEv3) := by
  unfold stepView visBetween; rw [move3_next, move3_ok]; rfl
private theorem stepView_move4 :
    visBetween move4_dec1 t8 t9 none true =
      stepView move4_dec1 t8 (DY.Libsignal.Composed.Refinement.runWrapped runEv4) := by
  unfold stepView visBetween; rw [move4_next, move4_ok]; rfl
unseal DY.Bytes in
private theorem stepView_move5 :
    visBetween move5_encReply0 t9 t10 none false =
      stepView move5_encReply0 t9 (DY.Libsignal.Composed.Refinement.runWrapped runEv5) := by
  have hw : DY.Libsignal.Composed.Refinement.runWrapped runEv5 = false := by decide +kernel
  unfold stepView visBetween
  rw [move5_next, move5_ok, hw]
  dsimp only [move5_encReply0]
  simp only [↓reduceIte]
  rw [encSendEntry_eq_between_none (tr := t9) (tr' := t10)]
  generalize h1 : pendingPreKey t9 _ = ppk
  dsimp (config := { zeta := false }) only [pendingPreKey, DY.ExecTrace.getLocalStateAt,
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents, sessionHasDecrypted] at h1
  simp (config := { zeta := false }) only [ite_sessionInfo_eq_fast, decide_sessionInfo_eq_fast] at h1
  subst h1; decide +kernel
private theorem stepView_move6 :
    visBetween move6_decReply0 t10 t11 none false =
      stepView move6_decReply0 t10 (DY.Libsignal.Composed.Refinement.runWrapped runEv6) := by
  unfold stepView visBetween; rw [move6_next, move6_ok]; rfl
private theorem stepView_move7 :
    visBetween move7_leakCkr t11 t12 none false = stepView move7_leakCkr t11 false := by
  unfold stepView visBetween; rw [move7_next, move7_ok]; rfl
private theorem stepView_move8 :
    visBetween move8_leakCks t12 t13 none false = stepView move8_leakCks t12 false := by
  unfold stepView visBetween; rw [move8_next, move8_ok]; rfl
unseal DY.Bytes in
private theorem stepView_move9 :
    visBetween move9_enc2 t13 t14 none false =
      stepView move9_enc2 t13 (DY.Libsignal.Composed.Refinement.runWrapped runEv7) := by
  have hw : DY.Libsignal.Composed.Refinement.runWrapped runEv7 = false := by decide +kernel
  unfold stepView visBetween
  rw [move9_next, move9_ok, hw]
  dsimp only [move9_enc2]
  simp only [↓reduceIte]
  rw [encSendEntry_eq_between_none (tr := t13) (tr' := t14)]
  generalize h1 : pendingPreKey t13 _ = ppk
  dsimp (config := { zeta := false }) only [pendingPreKey, DY.ExecTrace.getLocalStateAt,
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents, sessionHasDecrypted] at h1
  simp (config := { zeta := false }) only [ite_sessionInfo_eq_fast, decide_sessionInfo_eq_fast] at h1
  subst h1; decide +kernel
private theorem stepView_move10 :
    visBetween move10_dec2 t14 t15 none false =
      stepView move10_dec2 t14 (DY.Libsignal.Composed.Refinement.runWrapped runEv8) := by
  unfold stepView visBetween; rw [move10_next, move10_ok]; rfl

private theorem runMatches_0 :
    RunMatches myInterp r0 S0 myGhost t4 move0_init runEv0
      (visBetween move0_init t4 t5 none false) := by
  refine ⟨rfl, rfl, trivial, rfl, move0_ok, ⟨_, rfl⟩, stepView_move0, ?_⟩
  have hb0 := peel_step0.1
  dsimp only [kb0, visBetween, move0_init, DY.Libsignal.Composed.Refinement.aliceVis,
    List.cons_append] at hb0 ⊢
  obtain ⟨h_inp, h_drs⟩ := List.forall₂_cons.mp hb0
  refine ⟨_, _, [], congrArg (_ :: ·) (List.append_nil _).symm,
    ?_, ?_, rfl, trivial, fun _ _ => trivial⟩
  · rw [runEv0_input]; exact h_inp
  · refine ⟨initPieces, by decide, ?_,
      (List.forall₂_map_left_iff (R := BMatch) (f := (VisEventKind.rng, ·))).mp h_drs⟩
    have hc : initPieces.flatten = runEv0.coins := by decide +kernel
    rw [hc]

private theorem runMatches_1 :
    RunMatches myInterp r0 S0 myGhost t5 move1_enc0 runEv1
      (visBetween move1_enc0 t5 t6 (some (25, 26)) false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move1_ok, ⟨_, rfl⟩, stepView_move1, ?_⟩
  rcases peel_step1.1 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, trivial, fun _ _ => trivial⟩
  refine ⟨[cSend0.take 32], by decide, ?_, .cons h_rng .nil⟩
  change [cSend0.take 32].flatten <+: cSend0
  simpa using List.take_prefix 32 cSend0

private theorem runMatches_2 :
    RunMatches myInterp r0 S0 myGhost t6 move2_enc1 runEv2
      (visBetween move2_enc1 t6 t7 (some (25, 26)) false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move2_ok, ⟨_, rfl⟩, stepView_move2, ?_⟩
  rcases peel_step2.1 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, trivial, fun _ _ => trivial⟩
  refine ⟨[cSend1.take 32], by decide, ?_, .cons h_rng .nil⟩
  change [cSend1.take 32].flatten <+: cSend1
  simpa using List.take_prefix 32 cSend1

private theorem runMatches_3 :
    RunMatches myInterp r0 S0 myGhost t7 move3_bobStart runEv3
      (visBetween move3_bobStart t7 t8 none false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, rfl, move3_ok, ⟨_, rfl⟩, stepView_move3, ?_⟩
  have hb3 := peel_step3.1
  dsimp only [visBetween, move3_bobStart, DY.Libsignal.Composed.Refinement.bobVis,
    DY.Libsignal.Composed.Refinement.bobOpkPk, DY.Libsignal.Composed.Refinement.received,
    DY.Libsignal.Composed.Refinement.newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
    DY.Libsignal.Composed.Refinement.receivedPlaintext, exposures,
    List.map, List.append] at hb3 ⊢
  rcases hb3 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, ?_, ?_⟩
  · refine ⟨[rc3Bytes], by decide, ?_, .cons h_rng .nil⟩
    have hc : [rc3Bytes].flatten = runEv3.coins := by decide +kernel
    rw [hc]
  · change x3Rep ∈ preKeyRepresentationsOn myInterp r0 S0 myGhost t7 (wirePrekeyTag :: pkMsg0.bytes)
    rw [← show runTrace r0 msPre3 = t7 from runTrace_take_eq 3]
    exact x3Rep_mem_pre3
  · have hbd : bobDoneBaseKeys t7 = [] := rfl
    exact fun _ _ ⟨_, hmem, _⟩ => by rw [hbd] at hmem; cases hmem

private theorem mem_bobDoneBaseKeys_of_sessionBaseKeys {ek : DY.Bytes}
    (hek : ek ∈ sessionBaseKeys t8 53) : ek ∈ bobDoneBaseKeys t8 := by
  have hall : (List.range t8.length).all (fun i =>
    match t8.getEventAt DY.Libsignal.Composed.ComposedEvent i with
    | some (.HandshakeSession _ d) => decide (d < t8.length)
    | none => true) = true := by decide +kernel
  unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hek
  cases ht : (t8.at? 53 : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))) with
  | none => rw [ht] at hek; cases hek
  | some e =>
    rw [ht, Option.map_some] at hek
    dsimp only at hek
    obtain ⟨pqev, hpq_mem, hbd⟩ := List.mem_filterMap.mp hek
    obtain ⟨i, hi, hfi⟩ := List.mem_filterMap.mp hpq_mem
    have hd := List.all_eq_true.mp hall i hi
    cases hce : t8.getEventAt DY.Libsignal.Composed.ComposedEvent i with
    | none => rw [hce] at hfi; cases hfi
    | some ev =>
      rcases ev with ⟨s, d⟩
      rw [hce] at hfi hd
      dsimp only at hfi hd
      by_cases hs : s = e.st.state.sessionInfo e.st.participant
      · simp only [hs, ↓reduceIte] at hfi
        exact List.mem_filterMap.mpr ⟨d, List.mem_range.mpr (of_decide_eq_true hd),
          by rw [hfi]; cases pqev <;> exact hbd⟩
      · simp only [hs, ↓reduceIte] at hfi; cases hfi

private theorem runMatches_4 :
    RunMatches myInterp r0 S0 myGhost t8 move4_dec1 runEv4
      (visBetween move4_dec1 t8 t9 none true) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move4_ok, ⟨_, rfl⟩, stepView_move4, ?_⟩
  have hb4 := peel_step4.1
  dsimp only [visBetween, move4_dec1, decVis,
    DY.Libsignal.Composed.Refinement.newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
    DY.Libsignal.Composed.Refinement.receivedPlaintext, exposures,
    List.map, List.append] at hb4 ⊢
  rcases hb4 with _ | ⟨h_inp, _ | ⟨h_out, ⟨⟩⟩⟩
  refine ⟨_, [], [_], rfl, h_inp, ⟨[], by simp, List.nil_prefix, List.Forall₂.nil⟩,
    ⟨_, rfl, h_out⟩, ?_, ?_⟩
  · intro p hp
    change msg1Term ∈ recvRepresentationsOn myInterp S0 myGhost t8 p.message
    rw [← show runTrace r0 msPre4 = t8 from runTrace_take_eq 4]
    exact msg1Term_mem_pre4 hp
  · intro p hp
    obtain ⟨_, ⟨_, p', _, hp', _, _, ⟨ek, hek, hkey⟩, _⟩⟩ := h_inp
    dsimp only [runEv4, wire1] at hp
    change parsePreKeyWire wire1 = some p at hp
    rw [hp] at hp'
    cases hp'
    exact ⟨ek, mem_bobDoneBaseKeys_of_sessionBaseKeys hek, hkey.symm⟩

private theorem runMatches_5 :
    RunMatches myInterp r0 S0 myGhost t9 move5_encReply0 runEv5
      (visBetween move5_encReply0 t9 t10 none false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move5_ok, ⟨_, rfl⟩, stepView_move5, ?_⟩
  rcases peel_step5.1 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, trivial, fun _ _ => trivial⟩
  refine ⟨[cSendReply0.take 32], by decide, ?_, .cons h_rng .nil⟩
  change [cSendReply0.take 32].flatten <+: cSendReply0
  simpa using List.take_prefix 32 cSendReply0

private theorem runMatches_6 :
    RunMatches myInterp r0 S0 myGhost t10 move6_decReply0 runEv6
      (visBetween move6_decReply0 t10 t11 none false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move6_ok, ⟨_, rfl⟩, stepView_move6, ?_⟩
  have hb6 := peel_step6.1
  dsimp only [visBetween, move6_decReply0, decVis,
    DY.Libsignal.Composed.Refinement.newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
    DY.Libsignal.Composed.Refinement.receivedPlaintext, exposures,
    List.map, List.append] at hb6 ⊢
  rcases hb6 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, ?_, fun _ hp => by cases hp⟩
  · refine ⟨[rc6Bytes], by decide, ?_, .cons h_rng .nil⟩
    have hc : [rc6Bytes].flatten = runEv6.coins := by decide +kernel
    rw [hc]
  · change msgReply0Term ∈ recvRepresentationsOn myInterp S0 myGhost t10 bodyReply0
    rw [← show runTrace r0 msPre6 = t10 from runTrace_take_eq 6]
    exact msgReply0Term_mem_pre6

private theorem envMatches_7 :
    EnvMatches myInterp r0 S0 myGhost t11 move7_leakCkr leakEvCkr
      (visBetween move7_leakCkr t11 t12 none false) := by
  rcases peel_step7.1 with _ | ⟨h_leak, ⟨⟩⟩
  exact ⟨rfl, trivial, fun _ h => by injection h with h; exact h.symm,
    stepView_move7, ⟨_, rfl, h_leak⟩⟩

private theorem envMatches_8 :
    EnvMatches myInterp r0 S0 myGhost t12 move8_leakCks leakEvCks
      (visBetween move8_leakCks t12 t13 none false) := by
  rcases peel_step8.1 with _ | ⟨h_leak, ⟨⟩⟩
  exact ⟨rfl, trivial, fun _ h => by injection h with h; exact h.symm,
    stepView_move8, ⟨_, rfl, h_leak⟩⟩

private theorem runMatches_9 :
    RunMatches myInterp r0 S0 myGhost t13 move9_enc2 runEv7
      (visBetween move9_enc2 t13 t14 none false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move9_ok, ⟨_, rfl⟩, stepView_move9, ?_⟩
  rcases peel_step9.1 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, trivial, fun _ _ => trivial⟩
  refine ⟨[cSend2.take 32], by decide, ?_, .cons h_rng .nil⟩
  change [cSend2.take 32].flatten <+: cSend2
  simpa using List.take_prefix 32 cSend2

private theorem runMatches_10 :
    RunMatches myInterp r0 S0 myGhost t14 move10_dec2 runEv8
      (visBetween move10_dec2 t14 t15 none false) (some (initIds0 r0)) := by
  refine ⟨rfl, rfl, trivial, trivial, move10_ok, ⟨_, rfl⟩, stepView_move10, ?_⟩
  have hb10 := peel_step10.1
  dsimp only [visBetween, move10_dec2, decVis,
    DY.Libsignal.Composed.Refinement.newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
    DY.Libsignal.Composed.Refinement.receivedPlaintext, exposures,
    List.map, List.append] at hb10 ⊢
  rcases hb10 with _ | ⟨h_inp, _ | ⟨h_rng, _ | ⟨h_out, ⟨⟩⟩⟩⟩
  refine ⟨_, [_], [_], rfl, h_inp, ?_, ⟨_, rfl, h_out⟩, ?_, fun _ hp => by cases hp⟩
  · refine ⟨[rc8Bytes], by decide, ?_, .cons h_rng .nil⟩
    have hc : [rc8Bytes].flatten = runEv8.coins := by decide +kernel
    rw [hc]
  · change msg2Term ∈ recvRepresentationsOn myInterp S0 myGhost t14 body2
    rw [← show runTrace r0 msPre8 = t14 from runTrace_take_eq 10]
    exact msg2Term_mem_pre8

private theorem nextBundleIds_runEv0 :
    nextBundleIds none runEv0 = some (initIds0 r0) := by
  have hcmd : ∃ peer spk, runEv0.cmd = .init peer spk := ⟨_, _, rfl⟩
  obtain ⟨peer, spk, hcmd⟩ := hcmd
  simp only [nextBundleIds, hcmd, runEv0_input, r0_eq_comp, initIds0]
  decide +kernel

private theorem me_nil {initIds : Option BundlePreKeyIds} {tr : ExecTrace} :
    MatchesEventsAt myInterp r0 S0 myGhost initIds tr [] [] [] :=
  MatchesEventsAt.nil (fun _ h => nomatch h)

private abbrev mr0 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_0 (nextBundleIds_runEv0.symm ▸ move0_next ▸ h)
private abbrev mr1 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_1 (move1_next ▸ h)
private abbrev mr2 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_2 (move2_next ▸ h)
private abbrev mr3 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_3 (move3_next ▸ h)
private abbrev mr4 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_4 (move4_next ▸ h)
private abbrev mr5 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_5 (move5_next ▸ h)
private abbrev mr6 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_6 (move6_next ▸ h)
private abbrev me7 {ss evs vs} := fun h => matchesEvents_env (ss := ss) (evs := evs) (vs := vs) (initIds := some (initIds0 r0)) envMatches_7 (move7_next ▸ h)
private abbrev me8 {ss evs vs} := fun h => matchesEvents_env (ss := ss) (evs := evs) (vs := vs) (initIds := some (initIds0 r0)) envMatches_8 (move8_next ▸ h)
private abbrev mr9 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_9 (move9_next ▸ h)
private abbrev mr10 {ss evs vs} := fun h => matchesEvents_run1 (ss := ss) (evs := evs) (vs := vs) runMatches_10 (move10_next ▸ h)

theorem matchesEvents_take : ∀ (k : Nat), k ≤ 11 →
    MatchesEvents myInterp r0 S0 myGhost (setupTrace r0)
      (msExposed.take k) (evsExposed.take k) (visAt k) := by
  intro k hk
  rw [setupTrace_r0_eq]
  match k with
  | 0 => exact me_nil
  | 1 => exact mr0 me_nil
  | 2 => exact mr0 (mr1 me_nil)
  | 3 => exact mr0 (mr1 (mr2 me_nil))
  | 4 => exact mr0 (mr1 (mr2 (mr3 me_nil)))
  | 5 => exact mr0 (mr1 (mr2 (mr3 (mr4 me_nil))))
  | 6 => exact mr0 (mr1 (mr2 (mr3 (mr4 (mr5 me_nil)))))
  | 7 => exact mr0 (mr1 (mr2 (mr3 (mr4 (mr5 (mr6 me_nil))))))
  | 8 => exact mr0 (mr1 (mr2 (mr3 (mr4 (mr5 (mr6 (me7 me_nil)))))))
  | 9 => exact mr0 (mr1 (mr2 (mr3 (mr4 (mr5 (mr6 (me7 (me8 me_nil))))))))
  | 10 => exact mr0 (mr1 (mr2 (mr3 (mr4 (mr5 (mr6 (me7 (me8 (mr9 me_nil)))))))))
  | 11 => exact mr0 (mr1 (mr2 (mr3 (mr4 (mr5 (mr6 (me7 (me8 (mr9 (mr10 me_nil))))))))))
  | _ + 12 => omega

theorem explains_take (k : Nat) (hk : k ≤ 11) :
    Explains myInterp r0 S0 myGhost (msExposed.take k) (visAt k) (evsExposed.take k) :=
  ⟨myGhost_compat, ghostWF_visAt k, modelRunWF_take k, matchesEvents_take k hk⟩

theorem explains_nil : Explains myInterp r0 S0 myGhost [] [] [] := explains_take 0 (by decide)
theorem explains_pre1 :
    Explains myInterp r0 S0 myGhost (msExposed.take 1) (visAt 1) (evsExposed.take 1) :=
  explains_take 1 (by decide)
theorem explains_pre2 :
    Explains myInterp r0 S0 myGhost (msExposed.take 2) (visAt 2) (evsExposed.take 2) :=
  explains_take 2 (by decide)
theorem explains_pre3 : Explains myInterp r0 S0 myGhost msPre3 (visAt 3) evsPre3 :=
  explains_take 3 (by decide)
theorem explains_pre4 : Explains myInterp r0 S0 myGhost msPre4 (visAt 4) evsPre4 :=
  explains_take 4 (by decide)
theorem explains_pre5 : Explains myInterp r0 S0 myGhost msPre5 (visAt 5) evsPre5 :=
  explains_take 5 (by decide)
theorem explains_pre6 : Explains myInterp r0 S0 myGhost msPre6 (visAt 6) evsPre6 :=
  explains_take 6 (by decide)
theorem explains_honest : Explains myInterp r0 S0 myGhost msHonest (visAt 7) evsHonest :=
  explains_take 7 (by decide)
theorem explains_pre8 : Explains myInterp r0 S0 myGhost msPre8 (visAt 10) evsPre8 :=
  explains_take 10 (by decide)
theorem explains_exposed : Explains myInterp r0 S0 myGhost msExposed (visAt 11) evsExposed :=
  explains_take 11 (by decide)

end Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
