/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import Comparse.Basic
import DY.Comparse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
import Symbolic.Proofs.Tests.CliNonvacuity.Witness
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.Comparse.Basic
import Symbolic.DYBridge.DY.Comparse
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Trace-Randomness Invariant and Memo Byte-Length Exclusion

Proves `traceEntriesRand_of_reachable`: on any reachable composed trace `tr`, every
`DY.Random.Random` memo entry `(u, sh, v) ∈ (gamma' i S g b).memo` of any attacker-known term,
network message, stored state, or logged event corresponds to a `DY.Random.ExecEntryT` of matching
size on `tr`, and excludes non-`Random` memo entries of byte length `9`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (SessionInfo KeyDir KeyComponent RecvChain TRState TREvent TRSignalMsg parseTrSignalMsg
   lit hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 kdfRk createChain kdfCk chainKeyAt spqrB2A
   trMsgKeys computeMac trHonestWireMsg findRecvChain setRecvChain recvChainFor consumeMessageKey)
open DY.Libsignal.PQXDH
  (KeyKind PQXDHState PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles
   HandshakeKeys AliceHandshakeOut BobHandshakeOut zeroSalt pqxdhLabel
   serializedIk agree pqxdhIkm pqxdhKdf aliceAgreement bobAgreement extractDhSecretKey)
open DY.Libsignal.Composed (ComposedEvent aliceStart bobStart reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (kemDecap_eq_some_iff assumedInjective_eq_true_iff)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp length_hmacWith_32 length_myInterp_dhPk length_myInterp_dh le_length_myInterp_aesEnc
   length_myInterp_kyberEncap_take length_myInterp_kyberEncap_drop)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost ConcretizedTerm
   node opaqueNode spqrKeyNode
   concretizeRandom concretizeLit concretizeConcat concretizeDhPk concretizeDh
   concretizeKdf concretizeSym concretizeTrunc concretizeVariant
   concretizeKemPk concretizeKemEncap concretizeKemSS concretizeKemRej concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey concretizeSpqrSendMsg
   concretizeSpqrRecvState concretizeSpqrRecvKey concretizeSpqrChainKey concretizeTrWire
   concretizeAll gamma' gamma randTerm assumedInjective)

section Core
variable {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {T : ExecTrace}
attribute [local instance] termRandAt_compat

private theorem TRand.messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine TRand.bind (TRand.getLocalState me stateIdx) fun st hst => TRand.bind (TRand.guardP _) fun _ _ =>
    TRand.bind (TRand.genRand 32) fun m hm => TRand.bind (TRand.genRand coinsLen) fun coins hcoins => ?_
  have hspqr := termRandAt_spqrSend hst.2.2.2.2.2.2.1 hcoins
  refine TRand.bind (TRand.sendMessage hspqr.2.1) fun _ _ => TRand.bind (TRand.receiveMessage pqIdx) fun pqSalt hpqSalt =>
    TRand.bind (TRand.logEvent trivial) fun _ _ => ?_
  have hck := termRandAt_kdfCk hst.2.2.2.2.1; have hkeys := termRandAt_trMsgKeys hpqSalt hck.2
  have hwire := termRandAt_trHonestWireMsg (termRandAt_dhPk hst.2.2.2.1) st.ns st.pn (termRandAt_symEnc hkeys.1 hkeys.2.2 hm) hspqr.2.2
  exact TRand.bind (TRand.logMessageKeyAndStore me _ .sender _ _ _ _ _
    ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hck.1, hst.2.2.2.2.2.1, hspqr.1, hst.2.2.2.2.2.2.2⟩)
    fun _ _ => TRand.sendMessage (termRandAt_concat hwire (termRandAt_computeMac hkeys.2.1 hst.1 hst.2.1 hwire))
private theorem TRand.messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) :=
  TRand.bind (TRand.getLocalState me stateIdx) fun _ _ => TRand.bind (TRand.genRand 32) fun _ _ => TRand.failure
private theorem TRand.messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine TRand.bind (TRand.getLocalState me stateIdx) fun st₀ hst₀ => TRand.bind (TRand.receiveSignalMsg msgIdx) fun msg hmsg =>
    TRand.bind (TRand.ensureReceiverChain hst₀ hmsg.2.2.1) fun ⟨st, c, ratcheted⟩ ⟨hst, hc⟩ => ?_
  dsimp only; split
  · next seed c' hcm =>
    obtain ⟨_, hc'⟩ := termRandAt_consumeMessageKey hc hcm; split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := termRandAt_spqrRecv hst.2.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      refine TRand.bind (TRand.sendMessage hkey) fun _ _ => TRand.bind (TRand.receiveMessage pqIdx) fun pqSalt _ =>
        TRand.bind (TRand.verifyMacAndDecrypt hmsg) fun m hm => ?_
      have hrest : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True)
          (do DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stateIdx c.chainKey c.index (msg.counter.toNat - c.index.toNat)
              DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
              DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx stateIdx
                { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        TRand.bind (TRand.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ => TRand.bind (TRand.logEvent hm) fun _ _ =>
          TRand.logMessageKeyAndStore me _ .receiver _ _ _ _ _ (stateRandAt_setRecvChain hst hc' hspqr')
      split
      · exact TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.bind (TRand.logEvent trivial) fun _ _ => hrest
      · exact hrest
    · exact TRand.failure
  · exact TRand.failure
private theorem TRand.messageDecryptSkipped (me : Participant) (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine TRand.bind (TRand.getLocalState me stateIdx) fun st hst => TRand.bind (TRand.receiveSignalMsg msgIdx) fun msg hmsg =>
    TRand.bind (TRand.getEntry_tr skippedKeyEventIdx) fun _ _ => ?_
  split
  · refine TRand.bind (TRand.guardP _) fun _ _ => TRand.bind (TRand.guardTrace _) fun _ _ => ?_; split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := termRandAt_spqrRecv hst.2.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      exact TRand.bind (TRand.sendMessage hkey) fun _ _ => TRand.bind (TRand.receiveMessage pqIdx) fun _ _ =>
        TRand.bind (TRand.verifyMacAndDecrypt hmsg) fun m hm => TRand.bind (TRand.logEvent trivial) fun _ _ =>
        TRand.bind (TRand.logEvent hm) fun _ _ => TRand.logMessageKeyAndStore me _ .receiver _ _ _ _ _
          ⟨hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hspqr', hst.2.2.2.2.2.2.2⟩
    · exact TRand.failure
  · exact TRand.failure
private theorem TRand.exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stateIdx k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey; refine TRand.bind (TRand.getLocalState me stateIdx) fun st hst => ?_
  cases k with
  | rk => exact TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.sendMessage hst.2.2.1
  | dhs => exact TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.sendMessage hst.2.2.2.1
  | cks => exact TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.sendMessage hst.2.2.2.2.1
  | ckr _ =>
    dsimp only; split
    · next c hf => exact TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.sendMessage (termRandAt_findRecvChain hst hf).2
    · exact TRand.failure
private theorem TRand.exposeSpqr (me : Participant) (stateIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx) :=
  TRand.bind (TRand.getLocalState me stateIdx) fun _ hst => TRand.bind (TRand.logEvent hst.2.2.2.2.2.2.1) fun _ _ => TRand.sendMessage hst.2.2.2.2.2.2.1
private theorem TRand.exposeSkipped (skippedKeyEventIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped skippedKeyEventIdx) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped; refine TRand.bind (TRand.getEntry_tr skippedKeyEventIdx) fun e he => ?_; split
  · next s pk n seed rIdx src heq =>
    rw [heq] at he; have he' : TermRandAt i S g T seed ∧ TermRandAt i S g T pk := he
    exact TRand.bind (TRand.guardTrace _) fun _ _ => TRand.bind (TRand.logEvent he'.1) fun _ _ => TRand.sendMessage he'.1
  · exact TRand.failure
private theorem TRand.registerIdentity (p : Participant) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.registerIdentity p) :=
  TRand.bind (TRand.requireTracePredicate _) fun _ _ => TRand.bind (TRand.genRand 32) fun _ hik =>
    TRand.bind (TRand.logPQEvent ⟨termRandAt_dhPk hik, termRandAt_vk hik⟩) fun _ _ => TRand.bind (TRand.sendMessage (termRandAt_dhPk hik)) fun _ _ =>
    TRand.bind (TRand.sendMessage (termRandAt_vk hik)) fun _ _ => TRand.storePQLocalState p hik
private theorem TRand.registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) :=
  TRand.bind (TRand.requireTracePredicate _) fun _ _ => TRand.bind (TRand.receiveMessage skIdx) fun _ hik =>
    TRand.bind (TRand.logPQEvent ⟨termRandAt_dhPk hik, termRandAt_vk hik⟩) fun _ _ => TRand.logPQEvent trivial
private theorem TRand.genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b idStateIdx) :=
  TRand.bind (TRand.getKey b idStateIdx .identity) fun _ hik => TRand.bind (TRand.genRand 32) fun _ hspk =>
    TRand.bind (TRand.genRand 64) fun _ hnonce => TRand.bind (TRand.logPQEvent trivial) fun _ _ => TRand.bind (TRand.storePQLocalState b hspk) fun _ _ =>
    TRand.bind (TRand.sendMessage (termRandAt_dhPk hspk)) fun _ _ =>
    TRand.bind (TRand.sendMessage (termRandAt_sign hik hnonce (termRandAt_concat (termRandAt_literalToBytes i S g T _) (termRandAt_dhPk hspk)))) fun _ _ => TRand.pure trivial
private theorem TRand.genPQPrekey (b : Participant) (idStateIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.genPQPrekey b idStateIdx) :=
  TRand.bind (TRand.getKey b idStateIdx .identity) fun _ hik => TRand.bind (TRand.genRand 64) fun _ hpqsk =>
    TRand.bind (TRand.genRand 64) fun _ hnonce => TRand.bind (TRand.logPQEvent trivial) fun _ _ => TRand.bind (TRand.storePQLocalState b hpqsk) fun _ _ =>
    TRand.bind (TRand.sendMessage (termRandAt_kemPk hpqsk)) fun _ _ =>
    TRand.bind (TRand.sendMessage (termRandAt_sign hik hnonce (termRandAt_concat (termRandAt_literalToBytes i S g T _) (termRandAt_kemPk hpqsk)))) fun _ _ => TRand.pure trivial
private theorem TRand.genOneTimePrekey (b : Participant) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) :=
  TRand.bind (TRand.genRand 32) fun _ hopk => TRand.bind (TRand.logPQEvent trivial) fun _ _ =>
    TRand.bind (TRand.storePQLocalState b hopk) fun _ _ => TRand.bind (TRand.sendMessage (termRandAt_dhPk hopk)) fun _ _ => TRand.pure trivial
private theorem termRandAt_serializedIk {pk : DY.Bytes} (hpk : TermRandAt i S g T pk) : TermRandAt i S g T (serializedIk pk) := termRandAt_concat (termRandAt_literalToBytes i S g T _) hpk
private theorem termRandAt_agree {pk sk : DY.Bytes} (hpk : TermRandAt i S g T pk) (hsk : TermRandAt i S g T sk) : TermRandAt i S g T (agree pk sk) := termRandAt_dh (termRandAt_x25519Key hpk) hsk
private theorem termRandAt_pqxdhIkm {dh1 dh2 dh3 : DY.Bytes} {dh4 : Option DY.Bytes} {ss : DY.Bytes}
    (h1 : TermRandAt i S g T dh1) (h2 : TermRandAt i S g T dh2) (h3 : TermRandAt i S g T dh3) (h4 : ∀ x, dh4 = some x → TermRandAt i S g T x) (hss : TermRandAt i S g T ss) :
    TermRandAt i S g T (pqxdhIkm dh1 dh2 dh3 dh4 ss) := by
  unfold pqxdhIkm; refine termRandAt_concat (termRandAt_literalToBytes i S g T _) (termRandAt_concat h1 (termRandAt_concat h2 (termRandAt_concat h3 ?_)))
  cases dh4 with | none => exact hss | some d => exact termRandAt_concat (h4 d rfl) hss
private theorem termRandAt_pqxdhKdf {ikm : DY.Bytes} (hikm : TermRandAt i S g T ikm) :
    TermRandAt i S g T (pqxdhKdf ikm).rk ∧ TermRandAt i S g T (pqxdhKdf ikm).ck ∧ TermRandAt i S g T (pqxdhKdf ikm).pqr := by
  have hprk : TermRandAt i S g T (hmac zeroSalt ikm) := termRandAt_hmac (termRandAt_literalToBytes i S g T _) hikm
  have hinfo : TermRandAt i S g T pqxdhLabel := termRandAt_literalToBytes i S g T _
  exact ⟨termRandAt_hkdfBlock1 hprk hinfo, termRandAt_hkdfBlock2 hprk hinfo, termRandAt_hkdfBlock3 hprk hinfo⟩
private theorem termRandAt_aliceAgreement {ikA ek ikBPk spk pqpk : DY.Bytes} {opk : Option DY.Bytes} {entropy : DY.Bytes}
    (hikA : TermRandAt i S g T ikA) (hek : TermRandAt i S g T ek) (hikB : TermRandAt i S g T ikBPk) (hspk : TermRandAt i S g T spk)
    (hpqpk : TermRandAt i S g T pqpk) (hopk : ∀ o, opk = some o → TermRandAt i S g T o) (hent : TermRandAt i S g T entropy) :
    TermRandAt i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).1 ∧ TermRandAt i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.rk ∧
    TermRandAt i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.ck ∧ TermRandAt i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.pqr := by
  unfold aliceAgreement; obtain ⟨hct, hss⟩ := termRandAt_kemEncap hpqpk hent
  have hikm : TermRandAt i S g T (pqxdhIkm (agree spk ikA) (agree ikBPk ek) (agree spk ek) (opk.map (agree · ek)) (DY.PQKem.kemEncap pqpk entropy).2) := by
    refine termRandAt_pqxdhIkm (termRandAt_agree hspk hikA) (termRandAt_agree hikB hek) (termRandAt_agree hspk hek) ?_ hss
    intro d hd; cases opk with
    | none => cases hd
    | some o => simp only [Option.map_some, Option.some.injEq] at hd; subst hd; exact termRandAt_agree (hopk o rfl) hek
  obtain ⟨hrk, hck, hpqr⟩ := termRandAt_pqxdhKdf hikm; exact ⟨hct, hrk, hck, hpqr⟩
private theorem termRandAt_bobAgreement {ikB spkSk pqsk : DY.Bytes} {opkSk : Option DY.Bytes} {ikAPk ek ct : DY.Bytes}
    {keys : HandshakeKeys} (hikB : TermRandAt i S g T ikB) (hspkSk : TermRandAt i S g T spkSk) (hpqsk : TermRandAt i S g T pqsk)
    (hopkSk : ∀ o, opkSk = some o → TermRandAt i S g T o)
    (hikA : TermRandAt i S g T ikAPk) (hek : TermRandAt i S g T ek) (hct : TermRandAt i S g T ct) (hba : bobAgreement ikB spkSk pqsk opkSk ikAPk ek ct = some keys) :
    TermRandAt i S g T keys.rk ∧ TermRandAt i S g T keys.ck ∧ TermRandAt i S g T keys.pqr := by
  have hdh4 : ∀ x, (opkSk.map fun o => agree ek o) = some x → TermRandAt i S g T x := by
    intro x hx; obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hx; exact termRandAt_agree hek (hopkSk o ho)
  rcases hdec : DY.PQKem.kemDecap pqsk ct with _ | ss
  · simp only [bobAgreement, DY.Libsignal.PQXDH.errToOption, hdec, Option.getD_none, Option.pure_def, Option.some.injEq] at hba; subst hba
    exact termRandAt_pqxdhKdf (termRandAt_pqxdhIkm (termRandAt_agree hikA hspkSk) (termRandAt_agree hek hikB) (termRandAt_agree hek hspkSk) hdh4 (termRandAt_kemRej hpqsk hct))
  · simp only [bobAgreement, DY.Libsignal.PQXDH.errToOption, hdec, Option.getD_some, Option.pure_def, Option.some.injEq] at hba; subst hba
    exact termRandAt_pqxdhKdf (termRandAt_pqxdhIkm (termRandAt_agree hikA hspkSk) (termRandAt_agree hek hikB) (termRandAt_agree hek hspkSk) hdh4 (termRandAt_kemDecap hdec hct))
private def AliceHandshakeOk (o : AliceHandshakeOut) : Prop :=
  TermRandAt i S g T o.ikA ∧ TermRandAt i S g T o.ikB ∧ TermRandAt i S g T o.spk ∧ TermRandAt i S g T o.pqpk ∧
  (∀ opk, o.opk = some opk → TermRandAt i S g T opk) ∧ TermRandAt i S g T o.ek ∧ TermRandAt i S g T o.ct ∧
  TermRandAt i S g T o.keys.rk ∧ TermRandAt i S g T o.keys.ck ∧ TermRandAt i S g T o.keys.pqr
private theorem TRand.aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) :
    TRand (i := i) (S := S) (g := g) (T := T) (AliceHandshakeOk (i := i) (S := S) (g := g) (T := T)) (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TRand.bind (TRand.getKey a idStateIdx .identity); intro ikA hikA
  apply TRand.bind (TRand.lookupIdentity b regIdxB); intro p hkv
  rcases p with ⟨ikB, _⟩; dsimp only
  apply TRand.bind (TRand.receiveMessage h.spk); intro spk hspk
  apply TRand.bind (TRand.receiveMessage h.spkSig); intro _ _
  apply TRand.bind (TRand.receiveMessage h.pqpk); intro pqpk hpqpk
  apply TRand.bind (TRand.receiveMessage h.pqpkSig); intro _ _
  apply TRand.bind (TRand.guardP _); intro _ _
  apply TRand.bind (TRand.guardP _); intro _ _
  cases h.opk <;> dsimp only
  · apply TRand.bind (TRand.pure (Q := fun opk : Option DY.Bytes =>
        ∀ o, opk = some o → TermRandAt i S g T o) (fun _ hc => by cases hc)); intro opk hopk
    apply TRand.bind (TRand.genRand 32); intro ek hek
    apply TRand.bind (TRand.guardP _); intro _ _
    apply TRand.bind (TRand.guardP _); intro _ _
    apply TRand.bind (TRand.genRand 32); intro entropy hent
    obtain ⟨hct, hrk, hck, hpqr⟩ := termRandAt_aliceAgreement hikA hek hkv.1 hspk hpqpk hopk hent
    exact TRand.pure ⟨termRandAt_dhPk hikA, hkv.1, hspk, hpqpk, hopk, termRandAt_dhPk hek, hct, hrk, hck, hpqr⟩
  · apply TRand.bind (TRand.receiveMessage _); intro o ho
    apply TRand.bind (TRand.pure (Q := fun opk : Option DY.Bytes =>
        ∀ o', opk = some o' → TermRandAt i S g T o') (fun _ hc => Option.some.inj hc ▸ ho)); intro opk hopk
    apply TRand.bind (TRand.genRand 32); intro ek hek
    apply TRand.bind (TRand.guardP _); intro _ _
    apply TRand.bind (TRand.guardP _); intro _ _
    apply TRand.bind (TRand.genRand 32); intro entropy hent
    obtain ⟨hct, hrk, hck, hpqr⟩ := termRandAt_aliceAgreement hikA hek hkv.1 hspk hpqpk hopk hent
    exact TRand.pure ⟨termRandAt_dhPk hikA, hkv.1, hspk, hpqpk, hopk, termRandAt_dhPk hek, hct, hrk, hck, hpqr⟩
private theorem TRand.aliceStart (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TRand.bind (TRand.aliceHandshake a b idStateIdx regIdxB h) fun o ho => TRand.bind (TRand.genRand 32) fun dhsA hdhsA =>
    TRand.bind (TRand.sendMessage ho.2.2.2.2.2.1) fun _ _ => TRand.bind (TRand.sendMessage ho.2.2.2.2.2.2.1) fun _ _ =>
    TRand.bind TRand.traceLength fun _ _ => TRand.bind (TRand.logPQEvent trivial) fun _ _ =>
    TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.bind (TRand.logCEvent _) fun _ _ => ?_
  rcases ho with ⟨hikA, hikB, hspk, _, _, _, _, hrk, hck, hpqr⟩; have hc := termRandAt_createChain hrk hspk hdhsA
  refine TRand.storeLocalState a ⟨termRandAt_serializedIk hikA, termRandAt_serializedIk hikB, hc.1, hdhsA, hc.2,
    termRandAt_concat (termRandAt_dhPk hdhsA) hrk, termRandAt_spqrInit hpqr (termRandAt_spqrParams i S g T .a2b), fun c hmem => ?_⟩
  rcases List.mem_singleton.mp hmem with rfl; exact ⟨hspk, hck⟩
private def BobHandshakeOk (o : BobHandshakeOut) : Prop :=
  TermRandAt i S g T o.ikA ∧ TermRandAt i S g T o.ikB ∧ TermRandAt i S g T o.spkSk ∧
  TermRandAt i S g T o.keys.rk ∧ TermRandAt i S g T o.keys.ck ∧ TermRandAt i S g T o.keys.pqr ∧ TermRandAt i S g T o.ek
private theorem TRand.bobHandshake (b a : Participant) (h : BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TRand (i := i) (S := S) (g := g) (T := T) (BobHandshakeOk (i := i) (S := S) (g := g) (T := T)) (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TRand.bind (TRand.getKey b h.ik .identity); intro ikB hikB
  apply TRand.bind (TRand.getKey b h.spk .signedPrekey); intro spkSk hspkSk
  apply TRand.bind (TRand.getKey b h.pqspk .pqPrekey); intro pqsk hpqsk
  cases h.opk <;> dsimp only
  · apply TRand.bind (TRand.pure (Q := fun opkSk : Option DY.Bytes =>
        ∀ o, opkSk = some o → TermRandAt i S g T o) (fun _ hc => by cases hc)); intro _ hopk
    apply TRand.bind (TRand.lookupIdentity a regIdxA); intro p hkv
    rcases p with ⟨_, _⟩; dsimp only
    apply TRand.bind (TRand.receiveMessage ekIdx); intro ek hek
    apply TRand.bind (TRand.receiveMessage ctIdx); intro ct hct
    apply TRand.bind (TRand.guardP _); intro _ _
    split
    · next keys hba => obtain ⟨hrk, hck, hpqr⟩ := termRandAt_bobAgreement hikB hspkSk hpqsk hopk hkv.1 hek hct hba; exact TRand.pure ⟨hkv.1, termRandAt_dhPk hikB, hspkSk, hrk, hck, hpqr, hek⟩
    · exact TRand.failure
  · apply TRand.bind (TRand.getKey b _ .oneTimePrekey); intro o ho
    apply TRand.bind (TRand.pure (Q := fun opkSk : Option DY.Bytes =>
        ∀ o', opkSk = some o' → TermRandAt i S g T o') (fun _ hc => Option.some.inj hc ▸ ho)); intro _ hopk
    apply TRand.bind (TRand.lookupIdentity a regIdxA); intro p hkv
    rcases p with ⟨_, _⟩; dsimp only
    apply TRand.bind (TRand.receiveMessage ekIdx); intro ek hek
    apply TRand.bind (TRand.receiveMessage ctIdx); intro ct hct
    apply TRand.bind (TRand.guardP _); intro _ _
    split
    · next keys hba => obtain ⟨hrk, hck, hpqr⟩ := termRandAt_bobAgreement hikB hspkSk hpqsk hopk hkv.1 hek hct hba; exact TRand.pure ⟨hkv.1, termRandAt_dhPk hikB, hspkSk, hrk, hck, hpqr, hek⟩
    · exact TRand.failure
private theorem TRand.bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TRand.bind (TRand.bobHandshake b a kh regIdxA mh.ek mh.ct) fun o ho => TRand.bind (TRand.receiveSignalMsg mh.msg) fun msg hmsg => ?_
  rcases ho with ⟨hikA, hikB, hspkSk, hrk, hck, hpqr, hek⟩
  have hst0 : StateRandAt i S g T
      { peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk, dhs := o.spkSk, cks := o.keys.ck,
        ns := 0, pn := 0, sid := Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
        initiator := false, rIdx := 0, recv := [], spqr := DY.Spqr.spqrInit o.keys.pqr spqrB2A } :=
    ⟨termRandAt_serializedIk hikB, termRandAt_serializedIk hikA, hrk, hspkSk, hck,
     termRandAt_concat (termRandAt_x25519Key hmsg.2.2.1) hrk, termRandAt_spqrInit hpqr (termRandAt_spqrParams i S g T .b2a), fun _ hmem => nomatch hmem⟩
  refine TRand.bind (TRand.ensureReceiverChain hst0 hmsg.2.2.1) fun ⟨st, c, ratcheted⟩ ⟨hst, hc⟩ => ?_
  dsimp only; split
  · next seed c' hcm =>
    obtain ⟨_, hc'⟩ := termRandAt_consumeMessageKey hc hcm; split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := termRandAt_spqrRecv hst.2.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      refine TRand.bind (TRand.sendMessage hkey) fun _ _ => TRand.bind (TRand.receiveMessage pqIdx) fun pqSalt _ =>
        TRand.bind (TRand.verifyMacAndDecrypt hmsg) fun m hm => ?_
      have htail : ∀ doneIdx, TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True)
          (do if ratcheted then
                DY.ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DY.DiffieHellman.dhPk st.dhs))
                DY.ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
              DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
              let skipped := msg.counter.toNat - c.index.toNat
              let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
              DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
              DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
              DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
                { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
        intro doneIdx
        have hfin : ∀ _ : Bool, TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True)
            (do DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
                let skipped := msg.counter.toNat - c.index.toNat
                let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
                DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
                DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
                DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
                  { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun _ =>
          TRand.bind (TRand.logCEvent _) fun _ _ => TRand.bind TRand.traceLength fun _ _ =>
          TRand.bind (TRand.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
          TRand.bind (TRand.logEvent (ev := TREvent.Received b st.peer msg.ratchetKey msg.counter m) hm) fun _ _ =>
          TRand.logMessageKeyAndStore b _ .receiver _ _ _ _ _ (stateRandAt_setRecvChain hst hc' hspqr')
        split
        · exact TRand.bind (TRand.logEvent trivial) fun _ _ => TRand.bind (TRand.logEvent trivial) fun _ _ => hfin true
        · exact hfin false
      cases o.opk <;> dsimp only
      · exact TRand.bind TRand.traceLength fun doneIdx _ => TRand.bind (TRand.logPQEvent hek) fun _ _ => htail doneIdx
      · exact TRand.bind (TRand.requireTracePredicate _) fun _ _ => TRand.bind (TRand.logPQEvent trivial) fun _ _ =>
          TRand.bind TRand.traceLength fun doneIdx _ => TRand.bind (TRand.logPQEvent hek) fun _ _ => htail doneIdx
    · exact TRand.failure
  · exact TRand.failure
private theorem termRandAt_of_dhSkOf {pk sk : DY.Bytes} (h : extractDhSecretKey (DY.X25519.normalizeX25519Key pk) = some sk) (hpk : TermRandAt i S g T pk) :
    TermRandAt i S g T sk := by
  have hk := termRandAt_x25519Key hpk; unfold DY.Libsignal.PQXDH.extractDhSecretKey at h; split at h <;> try cases h
  next hx =>
  have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (DY.X25519.normalizeX25519Key pk)
  change (DY.X25519.normalizeX25519Key pk).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk } at hx
  rw [hx] at hpv; rw [← hpv] at hk; exact (termRandAt_dhPk_pack i S g T { sk := sk }).mp hk
private theorem termRandAt_of_kemPkInvert {pk sk : DY.Bytes} (h : (DY.PQKem.invertKemPublicKey pk : Option DY.Bytes) = some sk) (hpk : TermRandAt i S g T pk) :
    TermRandAt i S g T sk := by
  unfold DY.PQKem.invertKemPublicKey at h; split at h <;> try cases h
  next hx =>
  have hpv := DY.Bytes.pack_view? DY.PQKem.Pk.SubF pk
  change pk.view? DY.PQKem.Pk.SubF = some { sk := sk } at hx; rw [hx] at hpv; rw [← hpv] at hpk; exact (termRandAt_kemPk_pack i S g T { sk := sk }).mp hpk
private theorem TRand.compromiseIK (p : Participant) (stateIdx : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.compromiseIK p stateIdx) :=
  TRand.bind (TRand.getKey p stateIdx .identity) fun _ hik => TRand.bind (TRand.logPQEvent trivial) fun _ _ => TRand.sendMessage hik
private theorem TRand.compromiseSPK (b : Participant) (stateIdx : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.compromiseSPK b stateIdx) :=
  TRand.bind (TRand.getKey b stateIdx .signedPrekey) fun _ hspk => TRand.bind (TRand.logPQEvent trivial) fun _ _ => TRand.sendMessage hspk
private theorem TRand.compromisePQSPK (b : Participant) (stateIdx : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.compromisePQSPK b stateIdx) :=
  TRand.bind (TRand.getKey b stateIdx .pqPrekey) fun _ hpqsk => TRand.bind (TRand.logPQEvent trivial) fun _ _ => TRand.sendMessage hpqsk
private theorem TRand.compromiseOPK (b : Participant) (stateIdx : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.compromiseOPK b stateIdx) :=
  TRand.bind (TRand.getKey b stateIdx .oneTimePrekey) fun _ hopk =>
    TRand.bind (TRand.requireTracePredicate _) fun _ _ =>
      TRand.bind (TRand.logPQEvent trivial) fun _ _ => TRand.sendMessage hopk
private theorem TRand.breakDH : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) DY.Libsignal.PQXDH.breakDH := TRand.logPQEvent trivial
private theorem TRand.breakKEM : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) DY.Libsignal.PQXDH.breakKEM := TRand.logPQEvent trivial
private theorem TRand.invertDH (pkIdx : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH; refine TRand.bind (TRand.requireTracePredicate _) fun _ _ => TRand.bind (TRand.receiveMessage pkIdx) fun pk hpk => ?_
  rcases hdh : extractDhSecretKey (DY.X25519.normalizeX25519Key pk) with _ | sk
  · exact TRand.failure
  · exact TRand.sendMessage (termRandAt_of_dhSkOf hdh hpk)
private theorem TRand.invertKEM (pkIdx : Nat) : TRand (i := i) (S := S) (g := g) (T := T) (fun _ => True) (DY.Libsignal.PQXDH.invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine TRand.bind (TRand.requireTracePredicate _) fun _ _ => TRand.bind (TRand.receiveMessage pkIdx) fun pk hpk =>
    TRand.bind (Q₁ := TermRandAt i S g T) (fun _ _ htr => by
      erw [DY.Traceful.run_mk]
      exact ⟨htr, fun _ hsk => termRandAt_of_kemPkInvert hsk hpk⟩) fun _ hsk => TRand.sendMessage hsk

private theorem traceEntriesRand_step (input : reachability.Input) (tr : ExecTrace)
    (hpre : reachability.PreCond input tr)
    (hle : (((reachability.step input).snd).run tr).2.val ≤ T)
    (htr : TraceEntriesRand i S g T tr) :
    TraceEntriesRand i S g T (((reachability.step input).snd).run tr).2.val := by
  rcases input with ⟨⟨k, hk⟩, inp⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k'
  · exact (TRand.sendMessage (traceEntriesRand_knows htr hpre) tr hle htr).1
  · exact (TRand.registerIdentity inp tr hle htr).1
  · rcases inp with ⟨p, skIdx⟩; exact (TRand.registerCorruptIdentity p skIdx tr hle htr).1
  · rcases inp with ⟨b, idStateIdx⟩; exact (TRand.genSignedPrekey b idStateIdx tr hle htr).1
  · rcases inp with ⟨b, idStateIdx⟩; exact (TRand.genPQPrekey b idStateIdx tr hle htr).1
  · exact (TRand.genOneTimePrekey inp tr hle htr).1
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact (TRand.aliceStart a b idStateIdx regIdxB bh tr hle htr).1
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact (TRand.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hle htr).1
  · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩; exact (TRand.messageEncrypt me stH coinsLen pqIdx tr hle htr).1
  · rcases inp with ⟨me, stH⟩; exact (TRand.messageEncryptAbort me stH tr hle htr).1
  · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩; exact (TRand.messageDecrypt me stH msgH pqIdx spqrMsgIdx tr hle htr).1
  · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩; exact (TRand.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx tr hle htr).1
  · rcases inp with ⟨me, stH, comp⟩; exact (TRand.exposeKey me stH comp tr hle htr).1
  · rcases inp with ⟨me, stH⟩; exact (TRand.exposeSpqr me stH tr hle htr).1
  · exact (TRand.exposeSkipped inp tr hle htr).1
  · rcases inp with ⟨p, stateIdx⟩; exact (TRand.compromiseIK p stateIdx tr hle htr).1
  · rcases inp with ⟨b, stateIdx⟩; exact (TRand.compromiseSPK b stateIdx tr hle htr).1
  · rcases inp with ⟨b, stateIdx⟩; exact (TRand.compromisePQSPK b stateIdx tr hle htr).1
  · rcases inp with ⟨b, stateIdx⟩; exact (TRand.compromiseOPK b stateIdx tr hle htr).1
  · exact (TRand.breakDH tr hle htr).1
  · exact (TRand.breakKEM tr hle htr).1
  · exact (TRand.invertDH inp tr hle htr).1
  · exact (TRand.invertKEM inp tr hle htr).1
  · omega

theorem traceEntriesRand_of_reachable_le {tr : ExecTrace} (hreach : tr.Reachable reachability)
    (hle : tr ≤ T) : TraceEntriesRand i S g T tr := by
  induction hreach with
  | Base => exact traceEntriesRand_nil
  | @Step tr₀ input hpre _ ih =>
    have hle₀ : tr₀ ≤ T := DY.Trace.le_trans _ _ _ (((reachability.step input).snd).run tr₀).2.property hle
    exact traceEntriesRand_step input tr₀ hpre hle (ih hle₀)

theorem traceEntriesRand_of_reachable (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) {tr : ExecTrace} (hreach : tr.Reachable reachability) :
    TraceEntriesRand i S g tr tr :=
  traceEntriesRand_of_reachable_le hreach (DY.Trace.le_refl tr)

end Core

/-! ## Memo-Entry Inversion and Non-`Random` Byte-Length Exclusion (`≠ 9`) -/

def MemoEntryProp (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (t : DY.Bytes) : Prop :=
  ∀ (u sh : DY.Bytes) (v : HwBytes),
    (u, sh, v) ∈ (gamma' i S g t).memo →
      v = gamma i S g u ∧
      ∀ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
        u = x.pack → (gamma i S g x.entropy).length = 32

unseal DY.Bytes in
theorem pack_of_view_eq_some {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    {u : DY.Bytes} {x : F DY.Bytes} (h : u.view? F = some x) : u = DY.BytesView.pack x := by
  have hp := DY.Bytes.pack_view? F u; rw [h] at hp; exact hp.symm

section UnsealedMemo
unseal DY.Bytes

private theorem partialFunDep_memo_step
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm) [DY.Bytes.SubFunction pf (concretizeAll i S g)]
    (hstep : ∀ (x : F DY.Bytes),
      (∀ (y : DY.Bytes), sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → MemoEntryProp i S g y) →
      gamma' i S g (DY.BytesView.pack x) = pf x (fun y _ => gamma' i S g y) →
      MemoEntryProp i S g (DY.BytesView.pack x)) :
    DY.ALaCarte.Container.PartialFunDep F (g := DY.BytesF) (MemoEntryProp i S g) := by
  intro x ih
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x]
  apply hstep x ih; unfold gamma'; exact DY.Bytes.rec_eq pf (concretizeAll i S g) x

private theorem container_pack_inj_sub
    {F : Type → Type} [DY.ALaCarte.FunctorSizeOf F] [DY.ALaCarte.SubFunctorTC F DY.BytesF]
    (v : F (DY.ALaCarte.ContainerFor DY.BytesF)) :
    DY.ALaCarte.Container.pack DY.BytesF (DY.ALaCarte.SubFunctorTC.inj v) =
      DY.ALaCarte.Container.pack F v := by
  have hv := Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross F DY.BytesF v
  have hp := DY.ALaCarte.Container.pack_view DY.BytesF (DY.ALaCarte.Container.pack F v)
  rw [hv] at hp
  exact hp

private theorem partialFunDep_memo_step_sub
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm)
    (hstep : ∀ (x : F DY.Bytes),
      (∀ (y : DY.Bytes), sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → MemoEntryProp i S g y) →
      gamma' i S g (DY.BytesView.pack x) = pf x (fun y _ => gamma' i S g y) →
      MemoEntryProp i S g (DY.BytesView.pack x))
    (v : F (DY.ALaCarte.ContainerFor DY.BytesF))
    (rec : ∀ y : DY.ALaCarte.ContainerFor DY.BytesF,
      sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf v →
        MemoEntryProp i S g y)
    (hsub : DY.Bytes.SubFunction pf (concretizeAll i S g) := by
      refine @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => ?_⟩
      simp -failIfUnchanged only [concretizeAll,
        DY.Libsignal.Composed.Refinement.allFuns,
        DY.Libsignal.Composed.Refinement.litFuns,
        DY.Libsignal.Composed.Refinement.concatFuns,
        DY.Libsignal.Composed.Refinement.dhFuns,
        DY.Libsignal.Composed.Refinement.kdfFuns,
        DY.Libsignal.Composed.Refinement.symFuns,
        DY.Libsignal.Composed.Refinement.truncFuns,
        DY.Libsignal.Composed.Refinement.x25519Funs,
        DY.Libsignal.Composed.Refinement.kemFuns,
        DY.Libsignal.Composed.Refinement.sigFuns,
        DY.Libsignal.Composed.Refinement.spqrFuns,
        DY.Libsignal.Composed.Refinement.trWireFuns,
        Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
      rfl) :
    MemoEntryProp i S g
      (DY.ALaCarte.Container.pack DY.BytesF (DY.ALaCarte.SubFunctorTC.inj (g := DY.BytesF) v)) := by
  have := hsub
  rw [container_pack_inj_sub v]
  exact partialFunDep_memo_step i S g pf hstep v rec

private theorem rec_eq_concretizeAll
    {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm) (x : F DY.Bytes)
    (hsub : DY.Bytes.SubFunction pf (concretizeAll i S g) := by
      refine @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => ?_⟩
      simp -failIfUnchanged only [concretizeAll,
        DY.Libsignal.Composed.Refinement.allFuns,
        DY.Libsignal.Composed.Refinement.litFuns,
        DY.Libsignal.Composed.Refinement.concatFuns,
        DY.Libsignal.Composed.Refinement.dhFuns,
        DY.Libsignal.Composed.Refinement.kdfFuns,
        DY.Libsignal.Composed.Refinement.symFuns,
        DY.Libsignal.Composed.Refinement.truncFuns,
        DY.Libsignal.Composed.Refinement.x25519Funs,
        DY.Libsignal.Composed.Refinement.kemFuns,
        DY.Libsignal.Composed.Refinement.sigFuns,
        DY.Libsignal.Composed.Refinement.spqrFuns,
        DY.Libsignal.Composed.Refinement.trWireFuns,
        Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
      rfl) :
    DY.Bytes.rec (concretizeAll i S g) (DY.BytesView.pack x) =
      pf x (fun y _ => DY.Bytes.rec (concretizeAll i S g) y) := by
  have := hsub
  exact DY.Bytes.rec_eq pf (concretizeAll i S g) x

private theorem memoEntryProp_node {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {v : HwBytes} {self sh : DY.Bytes} {kids : List DY.Bytes}
    (hge : gamma' i S g self = node v self sh (kids.map (gamma' i S g)))
    (hnot_ss : self.view? DY.PQKem.SharedSecret.SubF = none)
    (hkids : ∀ y ∈ kids, MemoEntryProp i S g y) :
    MemoEntryProp i S g self := by
  intro u sh' v' hmem; rw [hge] at hmem
  rcases List.mem_cons.mp hmem with ⟨rfl, rfl, rfl⟩ | hmem'
  · refine ⟨by unfold gamma; rw [hge]; rfl, fun x hx => ?_⟩
    rw [hx, BytesView.view_pack x] at hnot_ss; cases hnot_ss
  · obtain ⟨c, hc, hcm⟩ := List.mem_flatMap.mp hmem'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
    exact hkids y hy u sh' v' hcm

private theorem memoEntryProp_opaque {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {self : DY.Bytes} {ct : ConcretizedTerm} {kids : List DY.Bytes}
    (hge : gamma' i S g self = ct)
    (hmemo : ct.memo = (kids.map (gamma' i S g)).flatMap (·.memo))
    (hkids : ∀ y ∈ kids, MemoEntryProp i S g y) :
    MemoEntryProp i S g self := by
  intro u sh' v' hmem; rw [hge, hmemo] at hmem
  obtain ⟨c, hc, hcm⟩ := List.mem_flatMap.mp hmem
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
  exact hkids y hy u sh' v' hcm

private theorem mem_kids_1 {P : DY.Bytes → Prop} {a : DY.Bytes} (ha : P a) : ∀ y ∈ [a], P y := by
  intro y hy; rw [List.mem_singleton.mp hy]; exact ha
private theorem mem_kids_2 {P : DY.Bytes → Prop} {a b : DY.Bytes} (ha : P a) (hb : P b) :
    ∀ y ∈ [a, b], P y := by
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl <;> assumption
private theorem mem_kids_3 {P : DY.Bytes → Prop} {a b c : DY.Bytes} (ha : P a) (hb : P b) (hc : P c) :
    ∀ y ∈ [a, b, c], P y := by
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl <;> assumption

theorem memo_entry_inv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (t : DY.Bytes) : MemoEntryProp i S g t := by
  refine DY.ALaCarte.Container.rec (f := DY.BytesF) (motive := MemoEntryProp i S g) ?_ t
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    refine partialFunDep_memo_step_sub i S g (concretizeRandom g) ?_ val rec
    intro x _ hg; dsimp only [concretizeRandom] at hg
    by_cases h0 : x.size = 0
    · simp only [h0, ↓reduceIte] at hg; intro _ _ _ hm; rw [hg] at hm; cases hm
    · simp only [h0, ↓reduceIte] at hg; exact memoEntryProp_node (kids := []) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (fun _ hy => nomatch hy)
  | 1 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g concretizeLit ?_ v rec; intro _ _ hg
           exact memoEntryProp_node (kids := []) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (fun _ hy => nomatch hy)
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g concretizeConcat ?_ v rec; intro ⟨l, r⟩ ih hg
           exact memoEntryProp_node (kids := [l, r]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeDhPk i) ?_ v rec; intro ⟨s⟩ ih hg
           exact memoEntryProp_node (kids := [s]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_1 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 1 => refine partialFunDep_memo_step_sub i S g (concretizeDh i) ?_ v rec; intro ⟨p, s⟩ ih hg
           exact memoEntryProp_node (kids := [p, s]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeKdf i) ?_ v rec; intro ⟨a, b⟩ ih hg
           exact memoEntryProp_node (kids := [a, b]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeSym i) ?_ v rec; intro ⟨k, iv, m⟩ ih hg
           exact memoEntryProp_node (kids := [k, iv, m]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_3 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g concretizeTrunc ?_ v rec; intro ⟨a⟩ ih hg
           exact memoEntryProp_node (kids := [a]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_1 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeVariant i) ?_ v rec; intro ⟨k, _, _⟩ ih hg
           exact memoEntryProp_node (kids := [k]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_1 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeKemPk S) ?_ v rec; intro ⟨s⟩ ih hg
           exact memoEntryProp_opaque (kids := [s]) hg rfl (mem_kids_1 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 1 =>
      refine partialFunDep_memo_step_sub i S g (concretizeKemEncap i) ?_ v rec; intro ⟨p, e⟩ ih hg; dsimp only [concretizeKemEncap] at hg
      have hk := mem_kids_2 (ih p (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih e (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]))
      by_cases h32 : (gamma' i S g e).bytes.length = 32 <;> simp only [h32, ↓reduceIte] at hg
      · exact memoEntryProp_node (kids := [p, e]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) hk
      · exact memoEntryProp_opaque (kids := [p, e]) hg rfl hk
    | 2 =>
      refine partialFunDep_memo_step_sub i S g (concretizeKemSS i S) ?_ v rec; intro ⟨p, e⟩ ih hg; dsimp only [concretizeKemSS] at hg
      have hp := ih p (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])
      have he := ih e (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])
      by_cases h32 : (gamma' i S g e).bytes.length = 32 <;> simp only [h32, ↓reduceIte] at hg
      · intro u sh' v' hmem; rw [hg] at hmem
        rcases List.mem_cons.mp hmem with ⟨rfl, rfl, rfl⟩ | hmem'
        · refine ⟨by unfold gamma; rw [hg]; rfl, fun x' hx' => ?_⟩
          have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.SharedSecret.SubF) hx'
          rw [BytesView.view_pack ({ pk := p, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes), BytesView.view_pack x'] at hv
          injection hv with heq; cases heq; exact h32
        · obtain ⟨c, hc, hcm⟩ := List.mem_flatMap.mp hmem'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact hp u sh' v' hcm
          · exact he u sh' v' hcm
      · exact memoEntryProp_opaque (kids := [p, e]) hg rfl (mem_kids_2 hp he)
    | 3 => refine partialFunDep_memo_step_sub i S g (concretizeKemRej S) ?_ v rec; intro ⟨s, c⟩ ih hg
           exact memoEntryProp_node (kids := [s, c]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeVk S) ?_ v rec; intro ⟨s⟩ ih hg
           exact memoEntryProp_opaque (kids := [s]) hg rfl (mem_kids_1 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 1 => refine partialFunDep_memo_step_sub i S g (concretizeSign S) ?_ v rec; intro ⟨s, n, m⟩ ih hg
           exact memoEntryProp_opaque (kids := [s, n, m]) hg rfl (mem_kids_3 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrInit S) ?_ v rec; intro ⟨a, p⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, p]) hg rfl (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 1 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrSendState S) ?_ v rec; intro ⟨a, b⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, b]) hg rfl (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 2 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrSendKey S) ?_ v rec; intro ⟨a, b⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, b]) hg rfl (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 3 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrSendMsg S) ?_ v rec; intro ⟨a, b⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, b]) hg rfl (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 4 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrRecvState S) ?_ v rec; intro ⟨a, b⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, b]) hg rfl (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 5 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrRecvKey S) ?_ v rec; intro ⟨a, b⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, b]) hg rfl (mem_kids_2 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | 6 => refine partialFunDep_memo_step_sub i S g (concretizeSpqrChainKey S) ?_ v rec; intro ⟨a, p, idx⟩ ih hg
           exact memoEntryProp_opaque (kids := [a, p, idx]) hg rfl (mem_kids_3 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, _⟩, v⟩; match sid with
    | 0 => refine partialFunDep_memo_step_sub i S g (concretizeTrWire g) ?_ v rec; intro ⟨_, rk, _, _, ct, pq, _⟩ ih hg
           exact memoEntryProp_node (kids := [rk, ct, pq]) hg (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (mem_kids_3 (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])) (ih _ (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])))
    | n + 1 => omega
  | n + 12 => omega

theorem gamma'_randTerm_32 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) :
    (gamma' i S g (randTerm ts 32)).memo = [(randTerm ts 32, randTerm ts 32, g.σ ts 32)] ∧
      gamma i S g (randTerm ts 32) = g.σ ts 32 := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]; exact ⟨rfl, rfl⟩

theorem gamma_randTerm_of_ne_zero (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (rnd : DY.Random.Random DY.Bytes) (hne : rnd.size ≠ 0) :
    gamma i S g rnd.pack = g.σ rnd.timestamp rnd.size ∧ rnd.pack = randTerm rnd.timestamp rnd.size := by
  refine ⟨?_, rfl⟩; unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  dsimp only [concretizeRandom, node]; simp only [hne, ↓reduceIte]

theorem nonRandom_assumedInjective_len_ne_9
    (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes)
    (hinj : assumedInjective u = true)
    (hss32 : ∀ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
      u = x.pack → (gamma myInterp S g x.entropy).length = 32)
    (hlen9 : (gamma myInterp S g u).length = 9) :
    ∃ rnd : DY.Random.Random DY.Bytes, u.view? DY.Random.Random = some rnd ∧ rnd.size ≠ 0 := by
  rcases (assumedInjective_eq_true_iff u).mp hinj with
    hrnd | hdhPk | hdh | hkdf | hsym | htrunc | hencap | hss
  · exact hrnd
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdhPk; rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma myInterp S g x.pack).length = 32 := by
      unfold gamma gamma'; rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) (concretizeDhPk myInterp) x]
      exact length_myInterp_dhPk _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdh; rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma myInterp S g x.pack).length = 32 := by
      unfold gamma gamma'; rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) (concretizeDh myInterp) x]
      exact length_myInterp_dh _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hkdf; rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma myInterp S g x.pack).length = 32 := by
      unfold gamma gamma'; rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) (concretizeKdf myInterp) x]
      exact length_hmacWith_32 (sha256CompressFunction myInterp) _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsym; rcases pack_of_view_eq_some hx with rfl
    have hg : 16 ≤ (gamma myInterp S g x.pack).length := by
      unfold gamma gamma'; rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) (concretizeSym myInterp) x]
      exact le_length_myInterp_aesEnc _ _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htrunc; rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma myInterp S g x.pack).length ≤ 8 := by
      unfold gamma gamma'; rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) concretizeTrunc x]
      exact List.length_take_le 8 _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hencap; rcases pack_of_view_eq_some hx with rfl
    unfold gamma gamma' at hlen9
    rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) (concretizeKemEncap myInterp) x] at hlen9
    dsimp only [concretizeKemEncap] at hlen9; split at hlen9
    · have hg : ((((myInterp kyberEncapsSymbol
          [(x.pk.rec (concretizeAll myInterp S g)).bytes,
           (x.entropy.rec (concretizeAll myInterp S g)).bytes]).getD []).take 1568)).length = 1568 :=
        length_myInterp_kyberEncap_take _ _
      dsimp only [node] at hlen9; omega
    · dsimp only [opaqueNode] at hlen9; cases hlen9
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hss; rcases pack_of_view_eq_some hx with rfl
    have he32 := hss32 x rfl
    have hg : (gamma myInterp S g x.pack).length = 32 := by
      unfold gamma gamma'; rw [rec_eq_concretizeAll (i := myInterp) (S := S) (g := g) (concretizeKemSS myInterp S) x]
      dsimp only [concretizeKemSS]
      simp only [show ((x.entropy.rec (concretizeAll myInterp S g)).bytes).length = 32 from he32, ↓reduceIte]
      exact length_myInterp_kyberEncap_drop _ _
    omega

end UnsealedMemo

end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
