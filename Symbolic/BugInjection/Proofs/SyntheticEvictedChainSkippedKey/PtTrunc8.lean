/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Monad
public import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Swarm.UA.HwKnows
import Symbolic.Proofs.Swarm.UA.XlateSteps
import DY.Bytes.Basic
import DY.Misc.Fixpoint
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.DYBridge.DY.Misc.Fixpoint

/-!
# Reachable-Trace `Trunc8` Invariant

Proves `prefixTerms_trunc8OK`: on any explained CLI prefix, every `DY.Trunc.Trunc8.SubF` memo
entry `(u, sh, v) ∈ (gamma' i S g t).memo` of any `t ∈ prefixTerms r (runTrace r ss) vis` either
satisfies `u.AttackerKnows (runTrace r ss)` or has byte length `8 ≤ v.length` (from honest
`computeMac` over 32-byte HMAC outputs).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.TripleRatchet
  (TREvent hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 createChain spqrB2A setRecvChain)
open DY.Libsignal.PQXDH
  (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles
   HandshakeKeys AliceHandshakeOut BobHandshakeOut zeroSalt pqxdhLabel
   serializedIk agree pqxdhIkm pqxdhKdf aliceAgreement bobAgreement extractDhSecretKey)
open DY.Libsignal.Composed (ComposedEvent reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   randTerm newRandoms aliceDraws aliceVis bobOpkPk bobVis encDraws encSendEntry decVis
   invertEntry stepView runSteps runTrace
   storedStates storedSecrets principalTerms
   runWrapped MatchesEventsAt Explains HwAttackerKnows
   plaintextTerms prefixTerms)
open DY.Libsignal.Composed.Refinement.Cli.UA
  (hwAttackerKnows_implies_attackerKnows_of_explains')
open Symbolic.BugInjection.Proofs.Common443.Census443Memo
  (memoOK_dhPk_elim memoOK_x25519Key memoOK_kemPk memoOK_spqrInit)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (memoOK_vk memoOK_sign)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (StEntry PQStEntry)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (runSteps_reachable exposures_kind encSendEntry_kind)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim
  (Trunc8RowOK TermTrunc8OK StateTrunc8 PQEventTrunc8
   termTrunc8OK_rand termTrunc8OK_lit termTrunc8OK_concat termTrunc8OK_dhPk termTrunc8OK_dh
   termTrunc8OK_kemEncap termTrunc8OK_kemDecap termTrunc8OK_kemRejKey memoOK_kemPk_elim termTrunc8OK_spqrRecv
   termTrunc8OK_hmac termTrunc8OK_hkdfBlock1 termTrunc8OK_hkdfBlock2 termTrunc8OK_hkdfBlock3
   termTrunc8OK_createChain termTrunc8OK_serialize_tr termTrunc8OK_serialize_pq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Monad
  (TraceEntriesTrunc8 traceEntriesTrunc8_nil traceEntriesTrunc8_knows
   traceEntriesTrunc8_at?_st traceEntriesTrunc8_at?_pqst
   TTrunc termTrunc8OK_consumeMessageKey stateTrunc8_setRecvChain)

export Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8Prim
  (Trunc8RowOK TermTrunc8OK)

section Algebra
variable {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {T : ExecTrace}

private theorem TTrunc.registerIdentity (p : Participant) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.registerIdentity p) :=
  TTrunc.bind (TTrunc.requireTracePredicate _) fun _ _ =>
    TTrunc.bind (TTrunc.genRand 32) fun sk hik =>
    TTrunc.bind (TTrunc.logPQEvent (ev := PQXDHEvent.IdentityRegistered p (DY.DiffieHellman.dhPk sk) (DY.Signature.vk sk) true)
      ⟨termTrunc8OK_dhPk hik, memoOK_vk hik⟩) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (termTrunc8OK_dhPk hik)) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (memoOK_vk hik)) fun _ _ => TTrunc.storePQLocalState p hik

private theorem TTrunc.registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) :=
  TTrunc.bind (TTrunc.requireTracePredicate _) fun _ _ =>
    TTrunc.bind (TTrunc.receiveMessage skIdx) fun sk hik =>
    TTrunc.bind (TTrunc.logPQEvent (ev := PQXDHEvent.IdentityRegistered p (DY.DiffieHellman.dhPk sk) (DY.Signature.vk sk) false)
      ⟨termTrunc8OK_dhPk hik, memoOK_vk hik⟩) fun _ _ =>
    TTrunc.logPQEvent trivial

private theorem TTrunc.genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.genSignedPrekey b idStateIdx) :=
  TTrunc.bind (TTrunc.getKey b idStateIdx .identity) fun _ hik =>
    TTrunc.bind (TTrunc.genRand 32) fun _ hspk =>
    TTrunc.bind (TTrunc.genRand 64) fun _ hnonce =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ =>
    TTrunc.bind (TTrunc.storePQLocalState b hspk) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (termTrunc8OK_dhPk hspk)) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (memoOK_sign hik hnonce (termTrunc8OK_concat (termTrunc8OK_lit _) (termTrunc8OK_dhPk hspk))))
      fun _ _ => TTrunc.pure trivial

private theorem TTrunc.genPQPrekey (b : Participant) (idStateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.genPQPrekey b idStateIdx) :=
  TTrunc.bind (TTrunc.getKey b idStateIdx .identity) fun _ hik =>
    TTrunc.bind (TTrunc.genRand 64) fun _ hpqsk =>
    TTrunc.bind (TTrunc.genRand 64) fun _ hnonce =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ =>
    TTrunc.bind (TTrunc.storePQLocalState b hpqsk) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (memoOK_kemPk hpqsk)) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (memoOK_sign hik hnonce (termTrunc8OK_concat (termTrunc8OK_lit _) (memoOK_kemPk hpqsk))))
      fun _ _ => TTrunc.pure trivial

private theorem TTrunc.genOneTimePrekey (b : Participant) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.genOneTimePrekey b) :=
  TTrunc.bind (TTrunc.genRand 32) fun _ hopk =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ =>
    TTrunc.bind (TTrunc.storePQLocalState b hopk) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage (termTrunc8OK_dhPk hopk)) fun _ _ => TTrunc.pure trivial

private theorem termTrunc8OK_serializedIk {pk : DY.Bytes} (hpk : TermTrunc8OK i S g T pk) :
    TermTrunc8OK i S g T (serializedIk pk) :=
  termTrunc8OK_concat (termTrunc8OK_lit _) hpk

private theorem termTrunc8OK_agree {pk sk : DY.Bytes}
    (hpk : TermTrunc8OK i S g T pk) (hsk : TermTrunc8OK i S g T sk) :
    TermTrunc8OK i S g T (agree pk sk) :=
  termTrunc8OK_dh (memoOK_x25519Key hpk) hsk

private theorem termTrunc8OK_pqxdhIkm {dh1 dh2 dh3 : DY.Bytes} {dh4 : Option DY.Bytes} {ss : DY.Bytes}
    (h1 : TermTrunc8OK i S g T dh1) (h2 : TermTrunc8OK i S g T dh2) (h3 : TermTrunc8OK i S g T dh3)
    (h4 : ∀ x, dh4 = some x → TermTrunc8OK i S g T x) (hss : TermTrunc8OK i S g T ss) :
    TermTrunc8OK i S g T (pqxdhIkm dh1 dh2 dh3 dh4 ss) := by
  unfold pqxdhIkm
  refine termTrunc8OK_concat (termTrunc8OK_lit _)
    (termTrunc8OK_concat h1 (termTrunc8OK_concat h2 (termTrunc8OK_concat h3 ?_)))
  cases dh4 with
  | none => exact hss
  | some d => exact termTrunc8OK_concat (h4 d rfl) hss

private theorem termTrunc8OK_pqxdhKdf {ikm : DY.Bytes} (hikm : TermTrunc8OK i S g T ikm) :
    TermTrunc8OK i S g T (pqxdhKdf ikm).rk ∧
      TermTrunc8OK i S g T (pqxdhKdf ikm).ck ∧
      TermTrunc8OK i S g T (pqxdhKdf ikm).pqr := by
  have hprk : TermTrunc8OK i S g T (hmac zeroSalt ikm) := termTrunc8OK_hmac (termTrunc8OK_lit _) hikm
  have hinfo : TermTrunc8OK i S g T pqxdhLabel := termTrunc8OK_lit _
  exact ⟨termTrunc8OK_hkdfBlock1 hprk hinfo, termTrunc8OK_hkdfBlock2 hprk hinfo, termTrunc8OK_hkdfBlock3 hprk hinfo⟩

private theorem termTrunc8OK_aliceAgreement {ikA ek ikBPk spk pqpk : DY.Bytes}
    {opk : Option DY.Bytes} {entropy : DY.Bytes}
    (hikA : TermTrunc8OK i S g T ikA) (hek : TermTrunc8OK i S g T ek)
    (hikB : TermTrunc8OK i S g T ikBPk) (hspk : TermTrunc8OK i S g T spk)
    (hpqpk : TermTrunc8OK i S g T pqpk)
    (hopk : ∀ o, opk = some o → TermTrunc8OK i S g T o)
    (hent : TermTrunc8OK i S g T entropy) :
    TermTrunc8OK i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).1 ∧
      TermTrunc8OK i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.rk ∧
      TermTrunc8OK i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.ck ∧
      TermTrunc8OK i S g T (aliceAgreement ikA ek ikBPk spk pqpk opk entropy).2.pqr := by
  unfold aliceAgreement
  obtain ⟨hct, hss⟩ := termTrunc8OK_kemEncap hpqpk hent
  have hikm : TermTrunc8OK i S g T
      (pqxdhIkm (agree spk ikA) (agree ikBPk ek) (agree spk ek) (opk.map (agree · ek))
        (DY.PQKem.kemEncap pqpk entropy).2) := by
    refine termTrunc8OK_pqxdhIkm
      (termTrunc8OK_agree hspk hikA) (termTrunc8OK_agree hikB hek) (termTrunc8OK_agree hspk hek) ?_ hss
    intro d hd; cases opk with
    | none => cases hd
    | some o =>
      simp only [Option.map_some, Option.some.injEq] at hd
      subst hd
      exact termTrunc8OK_agree (hopk o rfl) hek
  obtain ⟨hrk, hck, hpqr⟩ := termTrunc8OK_pqxdhKdf hikm
  exact ⟨hct, hrk, hck, hpqr⟩

private theorem termTrunc8OK_bobAgreement {ikB spkSk pqsk : DY.Bytes}
    {opkSk : Option DY.Bytes} {ikAPk ek ct : DY.Bytes} {keys : HandshakeKeys}
    (hikB : TermTrunc8OK i S g T ikB) (hspkSk : TermTrunc8OK i S g T spkSk)
    (hpqsk : TermTrunc8OK i S g T pqsk)
    (hopkSk : ∀ o, opkSk = some o → TermTrunc8OK i S g T o)
    (hikA : TermTrunc8OK i S g T ikAPk) (hek : TermTrunc8OK i S g T ek)
    (hct : TermTrunc8OK i S g T ct)
    (hba : bobAgreement ikB spkSk pqsk opkSk ikAPk ek ct = some keys) :
    TermTrunc8OK i S g T keys.rk ∧ TermTrunc8OK i S g T keys.ck ∧ TermTrunc8OK i S g T keys.pqr := by
  unfold bobAgreement at hba
  simp only [Pure.pure, Option.some.injEq] at hba
  subst hba
  have hss : TermTrunc8OK i S g T
      ((DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct)).getD
        (DY.PQKem.kemRejKey pqsk ct)) := by
    rcases hdec : DY.PQKem.kemDecap pqsk ct with _ | ss
    · exact termTrunc8OK_kemRejKey hpqsk hct
    · exact termTrunc8OK_kemDecap hdec hct
  have hdh4 : ∀ x, (opkSk.map fun o => agree ek o) = some x → TermTrunc8OK i S g T x := by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact termTrunc8OK_agree hek (hopkSk o ho)
  exact termTrunc8OK_pqxdhKdf
    (termTrunc8OK_pqxdhIkm (termTrunc8OK_agree hikA hspkSk) (termTrunc8OK_agree hek hikB)
      (termTrunc8OK_agree hek hspkSk) hdh4 hss)

private def AliceHandshakeTrunc8 (o : AliceHandshakeOut) : Prop :=
  TermTrunc8OK i S g T o.ikA ∧ TermTrunc8OK i S g T o.ikB ∧ TermTrunc8OK i S g T o.spk ∧
  TermTrunc8OK i S g T o.pqpk ∧ (∀ opk, o.opk = some opk → TermTrunc8OK i S g T opk) ∧
  TermTrunc8OK i S g T o.ek ∧ TermTrunc8OK i S g T o.ct ∧
  TermTrunc8OK i S g T o.keys.rk ∧ TermTrunc8OK i S g T o.keys.ck ∧ TermTrunc8OK i S g T o.keys.pqr

private theorem TTrunc.aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : BundleHandles) :
    TTrunc (i := i) (S := S) (g := g) (T := T)
      (AliceHandshakeTrunc8 (i := i) (S := S) (g := g) (T := T))
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TTrunc.bind (TTrunc.getKey a idStateIdx .identity); intro ikA hikA
  apply TTrunc.bind (TTrunc.lookupIdentity b regIdxB); intro p hkv
  rcases p with ⟨ikB, _⟩; dsimp only
  apply TTrunc.bind (TTrunc.receiveMessage h.spk); intro spk hspk
  apply TTrunc.bind (TTrunc.receiveMessage h.spkSig); intro _ _
  apply TTrunc.bind (TTrunc.receiveMessage h.pqpk); intro pqpk hpqpk
  apply TTrunc.bind (TTrunc.receiveMessage h.pqpkSig); intro _ _
  apply TTrunc.bind (TTrunc.guardP _); intro _ _
  apply TTrunc.bind (TTrunc.guardP _); intro _ _
  cases h.opk <;> dsimp only
  · apply TTrunc.bind (TTrunc.pure (Q := fun opk : Option DY.Bytes =>
        ∀ o, opk = some o → TermTrunc8OK i S g T o) (fun _ hc => by cases hc)); intro opk hopk
    apply TTrunc.bind (TTrunc.genRand 32); intro ek hek
    apply TTrunc.bind (TTrunc.guardP _); intro _ _
    apply TTrunc.bind (TTrunc.guardP _); intro _ _
    apply TTrunc.bind (TTrunc.genRand 32); intro entropy hent
    obtain ⟨hct, hrk, hck, hpqr⟩ := termTrunc8OK_aliceAgreement hikA hek hkv.1 hspk hpqpk hopk hent
    exact TTrunc.pure ⟨termTrunc8OK_dhPk hikA, hkv.1, hspk, hpqpk, hopk, termTrunc8OK_dhPk hek, hct, hrk, hck, hpqr⟩
  · apply TTrunc.bind (TTrunc.receiveMessage _); intro o ho
    apply TTrunc.bind (TTrunc.pure (Q := fun opk : Option DY.Bytes =>
        ∀ o', opk = some o' → TermTrunc8OK i S g T o') (fun _ hc => Option.some.inj hc ▸ ho)); intro opk hopk
    apply TTrunc.bind (TTrunc.genRand 32); intro ek hek
    apply TTrunc.bind (TTrunc.guardP _); intro _ _
    apply TTrunc.bind (TTrunc.guardP _); intro _ _
    apply TTrunc.bind (TTrunc.genRand 32); intro entropy hent
    obtain ⟨hct, hrk, hck, hpqr⟩ := termTrunc8OK_aliceAgreement hikA hek hkv.1 hspk hpqpk hopk hent
    exact TTrunc.pure ⟨termTrunc8OK_dhPk hikA, hkv.1, hspk, hpqpk, hopk, termTrunc8OK_dhPk hek, hct, hrk, hck, hpqr⟩

private theorem TTrunc.aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : BundleHandles) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TTrunc.bind (TTrunc.aliceHandshake a b idStateIdx regIdxB h) fun o ho =>
    TTrunc.bind (TTrunc.genRand 32) fun dhsA hdhsA =>
    TTrunc.bind (TTrunc.sendMessage ho.2.2.2.2.2.1) fun _ _ =>
    TTrunc.bind (TTrunc.sendMessage ho.2.2.2.2.2.2.1) fun _ _ =>
    TTrunc.bind TTrunc.traceLength fun _ _ =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ =>
    TTrunc.bind (TTrunc.logEvent trivial) fun _ _ =>
    TTrunc.bind (TTrunc.logCEvent _) fun _ _ => ?_
  rcases ho with ⟨hikA, hikB, hspk, _, _, _, _, hrk, hck, hpqr⟩
  have hc := termTrunc8OK_createChain hrk hspk hdhsA
  refine TTrunc.storeLocalState a
    ⟨termTrunc8OK_serializedIk hikA, termTrunc8OK_serializedIk hikB, hc.1, hdhsA, hc.2,
     termTrunc8OK_concat (termTrunc8OK_dhPk hdhsA) hrk,
     memoOK_spqrInit hpqr (termTrunc8OK_lit _), fun c hmem => ?_⟩
  rcases List.mem_singleton.mp hmem with rfl
  exact ⟨hspk, hck⟩

private def BobHandshakeTrunc8 (o : BobHandshakeOut) : Prop :=
  TermTrunc8OK i S g T o.ikA ∧ TermTrunc8OK i S g T o.ikB ∧ TermTrunc8OK i S g T o.spkSk ∧
  TermTrunc8OK i S g T o.keys.rk ∧ TermTrunc8OK i S g T o.keys.ck ∧
  TermTrunc8OK i S g T o.keys.pqr ∧ TermTrunc8OK i S g T o.ek

private theorem TTrunc.bobHandshake (b a : Participant) (h : BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T)
      (BobHandshakeTrunc8 (i := i) (S := S) (g := g) (T := T))
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TTrunc.bind (TTrunc.getKey b h.ik .identity); intro ikB hikB
  apply TTrunc.bind (TTrunc.getKey b h.spk .signedPrekey); intro spkSk hspkSk
  apply TTrunc.bind (TTrunc.getKey b h.pqspk .pqPrekey); intro pqsk hpqsk
  cases h.opk <;> dsimp only
  · apply TTrunc.bind (TTrunc.pure (Q := fun opkSk : Option DY.Bytes =>
        ∀ o, opkSk = some o → TermTrunc8OK i S g T o) (fun _ hc => by cases hc)); intro _ hopk
    apply TTrunc.bind (TTrunc.lookupIdentity a regIdxA); intro p hkv
    rcases p with ⟨_, _⟩; dsimp only
    apply TTrunc.bind (TTrunc.receiveMessage ekIdx); intro ek hek
    apply TTrunc.bind (TTrunc.receiveMessage ctIdx); intro ct hct
    apply TTrunc.bind (TTrunc.guardP _); intro _ _
    split
    · next keys hba =>
      obtain ⟨hrk, hck, hpqr⟩ := termTrunc8OK_bobAgreement hikB hspkSk hpqsk hopk hkv.1 hek hct hba
      exact TTrunc.pure ⟨hkv.1, termTrunc8OK_dhPk hikB, hspkSk, hrk, hck, hpqr, hek⟩
    · exact TTrunc.failure
  · apply TTrunc.bind (TTrunc.getKey b _ .oneTimePrekey); intro o ho
    apply TTrunc.bind (TTrunc.pure (Q := fun opkSk : Option DY.Bytes =>
        ∀ o', opkSk = some o' → TermTrunc8OK i S g T o') (fun _ hc => Option.some.inj hc ▸ ho)); intro _ hopk
    apply TTrunc.bind (TTrunc.lookupIdentity a regIdxA); intro p hkv
    rcases p with ⟨_, _⟩; dsimp only
    apply TTrunc.bind (TTrunc.receiveMessage ekIdx); intro ek hek
    apply TTrunc.bind (TTrunc.receiveMessage ctIdx); intro ct hct
    apply TTrunc.bind (TTrunc.guardP _); intro _ _
    split
    · next keys hba =>
      obtain ⟨hrk, hck, hpqr⟩ := termTrunc8OK_bobAgreement hikB hspkSk hpqsk hopk hkv.1 hek hct hba
      exact TTrunc.pure ⟨hkv.1, termTrunc8OK_dhPk hikB, hspkSk, hrk, hck, hpqr, hek⟩
    · exact TTrunc.failure

private theorem TTrunc.bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TTrunc.bind (TTrunc.bobHandshake b a kh regIdxA mh.ek mh.ct) fun o ho =>
    TTrunc.bind (TTrunc.receiveSignalMsg mh.msg) fun msg hmsg => ?_
  rcases ho with ⟨hikA, hikB, hspkSk, hrk, hck, hpqr, hek⟩
  have hst0 : StateTrunc8 (i := i) (S := S) (g := g) (T := T)
      { peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA,
        rk := o.keys.rk, dhs := o.spkSk, cks := o.keys.ck,
        ns := 0, pn := 0, sid := DY.Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
        initiator := false, rIdx := 0, recv := [], spqr := DY.Spqr.spqrInit o.keys.pqr spqrB2A } :=
    ⟨termTrunc8OK_serializedIk hikB, termTrunc8OK_serializedIk hikA, hrk, hspkSk, hck,
     termTrunc8OK_concat (memoOK_x25519Key hmsg.2.2.1) hrk,
     memoOK_spqrInit hpqr (termTrunc8OK_lit _), fun _ hmem => nomatch hmem⟩
  refine TTrunc.bind (TTrunc.ensureReceiverChain hst0 hmsg.2.2.1) fun ⟨st, c, ratcheted⟩ ⟨hst, hc⟩ => ?_
  dsimp only; split
  · next seed c' hcm =>
    obtain ⟨_, hc'⟩ := termTrunc8OK_consumeMessageKey hc hcm; split
    · next spqr' key hspqr =>
      obtain ⟨hspqr', hkey⟩ := termTrunc8OK_spqrRecv hst.2.2.2.2.2.2.1 hmsg.2.2.2.2 hspqr
      refine TTrunc.bind (TTrunc.sendMessage hkey) fun _ _ =>
        TTrunc.bind (TTrunc.receiveMessage pqIdx) fun pqSalt _ =>
        TTrunc.bind (TTrunc.verifyMacAndDecrypt hmsg) fun m hm => ?_
      have htail : ∀ doneIdx, TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
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
        have hfin : ∀ _ : Bool, TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
            (do DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
                let skipped := msg.counter.toNat - c.index.toNat
                let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
                DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
                DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
                DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
                  { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun _ =>
          TTrunc.bind (TTrunc.logCEvent _) fun _ _ =>
          TTrunc.bind TTrunc.traceLength fun _ _ =>
          TTrunc.bind (TTrunc.logSkippedKeys _ _ _ _ hmsg.2.2.1 _ _ _ hc.2) fun _ _ =>
          TTrunc.bind (TTrunc.logEvent (ev := TREvent.Received b st.peer msg.ratchetKey msg.counter m) hm) fun _ _ =>
          TTrunc.logMessageKeyAndStore b _ .receiver _ _ _ _ _ (stateTrunc8_setRecvChain hst hc' hspqr')
        split
        · exact TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => TTrunc.bind (TTrunc.logEvent trivial) fun _ _ => hfin true
        · exact hfin false
      have hek_ev : PQEventTrunc8 (i := i) (S := S) (g := g) (T := T)
          (PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys) := hek
      cases o.opk <;> dsimp only
      · exact TTrunc.bind TTrunc.traceLength fun doneIdx _ =>
          TTrunc.bind (TTrunc.logPQEvent hek_ev) fun _ _ => htail doneIdx
      · exact TTrunc.bind (TTrunc.requireTracePredicate _) fun _ _ =>
          TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ =>
          TTrunc.bind TTrunc.traceLength fun doneIdx _ =>
          TTrunc.bind (TTrunc.logPQEvent hek_ev) fun _ _ => htail doneIdx
    · exact TTrunc.failure
  · exact TTrunc.failure

private theorem termTrunc8OK_of_dhSkOf {pk sk : DY.Bytes}
    (h : extractDhSecretKey (DY.X25519.normalizeX25519Key pk) = some sk)
    (hpk : TermTrunc8OK i S g T pk) :
    TermTrunc8OK i S g T sk := by
  have hk := memoOK_x25519Key hpk
  unfold extractDhSecretKey at h
  split at h <;> try cases h
  next hx =>
    have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (DY.X25519.normalizeX25519Key pk)
    change (DY.X25519.normalizeX25519Key pk).view? DY.DiffieHellman.DhPk.SubF = some { sk := sk } at hx
    rw [hx] at hpv
    change TermTrunc8OK i S g T (DY.X25519.normalizeX25519Key pk) at hk
    rw [← hpv] at hk
    exact memoOK_dhPk_elim hk

private theorem termTrunc8OK_of_kemPkInvert {pk sk : DY.Bytes}
    (h : (DY.PQKem.invertKemPublicKey pk : Option DY.Bytes) = some sk)
    (hpk : TermTrunc8OK i S g T pk) :
    TermTrunc8OK i S g T sk := by
  unfold DY.PQKem.invertKemPublicKey at h
  split at h <;> try cases h
  next hx =>
    have hpv := DY.Bytes.pack_view? DY.PQKem.Pk.SubF pk
    change pk.view? DY.PQKem.Pk.SubF = some { sk := sk } at hx
    rw [hx] at hpv
    rw [← hpv] at hpk
    exact memoOK_kemPk_elim hpk

private theorem TTrunc.compromiseIK (p : Participant) (stateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.compromiseIK p stateIdx) :=
  TTrunc.bind (TTrunc.getKey p stateIdx .identity) fun _ hik =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ => TTrunc.sendMessage hik

private theorem TTrunc.compromiseSPK (b : Participant) (stateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.compromiseSPK b stateIdx) :=
  TTrunc.bind (TTrunc.getKey b stateIdx .signedPrekey) fun _ hspk =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ => TTrunc.sendMessage hspk

private theorem TTrunc.compromisePQSPK (b : Participant) (stateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.compromisePQSPK b stateIdx) :=
  TTrunc.bind (TTrunc.getKey b stateIdx .pqPrekey) fun _ hpqsk =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ => TTrunc.sendMessage hpqsk

private theorem TTrunc.compromiseOPK (b : Participant) (stateIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.compromiseOPK b stateIdx) :=
  TTrunc.bind (TTrunc.getKey b stateIdx .oneTimePrekey) fun _ hopk =>
    TTrunc.bind (TTrunc.requireTracePredicate _) fun _ _ =>
    TTrunc.bind (TTrunc.logPQEvent trivial) fun _ _ => TTrunc.sendMessage hopk

private theorem TTrunc.breakDH :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) DY.Libsignal.PQXDH.breakDH :=
  TTrunc.logPQEvent trivial

private theorem TTrunc.breakKEM :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True) DY.Libsignal.PQXDH.breakKEM :=
  TTrunc.logPQEvent trivial

private theorem TTrunc.invertDH (pkIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine TTrunc.bind (TTrunc.requireTracePredicate _) fun _ _ =>
    TTrunc.bind (TTrunc.receiveMessage pkIdx) fun pk hpk => ?_
  rcases hdh : extractDhSecretKey (DY.X25519.normalizeX25519Key pk) with _ | sk
  · exact TTrunc.failure
  · exact TTrunc.sendMessage (termTrunc8OK_of_dhSkOf hdh hpk)

private theorem TTrunc.invertKEM (pkIdx : Nat) :
    TTrunc (i := i) (S := S) (g := g) (T := T) (fun _ => True)
      (DY.Libsignal.PQXDH.invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine TTrunc.bind (TTrunc.requireTracePredicate _) fun _ _ =>
    TTrunc.bind (TTrunc.receiveMessage pkIdx) fun pk hpk =>
    TTrunc.bind (Q₁ := TermTrunc8OK i S g T) (fun _ _ htr => by
      erw [DY.Traceful.run_mk]
      exact ⟨htr, fun _ hsk => termTrunc8OK_of_kemPkInvert hsk hpk⟩) fun _ hsk =>
    TTrunc.sendMessage hsk

private theorem traceEntriesTrunc8_step (input : reachability.Input) (tr : ExecTrace)
    (hpre : reachability.PreCond input tr)
    (hle : (((reachability.step input).snd).run tr).2.val ≤ T)
    (htr : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr) :
    TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T)
      (((reachability.step input).snd).run tr).2.val := by
  have hle₀ : tr ≤ T := DY.Trace.le_trans _ _ _ (((reachability.step input).snd).run tr).2.property hle
  rcases input with ⟨⟨k, hk⟩, inp⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k'
  · exact (TTrunc.sendMessage (traceEntriesTrunc8_knows hle₀ htr hpre) tr hle htr).1
  · exact (TTrunc.registerIdentity inp tr hle htr).1
  · rcases inp with ⟨p, skIdx⟩; exact (TTrunc.registerCorruptIdentity p skIdx tr hle htr).1
  · rcases inp with ⟨b, idStateIdx⟩; exact (TTrunc.genSignedPrekey b idStateIdx tr hle htr).1
  · rcases inp with ⟨b, idStateIdx⟩; exact (TTrunc.genPQPrekey b idStateIdx tr hle htr).1
  · exact (TTrunc.genOneTimePrekey inp tr hle htr).1
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact (TTrunc.aliceStart a b idStateIdx regIdxB bh tr hle htr).1
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact (TTrunc.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hle htr).1
  · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩; exact (TTrunc.messageEncrypt me stH coinsLen pqIdx tr hle htr).1
  · rcases inp with ⟨me, stH⟩; exact (TTrunc.messageEncryptAbort me stH tr hle htr).1
  · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩; exact (TTrunc.messageDecrypt me stH msgH pqIdx spqrMsgIdx tr hle htr).1
  · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩; exact (TTrunc.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx tr hle htr).1
  · rcases inp with ⟨me, stH, comp⟩; exact (TTrunc.exposeKey me stH comp tr hle htr).1
  · rcases inp with ⟨me, stH⟩; exact (TTrunc.exposeSpqr me stH tr hle htr).1
  · exact (TTrunc.exposeSkipped inp tr hle htr).1
  · rcases inp with ⟨p, stateIdx⟩; exact (TTrunc.compromiseIK p stateIdx tr hle htr).1
  · rcases inp with ⟨b, stateIdx⟩; exact (TTrunc.compromiseSPK b stateIdx tr hle htr).1
  · rcases inp with ⟨b, stateIdx⟩; exact (TTrunc.compromisePQSPK b stateIdx tr hle htr).1
  · rcases inp with ⟨b, stateIdx⟩; exact (TTrunc.compromiseOPK b stateIdx tr hle htr).1
  · exact (TTrunc.breakDH tr hle htr).1
  · exact (TTrunc.breakKEM tr hle htr).1
  · exact (TTrunc.invertDH inp tr hle htr).1
  · exact (TTrunc.invertKEM inp tr hle htr).1
  · omega

private theorem traceEntriesTrunc8_of_reachable_le {tr : ExecTrace} (hreach : tr.Reachable reachability)
    (hle : tr ≤ T) : TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := T) tr := by
  induction hreach with
  | Base => exact traceEntriesTrunc8_nil
  | @Step tr₀ input hpre _ ih =>
    have hle₀ : tr₀ ≤ T := DY.Trace.le_trans _ _ _ (((reachability.step input).snd).run tr₀).2.property hle
    exact traceEntriesTrunc8_step input tr₀ hpre hle (ih hle₀)

private theorem traceEntriesTrunc8_of_reachable (i : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) {tr : ExecTrace}
    (hreach : tr.Reachable reachability) :
    TraceEntriesTrunc8 (i := i) (S := S) (g := g) (T := tr) tr :=
  traceEntriesTrunc8_of_reachable_le hreach (DY.Trace.le_refl tr)

end Algebra

private theorem isRand_of_mem_newRandoms {tr₀ tr₁ : ExecTrace} {m : DY.Bytes} {n : Nat}
    (h : (m, n) ∈ newRandoms tr₀ tr₁) :
    ∃ ts, m = randTerm ts n := by
  unfold newRandoms at h
  obtain ⟨ts, _, hm⟩ := List.mem_filterMap.mp h
  rcases hat : (tr₁.at? ts : Option DY.Random.ExecEntryT) with _ | ⟨sz⟩
  · rw [hat] at hm; cases hm
  · rw [hat] at hm
    injection hm with hp
    injection hp with hm_eq hn_eq
    subst hm_eq hn_eq
    exact ⟨ts, rfl⟩

private theorem aliceDraws_kind (done : Option Nat) (xs : List DY.Bytes) {v : VisEntry}
    (hv : v ∈ aliceDraws done xs) : v.kind = .rng := by
  cases xs with
  | nil => cases hv
  | cons ek rest =>
    cases rest with
    | nil => rcases List.mem_singleton.mp hv with rfl; rfl
    | cons ent rest2 =>
      rcases List.mem_cons.mp hv with rfl | htail
      · rfl
      · rcases List.mem_append.mp htail with hkyb | hdhs
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkyb; rfl
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hdhs; rfl

private theorem encDraws_pt_isRand {tr₀ tr₁ : ExecTrace} {v : VisEntry}
    (hv : v ∈ encDraws (newRandoms tr₀ tr₁)) (hk : v.kind = .pt) {t : DY.Bytes}
    (ht : t ∈ v.terms) : ∃ ts sz, t = randTerm ts sz := by
  cases hnr : newRandoms tr₀ tr₁ with
  | nil => rw [hnr] at hv; cases hv
  | cons r0 rest =>
    rcases r0 with ⟨m0, n0⟩
    rw [hnr] at hv
    rcases List.mem_cons.mp hv with rfl | hrest
    · rcases List.mem_singleton.mp ht with rfl
      have hmem0 : (t, n0) ∈ newRandoms tr₀ tr₁ := by rw [hnr]; exact List.mem_cons_self
      obtain ⟨ts, heq⟩ := isRand_of_mem_newRandoms hmem0
      exact ⟨ts, n0, heq⟩
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrest
      cases hk

private theorem stepView_pt_isRand (s : Step) (tr₀ : ExecTrace) (wrapped : Bool) {v : VisEntry}
    (hv : v ∈ stepView s tr₀ wrapped) (hk : v.kind = .pt) {t : DY.Bytes} (ht : t ∈ v.terms) :
    ∃ ts sz, t = randTerm ts sz := by
  unfold stepView at hv
  rcases List.mem_append.mp hv with hv_if | hexp
  · have hv_own : v ∈ (match s with
        | .aliceStart _ _ _ _ h => aliceVis tr₀ (s.next tr₀) h
        | .bobStart b _ kh _ mh _ _ => bobVis tr₀ (s.next tr₀) mh (bobOpkPk b kh tr₀)
        | .messageEncrypt _ stateIdx .. =>
          encDraws (newRandoms tr₀ (s.next tr₀)) ++ encSendEntry tr₀ (s.next tr₀) stateIdx wrapped
        | .messageEncryptAbort .. => encDraws (newRandoms tr₀ (s.next tr₀))
        | .messageDecrypt _ stateIdx msgIdx .. => decVis tr₀ (s.next tr₀) stateIdx msgIdx wrapped
        | .messageDecryptSkipped _ stateIdx msgIdx .. =>
          decVis tr₀ (s.next tr₀) stateIdx msgIdx wrapped
        | _ => []) := by
      split at hv_if
      · exact hv_if
      · exact (List.mem_filter.mp hv_if).1
    cases s with
    | messageEncrypt _ _ _ _ =>
      rcases List.mem_append.mp hv_own with hd | hs
      · exact encDraws_pt_isRand hd hk ht
      · exact absurd (hk.symm.trans (encSendEntry_kind hs)) (by decide)
    | messageEncryptAbort _ _ => exact encDraws_pt_isRand hv_own hk ht
    | aliceStart _ _ _ _ _ =>
      rcases List.mem_cons.mp hv_own with rfl | hd
      · cases hk
      · rw [aliceDraws_kind _ _ hd] at hk; cases hk
    | bobStart _ _ _ _ _ _ _ =>
      rcases List.mem_cons.mp hv_own with rfl | hb
      · cases hk
      · rcases List.mem_append.mp hb with hrng | hacc
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; cases hk
        · rcases hp : DY.Libsignal.Composed.Refinement.receivedPlaintext tr₀ _ with _ | _
          · rw [hp] at hacc; cases hacc
          · rw [hp] at hacc; rcases List.mem_singleton.mp hacc with rfl; cases hk
    | messageDecrypt _ _ _ _ _ | messageDecryptSkipped _ _ _ _ _ _ =>
      unfold decVis at hv_own
      rcases List.mem_append.mp hv_own with hv12 | hacc
      · rcases List.mem_append.mp hv12 with hrecv | hrng
        · rcases hm : tr₀.getMessageSentAt _ with _ | _
          · rw [hm] at hrecv; cases hrecv
          · rw [hm] at hrecv; rcases List.mem_singleton.mp hrecv with rfl; cases hk
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; cases hk
      · rcases hp : DY.Libsignal.Composed.Refinement.receivedPlaintext tr₀ _ with _ | _
        · rw [hp] at hacc; cases hacc
        · rw [hp] at hacc; rcases List.mem_singleton.mp hacc with rfl; cases hk
    | _ => cases hv_own
  · exact absurd (hk.symm.trans (exposures_kind hexp)) (by decide)

private theorem invertEntry_not_pt {s : Step} {tr : ExecTrace}
    {lay : DY.Libsignal.Composed.Refinement.VisByteLayout} {v : VisEntry}
    (hv : v ∈ invertEntry s tr lay) : v.kind ≠ .pt := by
  unfold invertEntry at hv
  rcases hls : DY.Libsignal.Composed.Refinement.lastSent tr (s.next tr) with _ | sk
  · rw [hls] at hv; cases hv
  · rw [hls] at hv
    rcases List.mem_singleton.mp hv with rfl
    intro h; cases h

private theorem matchesEvents_pt_isRand {i : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr₀ : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hMe : MatchesEventsAt i r S g initIds tr₀ ss evs vis) {v : VisEntry}
    (hv : v ∈ vis) (hk : v.kind = .pt) {t : DY.Bytes} (ht : t ∈ v.terms) :
    ∃ ts sz, t = randTerm ts sz := by
  induction hMe with
  | nil _ => cases hv
  | run0 _ _ _ ih => exact ih hv
  | @run1 _ tr pre s _ ev _ _ _ _ hrm _ ih =>
    rcases List.mem_append.mp hv with hv1 | hvs
    · rw [hrm.2.2.2.2.2.2.1] at hv1
      exact stepView_pt_isRand s (runSteps pre tr) (runWrapped ev) hv1 hk ht
    · exact ih hvs
  | @env _ tr pre s _ ev _ _ _ _ hem _ ih =>
    rcases List.mem_append.mp hv with hv1 | hvs
    · cases ev with
      | registerCorrupt _ _ => exact False.elim hem
      | breakDH | breakKEM => rw [hem.2] at hv1; cases hv1
      | invertDH _ _ | invertKEM _ _ =>
        obtain ⟨_, _, _, _, hv_eq, _⟩ := hem
        rw [hv_eq] at hv1
        exact absurd hk (invertEntry_not_pt hv1)
      | leak _ _ =>
        rw [hem.2.2.2.1] at hv1
        exact stepView_pt_isRand s (runSteps pre tr) false hv1 hk ht
    · exact ih hvs

theorem prefixTerms_trunc8OK
    {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent}
    (hex : Explains i r S g ss vis evs₁)
    {t : DY.Bytes} (ht : t ∈ prefixTerms r (runTrace r ss) vis) :
    TermTrunc8OK i S g (runTrace r ss) t := by
  have hreach : (runTrace r ss).Reachable reachability :=
    runSteps_reachable ss hex.2.2.1.2.1 hex.2.2.1.2.2.1
  have htr := traceEntriesTrunc8_of_reachable i S g hreach
  unfold prefixTerms principalTerms at ht
  rcases List.mem_append.mp ht with hprin | hpt
  · rcases List.mem_append.mp hprin with h12 | hsec
    · rcases List.mem_append.mp h12 with hsend | hst
      · obtain ⟨v, hv_filt, ht_v⟩ := List.mem_flatMap.mp hsend
        obtain ⟨hv_vis, hv_kind⟩ := List.mem_filter.mp hv_filt
        have hk : v.kind = .send := beq_iff_eq.mp hv_kind
        have hhw : HwAttackerKnows r vis t := by
          unfold HwAttackerKnows
          rw [Symbolic.DYBridge.DY.Fixpoint.mkLeastFixpoint_eq_1]
          exact fun _ hstep => hstep t (Or.inr (Or.inr ⟨v, hv_vis, ht_v, by rw [hk]; trivial⟩))
        exact traceEntriesTrunc8_knows (DY.Trace.le_refl _) htr
          (hwAttackerKnows_implies_attackerKnows_of_explains' hex hhw)
      · obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
        unfold storedStates DY.ExecTrace.getLocalStateAt at hls
        obtain ⟨idx, _, hidx⟩ := List.mem_filterMap.mp hls
        rcases hat : ((runTrace r ss).at? idx : Option StEntry) with _ | e
        · rw [hat] at hidx; cases hidx
        · rw [hat] at hidx; injection hidx with he; subst he
          exact termTrunc8OK_serialize_tr e.st (traceEntriesTrunc8_at?_st htr hat)
    · unfold storedSecrets DY.ExecTrace.getLocalStateAt at hsec
      simp only [Option.map_map] at hsec
      obtain ⟨idx, _, hidx⟩ := List.mem_filterMap.mp hsec
      rcases hat : ((runTrace r ss).at? idx : Option PQStEntry) with _ | e
      · rw [hat] at hidx; cases hidx
      · rw [hat] at hidx; injection hidx with he; subst he
        exact termTrunc8OK_serialize_pq e.st (traceEntriesTrunc8_at?_pqst htr hat)
  · unfold plaintextTerms at hpt
    obtain ⟨v, hv_filt, ht_v⟩ := List.mem_flatMap.mp hpt
    obtain ⟨hv_vis, hv_kind⟩ := List.mem_filter.mp hv_filt
    have hk : v.kind = .pt := beq_iff_eq.mp hv_kind
    obtain ⟨ts, sz, rfl⟩ := matchesEvents_pt_isRand hex.2.2.2 hv_vis hk ht_v
    exact termTrunc8OK_rand i S g (runTrace r ss) ts sz

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8
