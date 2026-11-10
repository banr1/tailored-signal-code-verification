/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRkCore
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Provenance-Indexed Honest-Spine Invariant

Proves preservation of `TraceOkR` across PQXDH key management, handshakes, session starts, and
composed moves, yielding `traceOkR_runTrace`, `spStateRk_runTrace`, `spineRk_send_runTrace`, and
`spineRk_recvSeed_runTrace`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (setRecvChain kdfCk createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf agree)

/-! ## PQXDH key management -/

section PQ

variable {T : ExecTrace} {k : Nat}

theorem tracefulF_compromiseIK (p : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseIK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact TracefulF.bind (TracefulF.getKey p j _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ _ => TracefulF.sendMessage _

theorem tracefulF_compromiseSPK (p : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact TracefulF.bind (TracefulF.getKey p j _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ _ => TracefulF.sendMessage _

theorem tracefulF_compromisePQSPK (p : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromisePQSPK p j) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact TracefulF.bind (TracefulF.getKey p j _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ _ => TracefulF.sendMessage _

theorem tracefulF_compromiseOPK (p : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.compromiseOPK p j) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact TracefulF.bind (TracefulF.getKey p j _) fun _ _ _ _ =>
    TracefulF.bind (tracefulF_guardOnTrace _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ _ => TracefulF.sendMessage _

theorem tracefulF_registerIdentity (p : Participant) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine TracefulF.bind (tracefulF_guardOnTrace _) fun _ _ _ _ => ?_
  refine TracefulF.bindE (TracefulF.genRand 32) fun ik m _ hg => ?_
  obtain ⟨L, _, rfl, rfl, _⟩ := hg
  refine TracefulR.bindF (TracefulR.logEventPQ _) fun _ m₁ _ hl => ?_
  obtain ⟨hev, _, rfl⟩ := hl
  refine TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.storeLocalStatePQ p (st := { kind := .identity, sk := randTerm L 32 }) ?_
  exact ⟨L, by omega, rfl, hev⟩

theorem tracefulF_genSignedPrekey (b : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine TracefulF.bind (TracefulF.getKey b j _) fun _ _ _ _ => ?_
  refine TracefulF.bindE (TracefulF.genRand 32) fun spk m _ hg => ?_
  obtain ⟨L, _, rfl, rfl, _⟩ := hg
  refine TracefulR.bind (TracefulR.genRand 64) fun _ m₁ _ hn => ?_
  obtain ⟨_, hne, rfl⟩ := hn
  refine TracefulR.bindF (TracefulR.logEventPQ _) fun _ m₂ _ hl => ?_
  obtain ⟨hev, _, rfl⟩ := hl
  refine TracefulF.bind
    (TracefulF.storeLocalStatePQ b (st := { kind := .signedPrekey, sk := randTerm L 32 }) ?_)
    fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ => TracefulF.pure fun _ _ => trivial
  exact ⟨L, by omega, rfl, hne, hev⟩

theorem tracefulF_genPQPrekey (b : Participant) (j : Nat) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact TracefulF.bind (TracefulF.getKey b j _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.genRand 64) fun pqsk _ _ _ =>
    TracefulF.bind (TracefulF.genRand 64) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ _ =>
    TracefulF.bind
      (TracefulF.storeLocalStatePQ b (st := { kind := .pqPrekey, sk := pqsk }) trivial)
      fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ => TracefulF.pure fun _ _ => trivial

theorem tracefulF_genOneTimePrekey (b : Participant) :
    TracefulF T k (fun _ _ => True) (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine TracefulF.bindE (TracefulF.genRand 32) fun opk m _ hg => ?_
  obtain ⟨L, _, rfl, rfl, _⟩ := hg
  refine TracefulR.bindF (TracefulR.logEventPQ _) fun _ m₁ _ hl => ?_
  obtain ⟨hev, _, rfl⟩ := hl
  refine TracefulF.bind
    (TracefulF.storeLocalStatePQ b (st := { kind := .oneTimePrekey, sk := randTerm L 32 }) ?_)
    fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ => TracefulF.pure fun _ _ => trivial
  exact ⟨L, by omega, rfl, hev⟩

theorem tracefulF_setupAct (a b : Participant) (withOpk : Bool) :
    TracefulF T k (fun _ _ => True) (setupAct a b withOpk) := by
  unfold setupAct
  apply TracefulF.bind (Q₁ := fun _ _ => True) (tracefulF_registerIdentity a)
  intro _ _ _ _
  apply TracefulF.bind (Q₁ := fun _ _ => True) (tracefulF_registerIdentity b)
  intro hB _ _ _
  apply TracefulF.bind (Q₁ := fun _ _ => True) (tracefulF_genSignedPrekey b hB)
  intro _ _ _ _
  apply TracefulF.bind (Q₁ := fun _ _ => True) (tracefulF_genPQPrekey b hB)
  intro _ _ _ _
  split
  · apply TracefulF.bind (Q₁ := fun _ _ => True) (tracefulF_genOneTimePrekey b)
    intro _ _ _ _
    exact TracefulF.pure fun _ _ => trivial
  · exact TracefulF.pure fun _ _ => trivial

end PQ

/-! ## Handshakes -/

/-- Alice's handshake output: identity secret drawn at `tᵢ` (`IkAt`), base secret at `tₑ`, KEM
randomness at `tₑ + 1` (no PQXDH event there), output length `tₑ + 2`. -/
def AliceHsOk (T : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (m : Nat) : Prop :=
  ∃ (tᵢ tₑ : Nat) (pk ent ikB : DY.Bytes) (opk' : Option DY.Bytes),
    tᵢ < tₑ ∧ IkAt T tᵢ ∧ ¬ PQEvAt T (tₑ + 1) ∧ m = tₑ + 2 ∧
    o.ct = (DY.PQKem.kemEncap pk ent).1 ∧
    o.keys = pqxdhKdf (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
      (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
      (DY.PQKem.kemEncap pk ent).2)

theorem tracefulF_aliceHandshake {T : ExecTrace} {k : Nat} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulF T k (fun (o : DY.Libsignal.PQXDH.AliceHandshakeOut) m => AliceHsOk T o m)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply TracefulF.bindD (TracefulF.getKey a idStateIdx _); intro ikA mₐ _ hikA
  simp only [PQSkAt] at hikA
  obtain ⟨tᵢ, htᵢ, rfl, hik⟩ := hikA
  apply TracefulF.bind (TracefulF.lookupIdentity b regIdxB); intro ikv _ _ _
  rcases ikv with ⟨ikB, vkB⟩
  dsimp only
  apply TracefulF.bind (TracefulF.receiveMessage h.spk); intro spk _ _ _
  apply TracefulF.bind (TracefulF.receiveMessage h.spkSig); intro _ _ _ _
  apply TracefulF.bind (TracefulF.receiveMessage h.pqpk); intro pqpk _ _ _
  apply TracefulF.bind (TracefulF.receiveMessage h.pqpkSig); intro _ _ _ _
  apply TracefulF.bind (TracefulF.guard _); intro _ _ _ _
  apply TracefulF.bind (TracefulF.guard _); intro _ _ _ _
  split
  case' h_1 i _ =>
    apply TracefulF.bind (TracefulF.receiveMessage i); intro _ _ _ _
    apply TracefulF.bind (TracefulF.pure (Q := fun (_ : Option DY.Bytes) _ => True)
      fun _ _ => trivial)
  case' h_2 =>
    apply TracefulF.bind (TracefulF.pure (Q := fun (_ : Option DY.Bytes) _ => True)
      fun _ _ => trivial)
  all_goals
    intro opk _ _ _
    apply TracefulF.bindE (TracefulF.genRand 32); intro ek m _ hg
    obtain ⟨tₑ, hkt, rfl, rfl, _⟩ := hg
    apply TracefulR.bind (TracefulR.guardP _); intro _ m₁ _ hg₁
    obtain ⟨_, rfl⟩ := hg₁
    apply TracefulR.bind (TracefulR.guardP _); intro _ m₂ _ hg₂
    obtain ⟨_, rfl⟩ := hg₂
    apply TracefulR.bind (TracefulR.genRand 32); intro ent m₃ _ hr
    obtain ⟨rfl, hne1, rfl⟩ := hr
    exact TracefulR.pure ⟨tᵢ, tₑ, pqpk, randTerm (tₑ + 1) 32, ikB, opk, by omega, hik, hne1, rfl,
      rfl, rfl⟩

/-- Bob's handshake output: logged-role-`true` provenance of its keys, and the signed-prekey secret
drawn before the output position, which is the top DH secret of the root key. -/
def BobHsOk (T : ExecTrace) (o : DY.Libsignal.PQXDH.BobHandshakeOut) (m : Nat) : Prop :=
  ∃ (ikm : DY.Bytes) (t : Nat) (pk' : DY.Bytes),
    CtKeysIkmR T true o.ct o.keys ikm ∧ t < m ∧ o.spkSk = randTerm t 32 ∧
    TopDhSecret o.keys.rk pk' t

theorem bobHsOk_of_bobAgreement {T : ExecTrace} {tᵢ tₛ : Nat} {pqsk ikA ek ct : DY.Bytes}
    {opk : Option DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hik : IkAt T tᵢ) (hspk : SpkAt T tₛ)
    (hopk : ∀ o, opk = some o → ∃ t, o = randTerm t 32 ∧ OpkAt T t)
    (h : DY.Libsignal.PQXDH.bobAgreement (randTerm tᵢ 32) (randTerm tₛ 32) pqsk opk ikA ek ct =
      some keys) :
    ∃ ikm, CtKeysIkmR T true ct keys ikm ∧ TopDhSecret keys.rk (DY.X25519.normalizeX25519Key ikA) tₛ := by
  dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at h
  injection h with hkeys
  subst hkeys
  refine ⟨_, ⟨_, _, _, _, _, ?_, rfl, rfl,
    ⟨DY.X25519.normalizeX25519Key ikA, tₛ, rfl, hspk⟩,
    ⟨DY.X25519.normalizeX25519Key ek, tᵢ, rfl, hik⟩,
    ⟨DY.X25519.normalizeX25519Key ek, tₛ, rfl, hspk⟩, fun v hv => ?_⟩, topDhSecret_pqxdh⟩
  · rcases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct) with _ | s
    · exact .inr ⟨pqsk, ct, rfl⟩
    · obtain ⟨e, _, rfl⟩ := Symbolic.Swarm.CREF.TR.kemDecap_eq_some_iff pqsk ct s hdec
      exact .inl ⟨_, e, rfl⟩
  · rcases opk with _ | o
    · cases hv
    · injection hv with hv
      subst hv
      obtain ⟨t, rfl, ho⟩ := hopk o rfl
      exact ⟨DY.X25519.normalizeX25519Key ek, t, rfl, ho⟩

theorem tracefulF_bobHandshake {T : ExecTrace} {k : Nat} (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    TracefulF T k (fun (o : DY.Libsignal.PQXDH.BobHandshakeOut) m => BobHsOk T o m)
      (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply TracefulF.bind (TracefulF.getKey b h.ik _); intro ikB mᵢ _ hikB
  simp only [PQSkAt] at hikB
  obtain ⟨tᵢ, _, rfl, hik⟩ := hikB
  apply TracefulF.bindD (TracefulF.getKey b h.spk _); intro spkSk mₛ _ hspkSk
  simp only [PQSkAt] at hspkSk
  obtain ⟨tₛ, htₛ, rfl, hspk⟩ := hspkSk
  apply TracefulF.bind (TracefulF.getKey b h.pqspk _); intro pqsk _ _ _
  split
  case' h_1 i _ =>
    apply TracefulF.bind (TracefulF.getKey b i _); intro o _ _ ho
    apply TracefulF.bind (TracefulF.pure
      (Q := fun (x : Option DY.Bytes) _ => ∀ d, x = some d → ∃ t, d = randTerm t 32 ∧ OpkAt T t)
      fun _ _ d hd => by
        cases hd
        obtain ⟨t, _, hsk, hr⟩ := ho
        exact ⟨t, hsk, hr⟩)
  case' h_2 =>
    apply TracefulF.bind (TracefulF.pure
      (Q := fun (x : Option DY.Bytes) _ => ∀ d, x = some d → ∃ t, d = randTerm t 32 ∧ OpkAt T t)
      fun _ _ d hd => by cases hd)
  all_goals
    intro opkSk _ _ hopk
    apply TracefulF.bind (TracefulF.lookupIdentity a regIdxA); intro ikv _ _ _
    rcases ikv with ⟨ikA, vkA⟩
    dsimp only
    apply TracefulF.bind (TracefulF.receiveMessage ekIdx); intro ek _ _ _
    apply TracefulF.bind (TracefulF.receiveMessage ctIdx); intro ct _ _ _
    apply TracefulF.bind (TracefulF.guard _); intro _ _ _ _
    split
    · next keys hkeys =>
      obtain ⟨ikm, hck, htop⟩ := bobHsOk_of_bobAgreement hik hspk hopk hkeys
      exact TracefulF.pure fun n hn => ⟨ikm, tₛ, _, hck, by omega, rfl, htop⟩
    · exact TracefulF.failure

/-! ## Session starts -/

theorem spineRk_of_ctKeys {B : Bool → DY.Bytes → Prop} {c : Bool} {ikm : DY.Bytes}
    {keys : DY.Libsignal.PQXDH.HandshakeKeys} (hkeys : keys = pqxdhKdf ikm) (hB : B c ikm) :
    SpineRk B c keys.rk ∧ SpineRk B c keys.ck := by
  subst hkeys
  exact ⟨.hsRk hB, .hsCk hB⟩

theorem tracefulF_aliceStart {T : ExecTrace} {k : Nat} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    TracefulF T k (fun _ _ => True)
      (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine TracefulF.bindE (tracefulF_aliceHandshake a b idStateIdx regIdxB h) fun o m _ ho => ?_
  obtain ⟨tᵢ, tₑ, pk, ent, ikB, opk', hlt, hik, hne1, rfl, hct, hkeys⟩ := ho
  refine TracefulR.bindF (TracefulR.genRand 32) fun dhsA m₁ _ hg => ?_
  obtain ⟨rfl, hne2, rfl⟩ := hg
  rcases hcc : createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32) with ⟨rkA, cksA⟩
  dsimp only
  refine TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.sendMessage _) fun _ _ _ _ =>
    TracefulF.bind tracefulF_traceLength fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ hlog =>
    TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
    TracefulF.bind (TracefulF.logEventC _) fun _ _ _ _ =>
    TracefulF.storeLocalState a ?_
  have hikm : CtKeysIkmR T false o.ct o.keys
      (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
        (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
        (DY.PQKem.kemEncap pk ent).2) := by
    refine ⟨pk, ent, _, _, _, _, hct, rfl, hkeys, ?_⟩
    refine ⟨⟨DY.X25519.normalizeX25519Key o.spk, tᵢ, rfl, hik⟩, ⟨DY.X25519.normalizeX25519Key ikB, tₑ, rfl, hne1, hne2⟩,
      ⟨DY.X25519.normalizeX25519Key o.spk, tₑ, rfl, hne1, hne2⟩, fun v hv => ?_⟩
    rcases opk' with _ | o'
    · cases hv
    · injection hv with hv
      subst hv
      exact ⟨DY.X25519.normalizeX25519Key o', tₑ, rfl, hne1, hne2⟩
  have hB : LoggedIkmRk T false
      (pqxdhIkm (agree o.spk (randTerm tᵢ 32)) (agree ikB (randTerm tₑ 32))
        (agree o.spk (randTerm tₑ 32)) (opk'.map (agree · (randTerm tₑ 32)))
        (DY.PQKem.kemEncap pk ent).2) :=
    ⟨_, hlog, hikm⟩
  obtain ⟨hrk0, hck0⟩ := spineRk_of_ctKeys hkeys hB
  have htop0 : TopDhSecret o.keys.rk (DY.X25519.normalizeX25519Key o.spk) tᵢ := by
    rw [hkeys]; exact topDhSecret_pqxdh
  have hh : RkHole false o.keys.rk (dh (DY.X25519.normalizeX25519Key o.spk) (randTerm (tₑ + 2) 32)) :=
    rkHole_false_intro htop0 (by omega)
  have hrkA : SpineRk (LoggedIkmRk T) true rkA := by
    have h1 := SpineRk.rkStep1 hrk0 hh
    have h2 : (createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32)).1 = rkA := by rw [hcc]
    rw [← h2]; exact h1
  have hcksA : SpineRk (LoggedIkmRk T) true cksA := by
    have h1 := SpineRk.rkStep2 hrk0 hh
    have h2 : (createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32)).2 = cksA := by rw [hcc]
    rw [← h2]; exact h1
  have htopA : TopDhSecret rkA (DY.X25519.normalizeX25519Key o.spk) (tₑ + 2) := by
    have h1 : TopDhSecret (createChain o.keys.rk o.spk (randTerm (tₑ + 2) 32)).1
        (DY.X25519.normalizeX25519Key o.spk) (tₑ + 2) := topDhSecret_kdfRk
    rw [hcc] at h1; exact h1
  refine ⟨hrkA, hcksA, fun c hc => ?_, ⟨tₑ + 2, _, by omega, rfl, htopA⟩⟩
  rcases List.mem_singleton.mp hc with rfl
  exact hck0

/-- The base predicate of Bob's in-memory start state: the role-`true` provenance of its keys. -/
def BobBase (T : ExecTrace) (ct : DY.Bytes) (keys : DY.Libsignal.PQXDH.HandshakeKeys)
    (c : Bool) (ikm : DY.Bytes) : Prop :=
  c = true ∧ CtKeysIkmR T true ct keys ikm

theorem tracefulF_bobStart {T : ExecTrace} {k : Nat} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    TracefulF T k (fun _ _ => True)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TracefulF.bindD (tracefulF_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o mₒ _ ho =>
    TracefulF.bind (tracefulF_receiveSignalMsg mh.msg) fun msg _ _ _ => ?_
  obtain ⟨ikm, t, pk', hck, ht, hspk, htop⟩ := ho
  have hkeys : o.keys = pqxdhKdf ikm := by
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hck
    exact hk
  obtain ⟨hrk0, hck0⟩ :=
    spineRk_of_ctKeys (B := BobBase T o.ct o.keys) (c := true) hkeys ⟨rfl, hck⟩
  refine TracefulF.bindD (tracefulF_ensureReceiverChain (B := BobBase T o.ct o.keys)
    (SpStateRk.mk hrk0 hck0 (fun _ h => (by simp at h)) ⟨t, pk', ht, hspk, htop⟩))
    fun x m₁ _ hst => ?_
  rcases x with ⟨st, c, ratcheted⟩
  dsimp only at hst ⊢
  split
  · next seed c' hcm =>
    have hc' := (spineRk_consumeMessageKey hst.2 hcm).2
    split
    · next spqr' key _ =>
      refine TracefulF.bind (TracefulF.sendMessage key) fun _ _ _ _ =>
        TracefulF.bind (TracefulF.receiveMessage pqIdx) fun pqSalt _ _ _ =>
        TracefulF.bind (tracefulF_verifyMacAndDecrypt st msg pqSalt seed) fun mm _ _ _ => ?_
      split
      all_goals first
        | refine TracefulF.bind (tracefulF_guardOnTrace _) fun _ _ _ _ =>
            TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ _ => ?_
        | skip
      all_goals refine TracefulF.bind tracefulF_traceLength fun _ _ _ _ =>
        TracefulF.bind (TracefulF.logEventPQ _) fun _ _ _ hlog => ?_
      all_goals
        have hfin : SpStateRk (LoggedIkmRk T) m₁
            { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
          (spStateRk_setRecv hst.1 hc' spqr').mono fun c ss hss => by
            obtain ⟨rfl, hss⟩ := hss
            exact ⟨_, hlog, hss⟩
      all_goals split
      all_goals first
        | refine TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
            TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ => ?_
        | skip
      all_goals exact TracefulF.bind (TracefulF.logEventC _) fun _ _ _ _ =>
          TracefulF.bind tracefulF_traceLength fun _ _ _ _ =>
          TracefulF.bind (tracefulF_logSkippedKeys _ _ _ _ _ _ _) fun _ _ _ _ =>
          TracefulF.bind (TracefulF.logEvent _) fun _ _ _ _ =>
          tracefulF_logMessageKeyAndStore b _ .receiver _ _ _ _ _ hfin
    · exact TracefulF.failure
  · exact TracefulF.failure

/-! ## Moves induction -/

theorem tracefulF_run_snd {T : ExecTrace} {α : Type} {Q : α → Nat → Prop} {x : Traceful α}
    (hx : TracefulF T 0 Q x) {tr : ExecTrace}
    (hT : ((x >>= fun _ => Pure.pure ()).run tr).2.val ≤ T) (htr : TraceOkR T tr) :
    TraceOkR T ((x >>= fun _ => Pure.pure ()).run tr).2.val :=
  (TracefulF.bind hx (fun _ _ _ _ => TracefulF.pure (Q := fun _ _ => True) fun _ _ => trivial)
    tr.length (Nat.zero_le _) tr rfl hT htr).1

theorem traceOkR_move_next {T tr : ExecTrace} {m : Move} (hT : m.next tr ≤ T)
    (htr : TraceOkR T tr) : TraceOkR T (m.next tr) := by
  unfold Move.next Move.act at hT ⊢
  cases m with
  | setup a b withOpk =>
    exact (tracefulF_setupAct (k := 0) a b withOpk tr.length (Nat.zero_le _) tr rfl hT htr).1
  | aliceStart a b idStateIdx regIdxB h _ =>
    exact tracefulF_run_snd (tracefulF_aliceStart a b idStateIdx regIdxB h) hT htr
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    exact tracefulF_run_snd (tracefulF_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) hT htr
  | encrypt me stateIdx coinsLen pqIdx _ =>
    exact tracefulF_run_snd (tracefulF_messageEncrypt me stateIdx coinsLen pqIdx) hT htr
  | encryptAbort me stateIdx =>
    exact tracefulF_run_snd (tracefulF_messageEncryptAbort me stateIdx) hT htr
  | encryptFail me stateIdx coinsLen =>
    exact (TracefulF.bind tracefulF_traceLength
      (fun n _ _ _ => TracefulF.bind (tracefulF_messageEncrypt me stateIdx coinsLen (n + 3))
        (fun _ _ _ _ => TracefulF.pure (Q := fun _ _ => True) fun _ _ => trivial))
      tr.length (Nat.zero_le _) tr rfl hT htr).1
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ =>
    exact tracefulF_run_snd (tracefulF_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)
      hT htr
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ =>
    exact tracefulF_run_snd
      (tracefulF_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx)
      hT htr
  | reject _ =>
    dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
    exact htr
  | compromiseIK p stateIdx => exact tracefulF_run_snd (tracefulF_compromiseIK p stateIdx) hT htr
  | compromiseSPK p stateIdx =>
    exact tracefulF_run_snd (tracefulF_compromiseSPK p stateIdx) hT htr
  | compromisePQSPK p stateIdx =>
    exact tracefulF_run_snd (tracefulF_compromisePQSPK p stateIdx) hT htr
  | compromiseOPK p stateIdx =>
    exact tracefulF_run_snd (tracefulF_compromiseOPK p stateIdx) hT htr
  | exposeKey me stateIdx kc => exact tracefulF_run_snd (tracefulF_exposeKey me stateIdx kc) hT htr
  | exposeSpqr me stateIdx => exact tracefulF_run_snd (tracefulF_exposeSpqr me stateIdx) hT htr
  | exposeSkipped skippedKeyEventIdx =>
    exact tracefulF_run_snd (tracefulF_exposeSkipped skippedKeyEventIdx) hT htr
  | attackerSend msg => exact tracefulF_run_snd (TracefulF.sendMessage msg) hT htr
  | brkDH =>
    exact (TracefulF.logEventPQ (k := 0) .BrokenDH tr.length (Nat.zero_le _) tr rfl hT htr).1
  | brkKEM =>
    exact (TracefulF.logEventPQ (k := 0) .BrokenKEM tr.length (Nat.zero_le _) tr rfl hT htr).1

theorem traceOkR_runMoves {T : ExecTrace} :
    ∀ (L : List Move) (tr : ExecTrace), (runMoves L tr).1 ≤ T →
      TraceOkR T tr → TraceOkR T (runMoves L tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hT, htr => by
    have hT' : (runMoves ms (m.next tr)).1 ≤ T := hT
    have hle : m.next tr ≤ T :=
      DY.Trace.le_trans _ _ _ (Symbolic.Swarm.CREF.runMoves_le ms (m.next tr)) hT'
    exact traceOkR_runMoves ms (m.next tr) hT' (traceOkR_move_next hle htr)

/-- Every entry of the run's trace satisfies `SpEntryOkR` relative to the run's own trace. -/
theorem traceOkR_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    TraceOkR (runTraceMoves r₀ ms) (runTraceMoves r₀ ms) :=
  traceOkR_runMoves (r₀.setupMove :: ms) DY.Trace.nil (DY.Trace.le_refl _) (traceOkR_nil _)

theorem spStateRk_of_mem_availableStates {r₀ : ProtocolSetup} {T tr : ExecTrace} (htr : TraceOkR T tr)
    {st : TRState} (hst : st ∈ availableStates r₀ tr) : SpStateRk (LoggedIkmRk T) tr.length st := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  unfold DY.Trace.at? at hat
  split at hat
  · next hj => exact ((htr j hj).1 e hat).mono_idx (Nat.le_of_lt hj)
  · cases hat

/-- Every available state of a run satisfies `SpStateRk (LoggedIkmRk (runTraceMoves r₀ ms))`. -/
theorem spStateRk_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) :
    SpStateRk (LoggedIkmRk (runTraceMoves r₀ ms)) (runTraceMoves r₀ ms).length st :=
  spStateRk_of_mem_availableStates (traceOkR_runTrace r₀ ms) hst

/-- The sending seed of an available state is a role-`true` spine term. -/
theorem spineRk_send_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) :
    SpineRk (LoggedIkmRk (runTraceMoves r₀ ms)) true (kdfCk st.cks).2 :=
  .ckStep2 (spStateRk_runTrace hst).cks

/-- A receiving seed of an available state is a role-`false` spine term. -/
theorem spineRk_recvSeed_runTrace {r₀ : ProtocolSetup} {ms : List Move} {st : TRState}
    {msg : TRSignalMsg} {seed : DY.Bytes} (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hseed : recvSeed st msg = some seed) :
    SpineRk (LoggedIkmRk (runTraceMoves r₀ ms)) false seed :=
  spineRk_of_recvSeed (spStateRk_runTrace hst) hseed

end Symbolic.Swarm.CREF.TR.G1.Spine
