/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpine
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# KEM Canonicity and Seed Uniqueness from Peel-Local Hole Injectivity

Proves `seed_eq_of_holes`, `kemCanonPeel_of_aliceKemLen32`, and `aliceKemLen32_of_matchedPrefix`,
establishing KEM shared-secret agreement on opposite-role PQXDH base pairs and seed uniqueness from
peel-local `DhHole` injectivity.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Every `AliceDone` event logged at `t + 5` on `T` has a 32-byte `gamma` image for its KEM coin
`randTerm (t + 1) 32`. -/
def AliceKemLen32 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (T : ExecTrace) : Prop :=
  ∀ t a b ikA ikB spk pqpk opk ek ct keys,
    T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) →
    (gamma i S g (randTerm (t + 1) 32)).length = 32

end Symbolic.Swarm.CREF.TR.G1.Spine

namespace Symbolic.Swarm.CREF.TR.G1.SkelLocal

cref_open
open DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (kdfCk kdfRk)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.G1.SpineIkm (Peel PeelKdf DhHole)
open Symbolic.Swarm.CREF.TR.G1.ShapeModKem (shape_concat_inj shape_kemLeaf_ne_concat)
open Symbolic.Swarm.CREF.TR.G1.Spine (LoggedIkmR IkmH ikmH_of_loggedIkmR seed_eq_of_shape_eq_peel
  ikAt_spkAt_false ekAt_ikAt_false ekAt_spkAt_false ekAt_opkAt_false loggedIkmRk_roleHoles
  spineRk_send_runTrace spineRk_recvSeed_runTrace hdh_of_spineRk AliceKemLen32)

/-! ## KEM canonicity and seed uniqueness on peel-reached pairs -/

/-- KEM canonicity on opposite-role logged base pairs reached by the peel from `(u₀, v₀)`: two
logged IKMs of opposite roles with the same DH tuple and equal-shape KEM leaves have equal leaves. -/
def KemCanonPeel (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (B : Bool → DY.Bytes → Prop)
    (u₀ v₀ : DY.Bytes) : Prop :=
  ∀ (c c' : Bool) (a b e : DY.Bytes) (d : Option DY.Bytes) (ss₁ ss₂ : DY.Bytes),
    PeelKdf u₀ v₀ (pqxdhIkm a b e d ss₁) (pqxdhIkm a b e d ss₂) →
    B c (pqxdhIkm a b e d ss₁) → B c' (pqxdhIkm a b e d ss₂) → (c ^^ c') = true →
    (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape →
    ShapeModKem.KemLeaf ss₁ → ShapeModKem.KemLeaf ss₂ → ss₁ = ss₂

/-- Peel-reached opposite-role base pairs with equal shapes are equal, given injectivity of the
peel-reached `DhHole` pairs and `KemCanonPeel`. -/
theorem ikm_eq_of_peel {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {B : Bool → DY.Bytes → Prop} {u₀ v₀ : DY.Bytes} (hB : ∀ c m, B c m → IkmH m)
    (hhole : ∀ d₁ d₂ : DY.Bytes, Peel u₀ v₀ d₁ d₂ → DhHole d₁ → DhHole d₂ →
      (gamma' i S g d₁).shape = (gamma' i S g d₂).shape → d₁ = d₂)
    (hkem : KemCanonPeel i S g B u₀ v₀) :
    ∀ (c c' : Bool) (m₁ m₂ : DY.Bytes), PeelKdf u₀ v₀ m₁ m₂ → B c m₁ → B c' m₂ →
      (c ^^ c') = true → (gamma' i S g m₁).shape = (gamma' i S g m₂).shape → m₁ = m₂ := by
  intro c c' m₁ m₂ hP hm₁ hm₂ hp h
  obtain ⟨a₁, b₁, e₁, d₁, ss₁, rfl, ha₁, hb₁, he₁, hd₁, hk₁⟩ := hB c m₁ hm₁
  obtain ⟨a₂, b₂, e₂, d₂, ss₂, rfl, ha₂, hb₂, he₂, hd₂, hk₂⟩ := hB c' m₂ hm₂
  have h' := h
  unfold pqxdhIkm at h'
  obtain ⟨_, h1⟩ := shape_concat_inj i S g h'
  obtain ⟨sha, h2⟩ := shape_concat_inj i S g h1
  obtain ⟨shb, h3⟩ := shape_concat_inj i S g h2
  obtain ⟨she, h4⟩ := shape_concat_inj i S g h3
  have ha : a₁ = a₂ := hhole _ _ (.ikmDh1 hP.peel) ha₁ ha₂ sha
  have hb : b₁ = b₂ := hhole _ _ (.ikmDh2 hP.peel) hb₁ hb₂ shb
  have he : e₁ = e₂ := hhole _ _ (.ikmDh3 hP.peel) he₁ he₂ she
  subst ha hb he
  cases d₁ with
  | none =>
    cases d₂ with
    | none => rw [hkem c c' _ _ _ none ss₁ ss₂ hP hm₁ hm₂ hp h4 hk₁ hk₂]
    | some v₂ => exact False.elim (shape_kemLeaf_ne_concat i S g hk₁ h4)
  | some v₁ =>
    cases d₂ with
    | none => exact False.elim (shape_kemLeaf_ne_concat i S g hk₂ h4.symm)
    | some v₂ =>
      obtain ⟨shd, hss⟩ := shape_concat_inj i S g h4
      have hd : v₁ = v₂ := hhole _ _ (.ikmDh4 hP.peel) (hd₁ v₁ rfl) (hd₂ v₂ rfl) shd
      subst hd
      rw [hkem c c' _ _ _ (some v₁) ss₁ ss₂ hP hm₁ hm₂ hp hss hk₁ hk₂]

/-- Shape-equal sending and receiving seeds of available states are equal, given injectivity of the
peel-reached `DhHole` pairs and `KemCanonPeel` on the logged IKMs. -/
theorem seed_eq_of_holes (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) {st_s st₀ : TRState}
    (hst_s : st_s ∈ availableStates r (runTraceMoves r ms))
    (hst₀ : st₀ ∈ availableStates r (runTraceMoves r ms)) {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hhole : ∀ d₁ d₂ : DY.Bytes, Peel (kdfCk st_s.cks).2 mkSeed d₁ d₂ → DhHole d₁ → DhHole d₂ →
      (gamma' interpretation S g d₁).shape = (gamma' interpretation S g d₂).shape → d₁ = d₂)
    (hkem : KemCanonPeel interpretation S g (LoggedIkmR (runTraceMoves r ms)) (kdfCk st_s.cks).2 mkSeed)
    (hshape : (gamma' interpretation S g (kdfCk st_s.cks).2).shape =
      (gamma' interpretation S g mkSeed).shape) :
    (kdfCk st_s.cks).2 = mkSeed :=
  seed_eq_of_shape_eq_peel interpretation r S g ms hst_s hst₀ hseed hhole
    (ikm_eq_of_peel (fun _ _ h => ikmH_of_loggedIkmR h) hhole hkem) hshape

end Symbolic.Swarm.CREF.TR.G1.SkelLocal

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhIkm pqxdhKdf BundleHandles)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

/-- On any reachable trace `T`, the fresh KEM encapsulation coin `randTerm (t + 1) 32` of an
`AliceDone` event logged at `t + 5` is never attacker-known. -/
theorem aliceDone_kemCoin_not_attackerKnows {T : ExecTrace} (hT : ReachableTrace T)
    {t : Nat} {a b : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : HandshakeKeys}
    (hev : T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5)) :
    ¬ (randTerm (t + 1) 32).AttackerKnows T := by
  intro hk
  have hinv := spqrInv_of_reachable _ hT
  obtain ⟨t', _, htEq, hslot, _⟩ := hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys (t + 5) hev
  have ht : t' = t := by omega
  subst ht
  exact not_pub_coins hinv hslot (pub_of_knows hinv hk)

/-- On any reachable trace `T` satisfying `AliceKemLen32`, if an `AliceDone` KEM shared secret
`(kemEncap pq₁ (randTerm (u + 1) 32)).2` has the same `gamma'` shape as `(kemEncap pq₂ e₂).2` whose
paired ciphertext `(kemEncap pq₂ e₂).1` is attacker-known on `T`, then `pq₁ = pq₂`,
`e₂ = randTerm (u + 1) 32`, and the two KEM shared secrets are equal. -/
theorem kemSS_alice_bob_eq_of_shape_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hT : ReachableTrace T) (hKem32 : AliceKemLen32 i S g T)
    {u : Nat} {a₁ b₁ : Participant} {ikA₁ ikB₁ spk₁ pq₁ : DY.Bytes} {opk₁ : Option DY.Bytes}
    {ek₁ ct₁ : DY.Bytes} {keys₁ : HandshakeKeys}
    (hev₁ : T.EventLoggedAt (PQXDHEvent.AliceDone a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁) (u + 5))
    {pq₂ e₂ ct₂ : DY.Bytes} (hct₂Ak : ct₂.AttackerKnows T)
    (hct₂ : ct₂ = (DY.PQKem.kemEncap pq₂ e₂).1)
    (hsh : (gamma' i S g (DY.PQKem.kemEncap pq₁ (randTerm (u + 1) 32)).2).shape =
      (gamma' i S g (DY.PQKem.kemEncap pq₂ e₂).2).shape) :
    pq₁ = pq₂ ∧ e₂ = randTerm (u + 1) 32 ∧
      (DY.PQKem.kemEncap pq₁ (randTerm (u + 1) 32)).2 = (DY.PQKem.kemEncap pq₂ e₂).2 := by
  have hlen : (gamma i S g (randTerm (u + 1) 32)).length = 32 :=
    hKem32 u a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁ hev₁
  obtain ⟨pk', e', hencEq, _, _, heSh⟩ :=
    Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 i S g hlen hsh.symm
  obtain ⟨_, rfl⟩ := Stage1Kyber.kemEncap_snd_inj hencEq
  have heEq : e₂ = randTerm (u + 1) 32 := (eq_randTerm32_of_shape_eq i S g (u + 1) heSh.symm).symm
  subst heEq
  subst hct₂
  rcases kemEncap_fst_attackerKnows_inv hT hct₂Ak with hkCoin |
      ⟨t', a', b', ikA', ikB', spk', pqpk', opk', ek', ct', keys', hev', hpqEq, hrndEq⟩
  · exact absurd hkCoin (aliceDone_kemCoin_not_attackerKnows hT hev₁)
  · have hu : u = t' := by
      have h1 := (Stage1Kyber.randTerm_inj hrndEq).1
      omega
    subst hu
    have hevEq : PQXDHEvent.AliceDone a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁ =
        PQXDHEvent.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' := by
      have h0 : (T.at? (u + 5) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some ⟨.AliceDone a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁⟩ := by
        rwa [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      have h1 : (T.at? (u + 5) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some ⟨.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys'⟩ := by
        rwa [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      have h2 := h0.symm.trans h1
      injection h2 with h2
      injection h2
    cases hevEq
    subst hpqEq
    exact ⟨rfl, rfl, rfl⟩

theorem pqxdhIkm_kemLeaf_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {a₁ b₁ e₁ a₂ b₂ e₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes} {ss₁ ss₂ : DY.Bytes}
    (hk₁ : ShapeModKem.KemLeaf ss₁) (hk₂ : ShapeModKem.KemLeaf ss₂)
    (h : pqxdhIkm a₁ b₁ e₁ d₁ ss₁ = pqxdhIkm a₂ b₂ e₂ d₂ ss₂) :
    ss₁ = ss₂ := by
  unfold pqxdhIkm at h
  have h1 := (Symbolic.Swarm.CREF.TR.G1.concat_injective h).2
  have h2 := (Symbolic.Swarm.CREF.TR.G1.concat_injective h1).2
  have h3 := (Symbolic.Swarm.CREF.TR.G1.concat_injective h2).2
  have h4 := (Symbolic.Swarm.CREF.TR.G1.concat_injective h3).2
  cases d₁ with
  | none =>
    cases d₂ with
    | none => exact h4
    | some v₂ =>
      exact False.elim (ShapeModKem.shape_kemLeaf_ne_concat i S g hk₁
        (congrArg (fun z => (gamma' i S g z).shape) h4))
  | some v₁ =>
    cases d₂ with
    | none =>
      exact False.elim (ShapeModKem.shape_kemLeaf_ne_concat i S g hk₂
        (congrArg (fun z => (gamma' i S g z).shape) h4.symm))
    | some v₂ => exact (Symbolic.Swarm.CREF.TR.G1.concat_injective h4).2

theorem loggedPQEv_iff_eventLogged {T : ExecTrace} {ev : PQXDHEvent} :
    LoggedPQEv T ev ↔ ∃ j, T.EventLoggedAt ev j := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  constructor
  · rintro ⟨j, ⟨ev'⟩, hj, rfl⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, ⟨ev⟩, hj, rfl⟩

private theorem pqxdhKdf_rk_inj_hsl {m₁ m₂ : DY.Bytes}
    (h : (DY.Libsignal.PQXDH.pqxdhKdf m₁).rk = (DY.Libsignal.PQXDH.pqxdhKdf m₂).rk) : m₁ = m₂ := by
  unfold DY.Libsignal.PQXDH.pqxdhKdf at h
  dsimp only at h
  exact (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective
    (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective h).1).2

private theorem aliceBob_kemCanon_step (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hT : ReachableTrace T) (hKem32 : AliceKemLen32 i S g T)
    {j₁ j₂ : Nat}
    {a₁ b₁ : Participant} {ikA₁ ikB₁ spk₁ pq₁ : DY.Bytes} {opk₁ : Option DY.Bytes}
    {ek₁ ct₁ : DY.Bytes} {keys₁ : HandshakeKeys}
    {b₂ a₂ : Participant} {ikB₂ ikA₂ spk₂ pq₂ : DY.Bytes} {opk₂ : Option DY.Bytes}
    {ek₂ ct₂ : DY.Bytes} {keys₂ : HandshakeKeys}
    {a b e : DY.Bytes} {d : Option DY.Bytes} {ssA ssB : DY.Bytes}
    (hevA : T.EventLoggedAt (PQXDHEvent.AliceDone a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁) j₁)
    (hevB : T.EventLoggedAt (PQXDHEvent.BobDone b₂ a₂ ikB₂ ikA₂ spk₂ pq₂ opk₂ ek₂ ct₂ keys₂) j₂)
    (hdA : CtKeysIkm ct₁ keys₁ (pqxdhIkm a b e d ssA))
    (hdB : CtKeysIkm ct₂ keys₂ (pqxdhIkm a b e d ssB))
    (hkA : ShapeModKem.KemLeaf ssA) (hkB : ShapeModKem.KemLeaf ssB)
    (hsh : (gamma' i S g ssA).shape = (gamma' i S g ssB).shape) :
    ssA = ssB := by
  have hinv := spqrInv_of_reachable _ hT
  obtain ⟨u, sA, rfl, _, _, _, _, hag, _⟩ :=
    hinv.aliceDone a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁ j₁ hevA
  have hkeysA' : ∃ (a₂ b₂ e₂ : DY.Bytes) (d₂ : Option DY.Bytes),
      keys₁ = DY.Libsignal.PQXDH.pqxdhKdf
        (pqxdhIkm a₂ b₂ e₂ d₂ (DY.PQKem.kemEncap pq₁ (randTerm (u + 1) 32)).2) := by
    change (ct₁, keys₁) = DY.Libsignal.PQXDH.aliceAgreement sA (randTerm u 32) ikB₁ spk₁ pq₁ opk₁
      (randTerm (u + 1) 32) at hag
    rcases hk : DY.PQKem.kemEncap pq₁ (randTerm (u + 1) 32) with ⟨c₀, s₀⟩
    unfold DY.Libsignal.PQXDH.aliceAgreement at hag
    rw [hk] at hag
    simp only [Prod.mk.injEq] at hag
    exact ⟨_, _, _, _, hag.2⟩
  obtain ⟨a₂, b₂, e₂, d₂, hkeysA'⟩ := hkeysA'
  obtain ⟨_, _, _, _, _, _, hikmA, hkeysA, _⟩ := hdA
  have hssA : ssA = (DY.PQKem.kemEncap pq₁ (randTerm (u + 1) 32)).2 :=
    pqxdhIkm_kemLeaf_eq i S g hkA (.inl ⟨_, _, rfl⟩)
      (pqxdhKdf_rk_inj_hsl (congrArg HandshakeKeys.rk (hkeysA.symm.trans hkeysA')))
  obtain ⟨ss₀, d1₂, d2₂, d3₂, d4₂, hkemB, hikmB, _, _⟩ := hdB
  rcases hkemB with ⟨pk₂, e₂', hct₂, rfl⟩ | ⟨sk₂, rfl⟩
  · have hssB : ssB = (DY.PQKem.kemEncap pk₂ e₂').2 :=
      pqxdhIkm_kemLeaf_eq i S g hkB (.inl ⟨pk₂, e₂', rfl⟩) hikmB
    have hct₂Ak : ct₂.AttackerKnows T :=
      (bobDone_ct_pqpk_attackerKnows_of_reachable hT hevB).1
    rw [hssA, hssB] at hsh ⊢
    exact (kemSS_alice_bob_eq_of_shape_eq i S g hT hKem32 hevA hct₂Ak hct₂ hsh).2.2
  · have hssB : ssB = DY.PQKem.kemRejKey sk₂ ct₂ :=
      pqxdhIkm_kemLeaf_eq i S g hkB (.inr ⟨sk₂, ct₂, rfl⟩) hikmB
    rw [hssA, hssB] at hsh
    have hlen : (gamma i S g (randTerm (u + 1) 32)).length = 32 :=
      hKem32 u a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁ hevA
    obtain ⟨pk', e', heq, _⟩ := Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 i S g hlen hsh.symm
    have hnone := (Stage1Kyber.view?_kemRejKey_disjoint sk₂ ct₂).2.2.2.2.2.2.2.2.2.1
    rw [heq, Stage1Kyber.kemEncap_snd_eq_pack, Stage1Kyber.view_kemSS_pack] at hnone
    cases hnone

/-- `KemCanonPeel` holds on `LoggedIkmR T` for any reachable trace `T` satisfying
`AliceKemLen32 i S g T`. -/
theorem kemCanonPeel_of_aliceKemLen32 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hT : ReachableTrace T) (hKem32 : AliceKemLen32 i S g T)
    (u₀ v₀ : DY.Bytes) :
    SkelLocal.KemCanonPeel i S g (LoggedIkmR T) u₀ v₀ := by
  intro c c' a b e d ss₁ ss₂ _ hB₁ hB₂ hxor hsh hk₁ hk₂
  obtain ⟨ev₁, hlog₁, hd₁⟩ := hB₁
  obtain ⟨ev₂, hlog₂, hd₂⟩ := hB₂
  obtain ⟨j₁, hev₁⟩ := loggedPQEv_iff_eventLogged.mp hlog₁
  obtain ⟨j₂, hev₂⟩ := loggedPQEv_iff_eventLogged.mp hlog₂
  cases c with
  | false =>
    cases c' with
    | false => cases hxor
    | true =>
      cases ev₁ <;> simp only [DoneIkmR] at hd₁
      cases ev₂ <;> simp only [DoneIkmR] at hd₂
      exact aliceBob_kemCanon_step i S g hT hKem32 hev₁ hev₂ hd₁ hd₂ hk₁ hk₂ hsh
  | true =>
    cases c' with
    | true => cases hxor
    | false =>
      cases ev₁ <;> simp only [DoneIkmR] at hd₁
      cases ev₂ <;> simp only [DoneIkmR] at hd₂
      exact (aliceBob_kemCanon_step i S g hT hKem32 hev₂ hev₁ hd₂ hd₁ hk₂ hk₁ hsh.symm).symm

/-! ## `AliceKemLen32` from `MatchedPrefix` -/

section AliceKemLen32Proof

open DY.Libsignal.TripleRatchet (SessionInfo KeyComponent KeyDir kdfCk kdfRk createChain
  dhRatchetStep ensureReceiverChain logMessageKeyAndStore logSkippedKeys verifyMacAndDecrypt
  messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped exposeKey exposeSpqr
  exposeSkipped parseTrSignalMsg guardTrace spqrA2B TREvent TRState TRSignalMsg)
open DY.Libsignal.PQXDH (serializedIk)

private def NoAliceDone {α : Type} (f : Traceful α) : Prop :=
  ∀ tr ev idx, isAliceDone ev = true → ((f.run tr).2.val).EventLoggedAt ev idx →
    tr.EventLoggedAt ev idx

private theorem NoAliceDone.pure {α : Type} (x : α) : NoAliceDone (Pure.pure x) := by
  intro _ _ _ _ h
  rw [Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
  exact h

private theorem NoAliceDone.failure {α : Type} : NoAliceDone (Alternative.failure : Traceful α) := by
  intro _ _ _ _ h
  rw [DY.Traceful.run_failure] at h
  exact h

private theorem NoAliceDone.bind {α β : Type} {f : Traceful α} {g : α → Traceful β}
    (hf : NoAliceDone f) (hg : ∀ x, NoAliceDone (g x)) : NoAliceDone (f >>= g) := by
  intro tr ev idx had h
  rw [run_bind_snd] at h
  rcases hrun : (f.run tr).1 with _ | x
  · rw [hrun] at h; exact hf tr ev idx had h
  · rw [hrun] at h; exact hf tr ev idx had (hg x _ ev idx had h)

private theorem NoAliceDone.guardP (p : Prop) [Decidable p] : NoAliceDone (_root_.guard p) := by
  intro tr ev idx had h
  by_cases hp : p <;> simp [_root_.guard, hp] at h
  · exact NoAliceDone.pure () tr ev idx had h
  · exact NoAliceDone.failure tr ev idx had h

private theorem noAliceDone_guardTrace (p : ExecTrace → Bool) :
    NoAliceDone (guardTrace p) := by
  intro _ _ _ _ h
  erw [DY.Traceful.run_mk] at h
  exact h

private theorem noAliceDone_guardOnTrace (p : ExecTrace → Bool) :
    NoAliceDone (DY.Libsignal.PQXDH.guardTrace p) := by
  intro _ _ _ _ h
  erw [DY.Traceful.run_mk] at h
  exact h

private theorem noAliceDone_traceLength : NoAliceDone DY.Libsignal.TripleRatchet.traceLength := by
  intro _ _ _ _ h
  erw [DY.Traceful.run_mk] at h
  exact h

private theorem noAliceDone_getEntry (E : Type) [ExecTraceTypes.Has E] (j : Nat) :
    NoAliceDone (DY.getEntry j : Traceful E) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1] at h; rw [Traceful.run_mk] at h; dsimp only at h
  cases (tr.at? j : Option E) <;> exact h

private theorem noAliceDone_receiveMessage (j : Nat) : NoAliceDone (DY.Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact NoAliceDone.bind (noAliceDone_getEntry _ j) fun _ => NoAliceDone.pure _

private theorem noAliceDone_receiveSignalMsg (j : Nat) :
    NoAliceDone (DY.Libsignal.TripleRatchet.receiveSignalMsg j) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine NoAliceDone.bind (noAliceDone_receiveMessage j) fun raw => ?_
  cases parseTrSignalMsg raw
  · exact NoAliceDone.failure
  · exact NoAliceDone.bind (NoAliceDone.guardP _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_getLocalStateTR (p : Participant) (j : Nat) :
    NoAliceDone (DY.PersistentLocalState.getLocalState p j : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact NoAliceDone.bind (NoAliceDone.bind (noAliceDone_getEntry _ j) fun _ => NoAliceDone.pure _)
    fun _ => NoAliceDone.bind (NoAliceDone.guardP _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_getLocalStatePQ (p : Participant) (j : Nat) :
    NoAliceDone (DY.PersistentLocalState.getLocalState p j : Traceful DY.Libsignal.PQXDH.PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact NoAliceDone.bind (NoAliceDone.bind (noAliceDone_getEntry _ j) fun _ => NoAliceDone.pure _)
    fun _ => NoAliceDone.bind (NoAliceDone.guardP _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_getKey (p : Participant) (j : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
    NoAliceDone (DY.Libsignal.PQXDH.getKey p j k) :=
  NoAliceDone.bind (noAliceDone_getLocalStatePQ p j) fun _ =>
    NoAliceDone.bind (NoAliceDone.guardP _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_lookupIdentity (p : Participant) (j : Nat) :
    NoAliceDone (DY.Libsignal.PQXDH.lookupIdentity p j) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine NoAliceDone.bind (noAliceDone_getEntry _ j) fun e => ?_
  cases e.ev
  · exact NoAliceDone.bind (NoAliceDone.guardP _) fun _ => NoAliceDone.pure _
  all_goals exact NoAliceDone.failure

private theorem noAliceDone_genRand (n : Nat) : NoAliceDone (DY.Random.genRand n) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
  exact eventLoggedAt_append_other h rfl

private theorem noAliceDone_sendMessage (m : DY.Bytes) : NoAliceDone (DY.Network.sendMessage m) := by
  intro _ _ _ _ h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noAliceDone_logEventTR (e : TREvent) : NoAliceDone (DY.ProtocolEvent.logEvent e) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
  exact eventLoggedAt_append_other h rfl

private theorem noAliceDone_logEventC (e : DY.Libsignal.Composed.ComposedEvent) :
    NoAliceDone (DY.ProtocolEvent.logEvent e) := by
  intro _ _ _ _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
  exact eventLoggedAt_append_other h rfl

private theorem noAliceDone_logEventPQ {e : PQXDHEvent} (he : isAliceDone e = false) :
    NoAliceDone (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx had h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1] at h
  rcases eventLoggedAt_append_ev_iff.mp h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact h
  · rw [he] at had; cases had

private theorem noAliceDone_storeTR (p : Participant) (st : TRState) :
    NoAliceDone (DY.PersistentLocalState.storeLocalState p st) := by
  intro _ _ _ _ h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noAliceDone_storePQ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    NoAliceDone (DY.PersistentLocalState.storeLocalState p st) := by
  intro _ _ _ _ h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noAliceDone_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    NoAliceDone (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact NoAliceDone.bind (NoAliceDone.guardP _) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 32) fun _ => NoAliceDone.pure _

private theorem noAliceDone_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    NoAliceDone (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact NoAliceDone.pure _
  · exact NoAliceDone.bind (noAliceDone_dhRatchetStep st pk) fun _ => NoAliceDone.pure _
  · exact NoAliceDone.failure

private theorem noAliceDone_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    NoAliceDone (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_storeTR me st

private theorem noAliceDone_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), NoAliceDone (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact NoAliceDone.pure _
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
      noAliceDone_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem noAliceDone_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) : NoAliceDone (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine NoAliceDone.bind (NoAliceDone.guardP _) fun _ => ?_
  intro tr ev idx _ h
  erw [DY.Traceful.run_mk] at h
  cases DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
    (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext <;> exact h

private theorem noAliceDone_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    NoAliceDone (messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold messageEncrypt
  exact NoAliceDone.bind (noAliceDone_getLocalStateTR me stateIdx) fun _ =>
    NoAliceDone.bind (NoAliceDone.guardP _) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 32) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand coinsLen) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
    NoAliceDone.bind (noAliceDone_receiveMessage pqIdx) fun _ =>
    NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
    NoAliceDone.bind (noAliceDone_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ =>
    noAliceDone_sendMessage _

private theorem noAliceDone_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    NoAliceDone (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact NoAliceDone.bind (noAliceDone_getLocalStateTR me stateIdx) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 32) fun _ => NoAliceDone.failure

private theorem noAliceDone_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) : NoAliceDone (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine NoAliceDone.bind (noAliceDone_getLocalStateTR me stateIdx) fun st₀ =>
    NoAliceDone.bind (noAliceDone_receiveSignalMsg msgIdx) fun msg =>
    NoAliceDone.bind (noAliceDone_ensureReceiverChain st₀ msg.ratchetKey) fun ⟨st, c, _⟩ => ?_
  dsimp only
  split
  · split
    · refine NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
        NoAliceDone.bind (noAliceDone_receiveMessage pqIdx) fun pqSalt =>
        NoAliceDone.bind (noAliceDone_verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      · exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
          NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
          NoAliceDone.bind (noAliceDone_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
          noAliceDone_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · exact NoAliceDone.bind (noAliceDone_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
          noAliceDone_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact NoAliceDone.failure
  · exact NoAliceDone.failure

private theorem noAliceDone_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    NoAliceDone (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine NoAliceDone.bind (noAliceDone_getLocalStateTR me stateIdx) fun st =>
    NoAliceDone.bind (noAliceDone_receiveSignalMsg msgIdx) fun msg =>
    NoAliceDone.bind (noAliceDone_getEntry _ skippedKeyEventIdx) fun _ => ?_
  split
  · refine NoAliceDone.bind (NoAliceDone.guardP _) fun _ =>
      NoAliceDone.bind (noAliceDone_guardTrace _) fun _ => ?_
    split
    · exact NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
        NoAliceDone.bind (noAliceDone_receiveMessage pqIdx) fun pqSalt =>
        NoAliceDone.bind (noAliceDone_verifyMacAndDecrypt st msg pqSalt _) fun _ =>
        NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
        NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
        noAliceDone_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact NoAliceDone.failure
  · exact NoAliceDone.failure

private theorem noAliceDone_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    NoAliceDone (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine NoAliceDone.bind (noAliceDone_getLocalStateTR me stateIdx) fun _ => ?_
  cases k with
  | rk => exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_sendMessage _
  | dhs => exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_sendMessage _
  | cks => exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_sendMessage _
  | ckr _ =>
    dsimp only; split
    · exact NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_sendMessage _
    · exact NoAliceDone.failure

private theorem noAliceDone_exposeSpqr (me : Participant) (stateIdx : Nat) :
    NoAliceDone (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact NoAliceDone.bind (noAliceDone_getLocalStateTR me stateIdx) fun _ =>
    NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_sendMessage _

private theorem noAliceDone_exposeSkipped (skippedKeyEventIdx : Nat) :
    NoAliceDone (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine NoAliceDone.bind (noAliceDone_getEntry _ skippedKeyEventIdx) fun _ => ?_
  split
  · exact NoAliceDone.bind (noAliceDone_guardTrace _) fun _ =>
      NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => noAliceDone_sendMessage _
  · exact NoAliceDone.failure

private theorem noAliceDone_registerIdentity (p : Participant) :
    NoAliceDone (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact NoAliceDone.bind (noAliceDone_guardOnTrace _) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 32) fun _ =>
    NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ => noAliceDone_storePQ p _

private theorem noAliceDone_genSignedPrekey (b : Participant) (j : Nat) :
    NoAliceDone (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact NoAliceDone.bind (noAliceDone_getKey b j _) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 32) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 64) fun _ =>
    NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ =>
    NoAliceDone.bind (noAliceDone_storePQ b _) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_genPQPrekey (b : Participant) (j : Nat) :
    NoAliceDone (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact NoAliceDone.bind (noAliceDone_getKey b j _) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 64) fun _ =>
    NoAliceDone.bind (noAliceDone_genRand 64) fun _ =>
    NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ =>
    NoAliceDone.bind (noAliceDone_storePQ b _) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_genOneTimePrekey (b : Participant) :
    NoAliceDone (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact NoAliceDone.bind (noAliceDone_genRand 32) fun _ =>
    NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ =>
    NoAliceDone.bind (noAliceDone_storePQ b _) fun _ =>
    NoAliceDone.bind (noAliceDone_sendMessage _) fun _ => NoAliceDone.pure _

private theorem noAliceDone_setupAct (a b : Participant) (withOpk : Bool) :
    NoAliceDone (setupAct a b withOpk) := by
  unfold setupAct
  refine NoAliceDone.bind (noAliceDone_registerIdentity a) fun _ =>
    NoAliceDone.bind (noAliceDone_registerIdentity b) fun hB =>
    NoAliceDone.bind (noAliceDone_genSignedPrekey b hB) fun _ =>
    NoAliceDone.bind (noAliceDone_genPQPrekey b hB) fun _ => ?_
  cases withOpk
  · exact NoAliceDone.pure _
  · exact NoAliceDone.bind (noAliceDone_genOneTimePrekey b) fun _ => NoAliceDone.pure _

private theorem noAliceDone_bobHandshake (b a : Participant)
    (h : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    NoAliceDone (DY.Libsignal.PQXDH.bobHandshake b a h regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  apply NoAliceDone.bind (noAliceDone_getKey b h.ik _); intro _
  apply NoAliceDone.bind (noAliceDone_getKey b h.spk _); intro _
  apply NoAliceDone.bind (noAliceDone_getKey b h.pqspk _); intro _
  split
  case' h_1 j _ =>
    apply NoAliceDone.bind (noAliceDone_getKey b j _); intro _
    apply NoAliceDone.bind (NoAliceDone.pure _)
  case' h_2 =>
    apply NoAliceDone.bind (NoAliceDone.pure _)
  all_goals
    intro _
    apply NoAliceDone.bind (noAliceDone_lookupIdentity a regIdxA); intro ⟨_, _⟩
    dsimp only
    apply NoAliceDone.bind (noAliceDone_receiveMessage ekIdx); intro _
    apply NoAliceDone.bind (noAliceDone_receiveMessage ctIdx); intro _
    apply NoAliceDone.bind (NoAliceDone.guardP _); intro _
    split
    · exact NoAliceDone.pure _
    · exact NoAliceDone.failure

private theorem noAliceDone_bobStart (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    NoAliceDone (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine NoAliceDone.bind (noAliceDone_bobHandshake b a kh regIdxA mh.ek mh.ct) fun _ =>
    NoAliceDone.bind (noAliceDone_receiveSignalMsg mh.msg) fun msg =>
    NoAliceDone.bind (noAliceDone_ensureReceiverChain _ msg.ratchetKey) fun ⟨st, _, _⟩ => ?_
  dsimp only
  split
  · split
    · refine NoAliceDone.bind (noAliceDone_sendMessage _) fun _ =>
        NoAliceDone.bind (noAliceDone_receiveMessage pqIdx) fun pqSalt =>
        NoAliceDone.bind (noAliceDone_verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      all_goals first
        | refine NoAliceDone.bind (noAliceDone_guardOnTrace _) fun _ =>
            NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ => ?_
        | skip
      all_goals refine NoAliceDone.bind noAliceDone_traceLength fun _ =>
        NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ => ?_
      all_goals split
      all_goals first
        | refine NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
            NoAliceDone.bind (noAliceDone_logEventTR _) fun _ => ?_
        | skip
      all_goals exact NoAliceDone.bind (noAliceDone_logEventC _) fun _ =>
        NoAliceDone.bind noAliceDone_traceLength fun _ =>
        NoAliceDone.bind (noAliceDone_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
        NoAliceDone.bind (noAliceDone_logEventTR _) fun _ =>
        noAliceDone_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _
    · exact NoAliceDone.failure
  · exact NoAliceDone.failure

private def aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : ExecTrace :=
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := randTerm tr2.length 32
  let rkA := (createChain o.keys.rk o.spk dhsA).1
  let cksA := (createChain o.keys.rk o.spk dhsA).2
  let stA : TRState :=
    { peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB,
      rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0,
      sid := Concat.concat (dhPk dhsA) o.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
      spqr := DY.Spqr.spqrInit o.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32)
  let tr4 := tr3.append (NetE o.ek)
  let tr5 := tr4.append (NetE o.ct)
  let tr6 := tr5.append (EvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))
  let tr7 := tr6.append (TREvE (.InitSession a b (dhPk dhsA) o.spk))
  let tr8 := tr7.append (CEvE (.HandshakeSession (stA.sessionInfo a) tr5.length))
  tr8.append (TRStE a stA)

@[simp] private theorem length_append_entry_asl {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (x : E) : (tr.append x).length = tr.length + 1 := by
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem at?_append_of_lt_asl {E A : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has A]
    (tr : ExecTrace) (x : E) {k : Nat} (hk : k < tr.length) :
    ((tr.append x).at? k : Option A) = (tr.at? k : Option A) := by
  have hi' : k < (tr.append x).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hk, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr (tr.append x) k hk (DY.Trace.append_le tr x)]

private theorem at?_append_self_asl {E A : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has A]
    (tr : ExecTrace) (x : E) {k : Nat} (hk : k = tr.length) :
    ((tr.append x).at? k : Option A) =
      TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hk
  have hlt : tr.length < (tr.append x).length := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [DY.Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

local macro "asl_at?_tr9_tac" : tactic =>
  `(tactic| (dsimp only [aliceStartTr9]
             repeat (rw [at?_append_of_lt_asl _ _ (by simp only [length_append_entry_asl]; omega)])
             rw [at?_append_self_asl _ _ (by simp [length_append_entry_asl])]; rfl))

private theorem newIndices_aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    newIndices tr (aliceStartTr9 tr a b o) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4,
       tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := by
  have hlen : (aliceStartTr9 tr a b o).length = tr.length + 9 := by
    dsimp only [aliceStartTr9]; simp only [length_append_entry_asl]
  unfold newIndices; rw [hlen, Nat.add_sub_cancel_left]
  simp [List.range', Nat.add_assoc]

private theorem newRandoms_aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    newRandoms tr (aliceStartTr9 tr a b o) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32),
       (randTerm (tr.length + 2) 32, 32)] := by
  unfold newRandoms; rw [newIndices_aliceStartTr9]
  have h0 : ((aliceStartTr9 tr a b o).at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by asl_at?_tr9_tac
  have h1 : ((aliceStartTr9 tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE 32) := by asl_at?_tr9_tac
  have h2 : ((aliceStartTr9 tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = some (RndE 32) := by asl_at?_tr9_tac
  have h3 : ((aliceStartTr9 tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by asl_at?_tr9_tac
  have h4 : ((aliceStartTr9 tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by asl_at?_tr9_tac
  have h5 : ((aliceStartTr9 tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by asl_at?_tr9_tac
  have h6 : ((aliceStartTr9 tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by asl_at?_tr9_tac
  have h7 : ((aliceStartTr9 tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := by asl_at?_tr9_tac
  have h8 : ((aliceStartTr9 tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := by asl_at?_tr9_tac
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, RndE]

private theorem getEventAt_pq_aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    let tr' := aliceStartTr9 tr a b o
    tr'.getEventAt PQXDHEvent tr.length = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 1) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 2) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 3) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 4) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 5) =
      some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) ∧
    tr'.getEventAt PQXDHEvent (tr.length + 6) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 7) = none ∧
    tr'.getEventAt PQXDHEvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((aliceStartTr9 tr a b o).at? tr.length : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h1 : ((aliceStartTr9 tr a b o).at? (tr.length + 1) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h2 : ((aliceStartTr9 tr a b o).at? (tr.length + 2) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h3 : ((aliceStartTr9 tr a b o).at? (tr.length + 3) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h4 : ((aliceStartTr9 tr a b o).at? (tr.length + 4) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h5 : ((aliceStartTr9 tr a b o).at? (tr.length + 5) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) =
      some (EvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by asl_at?_tr9_tac
  have h6 : ((aliceStartTr9 tr a b o).at? (tr.length + 6) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h7 : ((aliceStartTr9 tr a b o).at? (tr.length + 7) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  have h8 : ((aliceStartTr9 tr a b o).at? (tr.length + 8) : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by asl_at?_tr9_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, EvE]

private theorem getEventAt_tr_aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    let tr' := aliceStartTr9 tr a b o
    tr'.getEventAt TREvent tr.length = none ∧
    tr'.getEventAt TREvent (tr.length + 1) = none ∧
    tr'.getEventAt TREvent (tr.length + 2) = none ∧
    tr'.getEventAt TREvent (tr.length + 3) = none ∧
    tr'.getEventAt TREvent (tr.length + 4) = none ∧
    tr'.getEventAt TREvent (tr.length + 5) = none ∧
    tr'.getEventAt TREvent (tr.length + 6) =
      some (.InitSession a b (dhPk (randTerm (tr.length + 2) 32)) o.spk) ∧
    tr'.getEventAt TREvent (tr.length + 7) = none ∧
    tr'.getEventAt TREvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((aliceStartTr9 tr a b o).at? tr.length : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h1 : ((aliceStartTr9 tr a b o).at? (tr.length + 1) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h2 : ((aliceStartTr9 tr a b o).at? (tr.length + 2) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h3 : ((aliceStartTr9 tr a b o).at? (tr.length + 3) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h4 : ((aliceStartTr9 tr a b o).at? (tr.length + 4) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h5 : ((aliceStartTr9 tr a b o).at? (tr.length + 5) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h6 : ((aliceStartTr9 tr a b o).at? (tr.length + 6) : Option (ProtocolEvent.ExecEntryT TREvent)) =
      some (TREvE (.InitSession a b (dhPk (randTerm (tr.length + 2) 32)) o.spk)) := by
    dsimp only [aliceStartTr9]
    repeat (rw [at?_append_of_lt_asl _ _ (by simp only [length_append_entry_asl]; omega)])
    rw [at?_append_self_asl _ _ (by simp [length_append_entry_asl])]
    simp only [length_append_entry_asl, Nat.add_assoc]
    rfl
  have h7 : ((aliceStartTr9 tr a b o).at? (tr.length + 7) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  have h8 : ((aliceStartTr9 tr a b o).at? (tr.length + 8) : Option (ProtocolEvent.ExecEntryT TREvent)) = none := by asl_at?_tr9_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, TREvE]

private theorem eventIdx_aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    eventIdx isAliceDone tr (aliceStartTr9 tr a b o) = some (tr.length + 5) := by
  unfold eventIdx; rw [newIndices_aliceStartTr9]
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := getEventAt_pq_aliceStartTr9 tr a b o
  simp [h0, h1, h2, h3, h4, h5, isAliceDone]

private theorem exposures_aliceStartTr9 (tr : ExecTrace) (a b : Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    exposures tr (aliceStartTr9 tr a b o) = [] := by
  unfold exposures pqExposureAt trExposureAt; rw [newIndices_aliceStartTr9]
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := getEventAt_pq_aliceStartTr9 tr a b o
  obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ := getEventAt_tr_aliceStartTr9 tr a b o
  simp [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]

private theorem aliceDone_idx_eq_of_aliceStartTr9 {tr : ExecTrace} {a b : Participant}
    {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {ev : PQXDHEvent} {idx : Nat}
    (hnot : ¬ tr.EventLoggedAt ev idx)
    (hev : (aliceStartTr9 tr a b o).EventLoggedAt ev idx) :
    idx = tr.length + 5 := by
  dsimp only [aliceStartTr9] at hev
  have h6 := eventLoggedAt_append_other (eventLoggedAt_append_other (eventLoggedAt_append_other hev rfl) rfl) rfl
  rcases eventLoggedAt_append_ev_iff.mp h6 with ⟨_, h5⟩ | ⟨hidx, _⟩
  · have h0 := eventLoggedAt_append_other (eventLoggedAt_append_other
      (eventLoggedAt_append_other (eventLoggedAt_append_other
        (eventLoggedAt_append_other h5 rfl) rfl) rfl) rfl) rfl
    exact absurd h0 hnot
  · simp only [length_append_entry_asl] at hidx
    omega

private theorem mem_take_append_of_anchor_some {L R : List VisEntry} {shown idx : Nat}
    (hL : ∀ w ∈ L, w.anchor = none)
    (hv : ∃ v ∈ (L ++ R).take shown, v.anchor = some idx)
    {x : VisEntry} (hx : x ∈ L) : x ∈ (L ++ R).take shown := by
  by_cases hle : shown ≤ L.length
  · rw [List.take_append_of_le_length hle] at hv
    obtain ⟨v, hvMem, hvAnc⟩ := hv
    rw [hL v (List.mem_of_mem_take hvMem)] at hvAnc
    cases hvAnc
  · rw [List.take_append, List.take_of_length_le (by omega)]
    exact List.mem_append_left _ hx

private theorem run_discard_snd {α : Type} (f : Traceful α) (tr : ExecTrace) :
    ((f >>= fun _ => Pure.pure ()).run tr).2.val = (f.run tr).2.val := by
  rw [run_bind_snd]
  cases (f.run tr).1
  · rfl
  · dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1 (Pure.pure ())]
    rfl

private theorem aliceStart_kyberCoin_mem_vis
    (a0 b0 : Participant) (id0 reg0 : Nat) (bh : BundleHandles) (shown : Nat)
    {tr : ExecTrace} {ev : PQXDHEvent} {t : Nat}
    (hanc : (Move.aliceStart a0 b0 id0 reg0 bh shown).LogsSessionCompletion tr)
    (hnot : ¬ tr.EventLoggedAt ev (t + 5))
    (hev : ((Move.aliceStart a0 b0 id0 reg0 bh shown).next tr).EventLoggedAt ev (t + 5)) :
    (⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈
      (Move.aliceStart a0 b0 id0 reg0 bh shown).vis tr := by
  let m := Move.aliceStart a0 b0 id0 reg0 bh shown
  have hmnext : m.next tr = ((DY.Libsignal.Composed.aliceStart a0 b0 id0 reg0 bh).run tr).2.val :=
    run_discard_snd _ tr
  have hStep : ∀ tr' : ExecTrace,
      (tr' = tr ∨ tr' = tr.append (RndE 32) ∨
        ∃ o, tr' = aliceStartTr9 tr a0 b0 o) →
      m.next tr = tr' → tr'.EventLoggedAt ev (t + 5) →
      (⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ m.vis tr := by
    rintro tr' (rfl | rfl | ⟨o, rfl⟩) hmEq hev'
    · exact absurd hev' hnot
    · exact absurd (eventLoggedAt_append_other hev' rfl) hnot
    · have htEq : t + 5 = tr.length + 5 := aliceDone_idx_eq_of_aliceStartTr9 hnot hev'
      have ht : t = tr.length := by omega
      subst ht
      obtain ⟨_, hancF⟩ := hanc
      have hex : ∃ v ∈ m.vis tr, v.anchor = some (tr.length + 5) := by
        apply hancF (tr.length + 5)
        rw [hmEq]
        exact eventIdx_aliceStartTr9 tr a0 b0 o
      have hvisEq : m.vis tr =
          (((⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList), .bundle, none⟩ : VisEntry) ::
            rngEntry (randTerm tr.length 32) ::
            kyberCoinEntries (randTerm (tr.length + 1) 32)) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]).take shown := by
        dsimp only [m, Move.vis]
        rw [hmEq, exposures_aliceStartTr9, List.append_nil]
        unfold aliceVis
        rw [newRandoms_aliceStartTr9, eventIdx_aliceStartTr9]
        rfl
      rw [hvisEq] at hex ⊢
      refine mem_take_append_of_anchor_some ?_ hex ?_
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rfl
        · rcases List.mem_cons.mp hw with rfl | hw
          · rfl
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
            rfl
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨0, by simp [List.mem_range], rfl⟩))
  let P : ExecTrace → Prop := fun tr' =>
    tr' = tr ∨ tr' = tr.append (RndE 32) ∨ ∃ o, tr' = aliceStartTr9 tr a0 b0 o
  have hInv : P ((DY.Libsignal.Composed.aliceStart a0 b0 id0 reg0 bh).run tr).2.val := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine bind_aliceHandshake_at (Inv := P) a0 b0 id0 reg0 bh tr (Or.inl rfl) (Or.inr (Or.inl rfl))
      fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ =>
        Or.inr (Or.inr ⟨aliceOut tr ikA ikBPk spkPk pqPk opk, by
          simp only [DY.Libsignal.TripleRatchet.traceLength,
            Symbolic.DYBridge.DY.Random.genRand_eq_1,
            Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
            Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
            Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
            Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
            Symbolic.DYBridge.DY.appendEntry_eq_1,
            Symbolic.DYBridge.DY.Traceful.mk_eq_1,
            Symbolic.DYBridge.DY.Traceful.run_eq_1]
          rfl⟩)
  exact hStep _ hInv hmnext (hmnext ▸ hev)

private theorem move_not_aliceDone_of_nonAliceStart (m : Move)
    (hnotAs : ∀ a b i r h s, m ≠ .aliceStart a b i r h s) :
    ∀ tr ev idx, isAliceDone ev = true → (m.next tr).EventLoggedAt ev idx → tr.EventLoggedAt ev idx := by
  intro tr ev idx had hev
  dsimp only [Move.next, Move.act] at hev
  cases m with
  | setup a b w => exact noAliceDone_setupAct a b w tr ev idx had hev
  | aliceStart a b i r h s => exact absurd rfl (hnotAs a b i r h s)
  | bobStart b a kh r mh pq sp s =>
    rw [run_discard_snd] at hev; exact noAliceDone_bobStart b a kh r mh pq sp tr ev idx had hev
  | encrypt me st c pq w =>
    rw [run_discard_snd] at hev; exact noAliceDone_messageEncrypt me st c pq tr ev idx had hev
  | encryptAbort me st =>
    rw [run_discard_snd] at hev; exact noAliceDone_messageEncryptAbort me st tr ev idx had hev
  | encryptFail me st c =>
    have hf : NoAliceDone (do
        let n ← DY.Libsignal.TripleRatchet.traceLength
        let _ ← messageEncrypt me st c (n + 3); Pure.pure ()) :=
      NoAliceDone.bind noAliceDone_traceLength fun n =>
        NoAliceDone.bind (noAliceDone_messageEncrypt me st c (n + 3)) fun _ => NoAliceDone.pure _
    exact hf tr ev idx had hev
  | decrypt me st m pq sp w =>
    rw [run_discard_snd] at hev; exact noAliceDone_messageDecrypt me st m pq sp tr ev idx had hev
  | decryptSkipped me st m sk pq sp w =>
    rw [run_discard_snd] at hev; exact noAliceDone_messageDecryptSkipped me st m sk pq sp tr ev idx had hev
  | reject _ =>
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1] at hev
    exact hev
  | compromiseIK p st =>
    rw [run_discard_snd] at hev
    exact (NoAliceDone.bind (noAliceDone_getKey p st _) fun _ =>
      NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ => noAliceDone_sendMessage _) tr ev idx had hev
  | compromiseSPK b st =>
    rw [run_discard_snd] at hev
    exact (NoAliceDone.bind (noAliceDone_getKey b st _) fun _ =>
      NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ => noAliceDone_sendMessage _) tr ev idx had hev
  | compromisePQSPK b st =>
    rw [run_discard_snd] at hev
    exact (NoAliceDone.bind (noAliceDone_getKey b st _) fun _ =>
      NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ => noAliceDone_sendMessage _) tr ev idx had hev
  | compromiseOPK b st =>
    rw [run_discard_snd] at hev
    exact (NoAliceDone.bind (noAliceDone_getKey b st _) fun _ =>
      NoAliceDone.bind (noAliceDone_guardOnTrace _) fun _ =>
      NoAliceDone.bind (noAliceDone_logEventPQ rfl) fun _ => noAliceDone_sendMessage _) tr ev idx had hev
  | exposeKey me st k =>
    rw [run_discard_snd] at hev; exact noAliceDone_exposeKey me st k tr ev idx had hev
  | exposeSpqr me st =>
    rw [run_discard_snd] at hev; exact noAliceDone_exposeSpqr me st tr ev idx had hev
  | exposeSkipped sk =>
    rw [run_discard_snd] at hev; exact noAliceDone_exposeSkipped sk tr ev idx had hev
  | attackerSend msg =>
    rw [run_discard_snd] at hev; exact noAliceDone_sendMessage msg tr ev idx had hev
  | brkDH =>
    exact noAliceDone_logEventPQ (e := .BrokenDH) rfl tr ev idx had hev
  | brkKEM =>
    exact noAliceDone_logEventPQ (e := .BrokenKEM) rfl tr ev idx had hev

private theorem runMoves_kyberCoin_mem_vis :
    ∀ (ms : List Move) (tr : ExecTrace), MovesAnchored ms tr →
      ∀ {ev : PQXDHEvent} {t : Nat}, isAliceDone ev = true →
      ¬ tr.EventLoggedAt ev (t + 5) →
      (runMoves ms tr).1.EventLoggedAt ev (t + 5) →
      (⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ (runMoves ms tr).2
  | [], tr, _, _, _, _, hnot, hev => absurd hev hnot
  | m :: ms, tr, ⟨hanc, hancs⟩, ev, t, had, hnot, hev => by
    rw [runMoves_cons_fst] at hev
    rw [runMoves_cons_snd]
    by_cases hm : (m.next tr).EventLoggedAt ev (t + 5)
    · cases m with
      | aliceStart a0 b0 id0 reg0 bh shown =>
        exact List.mem_append_left _ (aliceStart_kyberCoin_mem_vis a0 b0 id0 reg0 bh shown hanc hnot hm)
      | _ =>
        exact absurd (move_not_aliceDone_of_nonAliceStart _ (by intros; rintro ⟨⟩) tr ev (t + 5) had hm) hnot
    · exact List.mem_append_right _ (runMoves_kyberCoin_mem_vis ms (m.next tr) hancs had hm hev)

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hrx⟩ := ih hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hrx⟩

/-- Under `MatchedPrefix`, every `AliceDone` event on `runTraceMoves r ms` is matched by a
`.kyberCoin 0` visible entry forcing `(gamma i S g (randTerm (t + 1) 32)).length = 32`. -/
theorem aliceKemLen32_of_matchedPrefix {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix i r S who g ms τ) :
    AliceKemLen32 i S g (runTraceMoves r ms) := by
  intro t a b ikA ikB spk pqpk opk ek ct keys hev
  have hAnc : MovesAnchored ms (setupTrace r) := hmp.2.1.2.2.1.2.1
  have hFor : List.Forall₂ (EventMatchesEntry i r S g) τ (runVis r ms) := hmp.2.2.2.2.2
  have hNotNil : ¬ Trace.nil.EventLoggedAt
      (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) := by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq, not_false_eq_true]
  have hNotSetup : ¬ (setupTrace r).EventLoggedAt
      (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) := fun hs =>
    hNotNil (move_not_aliceDone_of_nonAliceStart r.setupMove (by intros; rintro ⟨⟩)
      Trace.nil _ (t + 5) rfl hs)
  have hMemMoves : (⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈
      (runMoves ms (setupTrace r)).2 :=
    runMoves_kyberCoin_mem_vis ms (setupTrace r) hAnc rfl hNotSetup hev
  have hMemVis : (⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ runVis r ms := by
    unfold runVis
    rw [runMoves_cons_snd]
    exact List.mem_append_right _ hMemMoves
  obtain ⟨evHw, _, hMatch⟩ := forall₂_mem_right hFor hMemVis
  obtain ⟨_, _, t', htEq, hlen, _⟩ := hMatch
  injection htEq with htEq'
  subst htEq'
  exact hlen

end AliceKemLen32Proof

end Symbolic.Swarm.CREF.TR.G1.Spine

namespace Symbolic.Swarm.CREF.TR.G1.KemPeel

cref_open
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg kdfCk)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.G1.Spine

end Symbolic.Swarm.CREF.TR.G1.KemPeel

namespace Symbolic.Swarm.CREF.TR.G1.SkelLocal

end Symbolic.Swarm.CREF.TR.G1.SkelLocal
