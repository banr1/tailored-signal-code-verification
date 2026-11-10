/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSkelLocal
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeel

/-!
# Alice Handshake Key-Bundle Twins

Defines `AliceDoneKeys` and `BobDoneKeys` and proves `aliceDone_twin`: on a reachable trace
satisfying `AliceKemLen32`, two `AliceDone` key bundles whose root keys or chain keys have equal
`gamma'` shapes have equal root keys or chain keys unless their memo windows satisfy `KemSlotAlias`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhIkm pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-- `keys` is the key bundle of a logged `AliceDone` event. -/
def AliceDoneKeys (T : ExecTrace) (keys : HandshakeKeys) : Prop :=
  ∃ a b ikA ikB spk pqpk opk ek ct j,
    T.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j

/-- `keys` is the key bundle of a logged `BobDone` event. -/
def BobDoneKeys (T : ExecTrace) (keys : HandshakeKeys) : Prop :=
  ∃ b a ikB ikA spk pqpk opk ek ct j,
    T.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) j

/-! ## Alice handshake twins -/

private theorem seedSepBase_keys_of_aliceAgreement {ikA ek ikB spk pq e ct : DY.Bytes}
    {opk : Option DY.Bytes} {keys : HandshakeKeys}
    (h : (ct, keys) = DY.Libsignal.PQXDH.aliceAgreement ikA ek ikB spk pq opk e) :
    ∃ (a b c : DY.Bytes) (d : Option DY.Bytes),
      keys = pqxdhKdf (pqxdhIkm a b c d (DY.PQKem.kemEncap pq e).2) := by
  rcases hk : DY.PQKem.kemEncap pq e with ⟨c₀, s₀⟩
  unfold DY.Libsignal.PQXDH.aliceAgreement at h
  rw [hk] at h
  simp only [Prod.mk.injEq] at h
  exact ⟨_, _, _, _, h.2⟩

private theorem seedSepBase_ikm_shape {f : HandshakeKeys → DY.Bytes}
    (hf : f = HandshakeKeys.rk ∨ f = HandshakeKeys.ck) {ikm₁ ikm₂ : DY.Bytes}
    (hsh : (gamma' i S g (f (pqxdhKdf ikm₁))).shape = (gamma' i S g (f (pqxdhKdf ikm₂))).shape) :
    (gamma' i S g ikm₁).shape = (gamma' i S g ikm₂).shape := by
  rcases hf with rfl | rfl
  · exact (ShapeModKem.shape_kdfExtract_inj i S g (ShapeModKem.shape_kdfExtract_inj i S g hsh).1).2
  · exact (ShapeModKem.shape_kdfExtract_inj i S g (ShapeModKem.shape_kdfExtract_inj i S g hsh).1).2

private theorem seedSepBase_ss_shape {a₁ b₁ c₁ a₂ b₂ c₂ pk₁ e₁ pk₂ e₂ : DY.Bytes}
    {d₁ d₂ : Option DY.Bytes}
    (hsh : (gamma' i S g (pqxdhIkm a₁ b₁ c₁ d₁ (DY.PQKem.kemEncap pk₁ e₁).2)).shape =
      (gamma' i S g (pqxdhIkm a₂ b₂ c₂ d₂ (DY.PQKem.kemEncap pk₂ e₂).2)).shape) :
    (gamma' i S g (DY.PQKem.kemEncap pk₁ e₁).2).shape =
      (gamma' i S g (DY.PQKem.kemEncap pk₂ e₂).2).shape := by
  unfold pqxdhIkm at hsh
  have h := (shape_concat_inj i S g (shape_concat_inj i S g (shape_concat_inj i S g
    (shape_concat_inj i S g hsh).2).2).2).2
  cases d₁ <;> cases d₂ <;> dsimp only at h
  · exact h
  · exact absurd h (ShapeModKem.shape_kemLeaf_ne_concat i S g (.inl ⟨_, _, rfl⟩))
  · exact absurd h.symm (ShapeModKem.shape_kemLeaf_ne_concat i S g (.inl ⟨_, _, rfl⟩))
  · exact (shape_concat_inj i S g h).2

/-- On a reachable trace satisfying `AliceKemLen32`, two `AliceDone` key bundles whose root keys or
chain keys have equal `gamma'` shapes have equal outputs unless `KemSlotAlias` holds. -/
theorem aliceDone_twin {T : ExecTrace} (hT : ReachableTrace T) (hKem32 : AliceKemLen32 i S g T)
    {k₁ k₂ : HandshakeKeys}
    (h₁ : AliceDoneKeys T k₁) (h₂ : AliceDoneKeys T k₂)
    (f : HandshakeKeys → DY.Bytes) (hf : f = HandshakeKeys.rk ∨ f = HandshakeKeys.ck)
    {t₁ t₂ : DY.Bytes}
    (_hm₁ : ∀ e ∈ (gamma' i S g (f k₁)).memo, e ∈ (gamma' i S g t₁).memo)
    (_hm₂ : ∀ e ∈ (gamma' i S g (f k₂)).memo, e ∈ (gamma' i S g t₂).memo)
    (hsh : (gamma' i S g (f k₁)).shape = (gamma' i S g (f k₂)).shape) :
    f k₁ = f k₂ := by
  obtain ⟨a₁, b₁, ikA₁, ikB₁, spk₁, pq₁, opk₁, ek₁, ct₁, j₁, hev₁⟩ := h₁
  obtain ⟨a₂, b₂, ikA₂, ikB₂, spk₂, pq₂, opk₂, ek₂, ct₂, j₂, hev₂⟩ := h₂
  have hinv : SpqrInv T := spqrInv_of_reachable _ hT
  obtain ⟨u₁, sA₁, rfl, -, -, -, -, hag₁, -⟩ := hinv.aliceDone _ _ _ _ _ _ _ _ _ _ _ hev₁
  obtain ⟨u₂, sA₂, rfl, -, -, -, -, hag₂, -⟩ := hinv.aliceDone _ _ _ _ _ _ _ _ _ _ _ hev₂
  obtain ⟨x₁, y₁, z₁, d₁, hk₁⟩ := seedSepBase_keys_of_aliceAgreement hag₁
  obtain ⟨x₂, y₂, z₂, d₂, hk₂⟩ := seedSepBase_keys_of_aliceAgreement hag₂
  have hsh' := hsh
  rw [hk₁, hk₂] at hsh'
  have hss := seedSepBase_ss_shape i S g (seedSepBase_ikm_shape i S g hf hsh')
  have h32₁ : (gamma i S g (randTerm (u₁ + 1) 32)).length = 32 :=
    hKem32 u₁ a₁ b₁ ikA₁ ikB₁ spk₁ pq₁ opk₁ ek₁ ct₁ k₁ hev₁
  have hts : u₁ + 1 = u₂ + 1 := Stage1Kyber.kemSS_rand32_twin_ts_eq i S g h32₁ hss
  have hu : u₁ = u₂ := by omega
  subst hu
  have hev := CompInv.CompPresBob.evAt_unique hev₁ hev₂
  injection hev with _ _ _ _ _ _ _ _ _ hk
  exact hk ▸ rfl

end Symbolic.Swarm.CREF.TR.G1.Spine
