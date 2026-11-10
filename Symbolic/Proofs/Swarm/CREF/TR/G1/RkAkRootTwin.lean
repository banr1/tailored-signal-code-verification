/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepDefs
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepGood

/-!
# Chain-Root Shape Twins (`rootTwin`)

Proves `rootTwin` from `RkTwinStmt` and `aliceDone_twin`: an honest sending or Alice handshake
chain root (`RootX`) and an honest receive-chain root (`RecvRoot`) with equal `gamma'` shapes are
equal unless their memo windows satisfy `KemSlotAlias`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (createChain hkdfBlock1 hkdfBlock2 lit)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhLabel)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-- Under `RkTwinStmt`, the `hkdfBlock2` halves of a stored root key's expansion and of an `RkInter`
node's expansion with equal `gamma'` shapes are equal unless `KemSlotAlias` holds. -/
theorem sibling_twin {T : ExecTrace} (hRkTwin : RkTwinStmt i S g T)
    {p : Participant} {st : TRState} {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T)
    {pk x p₁ l₁ p₂ l₂ t₁ t₂ : DY.Bytes} (hx : RkInter T pk x)
    (hrk : st.rk = hkdfBlock1 p₁ l₁) (hxe : x = hkdfBlock1 p₂ l₂)
    (hm₁ : ∀ e ∈ (gamma' i S g (hkdfBlock2 p₁ l₁)).memo, e ∈ (gamma' i S g t₁).memo)
    (hm₂ : ∀ e ∈ (gamma' i S g (hkdfBlock2 p₂ l₂)).memo, e ∈ (gamma' i S g t₂).memo)
    (hsh : (gamma' i S g (hkdfBlock2 p₁ l₁)).shape = (gamma' i S g (hkdfBlock2 p₂ l₂)).shape) :
    hkdfBlock2 p₁ l₁ = hkdfBlock2 p₂ l₂ := by
  rw [shape_hkdfBlock2, shape_hkdfBlock2] at hsh
  obtain ⟨hp, hl⟩ := hkdfBlock2_inj hsh
  have hm₁' : ∀ e ∈ (gamma' i S g st.rk).memo, e ∈ (gamma' i S g t₁).memo := by
    intro e he
    rw [hrk] at he
    exact hm₁ _ (memo_hkdfBlock1_hkdfBlock2 i S g p₁ l₁ he)
  have hm₂' : ∀ e ∈ (gamma' i S g x).memo, e ∈ (gamma' i S g t₂).memo := by
    intro e he
    rw [hxe] at he
    exact hm₂ _ (memo_hkdfBlock1_hkdfBlock2 i S g p₂ l₂ he)
  have hsh' : (gamma' i S g st.rk).shape = (gamma' i S g x).shape := by
    rw [hrk, hxe, shape_hkdfBlock1, shape_hkdfBlock1, hp, hl]
  have h := hRkTwin hst hx hm₁' hm₂' hsh'
  obtain ⟨rfl, rfl⟩ := hkdfBlock1_inj (hrk.symm.trans (h.trans hxe))
  rfl

theorem shape_hkdfBlock2_wr_ne_pq (p₁ p₂ : DY.Bytes) :
    (gamma' i S g (hkdfBlock2 p₁ (lit "WhisperRatchet"))).shape ≠
      (gamma' i S g (hkdfBlock2 p₂ pqxdhLabel)).shape := by
  intro h
  rw [shape_hkdfBlock2, shape_hkdfBlock2, shape_lit, shape_pqxdhLabel] at h
  exact pqxdhLabel_ne_whisperRatchet_rk (hkdfBlock2_inj h).2.symm

/-- A `RootX` chain root and a `RecvRoot` chain root with equal `gamma'` shapes are equal unless
`KemSlotAlias` holds. -/
theorem rootTwin {T : ExecTrace} (hT : ReachableTrace T) (hKem32 : AliceKemLen32 i S g T)
    (hRkTwin : RkTwinStmt i S g T) :
    RootTwinStmt i S g T := by
  intro X pk R t₁ t₂ hX hR hm₁ hm₂ hsh
  rcases hX with ⟨p', st', i', j', hst', -, rk1, k, rfl, hrk⟩ | ⟨keysA, hA, rfl⟩
  · rcases hR with ⟨p₀, st₀, i₀, hst₀, rfl⟩ | ⟨keys, t, b, idx, hB, hspk, rfl⟩ | ⟨keys, hk, rfl⟩
    · exact sibling_twin i S g hRkTwin hst' (pk := pk) (x := (createChain st₀.rk pk st₀.dhs).1)
        (Or.inl ⟨p₀, st₀, i₀, hst₀, rfl⟩) (hrk.trans (createChain_fst_eq _ _ _))
        (createChain_fst_eq _ _ _) hm₁ hm₂ hsh
    · exact sibling_twin i S g hRkTwin hst' (pk := pk)
        (x := (createChain keys.rk pk (randTerm t 32)).1)
        (Or.inr ⟨keys, t, b, idx, hB, hspk, rfl⟩) (hrk.trans (createChain_fst_eq _ _ _))
        (createChain_fst_eq _ _ _) hm₁ hm₂ hsh
    · obtain ⟨ikm, rfl⟩ := aliceDoneKeys_pqxdh hT hk
      rw [createChain_snd_eq, pqxdhKdf_ck_eq] at hsh
      exact absurd hsh (shape_hkdfBlock2_wr_ne_pq i S g _ _)
  · obtain ⟨ikmA, rfl⟩ := aliceDoneKeys_pqxdh hT hA
    rcases hR with ⟨p₀, st₀, i₀, hst₀, rfl⟩ | ⟨keys, t, b, idx, hB, hspk, rfl⟩ | ⟨keys, hk, rfl⟩
    · rw [createChain_snd_eq, pqxdhKdf_ck_eq] at hsh
      exact absurd hsh.symm (shape_hkdfBlock2_wr_ne_pq i S g _ _)
    · rw [createChain_snd_eq, pqxdhKdf_ck_eq] at hsh
      exact absurd hsh.symm (shape_hkdfBlock2_wr_ne_pq i S g _ _)
    · exact aliceDone_twin i S g hT hKem32 hA hk HandshakeKeys.ck (.inr rfl) hm₁ hm₂ hsh

end Symbolic.Swarm.CREF.TR.G1.Spine
