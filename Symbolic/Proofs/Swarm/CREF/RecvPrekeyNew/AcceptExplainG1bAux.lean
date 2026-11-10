/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.MacInv
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkSpine
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr

/-!
# Ephemeral Key Honesty in the Honest-Send MAC Branch

Proves that if Bob's pre-key receive seed matches the sending seed `(kdfCk st_s.cks).2` of an
available session state `st_s`, then `normalizeX25519Key x'.ek` is the public key of an honest
32-byte random draw.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.DiffieHellman
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg)
open DY.Libsignal.TripleRatchet (RecvChain chainKeyAt consumeMessageKey kdfCk kdfRk)
open Symbolic.Swarm.CREF.MacInv
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

namespace G1bAux

theorem spineRk_of_chainKeyAt (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {B : Bool → DY.Bytes → Prop} {b : Bool} :
    ∀ (n : Nat) {ck : DY.Bytes}, SpineRk B b (chainKeyAt ck n) → SpineRk B b ck
  | 0, _, h => h
  | n + 1, _, h => spineRk_kdfCk_fst_inv i S g (spineRk_of_chainKeyAt i S g n h)

theorem ikAt_bob_runTrace {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move) :
    ∃ t, setupSecret r 1 = randTerm t 32 ∧ IkAt (runTraceMoves r ms) t := by
  have h := MacInv.runTrace_at?_9 r hne ms
  have htr := traceOkR_runTrace r ms
  change ((runTraceMoves r ms).at? 9 : Option Ik.IkPQStEntry) =
    some ⟨⟨r.bob, { kind := .identity, sk := setupSecret r 1 }⟩⟩ at h
  unfold DY.Trace.at? at h
  split at h
  · next hj =>
    have hp : ∃ t, t < 9 ∧ setupSecret r 1 = randTerm t 32 ∧ IkAt (runTraceMoves r ms) t :=
      (htr 9 hj).2 _ h
    obtain ⟨t, _, hsk, hik⟩ := hp
    exact ⟨t, hsk, hik⟩
  · cases h

theorem dh_eq_dh_of_ne {P pk' : DY.Bytes} {t₁ t₂ : Nat} (hne : t₁ ≠ t₂)
    (h : dh P (randTerm t₁ 32) = dh pk' (randTerm t₂ 32)) :
    P = dhPk (randTerm t₂ 32) := by
  obtain ⟨P₂, S₂, hd₂, hor₂⟩ := dh_eq_pack_and_or pk' (randTerm t₂ 32)
  rw [hd₂] at h
  dsimp only [CanDH.dh] at h
  split at h
  · next sk2 hv =>
    have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF P
    rw [hv] at hpv
    have hsk2 : sk2 = randTerm t₂ 32 := by
      by_cases hle : randTerm t₁ 32 ≤ sk2 <;> simp only [hle, ↓reduceIte] at h <;>
        obtain ⟨hP, hS⟩ := dh_pack_inj h <;> rcases hor₂ with rfl | rfl
      · exact absurd (randTerm32_injective hS) hne
      · exact dhPk_injective hP
      · exact hS
      · exact absurd (randTerm32_injective (dhPk_injective hP)) hne
    subst hsk2
    exact hpv.symm
  · next hv =>
    obtain ⟨hP, hS⟩ := dh_pack_inj h
    rcases hor₂ with rfl | rfl
    · exact absurd (randTerm32_injective hS) hne
    · exact hP

end G1bAux

open G1bAux in
/-- Bob's normalized pre-key `x'.ek` is an honest ephemeral public key whenever Bob's receive seed
equals the sending seed of an available session state. -/
theorem rpk_g1b_ek_honest (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x' : PreKeyRep}
    {keys' : PQXDH.HandshakeKeys} {msg' : TRSignalMsg} {seed' : DY.Bytes}
    {c' : TripleRatchet.RecvChain} {st_s : TRState}
    (hkeys : bobKeys r p x' = some keys')
    (hcmk : TripleRatchet.consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hst_s : st_s ∈ availableStates r (runTraceMoves r ms))
    (hseed : (kdfCk st_s.cks).2 = seed') :
    ∃ t, DY.X25519.normalizeX25519Key x'.ek = DY.DiffieHellman.dhPk (randTerm t 32) := by
  obtain ⟨hseed_eq, _⟩ := consumeMessageKey_eq_spine hcmk
  have hck_eq : st_s.cks =
      chainKeyAt (bobChain r keys' msg').chainKey (msg'.counter.toNat - (bobChain r keys' msg').index.toNat) := by
    have h := hseed.trans hseed_eq
    exact (kdfExtract_injective h).1
  have hsp : SpineRk (LoggedIkmRk (runTraceMoves r ms)) true st_s.cks := (spStateRk_runTrace hst_s).cks
  rw [hck_eq] at hsp
  have hsp1 := spineRk_of_chainKeyAt i S g _ hsp
  have hsp2 : SpineRk (LoggedIkmRk (runTraceMoves r ms)) true
      (kdfRk keys'.rk (dh (DY.X25519.normalizeX25519Key msg'.ratchetKey) (setupSecret r 2))).2 := hsp1
  obtain ⟨hrk, _⟩ := spineRk_kdfRk_snd_inv i S g hsp2
  obtain ⟨ikm, ⟨opk, _hsel, hikm⟩, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x' keys' hkeys
  rw [hkeys_eq] at hrk
  have hlog : LoggedIkmRk (runTraceMoves r ms) false ikm := spineRk_pqxdhKdf_rk_inv i S g hrk
  obtain ⟨a, b, e, d, ss, hm, hroles, _⟩ := loggedIkmRk_roleHoles hlog
  have hb : DY.Libsignal.PQXDH.agree x'.ek (setupSecret r 1) = b := by
    rw [hikm] at hm
    unfold DY.Libsignal.PQXDH.pqxdhIkm at hm
    exact (concat_injective (concat_injective (concat_injective hm).2).2).1
  obtain ⟨_, ⟨pk', t, hbdh, hek⟩, _, _⟩ := hroles
  obtain ⟨tᵢ, hik_eq, hikAt⟩ := ikAt_bob_runTrace hne ms
  have hdh : dh (DY.X25519.normalizeX25519Key x'.ek) (randTerm tᵢ 32) = dh pk' (randTerm t 32) := by
    rw [← hbdh, ← hb, hik_eq]; rfl
  have hne_t : tᵢ ≠ t := fun h => ekAt_ikAt_false _ t hek (h ▸ hikAt)
  exact ⟨t, dh_eq_dh_of_ne hne_t hdh⟩

end Symbolic.Swarm.CREF
