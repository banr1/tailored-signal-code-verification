/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSkelLocal
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineShapeModKemInv
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Init.Data.String.Defs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.KdfProvNon01Defs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkKDefs
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.DhSafe
import Symbolic.Proofs.Swarm.CREF.TR.G1.KdfProvNon01
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# One-Step Spine Peel and KEM Twin Closure

Proves `gamma'`-shape twin closure for KEM shared secrets and implicit-rejection keys
(`KemKnownFromTwin`, `IkmHolesKemK`) together with single-step KDF peel lemmas (`peel_outer`,
`peel_rk`, `peel_ikm`) along known-peer-key Double Ratchet and PQXDH spines.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (kdfCk kdfRk hmac hkdfBlock1 hkdfBlock2 lit litByte zeroSalt)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhLabel discontinuity)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvDecStep (shape_concat_tr)

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-! ## Shape disjointness -/

theorem shape_concat_inj {l₁ r₁ l₂ r₂ : DY.Bytes}
    (h : (gamma' i S g (Concat.concat l₁ r₁)).shape = (gamma' i S g (Concat.concat l₂ r₂)).shape) :
    (gamma' i S g l₁).shape = (gamma' i S g l₂).shape ∧
      (gamma' i S g r₁).shape = (gamma' i S g r₂).shape := by
  rw [shape_concat_tr, shape_concat_tr] at h
  exact concat_injective h

theorem shape_literal_ne_concat (b : ByteArray) (l r : DY.Bytes) :
    (gamma' i S g (Literal.literalToBytes b)).shape ≠ (gamma' i S g (Concat.concat l r)).shape := by
  rw [shape_literalToBytes, shape_concat_tr]
  exact literal_ne_concat b _ _

unseal DY.Bytes in
theorem literal_ne_dhPack (b : ByteArray) (p s : DY.Bytes) :
    Literal.literalToBytes b ≠ (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro h
  have h1 := DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) { pk := p, sk := s }
  change DY.Bytes.view? (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) _ = _ at h1
  have h2 : DY.Bytes.view? (Literal.literalToBytes b) DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [← h, h2] at h1
  contradiction

unseal DY.Bytes in
theorem concat_ne_dhPack (l r p s : DY.Bytes) :
    Concat.concat l r ≠ (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro h
  have h1 := DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) { pk := p, sk := s }
  change DY.Bytes.view? (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) _ = _ at h1
  have h2 : DY.Bytes.view? (Concat.concat l r) DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [← h, h2] at h1
  contradiction

theorem shape_dh_eq_pack (pk' r : DY.Bytes) : ∃ P Q : DY.Bytes,
    (gamma' i S g (dh pk' r)).shape = (({ pk := P, sk := Q } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  obtain ⟨P, Q, hd, -⟩ := dh_eq_pack_and_or pk' r
  rw [hd, shape_dhPack_c]
  exact ⟨_, _, rfl⟩

theorem shape_literal_ne_dh (b : ByteArray) (pk' r : DY.Bytes) :
    (gamma' i S g (Literal.literalToBytes b)).shape ≠ (gamma' i S g (dh pk' r)).shape := by
  obtain ⟨P, Q, h⟩ := shape_dh_eq_pack i S g pk' r
  rw [h, shape_literalToBytes]
  exact literal_ne_dhPack b P Q

theorem shape_concat_ne_dh (l r pk' sk : DY.Bytes) :
    (gamma' i S g (Concat.concat l r)).shape ≠ (gamma' i S g (dh pk' sk)).shape := by
  obtain ⟨P, Q, h⟩ := shape_dh_eq_pack i S g pk' sk
  rw [h, shape_concat_tr]
  exact concat_ne_dhPack _ _ P Q

unseal DY.Bytes in
theorem literalToBytes_inj {b₁ b₂ : ByteArray}
    (h : (Literal.literalToBytes b₁ : DY.Bytes) = Literal.literalToBytes b₂) : b₁ = b₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Literal.Literal.SubF) { lit := b₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Literal.Literal.SubF) { lit := b₂ }
  change DY.Bytes.view? (Literal.literalToBytes b₁) _ = _ at h1
  change DY.Bytes.view? (Literal.literalToBytes b₂) _ = _ at h2
  rw [h, h2] at h1
  injection h1 with h1
  exact (congrArg DY.Literal.Literal.SubF.lit h1).symm

theorem eq_of_shape_eq_literal {b₁ b₂ : ByteArray}
    (h : (gamma' i S g (Literal.literalToBytes b₁)).shape =
      (gamma' i S g (Literal.literalToBytes b₂)).shape) :
    (Literal.literalToBytes b₁ : DY.Bytes) = Literal.literalToBytes b₂ := by
  rwa [shape_literalToBytes, shape_literalToBytes] at h

theorem lit_wr_length : (lit "WhisperRatchet").length = 14 := by
  unfold lit
  rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperRatchet"), String.toByteArray_ofList]
  decide

theorem pqxdhLabel_length : pqxdhLabel.length = 46 := by
  unfold pqxdhLabel lit
  rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
      String.toByteArray_ofList]
  decide

theorem discontinuity_length : discontinuity.length = 32 := by
  unfold discontinuity; rw [Literal.length_literalToBytes]; rfl

theorem shape_lit_wr_ne_pq : (gamma' i S g (lit "WhisperRatchet")).shape ≠ (gamma' i S g pqxdhLabel).shape := by
  intro h
  have h1 := congrArg DY.Bytes.length (eq_of_shape_eq_literal i S g h)
  change (lit "WhisperRatchet").length = pqxdhLabel.length at h1
  rw [lit_wr_length, pqxdhLabel_length] at h1
  cases h1

theorem shape_lit_wr_ne_disc :
    (gamma' i S g (lit "WhisperRatchet")).shape ≠ (gamma' i S g discontinuity).shape := by
  intro h
  have h1 := congrArg DY.Bytes.length (eq_of_shape_eq_literal i S g h)
  change (lit "WhisperRatchet").length = discontinuity.length at h1
  rw [lit_wr_length, discontinuity_length] at h1
  cases h1

theorem shape_lb3_ne_lb2 : (gamma' i S g (litByte 3)).shape ≠ (gamma' i S g (litByte 2)).shape := by
  intro h
  have h1 := congrArg (fun b : ByteArray => b.data[0]!) (literalToBytes_inj (eq_of_shape_eq_literal i S g h))
  revert h1
  decide

/-! ## SPQR auth-key label exclusions -/

theorem no7_lit (b : ByteArray) (b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Literal.literalToBytes b)).shape :=
  fun h => shape_literal_ne_concat i S g b _ _ h.symm

theorem no7_x1 (L : DY.Bytes) (b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Concat.concat L (litByte 1))).shape :=
  fun h => shape_literal_ne_concat i S g _ _ _ (shape_concat_inj i S g h).2.symm

theorem no7_wr2 (X b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Concat.concat X (Concat.concat (lit "WhisperRatchet") (litByte 2)))).shape :=
  fun h => shape_lit_wr_ne_pq i S g (shape_concat_inj i S g (shape_concat_inj i S g h).2).1.symm

theorem no7_pq2 (X b1 : DY.Bytes) :
    (gamma' i S g (Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3)))).shape ≠
      (gamma' i S g (Concat.concat X (Concat.concat pqxdhLabel (litByte 2)))).shape :=
  fun h => shape_lb3_ne_lb2 i S g (shape_concat_inj i S g (shape_concat_inj i S g h).2).2

/-! ## Attacker-knowledge builders and KEM twin closure -/

theorem ak_lit {T : ExecTrace} (b : ByteArray) : (Literal.literalToBytes b : DY.Bytes).AttackerKnows T :=
  Literal.attacker_knows_literalToBytes b T

theorem ak_concat {T : ExecTrace} {l r : DY.Bytes} (hl : l.AttackerKnows T) (hr : r.AttackerKnows T) :
    (Concat.concat l r).AttackerKnows T :=
  Concat.attacker_knows_concat l r T hl hr

theorem ak_hmac {T : ExecTrace} {k m : DY.Bytes} (hk : k.AttackerKnows T) (hm : m.AttackerKnows T) :
    (hmac k m).AttackerKnows T :=
  KdfExtract.attacker_knows_kdfExtract k m T hk hm

theorem ak_hkdfBlock1 {T : ExecTrace} {prk info : DY.Bytes} (hp : prk.AttackerKnows T)
    (hi : info.AttackerKnows T) : (hkdfBlock1 prk info).AttackerKnows T :=
  ak_hmac hp (ak_concat hi (ak_lit _))

theorem ak_hkdfBlock2 {T : ExecTrace} {prk info : DY.Bytes} (hp : prk.AttackerKnows T)
    (hi : info.AttackerKnows T) : (hkdfBlock2 prk info).AttackerKnows T :=
  ak_hmac hp (ak_concat (ak_hkdfBlock1 hp hi) (ak_concat hi (ak_lit _)))

theorem ak_split {T : ExecTrace} {l r : DY.Bytes} (h : (Concat.concat l r).AttackerKnows T) :
    l.AttackerKnows T ∧ r.AttackerKnows T := by
  have h1 := Concat.attacker_knows_split _ l.length T h
  rw [Concat.split_concat] at h1
  exact h1

unseal DY.Bytes in
theorem dh_cases_c (pk' r : DY.Bytes) :
    (pk'.view? DY.DiffieHellman.DhPk.SubF = none ∧
      dh pk' r = (({ pk := pk', sk := r } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) ∨
    ∃ sk2 : DY.Bytes, pk' = dhPk sk2 ∧
      dh pk' r = (if r ≤ sk2 then (({ pk := dhPk sk2, sk := r } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)
        else (({ pk := dhPk r, sk := sk2 } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)) := by
  have hpv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk'
  dsimp only [CanDH.dh]; revert hpv
  cases pk'.view? DY.DiffieHellman.DhPk.SubF with
  | none => intro _; exact Or.inl ⟨rfl, rfl⟩
  | some y => intro hpv; exact Or.inr ⟨y.sk, hpv.symm, rfl⟩

theorem hole_known_of_twin {T : ExecTrace}
    (hpack : ∀ p s : DY.Bytes,
      (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).AttackerKnows T →
      (p.AttackerKnows T ∧ s.AttackerKnows T) ∨
      (∃ c, p = dhPk c ∧ c.AttackerKnows T ∧ (dhPk s).AttackerKnows T))
    (hpk : ∀ z : DY.Bytes, (dhPk z).AttackerKnows T → z.AttackerKnows T ∨ ∃ n, z = randTerm n 32)
    {pk' w : DY.Bytes} {t : Nat} (hpk' : pk'.AttackerKnows T) (hw : w.AttackerKnows T)
    (hsh : (gamma' i S g w).shape = (gamma' i S g (dh pk' (randTerm t 32))).shape) :
    (dh pk' (randTerm t 32)).AttackerKnows T := by
  have hrt : ∀ {x : DY.Bytes} {n : Nat}, x = randTerm n 32 → ∀ {y : DY.Bytes},
      y.AttackerKnows T → (gamma' i S g y).shape = (gamma' i S g x).shape → x.AttackerKnows T := by
    rintro x n rfl y hy hs; rw [eq_randTerm32_of_shape_eq i S g n hs.symm]; exact hy
  rcases dh_cases_c pk' (randTerm t 32) with ⟨hview, hd⟩ | ⟨sk2, rfl, hd⟩
  · rw [hd] at hsh; obtain ⟨p₀, s₀, rfl, hp, hs⟩ := dhPack_shape_eq_inv i S g hsh
    rcases hpack p₀ s₀ hw with ⟨_, hs₀⟩ | ⟨c, rfl, _, _⟩
    · exact DiffieHellman.attacker_knows_dh _ _ T hpk' (hrt rfl hs₀ hs)
    · rw [shape_dhPk_tr] at hp
      obtain ⟨sk, rfl, _⟩ := view?_dhPk_shape_eq_some_inv i S g pk' _
        (by rw [← hp]; exact DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF) _)
      change DY.Bytes.view? (({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)
        DY.DiffieHellman.DhPk.SubF = none at hview
      rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)] at hview; cases hview
  · have hdc : dh (dhPk sk2) (randTerm t 32) = dh (dhPk (randTerm t 32)) sk2 :=
      DiffieHellman.dh_commutes sk2 (randTerm t 32)
    by_cases hle : randTerm t 32 ≤ sk2
    · simp only [hle, ↓reduceIte] at hd; rw [hd] at hsh
      obtain ⟨p₀, s₀, rfl, hp, hs⟩ := dhPack_shape_eq_inv i S g hsh
      rcases hpack p₀ s₀ hw with ⟨_, hs₀⟩ | ⟨c, rfl, hc, hdpk⟩
      · exact DiffieHellman.attacker_knows_dh _ _ T hpk' (hrt rfl hs₀ hs)
      · rw [shape_dhPk_tr, shape_dhPk_tr] at hp
        have hc_sh : (gamma' i S g c).shape = (gamma' i S g sk2).shape := dhPk_injective hp
        have hsk2 : sk2.AttackerKnows T := (hpk sk2 hpk').elim id fun ⟨n, hn⟩ => hrt hn hc hc_sh
        rw [hdc]; exact DiffieHellman.attacker_knows_dh _ _ T (eq_randTerm32_of_shape_eq i S g t hs.symm ▸ hdpk) hsk2
    · simp only [hle, ↓reduceIte] at hd; rw [hd] at hsh
      obtain ⟨p₀, s₀, rfl, hp, hs⟩ := dhPack_shape_eq_inv i S g hsh
      have hp₀ := eq_dhPk_randTerm32_of_shape_eq i S g t hp.symm
      subst hp₀
      rcases hpack _ s₀ hw with ⟨hp₀, hs₀⟩ | ⟨c, hc_eq, hc, _⟩
      · have hsk2 : sk2.AttackerKnows T := (hpk sk2 hpk').elim id fun ⟨n, hn⟩ => hrt hn hs₀ hs
        rw [hdc]; exact DiffieHellman.attacker_knows_dh _ _ T hp₀ hsk2
      · exact DiffieHellman.attacker_knows_dh _ _ T hpk' (dhPk_injective hc_eq ▸ hc)

/-- On a reachable trace, an attacker-known `gamma'`-shape twin `w` of `dh pk' (randTerm t 32)` with
`pk'` attacker-known forces `dh pk' (randTerm t 32)` to be attacker-known. -/
theorem hole_known {T : ExecTrace} (hT : ReachableTrace T) {pk' w : DY.Bytes} {t : Nat}
    (hpk' : pk'.AttackerKnows T) (hw : w.AttackerKnows T)
    (hsh : (gamma' i S g w).shape = (gamma' i S g (dh pk' (randTerm t 32))).shape) :
    (dh pk' (randTerm t 32)).AttackerKnows T :=
  hole_known_of_twin i S g (fun _ _ h => dhPack_attackerKnows_inv hT h)
    (fun _ h => dhPk_attackerKnows_inv hT h) hpk' hw hsh

/-- Any attacker-known twin `R'` with the same `gamma'` shape as `ss` forces `ss` to be
attacker-known. -/
def KemKnownFromTwin (T : ExecTrace) (ss : DY.Bytes) : Prop :=
  ∀ R' : DY.Bytes, R'.AttackerKnows T →
    (gamma' i S g R').shape = (gamma' i S g ss).shape → ss.AttackerKnows T

theorem kemSS_aliceDone_knows_of_shape_eq {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T)
    {t : Nat} {a b : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hev : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5))
    {R' : DY.Bytes} (hR' : R'.AttackerKnows T)
    (hsh : (gamma' i S g R').shape =
      (gamma' i S g (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2).shape) :
    ((DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2).AttackerKnows T := by
  have hlen : (gamma i S g (randTerm (t + 1) 32)).length = 32 :=
    hKem32 t a b ikA ikB spk pqpk opk ek ct keys hev
  obtain ⟨pk', e', hR'Eq, _, _, heSh⟩ :=
    Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 i S g hlen hsh
  have heEq : e' = randTerm (t + 1) 32 := by
    first
    | exact eq_randTerm32_of_shape_eq i S g (t + 1) heSh
    | exact (eq_randTerm32_of_shape_eq i S g (t + 1) heSh.symm).symm
  subst hR'Eq
  subst heEq
  rcases kemEncap_snd_attackerKnows_inv hT hR' with hkCoin |
      ⟨t', a', b', ikA', ikB', spk', pqpk', opk', ek', ct', keys', hev', hpqEq, hrndEq⟩
  · exact absurd hkCoin (aliceDone_kemCoin_not_attackerKnows hT hev)
  · have ht : t = t' := by
      have h1 := (Stage1Kyber.randTerm_inj hrndEq).1
      omega
    subst ht
    have hevEq : DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys =
        DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' := by
      have h0 : (T.at? (t + 5) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
          some ⟨.AliceDone a b ikA ikB spk pqpk opk ek ct keys⟩ := by
        rwa [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      have h1 : (T.at? (t + 5) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
          some ⟨.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys'⟩ := by
        rwa [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      have h2 := h0.symm.trans h1
      injection h2 with h2
      injection h2
    cases hevEq
    subst hpqEq
    exact hR'

theorem kemKnownFromTwin_of_aliceDone {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T)
    {t : Nat} {a b : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hev : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5)) :
    KemKnownFromTwin i S g T (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2 :=
  fun _ hR' hsh => kemSS_aliceDone_knows_of_shape_eq i S g hT hKem32 hev hR' hsh

theorem kemSS_encap_knows_of_ct_pk_attackerKnows {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T)
    {pk e₀ R' : DY.Bytes}
    (hctAk : (DY.PQKem.kemEncap pk e₀).1.AttackerKnows T) (hpkAk : pk.AttackerKnows T)
    (hR' : R'.AttackerKnows T)
    (hsh : (gamma' i S g R').shape = (gamma' i S g (DY.PQKem.kemEncap pk e₀).2).shape) :
    (DY.PQKem.kemEncap pk e₀).2.AttackerKnows T := by
  rcases kemEncap_fst_attackerKnows_inv hT hctAk with he₀Ak |
      ⟨t, a, b, ikA, ikB, spk, pqpk, opk, ek, ct', keys, hev, hpqEq, hrndEq⟩
  · exact DY.Bytes.AttackerKnows.prove DY.PQKem.kemEncapSS.attackerKnowledge _ T
      ⟨pk, e₀, (DY.PQKem.kemEncap pk e₀).1, (Prod.eta _).symm, hpkAk, he₀Ak⟩
  · rw [hpqEq, hrndEq] at hsh ⊢
    exact kemSS_aliceDone_knows_of_shape_eq i S g hT hKem32 hev hR' hsh

theorem kemSS_decap_knows_of_shape_eq {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T)
    {sQ ct ss R' : DY.Bytes}
    (hctAk : ct.AttackerKnows T) (hpqAk : (DY.PQKem.kemPk sQ).AttackerKnows T)
    (hdec : DY.PQKem.kemDecap sQ ct = some ss)
    (hR' : R'.AttackerKnows T)
    (hsh : (gamma' i S g R').shape = (gamma' i S g ss).shape) :
    ss.AttackerKnows T := by
  obtain ⟨e₀, hct, hss⟩ := Stage1Kyber.kemDecap_eq_some_iff.mp hdec
  subst hct
  subst hss
  exact kemSS_encap_knows_of_ct_pk_attackerKnows i S g hT hKem32 hctAk hpqAk hR' hsh

theorem kemKnownFromTwin_of_decap {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T)
    {sQ ct ss : DY.Bytes}
    (hctAk : ct.AttackerKnows T) (hpqAk : (DY.PQKem.kemPk sQ).AttackerKnows T)
    (hdec : DY.PQKem.kemDecap sQ ct = some ss) :
    KemKnownFromTwin i S g T ss :=
  fun _ hR' hsh => kemSS_decap_knows_of_shape_eq i S g hT hKem32 hctAk hpqAk hdec hR' hsh

unseal DY.Bytes in
private instance subKemRejOSP : DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private theorem shape_kemRejKey_osp (sk ct : DY.Bytes) :
    (gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape =
      DY.PQKem.kemRejKey (gamma' i S g sk).shape (gamma' i S g ct).shape := by
  unfold gamma'
  show ((({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq (concretizeKemRej S) (concretizeAll i S g)]
  rfl

unseal DY.Bytes in
private theorem kemRejKey_inj_osp {sk₁ ct₁ sk₂ ct₂ : DY.Bytes}
    (h : DY.PQKem.kemRejKey sk₁ ct₁ = DY.PQKem.kemRejKey sk₂ ct₂) : sk₁ = sk₂ ∧ ct₁ = ct₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.PQKem.RejKey.SubF) { sk := sk₁, cipher := ct₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.PQKem.RejKey.SubF) { sk := sk₂, cipher := ct₂ }
  change DY.Bytes.view? (DY.PQKem.kemRejKey sk₁ ct₁) _ = _ at h1
  change DY.Bytes.view? (DY.PQKem.kemRejKey sk₂ ct₂) _ = _ at h2
  rw [h, h2] at h1
  injection h1 with h1
  injection h1 with hs hc
  exact ⟨hs.symm, hc.symm⟩

unseal DY.Bytes in
private theorem shape_eq_kemRejKey_inv_osp {u sh_s sh_c : DY.Bytes}
    (hsh : (gamma' i S g u).shape = DY.PQKem.kemRejKey sh_s sh_c) :
    ∃ sk' ct' : DY.Bytes, u = DY.PQKem.kemRejKey sk' ct' ∧
      (gamma' i S g sk').shape = sh_s ∧ (gamma' i S g ct').shape = sh_c := by
  rcases Stage1Kyber.gamma'_shape_cases i S g u with
    ⟨w, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
    ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨⟨sk', ct'⟩, rfl, h⟩ | ⟨_, h⟩
  · rw [h] at hsh
    unfold DY.Libsignal.Composed.Refinement.litOf at hsh
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh)
  all_goals try (
    rw [h] at hsh
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh))
  rw [h] at hsh
  obtain ⟨hs, hc⟩ := kemRejKey_inj_osp hsh
  exact ⟨sk', ct', rfl, hs, hc⟩

theorem kemRejKey_knows_of_shape_eq {T : ExecTrace} (hreach : ReachableTrace T)
    {sQ ct R' : DY.Bytes} {t : Nat}
    (hsQ : sQ = randTerm t 64) (hct : ct.AttackerKnows T)
    (hR' : R'.AttackerKnows T)
    (hsh : (gamma' i S g R').shape = (gamma' i S g (DY.PQKem.kemRejKey sQ ct)).shape) :
    (DY.PQKem.kemRejKey sQ ct).AttackerKnows T := by
  subst hsQ
  rw [shape_kemRejKey_osp i S g, shape_randTerm_of_ne_zero i S g t 64 (by decide)] at hsh
  obtain ⟨sk', ct', rfl, hskSh, _⟩ := shape_eq_kemRejKey_inv_osp i S g hsh
  have hskEq : sk' = randTerm t 64 := (Stage1Kyber.shape_eq_randTerm_iff i S g sk' (by decide)).mp hskSh
  subst hskEq
  have hskAk : (randTerm t 64).AttackerKnows T := ((kemRejKey_attackerKnows_iff_of_reachable hreach _ _).mp hR').1
  exact (kemRejKey_attackerKnows_iff_of_reachable hreach _ _).mpr ⟨hskAk, hct⟩

omit i S g in
theorem kemKnownFromTwin_of_rejKey {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    {sQ ct : DY.Bytes} {t : Nat} (hsQ : sQ = randTerm t 64) (hct : ct.AttackerKnows T) :
    KemKnownFromTwin interp S g T (DY.PQKem.kemRejKey sQ ct) :=
  fun _ hR' hsh => kemRejKey_knows_of_shape_eq interp S g hreach hsQ hct hR' hsh

theorem kemKnownFromTwin_bobKemShare {T : ExecTrace} (hT : ReachableTrace T)
    (hKem32 : AliceKemLen32 i S g T)
    {sQ ct : DY.Bytes} {t : Nat}
    (hsQ : sQ = randTerm t 64)
    (hctAk : ct.AttackerKnows T) (hpqAk : (DY.PQKem.kemPk sQ).AttackerKnows T) :
    KemKnownFromTwin i S g T
      ((DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sQ ct)).getD
        (DY.PQKem.kemRejKey sQ ct)) := by
  rcases hdec : DY.PQKem.kemDecap sQ ct with _ | ss
  · simpa only [DY.Libsignal.PQXDH.errToOption, hdec, Option.getD_none] using
      kemKnownFromTwin_of_rejKey hT hsQ hctAk
  · simpa only [DY.Libsignal.PQXDH.errToOption, hdec, Option.getD_some] using
      kemKnownFromTwin_of_decap i S g hT hKem32 hctAk hpqAk hdec

/-- Known-peer-key PQXDH IKM holes together with `KemKnownFromTwin` on the KEM shared secret. -/
def IkmHolesKemK (T : ExecTrace) (ikm : DY.Bytes) : Prop :=
  ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
    ikm = pqxdhIkm a b e d ss ∧
    DhHoleK (·.AttackerKnows T) a ∧ DhHoleK (·.AttackerKnows T) b ∧
    DhHoleK (·.AttackerKnows T) e ∧
    (∀ x, d = some x → DhHoleK (·.AttackerKnows T) x) ∧
    KemKnownFromTwin i S g T ss

/-! ## One peel step -/

/-- `Q` is closed under the chain-key and root-key predecessors of the Double Ratchet KDFs. -/
structure SpineDown (Q : DY.Bytes → Prop) : Prop where
  ck1 : ∀ {ck : DY.Bytes}, Q (kdfCk ck).1 → Q ck
  ck2 : ∀ {ck : DY.Bytes}, Q (kdfCk ck).2 → Q ck
  rk1 : ∀ {rk d : DY.Bytes}, Q (kdfRk rk d).1 → Q rk
  rk2 : ∀ {rk d : DY.Bytes}, Q (kdfRk rk d).2 → Q rk

/-- Reachable-trace KDF provenance of an attacker-known twin of `kdfExtract s₁ i₁`. -/
theorem peel_outer {T : ExecTrace} (hT : ReachableTrace T) {u s₁ i₁ : DY.Bytes}
    (hu : u.AttackerKnows T)
    (hsh : (gamma' i S g u).shape = (gamma' i S g (KdfExtract.kdfExtract s₁ i₁)).shape) :
    ∃ s' i', u = KdfExtract.kdfExtract s' i' ∧
      (gamma' i S g s').shape = (gamma' i S g s₁).shape ∧
      (gamma' i S g i').shape = (gamma' i S g i₁).shape ∧
      ((HonestKdfOut T u ∨ SkippedSeedLogged T u) ∨
        (∃ b1, i' = Concat.concat b1 (Concat.concat pqxdhLabel (litByte 3))) ∨
        (s'.AttackerKnows T ∧ i'.AttackerKnows T)) := by
  obtain ⟨s', i', hs, hi, rfl⟩ := kdfExtract_shape_eq_inv_c i S g hsh
  refine ⟨s', i', rfl, hs, hi, ?_⟩
  rcases kdfInputValidProv_of_attackerKnows_reachable hT hu with
    h1 | ⟨_, j, ses, pk, n, rIdx, src, hev⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | h7
  · exact .inr (.inr h1)
  · exact .inl (.inr ⟨j, ses, pk, n, rIdx, src, hev⟩)
  · exact .inl (.inl h)
  · exact .inl (.inl h)
  · exact .inl (.inl h)
  · exact .inl (.inl h)
  · exact .inr (.inl h7)

/-- Inner `kdfRk` peel: an attacker-known twin of `hmac rk d` (`d` a known-peer-key DH hole) has an
attacker-known root-key twin, and `d` is attacker-known. -/
theorem peel_rk {T : ExecTrace} (hT : ReachableTrace T) {rk d s' : DY.Bytes}
    (hd : DhHoleK (·.AttackerKnows T) d) (hs' : s'.AttackerKnows T)
    (hsh : (gamma' i S g s').shape = (gamma' i S g (KdfExtract.kdfExtract rk d)).shape) :
    ∃ rk' d', s' = KdfExtract.kdfExtract rk' d' ∧
      (gamma' i S g rk').shape = (gamma' i S g rk).shape ∧
      rk'.AttackerKnows T ∧ d.AttackerKnows T := by
  obtain ⟨pk', t, rfl, hpk'⟩ := hd
  obtain ⟨rk', d', hrk, hd', rfl⟩ := kdfExtract_shape_eq_inv_c i S g hsh
  rcases kdfInputValidProv_of_attackerKnows_reachable hT hs' with
    ⟨hrk', hdk'⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl⟩
  · exact ⟨rk', d', rfl, hrk, hrk', hole_known i S g hT hpk' hdk' hd'⟩
  · exact absurd hd' (shape_literal_ne_dh i S g _ _ _)
  · exact absurd hd' (shape_literal_ne_dh i S g _ _ _)
  · exact absurd hd' (shape_concat_ne_dh i S g _ _ _ _)
  · exact absurd hd' (shape_concat_ne_dh i S g _ _ _ _)
  · exact absurd hd' (shape_concat_ne_dh i S g _ _ _ _)
  · exact absurd hd' (shape_concat_ne_dh i S g _ _ _ _)

/-- Inner PQXDH peel: an attacker-known twin of `hmac zeroSalt ikm` (`ikm` satisfying `IkmHolesKemK`)
forces `ikm` to be attacker-known. -/
theorem peel_ikm {T : ExecTrace} (hT : ReachableTrace T) {ikm s' : DY.Bytes}
    (hIK : IkmHolesKemK i S g T ikm) (hs' : s'.AttackerKnows T)
    (hsh : (gamma' i S g s').shape = (gamma' i S g (hmac zeroSalt ikm)).shape) :
    ikm.AttackerKnows T := by
  obtain ⟨a, b, e, d, ss, rfl, ⟨pa, ta, rfl, hpa⟩, ⟨pb, tb, rfl, hpb⟩, ⟨pe, te, rfl, hpe⟩, hd, hKem⟩ := hIK
  obtain ⟨z', ikm', -, hikm, rfl⟩ := kdfExtract_shape_eq_inv_c i S g hsh
  rcases kdfInputValidProv_of_attackerKnows_reachable hT hs' with
    ⟨-, hk'⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl⟩
  rotate_left
  · exact absurd hikm (shape_literal_ne_concat i S g _ _ _)
  · exact absurd hikm (shape_literal_ne_concat i S g _ _ _)
  · exact absurd (shape_concat_inj i S g hikm).1 (shape_lit_wr_ne_disc i S g)
  · exact absurd (shape_concat_inj i S g (shape_concat_inj i S g hikm).2).1
      (shape_literal_ne_dh i S g _ _ _)
  · exact absurd (shape_concat_inj i S g (shape_concat_inj i S g hikm).2).1
      (shape_literal_ne_dh i S g _ _ _)
  · exact absurd (shape_concat_inj i S g (shape_concat_inj i S g hikm).2).1
      (shape_literal_ne_dh i S g _ _ _)
  unfold pqxdhIkm at hikm ⊢
  obtain ⟨δ', r1, rfl, -, h1⟩ := concat_shape_eq_inv i S g hikm
  obtain ⟨a', r2, rfl, ha', h2⟩ := concat_shape_eq_inv i S g h1
  obtain ⟨b', r3, rfl, hb', h3⟩ := concat_shape_eq_inv i S g h2
  obtain ⟨e', R', rfl, he', hR⟩ := concat_shape_eq_inv i S g h3
  obtain ⟨-, hk1⟩ := ak_split hk'
  obtain ⟨haK', hk2⟩ := ak_split hk1
  obtain ⟨hbK', hk3⟩ := ak_split hk2
  obtain ⟨heK', hRK'⟩ := ak_split hk3
  have haK := hole_known i S g hT hpa haK' ha'
  have hbK := hole_known i S g hT hpb hbK' hb'
  have heK := hole_known i S g hT hpe heK' he'
  have hdisc : discontinuity.AttackerKnows T := ak_lit _
  cases d with
  | none =>
    exact ak_concat hdisc (ak_concat haK (ak_concat hbK (ak_concat heK (hKem R' hRK' hR))))
  | some x =>
    obtain ⟨x', ss', rfl, hx', hss'⟩ := concat_shape_eq_inv i S g hR
    obtain ⟨hxK', hssK'⟩ := ak_split hRK'
    obtain ⟨px, tx, rfl, hpx⟩ := hd _ rfl
    have hxK := hole_known i S g hT hpx hxK' hx'
    exact ak_concat hdisc (ak_concat haK (ak_concat hbK (ak_concat heK
      (ak_concat hxK (hKem ss' hssK' hss')))))

end Symbolic.Swarm.CREF.TR.G1.Spine
