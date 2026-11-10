/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
public import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonRep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Attacker Knowledge of Skipped Keys on Non-Honest Ratchet Keys

Defines `LitJunk` and the trace invariant `SInvTR`, and proves `skippedSeedKnownTR_of_sinv`: on a
trace satisfying `SInvTR`, any logged `SkippedKeyStored` event whose ratchet key satisfies `LitJunk`
has both its ratchet key and its skipped seed attacker-known.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet (SessionInfo hmac hkdfBlock2 litByte createChain kdfCk kdfRk
  chainKeyAt computeMac)
open Symbolic.Swarm.CREF.TR

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Non-honest ratchet keys -/

/-- The decoded key of `pk` is not equal to any honest `dhPk (randTerm i 32)`. -/
abbrev LitJunk (pk : DY.Bytes) : Prop := JunkTR pk

/-! ## Forged-MAC inversion -/

section LkkInjectivity
unseal DY.Bytes

theorem lkk_concat_inj {l₁ r₁ l₂ r₂ : DY.Bytes}
    (h : Concat.concat l₁ r₁ = Concat.concat l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l₁, rhs := r₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l₂, rhs := r₂ }
  change DY.Bytes.view? (Concat.concat l₁ r₁) _ = _ at h1
  change DY.Bytes.view? (Concat.concat l₂ r₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl⟩

theorem lkk_kdfExtract_inj {s₁ i₁ s₂ i₂ : DY.Bytes}
    (h : KdfExtract.kdfExtract s₁ i₁ = KdfExtract.kdfExtract s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₁, ikm := i₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₂, ikm := i₂ }
  change DY.Bytes.view? (KdfExtract.kdfExtract s₁ i₁) _ = _ at h1
  change DY.Bytes.view? (KdfExtract.kdfExtract s₂ i₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl⟩

theorem lkk_trWireMsg_pack_inj {w₁ w₂ : TrWire.TrWireMsg.SubF DY.Bytes}
    (h : w₁.pack = w₂.pack) : w₁ = w₂ := by
  have h1 : DY.Bytes.view? w₁.pack DY.TrWire.TrWireMsg.SubF = some w₁ := DY.BytesView.view_pack w₁
  have h2 : DY.Bytes.view? w₂.pack DY.TrWire.TrWireMsg.SubF = some w₂ := DY.BytesView.view_pack w₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

theorem lkk_concat_ne_literal (l r : DY.Bytes) (b : ByteArray) :
    Concat.concat l r ≠ Literal.literalToBytes b := by
  intro h; have h1 := DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l, rhs := r }
  change DY.Bytes.view? (Concat.concat l r) _ = _ at h1
  have h2 : DY.Bytes.view? (Literal.literalToBytes b) DY.Concat.Concat.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [h, h2] at h1; contradiction

theorem lkk_kdfExtract_ne_literal (s i : DY.Bytes) (b : ByteArray) :
    KdfExtract.kdfExtract s i ≠ Literal.literalToBytes b := by
  intro h
  have h1 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s, ikm := i }
  change DY.Bytes.view? (KdfExtract.kdfExtract s i) _ = _ at h1
  have h2 : DY.Bytes.view? (Literal.literalToBytes b) DY.KdfExtract.KdfExtract.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [h, h2] at h1; contradiction

theorem lkk_kdfExtract_ne_concat (s i l r : DY.Bytes) :
    KdfExtract.kdfExtract s i ≠ Concat.concat l r := by
  intro h
  have h1 := DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l, rhs := r }
  change DY.Bytes.view? (Concat.concat l r) _ = _ at h1
  have h2 : DY.Bytes.view? (KdfExtract.kdfExtract s i) DY.Concat.Concat.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [← h, h2] at h1; contradiction

theorem lkk_dhPk_view_variant (sk : DY.Bytes) :
    DY.Bytes.view? (DY.DiffieHellman.dhPk sk) DY.X25519.Variant.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem lkk_dhPk_inj {x y : DY.Bytes}
    (h : DY.DiffieHellman.dhPk x = DY.DiffieHellman.dhPk y) : x = y := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.DiffieHellman.DhPk.SubF) h
  dsimp only [DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk] at hv
  simp only [BytesView.view_pack, Option.some.injEq, DY.DiffieHellman.DhPk.SubF.mk.injEq] at hv
  exact hv

/-- `dh` is injective in both arguments unless the right-hand public key is `dhPk` of the
left-hand secret (the swap case). -/
theorem lkk_dh_eq {X Y s s' : DY.Bytes} (hX : X ≠ DY.DiffieHellman.dhPk s')
    (h : DiffieHellman.dh Y s' = DiffieHellman.dh X s) : Y = X ∧ s' = s := by
  have hv := congrArg (fun x : DY.Bytes => x.view? DY.DiffieHellman.Dh.SubF) h
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh] at hv
  rcases hx : X.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩ <;>
    rcases hy : Y.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a'⟩⟩
  · rw [hx] at hv; rw [hy] at hv
    simp only [BytesView.view_pack, Option.some.injEq, DY.DiffieHellman.Dh.SubF.mk.injEq] at hv
    exact hv
  · rw [hx] at hv; rw [hy] at hv; dsimp only at hv
    split at hv <;>
    · simp only [BytesView.view_pack, Option.some.injEq, DY.DiffieHellman.Dh.SubF.mk.injEq] at hv
      rw [← hv.1, BytesView.view_pack] at hx; cases hx
  · rw [hx] at hv; rw [hy] at hv; dsimp only at hv
    split at hv <;>
    · simp only [BytesView.view_pack, Option.some.injEq, DY.DiffieHellman.Dh.SubF.mk.injEq] at hv
      rw [hv.1, BytesView.view_pack] at hy; cases hy
  · have hXv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF X
    have hYv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF Y
    rw [hx] at hv hXv; rw [hy] at hv hYv; dsimp only at hv hXv hYv
    split at hv <;> split at hv <;>
    · simp only [BytesView.view_pack, Option.some.injEq, DY.DiffieHellman.Dh.SubF.mk.injEq] at hv
      obtain ⟨h1, h2⟩ := hv
      have e1 := lkk_dhPk_inj h1
      subst_vars
      first | exact ⟨rfl, rfl⟩ | exact (hX rfl).elim

end LkkInjectivity

/-- On a reachable trace, attacker knowledge of `(trMsgKeys pqSalt (kdfCk ck).2).macKey` implies
attacker knowledge of `(kdfCk ck).2`. -/
theorem seed_known_of_macKey_known_tr {T : ExecTrace} (hT : ReachableTrace T)
    {pqSalt ck : DY.Bytes}
    (hmk : ((trMsgKeys pqSalt (kdfCk ck).2).macKey).AttackerKnows T) :
    ((kdfCk ck).2).AttackerKnows T := by
  dsimp only [trMsgKeys, hkdfBlock2, hmac] at hmk
  rcases kdfInputValidTR_of_attackerKnows_reachable hT hmk with
    ⟨hprk, _⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
  · rcases kdfInputValidTR_of_attackerKnows_reachable hT hprk with
      ⟨_, hseed⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hseed
    · exact absurd h01 (lkk_kdfExtract_ne_literal _ _ _)
    · exact absurd h02 (lkk_kdfExtract_ne_literal _ _ _)
    · exact absurd hwr1 (lkk_kdfExtract_ne_concat _ _ _ _)
    · exact hwr2.ne_kdfExtract.elim
  · exact absurd h01 (lkk_concat_ne_literal _ _ _)
  · exact absurd h02 (lkk_concat_ne_literal _ _ _)
  · exact absurd (lkk_concat_inj hwr1).2 (lkk_concat_ne_literal _ _ _)
  · exact hwr2.ne_whisperMessageKeys.elim

/-- An accepted MAC on a reachable trace either arises from an honest `messageEncrypt` whose
ratchet key is `dhPk (randTerm t 32)`, or has an attacker-known MAC key. -/
theorem ratchetKey_honest_or_macKey_known_tr {T : ExecTrace} (hT : ReachableTrace T)
    {t pqSalt seed peerIk myIk : DY.Bytes} {msg : TRSignalMsg}
    (ht : t.AttackerKnows T) (hparse : parseTrSignalMsg t = some msg)
    (hmacEq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire) :
    (∃ ts : Nat, msg.ratchetKey = dhPk (randTerm ts 32)) ∨
      ((trMsgKeys pqSalt seed).macKey).AttackerKnows T := by
  obtain ⟨x₀, hsplit, _hx₀, hpack, hrk_eq, _hct_eq, _hpq_eq⟩ := parseTrSignalMsg_unpack hparse
  have hsp_ak := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) T ht
  rw [hsplit] at hsp_ak
  have hmac_ak : msg.mac.AttackerKnows T := hsp_ak.2
  rw [hmacEq] at hmac_ak; unfold computeMac at hmac_ak
  rcases truncInputValidTRStrong_of_attackerKnows_reachable hT hmac_ak with
    hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a, ns, pn, m, pqMsg, t_s, stH, me, st_s,
      hinp_eq, _, _, ha_eq, _, _, _, _⟩
  · right
    unfold hmac at hinp_ak
    rcases kdfInputValidTR_of_attackerKnows_reachable hT hinp_ak with
      ⟨hmk, _⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hmk
    · exact absurd h01 (lkk_concat_ne_literal _ _ _)
    · exact absurd h02 (lkk_concat_ne_literal _ _ _)
    · exact absurd (lkk_concat_inj hwr1).2 (lkk_concat_ne_literal _ _ _)
    · rw [hpack] at hwr2; exact hwr2.ne_trWireMsg.elim
  · left
    unfold hmac at hinp_eq
    have hconcat1 := (lkk_kdfExtract_inj hinp_eq).2
    have hwire_honest := (lkk_concat_inj (lkk_concat_inj hconcat1).2).2
    have hx₀_eq := lkk_trWireMsg_pack_inj (hpack.symm.trans hwire_honest)
    exact ⟨t_s, (hrk_eq.trans (congrArg TrWire.TrWireMsg.SubF.senderRatchetKey hx₀_eq)).trans
      (by rw [ha_eq])⟩

/-- An accepted MAC on a `LitJunk` ratchet key implies that the Double Ratchet seed is
attacker-known. -/
theorem seed_known_of_forgedMac_tr {T : ExecTrace} (hT : ReachableTrace T)
    {t pqSalt ck peerIk myIk : DY.Bytes} {msg : TRSignalMsg}
    (ht : t.AttackerKnows T) (hparse : parseTrSignalMsg t = some msg)
    (hmacEq : msg.mac =
      computeMac (trMsgKeys pqSalt (kdfCk ck).2).macKey peerIk myIk msg.wire)
    (hj : LitJunk msg.ratchetKey) :
    ((kdfCk ck).2).AttackerKnows T := by
  rcases ratchetKey_honest_or_macKey_known_tr hT ht hparse hmacEq with ⟨ts, hts⟩ | hmk
  · exact absurd (by rw [hts]; unfold normalizeX25519Key; rw [lkk_dhPk_view_variant]) (hj ts)
  · exact seed_known_of_macKey_known_tr hT hmk

/-- An accepted MAC on a `Variant`-headed ratchet key implies that the Double Ratchet seed is
attacker-known. -/
theorem seed_known_of_forgedMac_variant_tr {T : ExecTrace} (hT : ReachableTrace T)
    {t pqSalt ck peerIk myIk : DY.Bytes} {msg : TRSignalMsg} {x : DY.X25519.Variant.SubF DY.Bytes}
    (ht : t.AttackerKnows T) (hparse : parseTrSignalMsg t = some msg)
    (hmacEq : msg.mac =
      computeMac (trMsgKeys pqSalt (kdfCk ck).2).macKey peerIk myIk msg.wire)
    (hVar : msg.ratchetKey.view? DY.X25519.Variant.SubF = some x) :
    ((kdfCk ck).2).AttackerKnows T := by
  rcases ratchetKey_honest_or_macKey_known_tr hT ht hparse hmacEq with ⟨ts, hts⟩ | hmk
  · rw [hts, lkk_dhPk_view_variant] at hVar; cases hVar
  · exact seed_known_of_macKey_known_tr hT hmk

/-! ## Seed and chain-key knowledge inversions -/

/-- On a reachable trace, an attacker-known seed `(kdfCk ck).2` either comes from an
attacker-known `ck` or was logged as a skipped seed. -/
theorem seedKnownCasesTR {T : ExecTrace} (hT : ReachableTrace T) {ck : DY.Bytes}
    (h : ((kdfCk ck).2).AttackerKnows T) :
    ck.AttackerKnows T ∨ ∃ j ses pk n rIdx src,
      T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n (kdfCk ck).2 rIdx src) j := by
  dsimp only [kdfCk, hmac] at h
  rcases kdfInputValidTR_of_attackerKnows_reachable hT h with
    ⟨hck, _⟩ | ⟨_, hlog⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
  · exact .inl hck
  · exact .inr hlog
  · exact absurd (Symbolic.Swarm.COMPOSED.CompTermAlgebra.litByte_inj h02) (by decide)
  · exact absurd hwr1 (lkk_concat_ne_literal _ _ _).symm
  · exact hwr2.ne_literal.elim

/-- `x` is the sending or a receiving chain key of a state stored on `T`. -/
def StoredCkTR (T : ExecTrace) (x : DY.Bytes) : Prop :=
  ∃ p st i, TRStateStoredAt p st i T ∧ (st.cks = x ∨ ∃ c ∈ st.recv, c.chainKey = x)

/-- Statement that on a reachable trace, an attacker-known next chain key `(kdfCk ck).1` either
comes from an attacker-known `ck` or is stored in a `TRState`. -/
def CkKnownCasesTRP : Prop :=
  ∀ {T : ExecTrace}, ReachableTrace T → ∀ {ck : DY.Bytes}, ((kdfCk ck).1).AttackerKnows T →
    ck.AttackerKnows T ∨ StoredCkTR T (kdfCk ck).1

/-! ## Chain-base algebra -/

/-- A chain base for ratchet key `pk`: a fresh `randTerm`, a receiving-half-step chain key
`(createChain rk pk (randTerm t 32)).2`, or an `aliceStart` handshake chain base
`(aliceAgreement ikA (randTerm t 32) ikB pk pqpk opk e).2.ck`. -/
def ChainBaseTR (pk b : DY.Bytes) : Prop :=
  (∃ i n, b = randTerm i n) ∨
  (∃ rk t, b = (createChain rk pk (randTerm t 32)).2) ∨
  (∃ ikA ikB pqpk opk t e,
    b = (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB pk pqpk opk e).2.ck)

theorem lkk_chainBase_root {pk b : DY.Bytes} (hb : ChainBaseTR pk b) :
    Symbolic.Swarm.COMPOSED.CompRatchet.IsChainRoot b := by
  rcases hb with ⟨i, n, rfl⟩ | ⟨rk, t, rfl⟩ | ⟨ikA, ikB, pqpk, opk, t, e, rfl⟩
  · exact Symbolic.Swarm.COMPOSED.CompRatchet.isChainRoot_mkRand i n
  · exact Symbolic.Swarm.COMPOSED.CompRatchet.isChainRoot_createChain_snd rk pk (randTerm t 32)
  · exact Symbolic.Swarm.COMPOSED.CompRatchet.isChainRoot_pqxdhKdf_ck _

/-- `chainKeyAt` is injective in `(base, depth)` over chain bases. -/
theorem chainKeyAt_base_inj_tr {pk pk' b b' : DY.Bytes} {k k' : Nat}
    (hb : ChainBaseTR pk b) (hb' : ChainBaseTR pk' b')
    (h : chainKeyAt b' k' = chainKeyAt b k) : k' = k ∧ b' = b := by
  obtain ⟨hb_eq, hk_eq⟩ :=
    Symbolic.Swarm.COMPOSED.CompRatchet.chainKeyAt_root_inj (lkk_chainBase_root hb')
      (lkk_chainBase_root hb) h
  exact ⟨hk_eq, hb_eq⟩

/-- For a `LitJunk` ratchet key and `randTerm` secrets, the `dh` swap case cannot occur, so equal
`createChain` chain keys have equal inputs. -/
theorem createChain_snd_litJunk_tr {rk pk rk' pk' : DY.Bytes} {t t' : Nat} (hj : LitJunk pk)
    (h : (createChain rk' pk' (randTerm t' 32)).2 = (createChain rk pk (randTerm t 32)).2) :
    rk' = rk ∧ DY.X25519.normalizeX25519Key pk' = DY.X25519.normalizeX25519Key pk ∧
      randTerm t' 32 = randTerm t 32 := by
  dsimp only [createChain, DY.X25519.agree, kdfRk, hkdfBlock2, hmac] at h
  obtain ⟨hrk, hdh⟩ := lkk_kdfExtract_inj (lkk_kdfExtract_inj h).1
  obtain ⟨hX, hs⟩ := lkk_dh_eq (hj t') hdh
  exact ⟨hrk, hX, hs⟩

theorem aliceAgreement_ck_litJunk_tr {ikA ikB pk pqpk e ikA' ikB' pk' pqpk' e' : DY.Bytes}
    {opk opk' : Option DY.Bytes} {t t' : Nat} (hj : LitJunk pk)
    (h : (DY.Libsignal.PQXDH.aliceAgreement ikA' (randTerm t' 32) ikB' pk' pqpk' opk' e').2.ck =
         (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB pk pqpk opk e).2.ck) :
    DY.X25519.normalizeX25519Key pk' = DY.X25519.normalizeX25519Key pk ∧
      randTerm t' 32 = randTerm t 32 := by
  have hikm := Symbolic.Swarm.COMPOSED.CompTermAlgebra.pqxdhKdf_ck_inj h
  obtain ⟨_, _, hdh, _, _, _⟩ :=
    Symbolic.Swarm.COMPOSED.CompTermAlgebra.pqxdhIkm_inj_kem hikm
  exact lkk_dh_eq (hj t') hdh

/-! ## Trace invariant `SInvTR` -/

/-- If `pk` is `LitJunk`, then `pk` and the chain base `b` are attacker-known on `tr`. -/
def GoodTR (tr : ExecTrace) (pk b : DY.Bytes) : Prop :=
  LitJunk pk → pk.AttackerKnows tr ∧ b.AttackerKnows tr

/-- `ck` descends from a chain base `b` for `pk` with `GoodTR tr pk b`. -/
def ChainOKTR (tr : ExecTrace) (pk ck : DY.Bytes) : Prop :=
  ∃ b k, ck = chainKeyAt b k ∧ GoodTR tr pk b ∧ ChainBaseTR pk b

/-- The sending chain key descends from `randTerm`, or from a sending half-step
`(createChain rk pk st.dhs).2` whose root output is `st.rk`. -/
def CksOKTR (st : TRState) : Prop :=
  (∃ i n k, st.cks = chainKeyAt (randTerm i n) k) ∨
    ∃ rk pk k, st.cks = chainKeyAt (createChain rk pk st.dhs).2 k ∧
      st.rk = (createChain rk pk st.dhs).1

/-- Trace invariant tracking `ChainOKTR` and attacker knowledge for chains and skipped keys on
`LitJunk` ratchet keys. -/
structure SInvTR (tr : ExecTrace) : Prop where
  recv : ∀ p st i, TRStateStoredAt p st i tr → ∀ c ∈ st.recv,
    ChainOKTR tr c.ratchetKey c.chainKey ∨
    ∃ ikA ikB pqpk opk t e,
      c.chainKey = (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB c.ratchetKey pqpk opk e).2.ck
  skip : ∀ s pk n seed rIdx src j,
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) j →
    ∃ ck, seed = (kdfCk ck).2 ∧ ChainOKTR tr pk ck
  cks : ∀ p st i, TRStateStoredAt p st i tr → CksOKTR st

theorem GoodTR.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {pk b : DY.Bytes} (h : GoodTR tr pk b) :
    GoodTR tr' pk b := fun hj =>
  ⟨DY.Bytes.AttackerKnows_le _ tr tr' hle (h hj).1, DY.Bytes.AttackerKnows_le _ tr tr' hle (h hj).2⟩

theorem ChainOKTR.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {pk ck : DY.Bytes}
    (h : ChainOKTR tr pk ck) : ChainOKTR tr' pk ck := by
  obtain ⟨b, k, hck, hg, hb⟩ := h
  exact ⟨b, k, hck, hg.mono hle, hb⟩

theorem attackerKnows_chainKeyAt_tr {tr : ExecTrace} :
    ∀ (k : Nat) {ck : DY.Bytes}, ck.AttackerKnows tr → (chainKeyAt ck k).AttackerKnows tr
  | 0, _, hck => hck
  | k + 1, ck, hck =>
    attackerKnows_chainKeyAt_tr k (ck := (kdfCk ck).1)
      (KdfExtract.attacker_knows_kdfExtract ck (litByte 0x02) tr hck
        (Literal.attacker_knows_literalToBytes _ tr))

theorem ChainOKTR.known {tr : ExecTrace} {pk ck : DY.Bytes} (h : ChainOKTR tr pk ck)
    (hj : LitJunk pk) : pk.AttackerKnows tr ∧ ck.AttackerKnows tr := by
  obtain ⟨b, k, rfl, hg, _⟩ := h
  exact ⟨(hg hj).1, attackerKnows_chainKeyAt_tr k (hg hj).2⟩

/-! ## Skipped-seed knowledge from `SInvTR` -/

/-- Under `SInvTR`, a logged skipped seed on a `LitJunk` ratchet key is attacker-known, as is the
ratchet key. -/
theorem skippedSeedKnownTR_of_sinv {tr : ExecTrace} (hI : SInvTR tr)
    {evIdx : Nat} {ses : SessionInfo} {pk : DY.Bytes} {n : UInt32} {seed : DY.Bytes}
    {rIdx src : Nat}
    (hlog : tr.EventLoggedAt (TREvent.SkippedKeyStored ses pk n seed rIdx src) evIdx)
    (hj : LitJunk pk) :
    pk.AttackerKnows tr ∧ seed.AttackerKnows tr := by
  obtain ⟨ck, rfl, hok⟩ := hI.skip ses pk n seed rIdx src evIdx hlog
  obtain ⟨hpk, hck⟩ := hok.known hj
  exact ⟨hpk, KdfExtract.attacker_knows_kdfExtract ck (litByte 0x01) tr hck
    (Literal.attacker_knows_literalToBytes _ tr)⟩

end Symbolic.Swarm.CREF.TR.G1
