/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.SM.Theorem7Proof
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionProofDefs

/-!
# Receiver-chain and symmetric-ratchet invariants

**Checked by Lean.**

Defines `storedEpochs`, symmetric chain stepping (`chainKeyValAt`, `msgSeedAt`), skipped-key list
evolution (`pushSkipped`, `advanceKeys`), and the receiver-chain invariant `RcvChainInv` for
`libsignal_corr`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open CryptoGames.CKA
open CryptoGames.Ratchet
open CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim
open CryptoGames.SM
open CryptoGames.SM.Construction

namespace CryptoGames.LibsignalSM.Proofs.Correctness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Stored epochs -/

theorem Party.sendsIn_of_sub_mod_two {P : Party} {e t : ℕ} (hle : e ≤ t)
    (he : P.sendsIn e = false) :
    P.sendsIn t = decide ((t - e) % 2 = 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, t = e + d := ⟨t - e, by omega⟩
  clear hle
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero =>
    simp [he]
  | succ d ih =>
    rw [← Nat.add_assoc, Party.sendsIn_succ, ih]
    by_cases h : d % 2 = 1
    · have h' : (d + 1) % 2 ≠ 1 := by omega
      simp [h, h']
    · have h' : (d + 1) % 2 = 1 := by omega
      simp [h, h']

/-- The list of ghost epochs of stored receiver chains for party `P` at party epoch `t`. -/
def storedEpochs (P : Party) : ℕ → List ℕ
  | 0 => match P with | .A => [0] | .B => []
  | t + 1 =>
    if P.sendsIn (t + 1) then storedEpochs P t
    else
      let l := storedEpochs P t ++ [t + 1]
      l.drop (l.length - maxReceiverChains)

theorem storedEpochs_length_le (P : Party) (t : ℕ) :
    (storedEpochs P t).length ≤ maxReceiverChains := by
  induction t with
  | zero =>
    cases P <;> decide
  | succ t ih =>
    dsimp only [storedEpochs]
    split
    · exact ih
    · simp only [List.length_drop, List.length_append, List.length_singleton, maxReceiverChains]
      omega

theorem mem_storedEpochs_imp (P : Party) (t : ℕ) :
    ∀ e ∈ storedEpochs P t, e ≤ t ∧ P.sendsIn e = false := by
  induction t with
  | zero =>
    intro e he
    cases P
    · simp only [storedEpochs, List.mem_singleton] at he
      subst he; decide
    · simp [storedEpochs] at he
  | succ t ih =>
    intro e he
    dsimp only [storedEpochs] at he
    split at he
    · rcases ih e he with ⟨hle, hs⟩
      exact ⟨by omega, hs⟩
    · rename_i hns
      have he' := List.mem_of_mem_drop he
      rw [List.mem_append, List.mem_singleton] at he'
      rcases he' with he_old | rfl
      · rcases ih e he_old with ⟨hle, hs⟩
        exact ⟨by omega, hs⟩
      · exact ⟨Nat.le_refl _, Bool.eq_false_iff.mpr hns⟩

theorem pairwise_drop {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) (n : ℕ) :
    (l.drop n).Pairwise R :=
  h.sublist (List.drop_sublist n l)

theorem storedEpochs_pairwise_lt (P : Party) (t : ℕ) :
    (storedEpochs P t).Pairwise (· < ·) := by
  induction t with
  | zero =>
    cases P <;> simp [storedEpochs]
  | succ t ih =>
    dsimp only [storedEpochs]
    split
    · exact ih
    · apply pairwise_drop
      rw [List.pairwise_append]
      refine ⟨ih, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      have hle := (mem_storedEpochs_imp P t a ha).1
      omega

theorem storedEpochs_getElem?_from_end (P : Party) (t : ℕ) :
    ∀ e ≤ t, P.sendsIn e = false → (t - e) / 2 < maxReceiverChains →
      (t - e) / 2 < (storedEpochs P t).length ∧
      (storedEpochs P t)[(storedEpochs P t).length - 1 - (t - e) / 2]? = some e := by
  induction t with
  | zero =>
    intro e hle hs hlt
    have he0 : e = 0 := by omega
    subst he0
    cases P
    · decide
    · simp [Party.sendsIn] at hs
  | succ t ih =>
    intro e hle hs hlt
    by_cases het : e = t + 1
    · subst het
      simp only [Nat.sub_self, Nat.zero_div, Nat.sub_zero]
      dsimp only [storedEpochs]
      simp only [hs, Bool.false_eq_true, ↓reduceIte, List.length_drop, List.length_append,
        List.length_singleton, List.getElem?_drop]
      have hlen_le := storedEpochs_length_le P t
      have hpos : 0 < (storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) := by
        dsimp only [maxReceiverChains] at hlen_le ⊢; omega
      have hidx : (storedEpochs P t).length + 1 - maxReceiverChains +
          ((storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) - 1) =
          (storedEpochs P t).length := by
        dsimp only [maxReceiverChains] at hlen_le ⊢; omega
      refine ⟨hpos, ?_⟩
      rw [hidx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    · have het_le : e ≤ t := by omega
      have hpar := Party.sendsIn_of_sub_mod_two (Nat.le_of_lt (by omega : e < t + 1)) hs
      dsimp only [storedEpochs]
      by_cases hst1 : P.sendsIn (t + 1) = true
      · simp only [hst1, ↓reduceIte]
        rw [hst1, eq_comm, decide_eq_true_eq] at hpar
        have hdiv : (t + 1 - e) / 2 = (t - e) / 2 := by omega
        rw [hdiv] at hlt ⊢
        exact ih e het_le hs hlt
      · have hst1' : P.sendsIn (t + 1) = false := Bool.eq_false_iff.mpr hst1
        simp only [hst1', Bool.false_eq_true, ↓reduceIte, List.length_drop, List.length_append,
          List.length_singleton, List.getElem?_drop]
        rw [hst1', eq_comm, decide_eq_false_iff_not] at hpar
        have hdiv : (t + 1 - e) / 2 = (t - e) / 2 + 1 := by omega
        have hlt_prev : (t - e) / 2 < maxReceiverChains := by omega
        rcases ih e het_le hs hlt_prev with ⟨hlen_prev, hget_prev⟩
        have hlen_le := storedEpochs_length_le P t
        have hlen_new : (t + 1 - e) / 2 <
            (storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) := by
          dsimp only [maxReceiverChains] at hlt hlen_prev hlen_le ⊢; omega
        have hidx : (storedEpochs P t).length + 1 - maxReceiverChains +
            ((storedEpochs P t).length + 1 - ((storedEpochs P t).length + 1 - maxReceiverChains) - 1 -
              (t + 1 - e) / 2) =
            (storedEpochs P t).length - 1 - (t - e) / 2 := by
          dsimp only [maxReceiverChains] at hlt hlen_prev hlen_le ⊢; omega
        have hlt_old : (storedEpochs P t).length - 1 - (t - e) / 2 < (storedEpochs P t).length := by
          omega
        refine ⟨hlen_new, ?_⟩
        rw [hidx, List.getElem?_append_left hlt_old]
        exact hget_prev

theorem mem_storedEpochs_of_lt_add_ten {P : Party} {e t : ℕ}
    (hle : e ≤ t) (hs : P.sendsIn e = false) (hlt : t < e + 10) :
    e ∈ storedEpochs P t := by
  have hdiv : (t - e) / 2 < maxReceiverChains := by
    dsimp only [maxReceiverChains]; omega
  rcases storedEpochs_getElem?_from_end P t e hle hs hdiv with ⟨_, hget⟩
  exact List.mem_of_getElem? hget

/-! ## Symmetric chain stepping -/

def chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) : ℕ → BitVec 256
  | 0 => ck0
  | n + 1 => HKDF.bytesToKey32 (Ratchet.chainHmac F (chainKeyValAt F ck0 n) Ratchet.chainKeySeed)

def msgSeedAt (F : ShaCompress) (ck0 : BitVec 256) (n : ℕ) : List (BitVec 8) :=
  Ratchet.chainHmac F (chainKeyValAt F ck0 n) Ratchet.messageKeySeed

theorem bitVec32_ofNat_ne_allOnes {n : ℕ} (hn : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 n ≠ BitVec.allOnes 32 := by
  intro h
  have hval := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, BitVec.toNat_allOnes] at hval
  omega

theorem bitVec32_ofNat_add_one (n : ℕ) :
    BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  simp [BitVec.ofNat_add]

theorem nextChainKey_chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) {n : ℕ}
    (hn : n + 1 < 2 ^ 32) :
    (LibsignalSession.ChainKey.mk (chainKeyValAt F ck0 n) (BitVec.ofNat 32 n)).nextChainKey F =
      Except.ok ⟨chainKeyValAt F ck0 (n + 1), BitVec.ofNat 32 (n + 1)⟩ := by
  dsimp only [LibsignalSession.ChainKey.nextChainKey]
  have hne := bitVec32_ofNat_ne_allOnes hn
  simp only [hne, ↓reduceIte, bitVec32_ofNat_add_one n]
  rfl

theorem nextChainKey_eq_ok_iff (F : ShaCompress) (ck ck' : LibsignalSession.ChainKey) :
    ck.nextChainKey F = Except.ok ck' ↔
      ck.index.toNat + 1 < 2 ^ 32 ∧
      ck' = ⟨HKDF.bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩ := by
  dsimp only [LibsignalSession.ChainKey.nextChainKey]
  have hall : (BitVec.allOnes 32).toNat = 2 ^ 32 - 1 := rfl
  by_cases h : ck.index = BitVec.allOnes 32
  · have hnat : ck.index.toNat = 2 ^ 32 - 1 := by rw [h, hall]
    simp only [h, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    intro hlt
    omega
  · have hlt : ck.index.toNat + 1 < 2 ^ 32 := by
      have hbound := ck.index.isLt
      have hne : ck.index.toNat ≠ 2 ^ 32 - 1 := by
        intro heq
        apply h
        apply BitVec.eq_of_toNat_eq
        rw [heq, hall]
      omega
    simp only [h, ↓reduceIte, Except.ok.injEq, hlt, true_and, eq_comm]

theorem messageKeys_chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) (n : ℕ) :
    (LibsignalSession.ChainKey.mk (chainKeyValAt F ck0 n) (BitVec.ofNat 32 n)).messageKeys F =
      ⟨msgSeedAt F ck0 n, BitVec.ofNat 32 n⟩ := rfl

/-! ## Skipped-key list -/

def pushSkipped (key : MessageKeyGenerator) (keys : List MessageKeyGenerator) :
    List MessageKeyGenerator :=
  let keys' := key :: keys
  if maxMessageKeys < keys'.length then keys'.dropLast else keys'

theorem mem_or_eq_getElem?_last_of_mem {α : Type} :
    ∀ {L : List α} {x : α}, x ∈ L →
      x ∈ L.dropLast ∨ L[L.length - 1]? = some x
  | [], _, hx => by simp at hx
  | [a], x, hx => by
    simp only [List.mem_singleton] at hx
    exact Or.inr (by simp [hx])
  | a :: b :: tl, x, hx => by
    simp only [List.dropLast, List.mem_cons] at hx ⊢
    rcases hx with rfl | hmem
    · exact Or.inl (Or.inl rfl)
    · rcases mem_or_eq_getElem?_last_of_mem (L := b :: tl) (List.mem_cons.mpr hmem) with hdl | hlast
      · exact Or.inl (Or.inr hdl)
      · exact Or.inr (by simpa using hlast)

theorem pairwise_gt_getElem_add_le :
    ∀ {ns : List ℕ}, ns.Pairwise (· > ·) →
      ∀ (idx : ℕ) (h : idx < ns.length),
        ns[idx] + idx ≤ ns[0]'(by omega)
  | [], _, _, h => by simp at h
  | [a], _, idx, h => by
    have h0 : idx = 0 := by simpa using h
    subst h0; simp
  | a :: b :: tl, hpw, 0, _ => by simp
  | a :: b :: tl, hpw, idx + 1, h => by
    rw [List.pairwise_cons] at hpw
    have hab : b < a := hpw.1 b List.mem_cons_self
    have hih := pairwise_gt_getElem_add_le hpw.2 idx (by simpa using h)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hih ⊢
    omega

theorem pushSkipped_subset (key : MessageKeyGenerator) (keys : List MessageKeyGenerator) :
    ∀ mk ∈ pushSkipped key keys, mk = key ∨ mk ∈ keys := by
  intro mk hmk
  dsimp only [pushSkipped] at hmk
  split at hmk
  · exact List.mem_cons.mp (List.dropLast_subset _ hmk)
  · exact List.mem_cons.mp hmk

theorem pushSkipped_pairwise_gt {key : MessageKeyGenerator} {keys : List MessageKeyGenerator}
    (hpw : (keys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·))
    (hgt : ∀ mk ∈ keys, mk.counter.toNat < key.counter.toNat) :
    ((pushSkipped key keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·) := by
  have hcons : ((key :: keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·) := by
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, hpw⟩
    rintro _ ⟨mk, hmk, rfl⟩
    exact hgt mk hmk
  dsimp only [pushSkipped]
  split
  · exact hcons.sublist (List.Sublist.map _ (List.dropLast_sublist _))
  · exact hcons

theorem mem_pushSkipped_head (key : MessageKeyGenerator) (keys : List MessageKeyGenerator) :
    key ∈ pushSkipped key keys := by
  dsimp only [pushSkipped]
  split
  · cases keys with
    | nil =>
      rename_i hlt
      simp [maxMessageKeys] at hlt
    | cons b tl =>
      simp [List.dropLast]
  · exact List.mem_cons_self

theorem mem_pushSkipped_or_dropped {key : MessageKeyGenerator} {keys : List MessageKeyGenerator}
    (hpw : (keys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·))
    (hgt : ∀ mk ∈ keys, mk.counter.toNat < key.counter.toNat)
    {mk : MessageKeyGenerator} (hmk : mk ∈ keys) :
    mk ∈ pushSkipped key keys ∨ mk.counter.toNat + maxMessageKeys ≤ key.counter.toNat := by
  have hcons : ((key :: keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·) := by
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, hpw⟩
    rintro _ ⟨m, hm, rfl⟩
    exact hgt m hm
  dsimp only [pushSkipped]
  split
  · rename_i hlen
    rcases mem_or_eq_getElem?_last_of_mem (List.mem_cons_of_mem key hmk) with hdl | hlast
    · exact Or.inl hdl
    · right
      have hidx : (key :: keys).length - 1 < ((key :: keys).map (fun m => m.counter.toNat)).length := by
        simp
      have hle := pairwise_gt_getElem_add_le hcons ((key :: keys).length - 1) hidx
      have hidx' : (key :: keys).length - 1 < (key :: keys).length := by simp
      rw [List.getElem?_eq_getElem hidx', Option.some.injEq] at hlast
      simp only [List.getElem_map, List.length_cons, Nat.add_sub_cancel,
        List.getElem_cons_zero] at hle hlast hlen
      rw [hlast] at hle
      omega
  · exact Or.inl (List.mem_cons_of_mem key hmk)

def advanceKeys (F : ShaCompress) (ck0 : BitVec 256) :
    ℕ → ℕ → List MessageKeyGenerator → List MessageKeyGenerator
  | 0, _, keys => keys
  | fuel + 1, p, keys =>
    advanceKeys F ck0 fuel (p + 1)
      (pushSkipped ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩ keys)

theorem advanceKeys_wf_and_desc (F : ShaCompress) (ck0 : BitVec 256) :
    ∀ (fuel p : ℕ) (keys : List MessageKeyGenerator),
      p + fuel < 2 ^ 32 →
      (∀ mk ∈ keys,
        mk.counter.toNat < p ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩) →
      (keys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·) →
      (∀ mk ∈ advanceKeys F ck0 fuel p keys,
        mk.counter.toNat < p + fuel ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩) ∧
      ((advanceKeys F ck0 fuel p keys).map (fun mk => mk.counter.toNat)).Pairwise (· > ·)
  | 0, p, keys, _, hwf, hpw => by
    simp only [advanceKeys, Nat.add_zero]
    exact ⟨hwf, hpw⟩
  | fuel + 1, p, keys, hlt, hwf, hpw => by
    dsimp only [advanceKeys]
    set key : MessageKeyGenerator := ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩
    have hp_lt : p < 2 ^ 32 := by omega
    have hkey_toNat : key.counter.toNat = p := by
      dsimp only [key]
      exact Nat.mod_eq_of_lt hp_lt
    have hgt : ∀ mk ∈ keys, mk.counter.toNat < key.counter.toNat := by
      intro mk hmk
      rw [hkey_toNat]
      exact (hwf mk hmk).1
    have hwf' : ∀ mk ∈ pushSkipped key keys,
        mk.counter.toNat < p + 1 ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩ := by
      intro mk hmk
      rcases pushSkipped_subset key keys mk hmk with rfl | hmem
      · rw [hkey_toNat]
        exact ⟨by omega, rfl⟩
      · rcases hwf mk hmem with ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    have hpw' := pushSkipped_pairwise_gt hpw hgt
    have hih := advanceKeys_wf_and_desc F ck0 fuel (p + 1) (pushSkipped key keys)
      (by omega) hwf' hpw'
    have hadd : p + 1 + fuel = p + (fuel + 1) := by omega
    rw [hadd] at hih
    exact hih

theorem advanceKeys_avail (F : ShaCompress) (ck0 : BitVec 256) :
    ∀ (fuel p : ℕ) (keys : List MessageKeyGenerator) (i : ℕ),
      p + fuel < 2 ^ 32 →
      1 ≤ i → i ≤ p + fuel →
      (∀ mk ∈ keys,
        mk.counter.toNat < p ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩) →
      (keys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·) →
      (p < i ∨ i + maxMessageKeys ≤ p ∨
        ⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ ∈ keys) →
      i + maxMessageKeys ≤ p + fuel ∨
        ⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ ∈ advanceKeys F ck0 fuel p keys
  | 0, p, keys, i, _, _, hile, _, _, hav => by
    simp only [advanceKeys, Nat.add_zero] at hile ⊢
    rcases hav with hgt | hdrop | hmem
    · omega
    · exact Or.inl hdrop
    · exact Or.inr hmem
  | fuel + 1, p, keys, i, hlt, hi1, hile, hwf, hpw, hav => by
    dsimp only [advanceKeys]
    set key : MessageKeyGenerator := ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩
    have hp_lt : p < 2 ^ 32 := by omega
    have hkey_toNat : key.counter.toNat = p := Nat.mod_eq_of_lt hp_lt
    have hgt : ∀ mk ∈ keys, mk.counter.toNat < key.counter.toNat := by
      intro mk hmk; rw [hkey_toNat]; exact (hwf mk hmk).1
    have hwf' : ∀ mk ∈ pushSkipped key keys,
        mk.counter.toNat < p + 1 ∧
        mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩ := by
      intro mk hmk
      rcases pushSkipped_subset key keys mk hmk with rfl | hmem
      · rw [hkey_toNat]; exact ⟨by omega, rfl⟩
      · rcases hwf mk hmem with ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    have hpw' := pushSkipped_pairwise_gt hpw hgt
    have hav' : p + 1 < i ∨ i + maxMessageKeys ≤ p + 1 ∨
        ⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ ∈ pushSkipped key keys := by
      rcases hav with hgt_i | hdrop | hmem
      · by_cases hieq : i = p + 1
        · subst hieq
          right; right
          simpa [key] using mem_pushSkipped_head key keys
        · left; omega
      · right; left; omega
      · rcases mem_pushSkipped_or_dropped hpw hgt hmem with hmem' | hdropped
        · right; right; exact hmem'
        · right; left
          have hi_lt : i - 1 < 2 ^ 32 := by omega
          have hcnt : (⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ : MessageKeyGenerator).counter.toNat =
              i - 1 := Nat.mod_eq_of_lt hi_lt
          rw [hcnt, hkey_toNat] at hdropped
          omega
    have hadd : p + 1 + fuel = p + (fuel + 1) := by omega
    have hih := advanceKeys_avail F ck0 fuel (p + 1) (pushSkipped key keys) i
      (by omega) hi1 (by omega) hwf' hpw' hav'
    rw [hadd] at hih
    exact hih

/-! ## Receiver-chain invariant -/

/-- Invariant on a stored `ReceiverChain` for an epoch with initial chain key `ck0` and maximum
accepted 1-based index `maxAcc`. -/
structure RcvChainInv (F : ShaCompress) (ck0 : BitVec 256) (maxAcc : ℕ)
    (c : ReceiverChain) : Prop where
  maxAcc_lt : maxAcc < 2 ^ 32
  ck_eq : c.chainKey = some ⟨chainKeyValAt F ck0 maxAcc, BitVec.ofNat 32 maxAcc⟩
  keys_wf : ∀ mk ∈ c.messageKeys,
    mk.counter.toNat < maxAcc ∧
    mk = ⟨msgSeedAt F ck0 mk.counter.toNat, BitVec.ofNat 32 mk.counter.toNat⟩
  keys_desc : (c.messageKeys.map (fun mk => mk.counter.toNat)).Pairwise (· > ·)

/-- 1-based index `i` is available (or was evicted due to `maxMessageKeys` cap with
`i + maxMessageKeys < maxAcc`) in receiver chain `c`. -/
def IndexAvailableL (F : ShaCompress) (ck0 : BitVec 256) (maxAcc : ℕ)
    (c : ReceiverChain) (i : ℕ) : Prop :=
  maxAcc < i ∨
    i + maxMessageKeys < maxAcc ∨
    ⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ ∈ c.messageKeys

theorem rcvChainInv_init (F : ShaCompress) (ck0 : BitVec 256) (their : PublicKey) :
    RcvChainInv F ck0 0 ⟨their, some ⟨ck0, 0⟩, []⟩ := by
  refine ⟨by decide, rfl, fun mk hmk => by simp at hmk, by simp⟩

theorem indexAvailableL_init (F : ShaCompress) (ck0 : BitVec 256) (their : PublicKey)
    {i : ℕ} (hi : 1 ≤ i) :
    IndexAvailableL F ck0 0 ⟨their, some ⟨ck0, 0⟩, []⟩ i :=
  Or.inl (by omega)

def updateChainAt (s : RatchetState) (idx : ℕ) (c' : ReceiverChain) : RatchetState :=
  { s with receiverChains := s.receiverChains.set idx c' }

theorem list_set_getElem?_self {α : Type} :
    ∀ {l : List α} {idx : ℕ} {x : α},
      l[idx]? = some x → l.set idx x = l
  | [], _, _, h => by simp at h
  | a :: tl, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; rfl
  | a :: tl, idx + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [list_set_getElem?_self h]

theorem updateChainAt_self {s : RatchetState} {idx : ℕ} {c : ReceiverChain}
    (hget : s.receiverChains[idx]? = some c) :
    updateChainAt s idx c = s := by
  dsimp only [updateChainAt]
  rw [list_set_getElem?_self hget]

theorem updateChainAt_updateChainAt (s : RatchetState) (idx : ℕ) (c₁ c₂ : ReceiverChain) :
    updateChainAt (updateChainAt s idx c₁) idx c₂ = updateChainAt s idx c₂ := by
  dsimp only [updateChainAt]
  rw [List.set_set]

theorem findIdx?_senderRatchetKey_set :
    ∀ (l : List ReceiverChain) (idx : ℕ) (c c' : ReceiverChain) (their : PublicKey),
      l[idx]? = some c → c'.senderRatchetKey = c.senderRatchetKey →
      (l.set idx c').findIdx? (fun d => d.senderRatchetKey == their) =
        l.findIdx? (fun d => d.senderRatchetKey == their)
  | [], _, _, _, _, hget, _ => by simp at hget
  | d :: tl, 0, c, c', their, hget, hrk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    simp [List.findIdx?_cons, hrk]
  | d :: tl, idx + 1, c, c', their, hget, hrk => by
    simp only [List.getElem?_cons_succ] at hget
    simp [List.findIdx?_cons, findIdx?_senderRatchetKey_set tl idx c c' their hget hrk]

theorem findReceiverChainIndex_updateChainAt {s : RatchetState} {idx : ℕ}
    {c c' : ReceiverChain} (their : PublicKey)
    (hget : s.receiverChains[idx]? = some c)
    (hrk : c'.senderRatchetKey = c.senderRatchetKey) :
    (updateChainAt s idx c').findReceiverChainIndex their = s.findReceiverChainIndex their :=
  findIdx?_senderRatchetKey_set s.receiverChains idx c c' their hget hrk

theorem getElem?_updateChainAt_self {s : RatchetState} {idx : ℕ} {c : ReceiverChain}
    (hget : s.receiverChains[idx]? = some c) (c' : ReceiverChain) :
    (updateChainAt s idx c').receiverChains[idx]? = some c' := by
  have hlt : idx < s.receiverChains.length := (List.getElem?_eq_some_iff.mp hget).1
  exact List.getElem?_set_self hlt

theorem findIdx?_eq_some_getElem? {α : Type} :
    ∀ {l : List α} {p : α → Bool} {pos : ℕ},
      l.findIdx? p = some pos → ∃ x, l[pos]? = some x ∧ p x = true
  | [], _, _, h => by simp at h
  | a :: tl, p, pos, h => by
    simp only [List.findIdx?_cons] at h
    by_cases hpa : p a = true
    · simp only [hpa, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨a, rfl, hpa⟩
    · have hpa' : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpa', Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨pos', hfind, rfl⟩
      rcases findIdx?_eq_some_getElem? hfind with ⟨x, hget, hpx⟩
      exact ⟨x, hget, hpx⟩

theorem exists_findIdx?_of_mem {α : Type} :
    ∀ {l : List α} {p : α → Bool} {y : α},
      y ∈ l → p y = true →
      ∃ pos x, l.findIdx? p = some pos ∧ l[pos]? = some x ∧ p x = true
  | [], _, _, hy, _ => by simp at hy
  | a :: tl, p, y, hy, hpy => by
    simp only [List.findIdx?_cons]
    by_cases hpa : p a = true
    · exact ⟨0, a, by simp [hpa], rfl, hpa⟩
    · have hpa' : p a = false := Bool.eq_false_iff.mpr hpa
      rcases List.mem_cons.mp hy with rfl | hmem
      · rw [hpy] at hpa'; contradiction
      · rcases exists_findIdx?_of_mem hmem hpy with ⟨pos, x, hfind, hget, hpx⟩
        exact ⟨pos + 1, x, by simp [hpa', hfind], hget, hpx⟩

theorem mem_eraseIdx_of_getElem?_of_ne {α : Type} :
    ∀ {l : List α} {pos : ℕ} {x y : α},
      l[pos]? = some x → y ≠ x → y ∈ l → y ∈ l.eraseIdx pos
  | [], _, _, _, hget, _, _ => by simp at hget
  | a :: tl, 0, x, y, hget, hne, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact absurd rfl hne
    · exact hmem
  | a :: tl, pos + 1, x, y, hget, hne, hy => by
    simp only [List.getElem?_cons_succ] at hget
    simp only [List.eraseIdx_cons_succ, List.mem_cons]
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (mem_eraseIdx_of_getElem?_of_ne hget hne hmem)

theorem Mut.exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match (Mut.exec m s).1 with
      | Except.ok a => Mut.exec (f a) (Mut.exec m s).2
      | Except.error e => (Except.error e, (Mut.exec m s).2) := by
  dsimp only [Mut.exec, bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, StateT.run]
  rcases m s with ⟨r, s'⟩
  cases r <;> rfl

theorem Mut.exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (Except.ok s, s) := rfl

theorem Mut.exec_set {σ : Type} (s s' : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (Except.ok (), s') := rfl

theorem Mut.exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (Except.ok a, s) := rfl

theorem Mut.exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (Except.error e, s) := rfl

theorem Mut.exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

theorem storeSkippedKey_exec {s : RatchetState} {their : PublicKey} {idx : ℕ} {c : ReceiverChain}
    (hfind : s.findReceiverChainIndex their = some idx)
    (hget : s.receiverChains[idx]? = some c) (key : MessageKeyGenerator) :
    Mut.exec (RatchetState.storeSkippedKey their key) s =
      (Except.ok (), updateChainAt s idx { c with messageKeys := pushSkipped key c.messageKeys }) := by
  unfold RatchetState.storeSkippedKey
  rw [Mut.exec_bind, Mut.exec_get]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hget]
  rfl

theorem setReceiverChainKey_exec {s : RatchetState} {their : PublicKey} {idx : ℕ} {c : ReceiverChain}
    (hfind : s.findReceiverChainIndex their = some idx)
    (hget : s.receiverChains[idx]? = some c) (ck : LibsignalSession.ChainKey) :
    Mut.exec (RatchetState.setReceiverChainKey their ck) s =
      (Except.ok (), updateChainAt s idx { c with chainKey := some ck }) := by
  unfold RatchetState.setReceiverChainKey
  rw [Mut.exec_bind, Mut.exec_get]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hget]
  rfl

theorem advanceChain_exec (F : ShaCompress) (ck0 : BitVec 256) (their : PublicKey)
    (counter : BitVec 32) :
    ∀ (fuel p : ℕ) (s : RatchetState) (idx : ℕ) (c : ReceiverChain),
      p + fuel = counter.toNat →
      s.findReceiverChainIndex their = some idx →
      s.receiverChains[idx]? = some c →
      Mut.exec
        (RatchetState.advanceChain F their counter fuel
          ⟨chainKeyValAt F ck0 p, BitVec.ofNat 32 p⟩) s =
        (Except.ok ⟨chainKeyValAt F ck0 (p + fuel), BitVec.ofNat 32 (p + fuel)⟩,
          updateChainAt s idx { c with messageKeys := advanceKeys F ck0 fuel p c.messageKeys })
  | 0, p, s, idx, c, _, _, hget => by
    dsimp only [RatchetState.advanceChain, advanceKeys, Nat.add_zero]
    rw [updateChainAt_self hget]
    rfl
  | fuel + 1, p, s, idx, c, hsum, hfind, hget => by
    have hcnt_lt : counter.toNat < 2 ^ 32 := counter.isLt
    have hp_lt_cnt : p < counter.toNat := by omega
    have hp1_lt : p + 1 < 2 ^ 32 := by omega
    have hbv_lt : BitVec.ofNat 32 p < counter := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hp_lt_cnt
    have hstore := storeSkippedKey_exec hfind hget ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩
    have hnext := nextChainKey_chainKeyValAt F ck0 hp1_lt
    set c₁ : ReceiverChain :=
      { c with messageKeys := pushSkipped ⟨msgSeedAt F ck0 p, BitVec.ofNat 32 p⟩ c.messageKeys }
    set s₁ := updateChainAt s idx c₁
    have hfind₁ : s₁.findReceiverChainIndex their = some idx := by
      have hrk : c₁.senderRatchetKey = c.senderRatchetKey := rfl
      rw [findReceiverChainIndex_updateChainAt their hget hrk, hfind]
    have hget₁ : s₁.receiverChains[idx]? = some c₁ := getElem?_updateChainAt_self hget c₁
    have hih := advanceChain_exec F ck0 their counter fuel (p + 1) s₁ idx c₁
      (by omega) hfind₁ hget₁
    dsimp only [RatchetState.advanceChain, advanceKeys]
    simp only [hbv_lt, ↓reduceIte]
    rw [Mut.exec_bind, messageKeys_chainKeyValAt, hstore]
    dsimp only
    rw [Mut.exec_bind, Mut.exec_liftE, hnext]
    dsimp only
    rw [hih, updateChainAt_updateChainAt]
    have hadd : p + 1 + fuel = p + (fuel + 1) := by omega
    rw [hadd]

theorem takeSkippedKey_exec_some {s : RatchetState} {their : PublicKey} {idx : ℕ}
    {c : ReceiverChain} {counter : BitVec 32} {pos : ℕ} {key : MessageKeyGenerator}
    (hfind : s.findReceiverChainIndex their = some idx)
    (hget : s.receiverChains[idx]? = some c)
    (hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) = some pos)
    (hkey : c.messageKeys[pos]? = some key) :
    Mut.exec (RatchetState.takeSkippedKey their counter) s =
      (Except.ok (some key),
        updateChainAt s idx { c with messageKeys := c.messageKeys.eraseIdx pos }) := by
  unfold RatchetState.takeSkippedKey
  rw [Mut.exec_bind, Mut.exec_get]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hget]
  dsimp only
  rw [hpos]
  dsimp only
  rw [hkey]
  rfl

theorem takeSkippedKey_exec_none {s : RatchetState} {their : PublicKey} {idx : ℕ}
    {c : ReceiverChain} {counter : BitVec 32}
    (hfind : s.findReceiverChainIndex their = some idx)
    (hget : s.receiverChains[idx]? = some c)
    (hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) = none) :
    Mut.exec (RatchetState.takeSkippedKey their counter) s =
      (Except.ok none, s) := by
  unfold RatchetState.takeSkippedKey
  rw [Mut.exec_bind, Mut.exec_get]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hget]
  dsimp only
  rw [hpos]
  rfl

theorem bitVec32_ofNat_toNat (x : BitVec 32) :
    BitVec.ofNat 32 x.toNat = x := by
  simp

theorem consumeMessageKey_ok {F : ShaCompress} {ck0 : BitVec 256} {maxAcc : ℕ}
    {s s' : RatchetState} {their : PublicKey} {idx : ℕ} {c : ReceiverChain}
    {counter : BitVec 32} {msgType : MessageType} {key : MessageKeyGenerator}
    (hfind : s.findReceiverChainIndex their = some idx)
    (hget : s.receiverChains[idx]? = some c)
    (hinv : RcvChainInv F ck0 maxAcc c)
    (hexec : Mut.exec
      (RatchetState.consumeMessageKey F their
        ⟨chainKeyValAt F ck0 maxAcc, BitVec.ofNat 32 maxAcc⟩ counter msgType) s =
      (Except.ok key, s')) :
    ∃ c' : ReceiverChain,
      s' = updateChainAt s idx c' ∧
      c'.senderRatchetKey = c.senderRatchetKey ∧
      counter.toNat + 1 < 2 ^ 32 ∧
      key = ⟨msgSeedAt F ck0 counter.toNat, counter⟩ ∧
      RcvChainInv F ck0 (max maxAcc (counter.toNat + 1)) c' ∧
      (∀ i, 1 ≤ i → i < 2 ^ 32 → i ≠ counter.toNat + 1 →
        IndexAvailableL F ck0 maxAcc c i →
        IndexAvailableL F ck0 (max maxAcc (counter.toNat + 1)) c' i) := by
  unfold RatchetState.consumeMessageKey at hexec
  have hmax_lt := hinv.maxAcc_lt
  by_cases hlt : counter < BitVec.ofNat 32 maxAcc
  · simp only [hlt, ↓reduceIte] at hexec
    rw [Mut.exec_bind] at hexec
    cases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
    | none =>
      rw [takeSkippedKey_exec_none hfind hget hpos] at hexec
      simp [Mut.exec_throw] at hexec
    | some pos =>
      rcases findIdx?_eq_some_getElem? hpos with ⟨k0, hk0_get, hk0_eq⟩
      rw [beq_iff_eq] at hk0_eq
      rw [takeSkippedKey_exec_some hfind hget hpos hk0_get] at hexec
      simp only [Mut.exec_pure, Prod.mk.injEq, Except.ok.injEq] at hexec
      rcases hexec with ⟨rfl, rfl⟩
      have hk0_mem : k0 ∈ c.messageKeys := List.mem_of_getElem? hk0_get
      rcases hinv.keys_wf k0 hk0_mem with ⟨hk0_lt, hk0_wf⟩
      rw [hk0_eq] at hk0_lt hk0_wf
      rw [bitVec32_ofNat_toNat] at hk0_wf
      have hmax_eq : max maxAcc (counter.toNat + 1) = maxAcc := by omega
      refine ⟨{ c with messageKeys := c.messageKeys.eraseIdx pos }, rfl, rfl, by omega, hk0_wf, ?_, ?_⟩
      · rw [hmax_eq]
        refine ⟨hmax_lt, hinv.ck_eq, ?_, ?_⟩
        · intro mk hmk
          exact hinv.keys_wf mk (List.mem_of_mem_eraseIdx hmk)
        · exact hinv.keys_desc.sublist (List.Sublist.map _ (List.eraseIdx_sublist _ _))
      · intro i hi1 hi_lt hine hav
        rw [hmax_eq]
        rcases hav with hgt | hdrop | hmem
        · exact Or.inl hgt
        · exact Or.inr (Or.inl hdrop)
        · right; right
          have hne_mk : (⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ : MessageKeyGenerator) ≠ k0 := by
            intro heq
            have hcnt := congrArg MessageKeyGenerator.counter heq
            rw [hk0_eq] at hcnt
            have hval := congrArg BitVec.toNat hcnt
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i - 1 < 2 ^ 32)] at hval
            omega
          exact mem_eraseIdx_of_getElem?_of_ne hk0_get hne_mk hmem
  · simp only [hlt, ↓reduceIte] at hexec
    have hge : maxAcc ≤ counter.toNat := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt, not_lt] at hlt
      exact hlt
    have hjump : (counter - BitVec.ofNat 32 maxAcc).toNat = counter.toNat - maxAcc := by
      rw [BitVec.toNat_sub_of_le]
      · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt]
      · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt]
        exact hge
    rw [Mut.exec_bind, Mut.exec_get] at hexec
    dsimp only at hexec
    by_cases hfar : s.maxForwardJumps < (counter - BitVec.ofNat 32 maxAcc).toNat
    · simp only [hfar, ↓reduceIte] at hexec
      rw [Mut.exec_bind, Mut.exec_throw] at hexec
      simp at hexec
    · simp only [hfar, ↓reduceIte, pure_bind] at hexec
      have hsum : maxAcc + (counter - BitVec.ofNat 32 maxAcc).toNat = counter.toNat := by omega
      have hadv := advanceChain_exec F ck0 their counter
        ((counter - BitVec.ofNat 32 maxAcc).toNat) maxAcc s idx c hsum hfind hget
      rw [Mut.exec_bind, hadv] at hexec
      dsimp only at hexec
      rw [hsum, bitVec32_ofNat_toNat] at hexec
      rw [Mut.exec_bind, Mut.exec_liftE] at hexec
      cases hnext : (LibsignalSession.ChainKey.mk (chainKeyValAt F ck0 counter.toNat) counter).nextChainKey F with
      | error e =>
        rw [hnext] at hexec
        simp at hexec
      | ok ck_next =>
        rw [hnext] at hexec
        dsimp only at hexec
        rcases (nextChainKey_eq_ok_iff F _ ck_next).mp hnext with ⟨hcnt1_lt, hck_next⟩
        have hck_next' : ck_next =
            ⟨chainKeyValAt F ck0 (counter.toNat + 1), BitVec.ofNat 32 (counter.toNat + 1)⟩ := by
          rw [hck_next]
          rfl
        set c_mid : ReceiverChain :=
          { c with messageKeys := advanceKeys F ck0 (counter.toNat - maxAcc) maxAcc c.messageKeys }
        have hfind_mid : (updateChainAt s idx c_mid).findReceiverChainIndex their = some idx := by
          have hrk : c_mid.senderRatchetKey = c.senderRatchetKey := rfl
          rw [findReceiverChainIndex_updateChainAt their hget hrk, hfind]
        have hget_mid : (updateChainAt s idx c_mid).receiverChains[idx]? = some c_mid :=
          getElem?_updateChainAt_self hget c_mid
        rw [hjump] at hexec
        rw [Mut.exec_bind, setReceiverChainKey_exec hfind_mid hget_mid ck_next] at hexec
        simp only [Mut.exec_pure, updateChainAt_updateChainAt, Prod.mk.injEq, Except.ok.injEq] at hexec
        rcases hexec with ⟨hkey_eq, hs'_eq⟩
        have hmax_eq : max maxAcc (counter.toNat + 1) = counter.toNat + 1 := by omega
        set c' : ReceiverChain := { c_mid with chainKey := some ck_next }
        refine ⟨c', hs'_eq.symm, rfl, hcnt1_lt, hkey_eq.symm, ?_, ?_⟩
        · rw [hmax_eq]
          have hadv_wf := advanceKeys_wf_and_desc F ck0 (counter.toNat - maxAcc) maxAcc c.messageKeys
            (by omega) hinv.keys_wf hinv.keys_desc
          have hsum' : maxAcc + (counter.toNat - maxAcc) = counter.toNat := by omega
          rw [hsum'] at hadv_wf
          refine ⟨hcnt1_lt, ?_, ?_, hadv_wf.2⟩
          · dsimp only [c']
            rw [hck_next']
          · intro mk hmk
            rcases hadv_wf.1 mk hmk with ⟨h1, h2⟩
            exact ⟨by omega, h2⟩
        · intro i hi1 _hi_lt hine hav
          rw [hmax_eq]
          by_cases hgt' : counter.toNat + 1 < i
          · exact Or.inl hgt'
          · have hile : i ≤ maxAcc + (counter.toNat - maxAcc) := by omega
            have hav0 : maxAcc < i ∨ i + maxMessageKeys ≤ maxAcc ∨
                ⟨msgSeedAt F ck0 (i - 1), BitVec.ofNat 32 (i - 1)⟩ ∈ c.messageKeys := by
              rcases hav with h1 | h2 | h3
              · exact Or.inl h1
              · exact Or.inr (Or.inl (by omega))
              · exact Or.inr (Or.inr h3)
            rcases advanceKeys_avail F ck0 (counter.toNat - maxAcc) maxAcc c.messageKeys i
                (by omega) hi1 hile hinv.keys_wf hinv.keys_desc hav0 with hdrop | hmem
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inr (Or.inr hmem)

end CryptoGames.LibsignalSM.Proofs.Correctness
