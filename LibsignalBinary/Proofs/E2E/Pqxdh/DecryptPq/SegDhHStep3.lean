/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import ProofLib.SepLogic.WPp

/-!
# `Vec<Chain>` Buffer Growth and Slot Exposure Helpers for `S3CommitSpec`

Stack-budget and `vecBuf` slot-exposure lemmas (`growOneStack`, `vecBuf_expose_next_slot_empty`,
`vecBuf_expose_next_slot_pos`, `vecBuf_push_singleton`) for pushing a new `ReceiverChain` in
`S3CommitSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev growOneStack : Nat := 4608

theorem vecBuf_chainAt_expose_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainArrayBytes gcs bs ∧ bs.length = gcs.length * 104 ∧
          gcs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else
           A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
             chainHeaps A gcs) := by
  by_cases hcap : cap = 0
  · subst hcap
    rw [vecBuf_zero, ← sepConj_emp ⌜gcs = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨rfl, hptr⟩
    apply Entails.sepExists_right []
    apply Entails.pure_right ⟨ChainArrayBytes.nil, rfl, by decide, by decide, hptr⟩
    simp
    exact Entails.refl _
  · refine Entails.trans (vecBuf_chainAt_entails_bytes A cap ptr gcs hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.sepExists_right bs
    simp only [hcap, ↓reduceIte]
    exact Entails.refl _

theorem vecBuf_expose_for_grow (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (bs : List (BitVec 8))
    (hlen_bs : bs.length = gcs.length * 104) (hlen_eq_cap : gcs.length = cap.toNat) :
    (if cap = 0 then emp
     else
       A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
         chainHeaps A gcs) =
    ((if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ chainHeaps A gcs) := by
  by_cases hcap : cap = 0
  · subst hcap
    have h0 : gcs.length = 0 := hlen_eq_cap
    rcases List.eq_nil_of_length_eq_zero h0 with rfl
    simp [chainHeaps]
  · simp only [hcap, ↓reduceIte, hlen_bs, hlen_eq_cap, Nat.sub_self, Nat.zero_mul,
      memRegion_zero]
    ac_rfl

theorem vecBuf_expose_for_push (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hlt : gcs.length < cap.toNat) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ⌜cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 ptr gcs ∗
      memRegion (ptr + BitVec.ofNat 64 gcs.length * 104#64) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
        ((cap.toNat - (gcs.length + 1)) * 104) := by
  have hcap : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_left
  rintro ⟨_hle, hcap_lt, hptr⟩
  apply Entails.pure_right ⟨hcap_lt, hptr⟩
  have hrem : (cap.toNat - gcs.length) * 104 =
      104 + (cap.toNat - (gcs.length + 1)) * 104 := by
    have : cap.toNat - gcs.length = 1 + (cap.toNat - (gcs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (gcs.length * 104) = BitVec.ofNat 64 gcs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (gcs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
