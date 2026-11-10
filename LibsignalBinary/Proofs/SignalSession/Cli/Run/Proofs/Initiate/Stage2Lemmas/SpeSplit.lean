/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned
import LibsignalBinary.Specifications.AsmConstants

/-!
# Six-Word Register Move for `RunDrop.speOwnedAt`

Proves `speOwnedAt_split_move` for every variant of `RunDrop.SpeOwned`, decomposing
`RunDrop.speOwnedAt A src k` into 6 aligned 64-bit words `w0..w5` at `src + 0..40` with
`w0 ≠ 0#64 - 3#64` (`cmn x26, #3; b.ne` always taken) and a residual frame `R` that reassembles
`RunDrop.speOwnedAt A dst k` once `w0..w5` are stored to `dst + 0..40`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

private theorem speWord_ne_neg3 {i : Nat} (hi : i < 35) :
    speWord i ≠ (0#64 - 3#64) := by
  intro h
  have ht := congrArg BitVec.toNat h
  dsimp only [speWord] at ht
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at ht
  have h1 : 9223372036854775808 % 2 ^ 64 = 2 ^ 63 := by decide
  have h2 : (0#64 - 3#64).toNat = 2 ^ 64 - 3 := by decide
  rw [h1, h2] at ht
  omega

private theorem cap_lt_ne_neg3 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap ≠ (0#64 - 3#64) := by
  intro heq
  subst heq
  have h2 : (0#64 - 3#64).toNat = 2 ^ 64 - 3 := by decide
  omega

private theorem chunk_u8 (v : BitVec 8) (b : BitVec 64) :
    (b ↦₈ v) = (b ↦ₛ [v]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

private def ByteMovable (n : Nat) (F : BitVec 64 → SepProp) : Prop :=
  ∃ G : List (BitVec 8) → SepProp,
    (∀ src, F src ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (src ↦ₛ bs) ∗ G bs) ∧
    (∀ dst bs, bs.length = n → (dst ↦ₛ bs) ∗ G bs ⊢ F dst)

private theorem byteMovable_u64 (v : BitVec 64) : ByteMovable 8 (fun b => b ↦₆₄ v) := by
  refine ⟨fun bs => ⌜bs = unpack64 v⌝, fun src => ?_, fun dst bs _ => ?_⟩
  · dsimp only
    rw [pointsTo64_eq_pointsToBytes]
    refine Entails.sepExists_right (unpack64 v) ?_
    rw [sepConj_comm (src ↦ₛ unpack64 v)]
    exact Entails.pure_right (unpack64_length v) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only
    rw [sepConj_comm]
    refine Entails.pure_left fun hbs => ?_
    subst hbs
    rw [← pointsTo64_eq_pointsToBytes]
    exact Entails.refl _

private theorem byteMovable_u32 (v : BitVec 32) : ByteMovable 4 (fun b => b ↦₃₂ v) := by
  refine ⟨fun bs => ⌜bs = unpack32 v⌝, fun src => ?_, fun dst bs _ => ?_⟩
  · dsimp only
    rw [pointsTo32_eq_pointsToBytes]
    refine Entails.sepExists_right (unpack32 v) ?_
    rw [sepConj_comm (src ↦ₛ unpack32 v)]
    exact Entails.pure_right (by simp [unpack32]) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only
    rw [sepConj_comm]
    refine Entails.pure_left fun hbs => ?_
    subst hbs
    rw [← pointsTo32_eq_pointsToBytes]
    exact Entails.refl _

private theorem byteMovable_u8 (v : BitVec 8) : ByteMovable 1 (fun b => b ↦₈ v) := by
  refine ⟨fun bs => ⌜bs = [v]⌝, fun src => ?_, fun dst bs _ => ?_⟩
  · dsimp only
    rw [chunk_u8 v src]
    refine Entails.sepExists_right [v] ?_
    rw [sepConj_comm (src ↦ₛ [v])]
    exact Entails.pure_right rfl (Entails.pure_right rfl (Entails.refl _))
  · dsimp only
    rw [sepConj_comm]
    refine Entails.pure_left fun hbs => ?_
    subst hbs
    rw [← chunk_u8 v dst]
    exact Entails.refl _

private theorem byteMovable_memRegion (n : Nat) (hn : n ≤ 2 ^ 64 := by decide) :
    ByteMovable n (fun b => memRegion b n) := by
  refine ⟨fun _ => emp, fun src => ?_, fun dst bs hbs => ?_⟩
  · dsimp only
    rw [memRegion_eq_exists_bytes src n hn]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only
    rw [sepConj_emp, ← hbs]
    exact ProofLib.pointsToBytes_entails_memRegion dst bs

private theorem byteMovable_frame (R : SepProp) {n : Nat} {F : BitVec 64 → SepProp}
    (h : ByteMovable n F) :
    ByteMovable n (fun b => F b ∗ R) := by
  obtain ⟨G, hf, hb⟩ := h
  refine ⟨fun bs => G bs ∗ R, fun src => ?_, fun dst bs hbs => ?_⟩
  · refine Entails.trans (sepConj_mono_left (hf src)) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    dsimp only
    exact Entails.of_eq (by ac_rfl)
  · dsimp only
    refine Entails.trans (Entails.of_eq (show
        ((dst ↦ₛ bs) ∗ (G bs ∗ R)) = (((dst ↦ₛ bs) ∗ G bs) ∗ R) by ac_rfl)) ?_
    exact sepConj_mono_left (hb dst bs hbs)

private theorem byteMovable_seq {n1 n2 : Nat} {F1 F2 : BitVec 64 → SepProp}
    (h1 : ByteMovable n1 F1) (h2 : ByteMovable n2 F2) :
    ByteMovable (n1 + n2) (fun b => F1 b ∗ F2 (b + BitVec.ofNat 64 n1)) := by
  obtain ⟨G1, hf1, hb1⟩ := h1
  obtain ⟨G2, hf2, hb2⟩ := h2
  refine ⟨fun bs => G1 (bs.take n1) ∗ G2 (bs.drop n1), fun src => ?_, fun dst bs hbs => ?_⟩
  · refine Entails.trans (sepConj_mono (hf1 src) (hf2 (src + BitVec.ofNat 64 n1))) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun bs1 => ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs2 => ?_
    have hpull :
        ((⌜bs1.length = n1⌝ ∗ (src ↦ₛ bs1) ∗ G1 bs1) ∗
          (⌜bs2.length = n2⌝ ∗ ((src + BitVec.ofNat 64 n1) ↦ₛ bs2) ∗ G2 bs2)) =
        (⌜bs1.length = n1⌝ ∗ (⌜bs2.length = n2⌝ ∗
          (((src ↦ₛ bs1) ∗ ((src + BitVec.ofNat 64 n1) ↦ₛ bs2)) ∗ (G1 bs1 ∗ G2 bs2)))) := by
      ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hl1 => Entails.pure_left fun hl2 => ?_
    have htake : (bs1 ++ bs2).take n1 = bs1 := by simp [hl1]
    have hdrop : (bs1 ++ bs2).drop n1 = bs2 := by simp [hl1]
    have hcat : ((src ↦ₛ bs1) ∗ ((src + BitVec.ofNat 64 n1) ↦ₛ bs2)) = (src ↦ₛ (bs1 ++ bs2)) := by
      rw [← hl1, ← pointsToBytes_append]
    rw [hcat]
    refine Entails.sepExists_right (bs1 ++ bs2) ?_
    dsimp only
    rw [htake, hdrop]
    exact Entails.pure_right (by simp [hl1, hl2]) (Entails.refl _)
  · dsimp only
    have hl1 : (bs.take n1).length = n1 := by simp [hbs]
    have hl2 : (bs.drop n1).length = n2 := by simp [hbs]
    have hsplit : (dst ↦ₛ bs) =
        ((dst ↦ₛ bs.take n1) ∗ ((dst + BitVec.ofNat 64 n1) ↦ₛ bs.drop n1)) := by
      conv_lhs => rw [← List.take_append_drop n1 bs]
      rw [pointsToBytes_append, hl1]
    rw [hsplit]
    have hassoc :
        (((dst ↦ₛ bs.take n1) ∗ ((dst + BitVec.ofNat 64 n1) ↦ₛ bs.drop n1)) ∗
          (G1 (bs.take n1) ∗ G2 (bs.drop n1))) =
        (((dst ↦ₛ bs.take n1) ∗ G1 (bs.take n1)) ∗
          (((dst + BitVec.ofNat 64 n1) ↦ₛ bs.drop n1) ∗ G2 (bs.drop n1))) := by ac_rfl
    rw [hassoc]
    exact sepConj_mono (hb1 dst (bs.take n1) hl1) (hb2 (dst + BitVec.ofNat 64 n1) (bs.drop n1) hl2)

private theorem byteMovable_exists {α : Type} {n : Nat} {F : α → BitVec 64 → SepProp}
    (h : ∀ x, ByteMovable n (F x)) :
    ByteMovable n (fun b => ∃∗ x : α, F x b) := by
  refine ⟨fun bs => ∃∗ x : α, Classical.choose (h x) bs, fun src => ?_, fun dst bs hbs => ?_⟩
  · refine Entails.sepExists_elim fun x => ?_
    refine Entails.trans ((Classical.choose_spec (h x)).1 src) ?_
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    dsimp only
    exact sepConj_mono_right (sepConj_mono_right (Entails.sepExists_right x (Entails.refl _)))
  · dsimp only
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun x => ?_
    exact Entails.trans ((Classical.choose_spec (h x)).2 dst bs hbs)
      (Entails.sepExists_right x (Entails.refl _))

private theorem byteMovable_congr {n : Nat} {F1 F2 : BitVec 64 → SepProp}
    (h1 : ByteMovable n F1) (heq : ∀ b, F1 b = F2 b) :
    ByteMovable n F2 := by
  obtain ⟨G, hf, hb⟩ := h1
  exact ⟨G, fun src => by rw [← heq src]; exact hf src,
    fun dst bs hbs => by rw [← heq dst]; exact hb dst bs hbs⟩

private theorem byteMovable_strRefAt (lit : List (BitVec 8)) :
    ByteMovable 16 (fun b => strRefAt b lit) := by
  apply byteMovable_exists; intro p
  apply byteMovable_congr
    (byteMovable_frame (p ↦ᵣ lit)
      (byteMovable_seq (byteMovable_u64 p) (byteMovable_u64 (BitVec.ofNat 64 lit.length))))
  intro b; ac_rfl

private def vecTail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

private theorem byteMovable_vecU8 (A : RustAlloc) (bs : List (BitVec 8)) :
    ByteMovable 24 (fun b => RustHeap.vecU8 A b bs) := by
  apply byteMovable_congr (F1 := fun b =>
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      (((b ↦₆₄ cap) ∗ ((b + 8#64) ↦₆₄ ptr)) ∗ ((b + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        vecTail A cap ptr bs)
  · apply byteMovable_exists; intro cap
    apply byteMovable_exists; intro ptr
    apply byteMovable_frame
    exact byteMovable_seq (byteMovable_seq (byteMovable_u64 cap) (byteMovable_u64 ptr))
      (byteMovable_u64 (BitVec.ofNat 64 bs.length))
  · intro b
    dsimp only [RustHeap.vecU8, vecU8At, vecHeader, vecTail]
    apply ProofLib.sepExists_congr; intro cap
    apply ProofLib.sepExists_congr; intro ptr
    ac_rfl

private theorem byteMovable_addrCloneAt (A : RustAlloc) (v : AddrVal) :
    ByteMovable 32 (fun b => addrCloneAt A b v) := by
  have h8 : ByteMovable 8 (fun b => (b ↦₈ v.device) ∗ memRegion (b + 1#64) 7) :=
    byteMovable_seq (byteMovable_u8 v.device) (byteMovable_memRegion 7)
  apply byteMovable_congr (byteMovable_seq (byteMovable_vecU8 A v.name) h8)
  intro b
  dsimp only [addrCloneAt]
  rw [show (b + 24#64) + 1#64 = b + 0x19#64 by bv_omega]

private theorem exists_words5_of_length_40 {bs : List (BitVec 8)} (h : bs.length = 40) :
    ∃ w1 w2 w3 w4 w5 : BitVec 64,
      ∀ base : BitVec 64,
        ((base + 8#64) ↦ₛ bs) =
          (((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗
            ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5)) := by
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 (bs := bs.take 8) (by simp [h])
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 24).take 8) (by simp [h])
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 (bs := bs.drop 32) (by simp [h])
  have hbs : bs = unpack64 w1 ++ (unpack64 w2 ++ (unpack64 w3 ++ (unpack64 w4 ++ unpack64 w5))) := by
    rw [← hw1, ← hw2, ← hw3, ← hw4, ← hw5]
    have s4 : (bs.drop 24).take 8 ++ bs.drop 32 = bs.drop 24 := by
      have := List.take_append_drop 8 (bs.drop 24); rwa [List.drop_drop] at this
    have s3 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
      have := List.take_append_drop 8 (bs.drop 16); rwa [List.drop_drop] at this
    have s2 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
      have := List.take_append_drop 8 (bs.drop 8); rwa [List.drop_drop] at this
    rw [s4, s3, s2, List.take_append_drop]
  refine ⟨w1, w2, w3, w4, w5, fun base => ?_⟩
  rw [hbs,
      pointsToBytes_append, unpack64_length, show base + 8#64 + 8#64 = base + 16#64 by bv_omega,
      pointsToBytes_append, unpack64_length, show base + 16#64 + 8#64 = base + 24#64 by bv_omega,
      pointsToBytes_append, unpack64_length, show base + 24#64 + 8#64 = base + 32#64 by bv_omega,
      pointsToBytes_append, unpack64_length, show base + 32#64 + 8#64 = base + 40#64 by bv_omega,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]

private def SpeMovePost (src dst : BitVec 64) (P : BitVec 64 → SepProp) : SepProp :=
  ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
  ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ R : SepProp,
    ⌜w0 ≠ (0#64 - 3#64) ∧
      (((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
        ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ R) ⊢
        P dst)⌝ ∗
    (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
    ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗ R

private theorem speWord40_move_from {w0 src dst : BitVec 64} (hw0 : w0 ≠ (0#64 - 3#64))
    {S : SepProp} {P G : BitVec 64 → SepProp} (hG : ByteMovable 40 G)
    (hsrc : S ⊢ (src ↦₆₄ w0) ∗ G (src + 8#64))
    (hdst : ((dst ↦₆₄ w0) ∗ G (dst + 8#64)) ⊢ P dst) :
    S ⊢ SpeMovePost src dst P := by
  obtain ⟨H, hf, hb⟩ := hG
  refine Entails.trans hsrc ?_
  refine Entails.trans (sepConj_mono_right (hf (src + 8#64))) ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  have hpull :
      ((src ↦₆₄ w0) ∗ (⌜bs.length = 40⌝ ∗ ((src + 8#64) ↦ₛ bs) ∗ H bs)) =
      (⌜bs.length = 40⌝ ∗ ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦ₛ bs) ∗ H bs)) := by ac_rfl
  rw [hpull]
  refine Entails.pure_left fun hlen => ?_
  obtain ⟨w1, w2, w3, w4, w5, hw⟩ := exists_words5_of_length_40 hlen
  rw [hw src]
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right (H bs) ?_))))))
  refine Entails.pure_right ⟨hw0, ?_⟩ (Entails.of_eq (by ac_rfl))
  have hback :
      ((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
        ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ H bs) =
      ((dst ↦₆₄ w0) ∗ (((dst + 8#64) ↦ₛ bs) ∗ H bs)) := by
    rw [hw dst]; ac_rfl
  rw [hback]
  exact Entails.trans (sepConj_mono_right (hb (dst + 8#64) bs hlen)) hdst

private theorem speTag40_eq {i : Nat} {P G : BitVec 64 → SepProp} {src dst : BitVec 64}
    (hG : ByteMovable 40 G)
    (heq : ∀ b, P b = (b ↦₆₄ speWord i) ∗ G (b + 8#64))
    (hi : i < 35 := by decide) :
    P src ⊢ SpeMovePost src dst P :=
  speWord40_move_from (speWord_ne_neg3 hi) hG (Entails.of_eq (heq src)) (Entails.of_eq (heq dst).symm)

private theorem forall_mem_lt35 : ∀ {l : List Nat}, l.all (· < 35) = true → ∀ {i}, i ∈ l → i < 35
  | [], _, _, hmem => nomatch hmem
  | _ :: _, hall, _, hmem => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact hall.1
    · exact forall_mem_lt35 hall.2 htl

theorem plainSpeTag_lt35 {i : Nat} (h : RunDrop.PlainSpeTag i) : i < 35 :=
  forall_mem_lt35 (by decide) h

theorem strSpeTag_lt35 {i : Nat} (h : RunDrop.StrSpeTag i) : i < 35 :=
  forall_mem_lt35 (by decide) h

theorem speOwnedAt_split_move (A : RustAlloc) (src dst : BitVec 64) (k : RunDrop.SpeOwned) :
    RunDrop.speOwnedAt A src k ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ R : SepProp,
        ⌜w0 ≠ (0#64 - 3#64) ∧
          (((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
            ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗ ((dst + 40#64) ↦₆₄ w5) ∗ R) ⊢
            RunDrop.speOwnedAt A dst k)⌝ ∗
        (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
        ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗ R := by
  change RunDrop.speOwnedAt A src k ⊢ SpeMovePost src dst (fun b => RunDrop.speOwnedAt A b k)
  cases k with
  | badKemKeyType =>
    exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b .badKemKeyType)
      (byteMovable_memRegion 40) (fun _ => rfl) (by decide)
  | badKemKeyLength =>
    exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b .badKemKeyLength)
      (byteMovable_memRegion 40) (fun _ => rfl) (by decide)
  | plain i hi =>
    exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.plain i hi))
      (byteMovable_memRegion 40) (fun _ => rfl) (plainSpeTag_lt35 hi)
  | withString i hi =>
    exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.withString i hi))
      (byteMovable_seq (byteMovable_exists fun bs => byteMovable_vecU8 A bs)
        (byteMovable_memRegion 16))
      (fun b => by
        dsimp only [RunDrop.speOwnedAt]
        rw [show b + 0x20#64 = (b + 8#64) + 24#64 by bv_omega])
      (strSpeTag_lt35 hi)
  | untrustedIdentity addr =>
    exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.untrustedIdentity addr))
      (byteMovable_seq (byteMovable_addrCloneAt A addr) (byteMovable_memRegion 8))
      (fun b => by
        dsimp only [RunDrop.speOwnedAt, apiErrAt]
        rw [show b + 0x28#64 = (b + 8#64) + 32#64 by bv_omega])
      (by decide)
  | sessionNotFound addr op =>
    have hdecomp : ∀ b, RunDrop.speOwnedAt A b (.sessionNotFound addr op) =
        ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ((b ↦₆₄ cap) ∗
            ((((b + 8#64) ↦₆₄ ptr) ∗ ((b + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)) ∗
              ((((b + 8#64 + 16#64) ↦₈ addr.device) ∗ memRegion (b + 8#64 + 16#64 + 1#64) 7) ∗
                strRefAt (b + 8#64 + 16#64 + 8#64) (utf8 op)) ∗
              vecTail A cap ptr addr.name)) := by
      intro b
      dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, RustHeap.vecU8, vecU8At, vecHeader, vecTail]
      rw [sepExists_sepConj_left, sepExists_sepConj_left]
      apply ProofLib.sepExists_congr; intro cap
      rw [sepExists_sepConj_left, sepExists_sepConj_left]
      apply ProofLib.sepExists_congr; intro ptr
      rw [show b + 8#64 + 8#64 = b + 16#64 by bv_omega,
          show b + 8#64 + 16#64 = b + 0x18#64 by bv_omega,
          show (b + 0x18#64) + 1#64 = b + 0x19#64 by bv_omega,
          show (b + 0x18#64) + 8#64 = b + 0x20#64 by bv_omega]
      ac_rfl
    rw [hdecomp src]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    let tail : SepProp :=
      if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ addr.name) ∗
        memRegion (ptr + BitVec.ofNat 64 addr.name.length) (cap.toNat - addr.name.length)
    have hpull_cap :
        vecTail A cap ptr addr.name =
          (⌜addr.name.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ tail) := rfl
    have hpure_out :
        ((src ↦₆₄ cap) ∗
          ((((src + 8#64) ↦₆₄ ptr) ∗ ((src + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)) ∗
            ((((src + 8#64 + 16#64) ↦₈ addr.device) ∗ memRegion (src + 8#64 + 16#64 + 1#64) 7) ∗
              strRefAt (src + 8#64 + 16#64 + 8#64) (utf8 op)) ∗
            vecTail A cap ptr addr.name)) ⊢
        ⌜cap.toNat < 2 ^ 63⌝ ∗
          ((src ↦₆₄ cap) ∗
            ((((src + 8#64) ↦₆₄ ptr) ∗ ((src + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)) ∗
              ((((src + 8#64 + 16#64) ↦₈ addr.device) ∗ memRegion (src + 8#64 + 16#64 + 1#64) 7) ∗
                strRefAt (src + 8#64 + 16#64 + 8#64) (utf8 op)) ∗
              vecTail A cap ptr addr.name)) := by
      rw [hpull_cap]
      have hassoc :
          ((src ↦₆₄ cap) ∗
            ((((src + 8#64) ↦₆₄ ptr) ∗ ((src + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)) ∗
              ((((src + 8#64 + 16#64) ↦₈ addr.device) ∗ memRegion (src + 8#64 + 16#64 + 1#64) 7) ∗
                strRefAt (src + 8#64 + 16#64 + 8#64) (utf8 op)) ∗
              (⌜addr.name.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ tail))) =
          (⌜addr.name.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            ((src ↦₆₄ cap) ∗
              ((((src + 8#64) ↦₆₄ ptr) ∗ ((src + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)) ∗
                ((((src + 8#64 + 16#64) ↦₈ addr.device) ∗ memRegion (src + 8#64 + 16#64 + 1#64) 7) ∗
                  strRefAt (src + 8#64 + 16#64 + 8#64) (utf8 op)) ∗
                tail))) := by ac_rfl
      rw [hassoc]
      refine Entails.pure_left fun hcap => Entails.pure_right hcap.2.1 ?_
      exact Entails.pure_right hcap (Entails.refl _)
    refine Entails.trans hpure_out (Entails.pure_left fun hcap => ?_)
    have hG40 : ByteMovable 40 (fun u =>
        (((u ↦₆₄ ptr) ∗ ((u + 8#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)) ∗
          ((((u + 16#64) ↦₈ addr.device) ∗ memRegion (u + 16#64 + 1#64) 7) ∗
            strRefAt (u + 16#64 + 8#64) (utf8 op))) ∗
          vecTail A cap ptr addr.name) := by
      apply byteMovable_frame
      exact byteMovable_seq
        (byteMovable_seq (byteMovable_u64 ptr) (byteMovable_u64 (BitVec.ofNat 64 addr.name.length)))
        (byteMovable_seq
          (byteMovable_seq (byteMovable_u8 addr.device) (byteMovable_memRegion 7))
          (byteMovable_strRefAt (utf8 op)))
    exact speWord40_move_from (P := fun b => RunDrop.speOwnedAt A b (.sessionNotFound addr op))
      (cap_lt_ne_neg3 hcap) hG40
      (Entails.of_eq (by ac_rfl))
      (by
        rw [hdecomp dst]
        exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))
  | proto fnName e =>
    cases e with
    | panic =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      exact Entails.pure_left_only False.elim
    | invalidProtobufEncoding =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName .invalidProtobufEncoding))
        (byteMovable_memRegion 40) (fun _ => rfl) (by decide)
    | noKeyTypeIdentifier =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName .noKeyTypeIdentifier))
        (byteMovable_memRegion 40) (fun _ => rfl) (by decide)
    | invalidKeyAgreement =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName .invalidKeyAgreement))
        (byteMovable_memRegion 40) (fun _ => rfl) (by decide)
    | ciphertextMessageTooShort n =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.ciphertextMessageTooShort n)))
        (byteMovable_seq (byteMovable_u64 (BitVec.ofNat 64 n)) (byteMovable_memRegion 32))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% (spePayloadOff + 8) = (b + 8#64) + 8#64 by bv_omega])
        (by decide)
    | badKeyLength n =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.badKeyLength n)))
        (byteMovable_seq (byteMovable_u64 (BitVec.ofNat 64 n)) (byteMovable_memRegion 32))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% (spePayloadOff + 8) = (b + 8#64) + 8#64 by bv_omega])
        (by decide)
    | legacyCiphertextVersion v =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.legacyCiphertextVersion v)))
        (byteMovable_seq (byteMovable_u8 v) (byteMovable_memRegion 39))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% (spePayloadOff + 1) = (b + 8#64) + 1#64 by bv_omega])
        (by decide)
    | unrecognizedCiphertextVersion v =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.unrecognizedCiphertextVersion v)))
        (byteMovable_seq (byteMovable_u8 v) (byteMovable_memRegion 39))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% (spePayloadOff + 1) = (b + 8#64) + 1#64 by bv_omega])
        (by decide)
    | badKeyType t =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.badKeyType t)))
        (byteMovable_seq (byteMovable_u8 t) (byteMovable_memRegion 39))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% (spePayloadOff + 1) = (b + 8#64) + 1#64 by bv_omega])
        (by decide)
    | invalidSessionStructure r =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.invalidSessionStructure r)))
        (byteMovable_seq (byteMovable_strRefAt (invalidSessionStructureStr r)) (byteMovable_memRegion 24))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% (spePayloadOff + boxSliceSize) = (b + 8#64) + 16#64 by bv_omega])
        (by decide)
    | duplicatedMessage i c =>
      exact speTag40_eq (i := 23)
        (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.duplicatedMessage i c)))
        (byteMovable_seq (byteMovable_seq (byteMovable_u32 i) (byteMovable_u32 c))
          (byteMovable_memRegion 32))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% speDupCounterOff = (b + 8#64) + 4#64 by bv_omega,
              show b + asm64% (speDupCounterOff + 4) = (b + 8#64) + 8#64 by bv_omega,
              show (b + 8#64) + BitVec.ofNat 64 (4 + 4) = (b + 8#64) + 8#64 from rfl]
          ac_rfl)
        (by decide)
    | invalidState =>
      exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName .invalidState))
        (byteMovable_seq (byteMovable_exists fun bs => byteMovable_vecU8 A bs)
          (byteMovable_strRefAt fnName))
        (fun b => by
          dsimp only [RunDrop.speOwnedAt, speAt]
          rw [show b + asm64% speInvalidStateFnOff = (b + 8#64) + 24#64 by bv_omega])
        (by decide)
    | invalidMessage t r =>
      cases r with
      | decryptionFailed =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        rw [← sepConj_assoc, sepConj_comm (src ↦₆₄ _), sepConj_assoc]
        exact Entails.pure_left False.elim
      | tooFarInFuture =>
        exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.invalidMessage t .tooFarInFuture)))
          (byteMovable_seq (byteMovable_vecU8 A tooFarInFutureStr)
            (byteMovable_seq (byteMovable_u8 (msgTypeByte t)) (byteMovable_memRegion 15)))
          (fun b => by
            dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
            rw [show b + asm64% speInvalidMessageTypeOff = (b + 8#64) + 24#64 by bv_omega,
                show b + asm64% (speInvalidMessageTypeOff + 1) = (b + 8#64) + 24#64 + 1#64 by bv_omega])
          (by decide)
      | macFailed =>
        exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.invalidMessage t .macFailed)))
          (byteMovable_seq (byteMovable_vecU8 A macFailedStr)
            (byteMovable_seq (byteMovable_u8 (msgTypeByte t)) (byteMovable_memRegion 15)))
          (fun b => by
            dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
            rw [show b + asm64% speInvalidMessageTypeOff = (b + 8#64) + 24#64 by bv_omega,
                show b + asm64% (speInvalidMessageTypeOff + 1) = (b + 8#64) + 24#64 + 1#64 by bv_omega])
          (by decide)
      | pqRatchet =>
        exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.invalidMessage t .pqRatchet)))
          (byteMovable_seq (byteMovable_exists fun bs => byteMovable_vecU8 A bs)
            (byteMovable_seq (byteMovable_u8 (msgTypeByte t)) (byteMovable_memRegion 15)))
          (fun b => by
            dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
            rw [show b + asm64% speInvalidMessageTypeOff = (b + 8#64) + 24#64 by bv_omega,
                show b + asm64% (speInvalidMessageTypeOff + 1) = (b + 8#64) + 24#64 + 1#64 by bv_omega])
          (by decide)
      | badCiphertext =>
        exact speTag40_eq (P := fun b => RunDrop.speOwnedAt A b (.proto fnName (.invalidMessage t .badCiphertext)))
          (byteMovable_seq (byteMovable_exists fun bs => byteMovable_vecU8 A bs)
            (byteMovable_seq (byteMovable_u8 (msgTypeByte t)) (byteMovable_memRegion 15)))
          (fun b => by
            dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
            rw [show b + asm64% speInvalidMessageTypeOff = (b + 8#64) + 24#64 by bv_omega,
                show b + asm64% (speInvalidMessageTypeOff + 1) = (b + 8#64) + 24#64 + 1#64 by bv_omega])
          (by decide)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
