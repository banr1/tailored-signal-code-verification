/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailSym
import ProofLib.RegChain

/-!
# `segPreKey` `PreKeySignalMessage` Construction (`+0x8c8..+0xa70`)

On the `Ok sm` return of `OTR::encrypt` at `+0x8c8` (`PreKeyEncryptRetState`), relocates the inner
`SignalMessage`, optional Kyber payload, base key, and local identity key, invokes
`PreKeySignalMessage::new` (`+0x98c`), and copies the 248-byte result to `sp + 0x370` to establish
`CmState` at `+0xa70`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Word and `memRegion` Decomposition Helpers -/

theorem words64At_append : ∀ (ws1 ws2 : List (BitVec 64)) (a : BitVec 64),
    words64At a (ws1 ++ ws2) =
      words64At a ws1 ∗ words64At (a + BitVec.ofNat 64 (8 * ws1.length)) ws2
  | [], ws2, a => by
    simp only [List.nil_append, words64At, List.length_nil, Nat.mul_zero,
      BitVec.add_zero, emp_sepConj]
  | w :: ws1, ws2, a => by
    simp only [List.cons_append, words64At, List.length_cons,
      words64At_append ws1 ws2 (a + 8#64), sepConj_assoc]
    have h : a + 8#64 + BitVec.ofNat 64 (8 * ws1.length) =
        a + BitVec.ofNat 64 (8 * (ws1.length + 1)) := by bv_omega
    rw [h]

theorem memRegion_24_exists_words3 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ w0 w1 w2 : BitVec 64, m ⊨ words64At a [w0, w1, w2] ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := SegFrom.memRegion_exists_words64At 3 a (by decide) hm
  rcases ws with _ | ⟨w0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, hws⟩
  · nomatch hlen

theorem memRegion_32_exists_words4 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ w0 w1 w2 w3 : BitVec 64, m ⊨ words64At a [w0, w1, w2, w3] ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := SegFrom.memRegion_exists_words64At 4 a (by decide) hm
  rcases ws with _ | ⟨w0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w3, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, hws⟩
  · nomatch hlen

theorem memRegion_120_exists_words15 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 120 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 : BitVec 64,
      m ⊨ words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗ R := by
  rw [memRegion_split a 32 88 (by decide),
      memRegion_split (a + 32#64) 32 56 (by decide),
      memRegion_split (a + 32#64 + 32#64) 32 24 (by decide)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm
  obtain ⟨d0, d1, d2, d3, hm⟩ := memRegion_32_exists_words4 a hm
  have hm1 : m ⊨ memRegion (a + 32#64) 32 ∗
      (memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 24 ∗
        words64At a [d0, d1, d2, d3] ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
  obtain ⟨d4, d5, d6, d7, hm1⟩ := memRegion_32_exists_words4 (a + 32#64) hm1
  have hm2 : m ⊨ memRegion (a + 64#64) 32 ∗
      (memRegion (a + 96#64) 24 ∗
        words64At a [d0, d1, d2, d3] ∗ words64At (a + 32#64) [d4, d5, d6, d7] ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm1
  obtain ⟨d8, d9, d10, d11, hm2⟩ := memRegion_32_exists_words4 (a + 64#64) hm2
  have hm3 : m ⊨ memRegion (a + 96#64) 24 ∗
      (words64At a [d0, d1, d2, d3] ∗ words64At (a + 32#64) [d4, d5, d6, d7] ∗
        words64At (a + 64#64) [d8, d9, d10, d11] ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm2
  obtain ⟨d12, d13, d14, hm3⟩ := memRegion_24_exists_words3 (a + 96#64) hm3
  refine ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, ?_⟩
  have hcomb :
      words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] =
      words64At a [d0, d1, d2, d3] ∗ words64At (a + 32#64) [d4, d5, d6, d7] ∗
        words64At (a + 64#64) [d8, d9, d10, d11] ∗ words64At (a + 96#64) [d12, d13, d14] := by
    rw [show [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] =
        [d0, d1, d2, d3] ++ ([d4, d5, d6, d7] ++ ([d8, d9, d10, d11] ++ [d12, d13, d14])) from rfl,
      words64At_append, words64At_append, words64At_append]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd]
  rw [hcomb]
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm3

theorem memRegion_248_exists_words31 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 248 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14
      d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 : BitVec 64,
      m ⊨ words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
        d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30] ∗ R := by
  rw [memRegion_split a 120 128 (by decide),
      memRegion_split (a + 120#64) 120 8 (by decide),
      ProofLib.memRegion_eight (a + 120#64 + 120#64)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨d30, hm⟩ := hm
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, hm⟩ :=
    memRegion_120_exists_words15 a hm
  have hm1 : m ⊨ memRegion (a + 120#64) 120 ∗
      (words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗
        ((a + 240#64) ↦₆₄ d30) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
  obtain ⟨d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, hm1⟩ :=
    memRegion_120_exists_words15 (a + 120#64) hm1
  refine ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, ?_⟩
  have hcomb :
      words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
        d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30] =
      words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗
        words64At (a + 120#64) [d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29] ∗
        ((a + 240#64) ↦₆₄ d30) := by
    rw [show [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
          d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30] =
        [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ++
          ([d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29] ++ [d30]) from rfl,
      words64At_append, words64At_append]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd, words64At, sepConj_emp, sepConj_assoc]
  rw [hcomb]
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm1

/-! ## Representation Relocation Helpers -/

theorem pqCap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

theorem words64At_2 (a w0 w1 : BitVec 64) :
    words64At a [w0, w1] = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) := by
  simp only [words64At, sepConj_emp]

theorem words64At_3 (a w0 w1 w2 : BitVec 64) :
    words64At a [w0, w1, w2] = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem bytes32_exists_words64At {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a [w0, w1, w2, w3] := by
  obtain ⟨w0, w1, w2, w3, _, heq⟩ := exists_unpack64_of_length_32 h
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [heq a]
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

def otrRestAt (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) : SepProp :=
  vecU8At A o pqCap pqPtr ot.pqrState ∗
    ((o + 0x18#64) ↦ₛ ot.senderRatchetKey.publicKey.bytes.toList) ∗
    ((o + 0x38#64) ↦ₛ ot.senderRatchetKey.privateKey.bytes.toList) ∗
    ((o + 0x78#64) ↦ₛ ot.remoteIdentityKey.publicKey.bytes.toList) ∗
    ((o + 0x98#64) ↦ₛ chainKeyBytes ot.senderChainKey) ∗
    ((o + 0xbc#64) ↦₃₂ ot.previousCounter) ∗
    memRegion (o + 0xc1#64) 7

theorem otrAt_eq_ik_ver_rest (A : RustAlloc) (sp pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) (ik0 ik1 ik2 ik3 : BitVec 64)
    (hik : ∀ a : BitVec 64,
      (a ↦ₛ ot.localIdentityKey.publicKey.bytes.toList) = words64At a [ik0, ik1, ik2, ik3]) :
    otrAt A (sp + 0x288#64) pqCap pqPtr ot =
      words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
      ((sp + 0x348#64) ↦₈ ot.sessionVersion) ∗
      otrRestAt A (sp + 0x288#64) pqCap pqPtr ot := by
  unfold otrAt otrRestAt
  have h2e0 : sp + 0x288#64 + 0x58#64 = sp + 0x2e0#64 := by bv_omega
  have h348 : sp + 0x288#64 + 0xc0#64 = sp + 0x348#64 := by bv_omega
  rw [h2e0, h348, hik (sp + 0x2e0#64)]
  ac_rfl

theorem signalMessageWordsAt_eq_words64At (g : SignalMessageGhost) (m : SignalMessage)
    (a m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt g m a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [g.pqCap, g.pqPtr, BitVec.ofNat 64 m.pqRatchet.length,
        g.ctPtr, BitVec.ofNat 64 m.ciphertext.length,
        g.serPtr, BitVec.ofNat 64 m.serialized.length,
        m7, m8, m9, m10, m11, m12, m.previousCounter ++ m.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem signalMessageHeap_serialized_lt (A : RustAlloc) (g : SignalMessageGhost) (m : SignalMessage)
    (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14 ⊢
      ⌜m.serialized.length < 2 ^ 40⌝ ∗ signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14 := by
  unfold signalMessageHeap
  refine Entails.pure_left fun h => ?_
  exact Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem signalMessageAt_relocate (A : RustAlloc) (g : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A g src sm ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      w0 + 1#64 ≠ 0#64 ∧
      sm.serialized.length < 2 ^ 40 ∧
      (m ⊨ words64At src [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H ⊢
          signalMessageAt A g dst sm) := by
  have hm1 := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A g src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨hpqCap, hm1⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  rcases hm1 with ⟨m7, m8, m9, m10, m11, m12, m14, hm1⟩
  have hm2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (signalMessageHeap_serialized_lt A g sm m7 m8 m9 m10 m11 m12 m14))) hm1
  have hm3 : m ⊨ ⌜sm.serialized.length < 2 ^ 40⌝ ∗
      (signalMessageWordsAt g sm src m7 m8 m9 m10 m11 m12 m14 ∗
        signalMessageHeap A g sm m7 m8 m9 m10 m11 m12 m14 ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm2
  rw [satisfies_pure_sepConj, signalMessageWordsAt_eq_words64At] at hm3
  rcases hm3 with ⟨hser, hm3⟩
  refine ⟨g.pqCap, g.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length,
    g.ctPtr, BitVec.ofNat 64 sm.ciphertext.length,
    g.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A g sm m7 m8 m9 m10 m11 m12 m14,
    pqCap_add_one_ne_zero hpqCap, hser, hm3, ?_⟩
  intro dst
  rw [← signalMessageWordsAt_eq_words64At]
  exact signalMessageAt_pack A g dst sm m7 m8 m9 m10 m11 m12 m14

theorem optKyberAt_relocate (A : RustAlloc) (src ptr : BitVec 64) (kp : Option KyberPayload)
    {m : Memory} {R : SepProp}
    (hm : m ⊨ optKyberAt A src ptr kp ∗ R) :
    ∃ (k0 k1 k2 : BitVec 64) (H : SepProp),
      (m ⊨ words64At src [k0, k1, k2] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64, words64At dst [k0, k1, k2] ∗ H ⊢ optKyberAt A dst ptr kp) := by
  cases kp with
  | none =>
    dsimp only [optKyberAt] at hm
    rw [memRegion_split (src + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight (src + 8#64),
        ProofLib.memRegion_eight (src + 8#64 + 8#64)] at hm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm
    rcases hm with ⟨k2, k1, hm⟩
    refine ⟨0#64, k1, k2, emp, ?_, ?_⟩
    · simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
        emp_sepConj]
      exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    · intro dst
      dsimp only [optKyberAt]
      rw [sepConj_emp]
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
      rw [memRegion_split (dst + 8#64) 8 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (sepConj_mono
        (pointsTo64_entails_memRegion (dst + 8#64) k1)
        (pointsTo64_entails_memRegion (dst + 16#64) k2))
  | some k =>
    dsimp only [optKyberAt] at hm
    rw [boxU8At_eq_header_sep_buf, ProofLib.memRegion_four (src + 0x14#64)] at hm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc] at hm
    obtain ⟨hi, hm⟩ := hm
    have hpair : ∀ a : BitVec 64,
        ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗ ((a + 0x14#64) ↦₃₂ hi) =
          ((a + 16#64) ↦₆₄ (hi ++ k.preKeyId)) := by
      intro a
      have hp := pointsTo32_pair (a + 16#64) k.preKeyId hi
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp
    refine ⟨ptr, BitVec.ofNat 64 k.ciphertext.length, hi ++ k.preKeyId,
      Encrypt.boxU8Buf A ptr k.ciphertext, ?_, ?_⟩
    · simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      rw [← hpair src]
      exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    · intro dst
      dsimp only [optKyberAt]
      rw [boxU8At_eq_header_sep_buf]
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      rw [← hpair dst]
      have hhi := pointsTo32_entails_memRegion (dst + 0x14#64) hi
      have hrearr :
          ((dst ↦₆₄ ptr) ∗ ((dst + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
            (((dst + 0x10#64) ↦₃₂ k.preKeyId) ∗ ((dst + 0x14#64) ↦₃₂ hi)) ∗
            Encrypt.boxU8Buf A ptr k.ciphertext) =
          ((dst ↦₆₄ ptr) ∗ ((dst + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
            Encrypt.boxU8Buf A ptr k.ciphertext ∗
            ((dst + 0x10#64) ↦₃₂ k.preKeyId) ∗ ((dst + 0x14#64) ↦₃₂ hi)) := by
        ac_rfl
      rw [hrearr]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hhi)))

theorem optU32At_pack64 (b : BitVec 64) (opt : Option (BitVec 32)) (val : BitVec 32) :
    (⌜optU32ValProp opt val⌝ ∗ (b ↦₆₄ (val ++ (if opt.isSome then 1#32 else 0#32)))) ⊢
      optU32At b opt := by
  refine Entails.pure_left fun hval => ?_
  rw [← pointsTo32_pair]
  cases opt with
  | none =>
    unfold optU32At
    exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
  | some v =>
    unfold optU32At
    rw [hval v rfl]
    exact Entails.refl _

theorem preKeyMsgAt_relocate (A : RustAlloc) (g : PreKeyMsgGhost) (src : BitVec 64)
    (psm : PreKeySignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ preKeyMsgAt A g src psm ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
        w25 w26 w27 w28 w29 w30 : BitVec 64) (H : SepProp),
      w0 + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗ H ⊢
        preKeyMsgAt A g dst psm) := by
  obtain ⟨w21, w22, w23, w24, hbk⟩ :=
    bytes32_exists_words64At (bs := psm.baseKey.bytes.toList) (List.Vector.toList_length _)
  obtain ⟨w25, w26, w27, w28, hik⟩ :=
    bytes32_exists_words64At (bs := psm.identityKey.publicKey.bytes.toList) (List.Vector.toList_length _)
  unfold preKeyMsgAt at hm
  rw [sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    H_sm, hw0, _, hm, hpack_sm⟩ := signalMessageAt_relocate A g.msg src psm.message hm
  let W15 := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
  let F_tail := boxU8At A (src + 0x80#64) g.serPtr psm.serialized ∗
    ((src + 0xa8#64) ↦ₛ psm.baseKey.bytes.toList) ∗
    ((src + 0xc8#64) ↦ₛ psm.identityKey.publicKey.bytes.toList) ∗
    ((src + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((src + 0xec#64) ↦₃₂ psm.signedPreKeyId)
  have hm_ky : m ⊨ optKyberAt A (src + 0x90#64) g.kyberPtr psm.kyberPayload ∗
      (words64At src W15 ∗ H_sm ∗ optU32At (src + 0x78#64) psm.preKeyId ∗ F_tail ∗
        ((src + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (src + 0xf1#64) 7 ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by dsimp only [W15, F_tail]; ac_rfl)) hm
  obtain ⟨w18, w19, w20, H_ky, hm_ky, hpack_ky⟩ :=
    optKyberAt_relocate A (src + 0x90#64) g.kyberPtr psm.kyberPayload hm_ky
  have hpk_unp := optU32At_unpack64 (src + 0x78#64) psm.preKeyId
  have hver_unp : ((src + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (src + 0xf1#64) 7 ⊢
      ∃∗ w30 : BitVec 64, ⌜versionPadProp psm.messageVersion w30⌝ ∗ ((src + 0xf0#64) ↦₆₄ w30) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using versionPad_unpack (src + 0xf0#64) psm.messageVersion
  have hm_sub : m ⊨ (optU32At (src + 0x78#64) psm.preKeyId ∗
      (((src + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (src + 0xf1#64) 7)) ∗
      (words64At src W15 ∗ words64At (src + 0x90#64) [w18, w19, w20] ∗ F_tail ∗ H_sm ∗ H_ky ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_ky
  have hm_sub' := Satisfies.mono (sepConj_mono_left (sepConj_mono hpk_unp hver_unp)) hm_sub
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc] at hm_sub'
  rcases hm_sub' with ⟨w30, pkVal, hm_sub'⟩
  have hm_pure : m ⊨ ⌜optU32ValProp psm.preKeyId pkVal⌝ ∗ ⌜versionPadProp psm.messageVersion w30⌝ ∗
      (((src + 0x78#64) ↦₆₄ (pkVal ++ (if psm.preKeyId.isSome then 1#32 else 0#32))) ∗
        ((src + 0xf0#64) ↦₆₄ w30) ∗ words64At src W15 ∗
        words64At (src + 0x90#64) [w18, w19, w20] ∗ F_tail ∗ H_sm ∗ H_ky ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_sub'
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hpkVal, hvp, hm_pure⟩
  let w15 := pkVal ++ (if psm.preKeyId.isSome then 1#32 else 0#32)
  let w16 := g.serPtr
  let w17 := BitVec.ofNat 64 psm.serialized.length
  let w29 := psm.signedPreKeyId ++ psm.registrationId
  have hpair29 : ∀ a : BitVec 64,
      ((a + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((a + 0xec#64) ↦₃₂ psm.signedPreKeyId) =
        ((a + 0xe8#64) ↦₆₄ w29) := fun a => by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, w29] using
      pointsTo32_pair (a + 0xe8#64) psm.registrationId psm.signedPreKeyId
  have hwords31 : ∀ a : BitVec 64,
      words64At a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] =
      words64At a W15 ∗ ((a + 0x78#64) ↦₆₄ w15) ∗ ((a + 0x80#64) ↦₆₄ w16) ∗ ((a + 0x88#64) ↦₆₄ w17) ∗
        words64At (a + 0x90#64) [w18, w19, w20] ∗ words64At (a + 0xa8#64) [w21, w22, w23, w24] ∗
        words64At (a + 0xc8#64) [w25, w26, w27, w28] ∗
        ((a + 0xe8#64) ↦₆₄ w29) ∗ ((a + 0xf0#64) ↦₆₄ w30) := by
    intro a
    rw [show [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] =
        W15 ++ ([w15, w16, w17] ++ ([w18, w19, w20] ++ ([w21, w22, w23, w24] ++
          ([w25, w26, w27, w28] ++ [w29, w30])))) from rfl,
      words64At_append, words64At_append, words64At_append, words64At_append, words64At_append]
    simp only [W15, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd, words64At_3 (a + 120#64), words64At_2 (a + 232#64),
      sepConj_assoc]
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    H_sm ∗ Encrypt.boxU8Buf A g.serPtr psm.serialized ∗ H_ky, hw0, ?_, ?_⟩
  · dsimp only [F_tail] at hm_pure
    rw [boxU8At_eq_header_sep_buf, hbk (src + 0xa8#64), hik (src + 0xc8#64), hpair29 src] at hm_pure
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_pure
    rw [hwords31 src]
    exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_pure
  · intro dst
    unfold preKeyMsgAt
    rw [hwords31 dst, boxU8At_eq_header_sep_buf, hbk (dst + 0xa8#64), hik (dst + 0xc8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [← sepConj_assoc ((dst + 0xe8#64) ↦₃₂ psm.registrationId), hpair29 dst]
    have hpk_pack : ((dst + 0x78#64) ↦₆₄ w15) ⊢ optU32At (dst + 0x78#64) psm.preKeyId :=
      Entails.trans (Entails.pure_right hpkVal (Entails.refl _))
        (optU32At_pack64 (dst + 0x78#64) psm.preKeyId pkVal)
    have hver_pack : ((dst + 0xf0#64) ↦₆₄ w30) ⊢
        ((dst + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (dst + 0xf1#64) 7 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        Entails.trans (Entails.pure_right hvp (Entails.refl _))
          (versionPad_pack (dst + 0xf0#64) psm.messageVersion w30)
    refine Entails.trans (Entails.of_eq (show _ =
        (words64At dst W15 ∗ H_sm) ∗ ((dst + 0x78#64) ↦₆₄ w15) ∗
          (((dst + 0x80#64) ↦₆₄ w16) ∗ ((dst + 0x88#64) ↦₆₄ w17) ∗
            Encrypt.boxU8Buf A g.serPtr psm.serialized) ∗
          (words64At (dst + 0x90#64) [w18, w19, w20] ∗ H_ky) ∗
          words64At (dst + 0xa8#64) [w21, w22, w23, w24] ∗
          words64At (dst + 0xc8#64) [w25, w26, w27, w28] ∗
          ((dst + 0xe8#64) ↦₆₄ w29) ∗ ((dst + 0xf0#64) ↦₆₄ w30) by ac_rfl)) ?_
    exact sepConj_mono (hpack_sm dst)
      (sepConj_mono hpk_pack (sepConj_mono (Entails.refl _)
        (sepConj_mono (hpack_ky (dst + 0x90#64))
          (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
            (sepConj_mono_right hver_pack))))))

/-! ## Frame Unpack and Pack Helpers -/

def buildPreKeyMsgScratchRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 8#64) 0xc ∗ memRegion (sp + 0x18#64) 0xc ∗ memRegion (sp + 0x28#64) 0xc ∗
    ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
    ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

theorem preKeyEncryptScratch'_unpack (sp : BitVec 64) (regId spk pkVal : BitVec 32)
    {m : Memory} {R : SepProp} (hm : m ⊨ preKeyEncryptScratch' sp regId spk pkVal ∗ R) :
    ∃ u0 : BitVec 64,
      m ⊨ ((sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ regId) ∗
        ((sp + 0x24#64) ↦₃₂ spk) ∗ ((sp + 0x34#64) ↦₃₂ pkVal)) ∗ buildPreKeyMsgScratchRest sp ∗ R := by
  dsimp only [preKeyEncryptScratch', buildPreKeyMsgScratchRest] at hm ⊢
  rw [memRegion_split sp 8 0xc (by decide), ProofLib.memRegion_eight sp] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨u0, hm⟩ := hm
  exact ⟨u0, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm⟩

theorem preKeyEncryptScratch'_to_cmScratch (sp u0 : BitVec 64) (regId spk pkVal : BitVec 32) :
    (sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ regId) ∗
      ((sp + 0x24#64) ↦₃₂ spk) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp ⊢ cmScratch sp := by
  unfold buildPreKeyMsgScratchRest cmScratch
  have h38 : memRegion sp 0x38 =
      memRegion sp 8 ∗ memRegion (sp + 8#64) 0xc ∗ memRegion (sp + 0x14#64) 4 ∗
        memRegion (sp + 0x18#64) 0xc ∗ memRegion (sp + 0x24#64) 4 ∗
        memRegion (sp + 0x28#64) 0xc ∗ memRegion (sp + 0x34#64) 4 := by
    rw [memRegion_split sp 8 0x30 (by decide), mr_cut_add sp 8 0xc 0x24 (by decide),
        mr_cut_add sp 0x14 4 0x20 (by decide), mr_cut_add sp 0x18 0xc 0x14 (by decide),
        mr_cut_add sp 0x24 4 0x10 (by decide), mr_cut_add sp 0x28 0xc 4 (by decide)]
  rw [h38]
  refine Entails.trans (Entails.of_eq (show _ =
      ((sp ↦₆₄ u0) ∗ memRegion (sp + 8#64) 0xc ∗ ((sp + 0x14#64) ↦₃₂ regId) ∗
        memRegion (sp + 0x18#64) 0xc ∗ ((sp + 0x24#64) ↦₃₂ spk) ∗
        memRegion (sp + 0x28#64) 0xc ∗ ((sp + 0x34#64) ↦₃₂ pkVal)) ∗
        ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono (pointsTo64_entails_memRegion sp u0)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x14#64) regId)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x24#64) spk)
              (sepConj_mono (Entails.refl _)
                (pointsTo32_entails_memRegion (sp + 0x34#64) pkVal)))))))
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x48#64) (sp + 0xc0#64)) (Entails.refl _))))

def encCommonRest (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff img ∗
    memRegion ((s0.sp - 0xbe0#64) - BitVec.ofNat 64 encSubStack) (encSubStack - preKeyMsgNewStack) ∗
    encSavedRegs s0.sp s0

theorem encCommon_eq_preKeyMsg (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    encCommon A ctl img x draws s0 =
      A.pool ∗ stackAt (s0.sp - 0xbe0#64) preKeyMsgNewStack ∗ encCommonRest A ctl img x draws s0 := by
  unfold encCommon encCommonRest
  have hstk : stackAt (s0.sp - 0xbe0#64) encSubStack =
      memRegion ((s0.sp - 0xbe0#64) - BitVec.ofNat 64 encSubStack) (encSubStack - preKeyMsgNewStack) ∗
        stackAt (s0.sp - 0xbe0#64) preKeyMsgNewStack := by
    show memRegion ((s0.sp - 0xbe0#64) - BitVec.ofNat 64 encSubStack) encSubStack = _
    rw [mr_cut' (s0.sp - 0xbe0#64) encSubStack preKeyMsgNewStack (encSubStack - preKeyMsgNewStack)
      preKeyMsgNewStack encSubStack rfl rfl (by decide) (by decide) (by decide)]
  rw [hstk]; ac_rfl

def buildPreKeyMsgRestFrame {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (draws : Nat) (sp : BitVec 64) (H_sm H_ky : SepProp) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗ buildPreKeyMsgScratchRest sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 128 ∗
    memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x930#64) 0x20 ∗
    memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xad4#64) 0xc ∗
    memRegion (sp + 0xb20#64) 0x60 ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x draws s0 ∗ H_sm ∗ H_ky

theorem buildPreKeyMsg_pre_unpack {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' kyBoxPtr : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (sm : SignalMessage)
    (draws : Nat) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hm : s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0 ∗ R) :
    let kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)
    ∃ (msgG : SignalMessageGhost) (u0 ik0 ik1 ik2 ik3 : BitVec 64)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 : BitVec 64)
      (k0 k1 k2 kd0 kd1 kd2 bk0 bk1 bk2 bk3 bkd0 bkd1 bkd2 bkd3 ikd0 ikd1 ikd2 ikd3 : BitVec 64)
      (H_sm H_ky : SepProp),
      w0 + 1#64 ≠ 0#64 ∧ sm.serialized.length < 2 ^ 40 ∧
      (∀ a : BitVec 64,
        (a ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) = words64At a [ik0, ik1, ik2, ik3]) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ items.baseKey.bytes.toList) = words64At a [bk0, bk1, bk2, bk3]) ∧
      (∀ dst : BitVec 64,
        words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H_sm ⊢
          signalMessageAt A msgG dst sm) ∧
      (∀ dst : BitVec 64,
        words64At dst [k0, k1, k2] ∗ H_ky ⊢ optKyberAt A dst kyBoxPtr kp) ∧
      (s.mem ⊨
        ((sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
          ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
          words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
          words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          words64At (sp + 0x8a0#64) [k0, k1, k2] ∗
          words64At (sp + 0x8b8#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗
          words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗
          words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗
          words64At (sp + 0xae0#64) [bkd0, bkd1, bkd2, bkd3] ∗
          words64At (sp + 0xb00#64) [ikd0, ikd1, ikd2, ikd3]) ∗
        (buildPreKeyMsgRestFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
          H_sm H_ky s0 ∗ R)) := by
  intro kp
  obtain ⟨ik0, ik1, ik2, ik3, hik⟩ :=
    bytes32_exists_words64At (bs := otr'.localIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨bk0, bk1, bk2, bk3, hbk⟩ :=
    bytes32_exists_words64At (bs := items.baseKey.bytes.toList) (List.Vector.toList_length _)
  dsimp only [signalMessageResultAt] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨msgG, hm⟩ := hm
  rw [otrAt_eq_ik_ver_rest A sp pqCap' pqPtr' otr' ik0 ik1 ik2 ik3 hik, hbk (sp + 0xab4#64)] at hm
  have h5f8 : memRegion (sp + 0x5f8#64) 0x2a8 =
      memRegion (sp + 0x5f8#64) 128 ∗ memRegion (sp + 0x678#64) 0x228 :=
    mr_cut_add sp 0x5f8 128 0x228 (by decide)
  have h8b8 : memRegion (sp + 0x8b8#64) 0x1fc =
      memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x930#64) 0x20 ∗
        memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0x968#64) 0x14c := by
    rw [mr_cut_add sp 0x8b8 120 0x184 (by decide),
        mr_cut_add sp 0x930 0x20 0x164 (by decide), mr_cut_add sp 0x950 24 0x14c (by decide)]
  have had4 : memRegion (sp + 0xad4#64) 0xac =
      memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
        memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60 := by
    rw [mr_cut_add sp 0xad4 0xc 0xa0 (by decide),
        mr_cut_add sp 0xae0 32 0x80 (by decide), mr_cut_add sp 0xb00 32 0x60 (by decide)]
  rw [h5f8, h8b8, had4] at hm
  let F_rest :=
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 128 ∗
      memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x930#64) 0x20 ∗
      memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xad4#64) 0xc ∗
      memRegion (sp + 0xb20#64) 0x60 ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R
  have hm_scr : s.mem ⊨ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      (signalMessageAt A msgG (sp + 0x580#64) sm ∗ optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
        memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
        ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
        words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [F_rest]; ac_rfl)) hm
  obtain ⟨u0, hm_scr⟩ := preKeyEncryptScratch'_unpack sp sess.localRegistrationId items.signedPreKeyId pkVal hm_scr
  let S_sc := (sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
    ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
    words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
    words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3]
  have hm_sm : s.mem ⊨ signalMessageAt A msgG (sp + 0x580#64) sm ∗
      (optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
        memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        S_sc ∗ buildPreKeyMsgScratchRest sp ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [S_sc]; ac_rfl)) hm_scr
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    H_sm, hw0, hmsg_len, hm_sm, hpack_sm⟩ :=
    signalMessageAt_relocate A msgG (sp + 0x580#64) sm hm_sm
  let W_sm := words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
  have hm_ky : s.mem ⊨ optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
      (memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ S_sc ∗ H_sm ∗ buildPreKeyMsgScratchRest sp ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [W_sm]; ac_rfl)) hm_sm
  obtain ⟨k0, k1, k2, H_ky, hm_ky, hpack_ky⟩ :=
    optKyberAt_relocate A (sp + 0x8a0#64) kyBoxPtr kp hm_ky
  let F_e6d := buildPreKeyMsgRestFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
    H_sm H_ky s0 ∗ R
  have hm_d : s.mem ⊨ memRegion (sp + 0x8b8#64) 120 ∗
      (memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ S_sc ∗ F_e6d) := by
    dsimp only [F_e6d]; unfold buildPreKeyMsgRestFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [F_rest]; ac_rfl)) hm_ky
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, hm_d⟩ :=
    memRegion_120_exists_words15 (sp + 0x8b8#64) hm_d
  let W_d := words64At (sp + 0x8b8#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14]
  have hm_kd : s.mem ⊨ memRegion (sp + 0x950#64) 24 ∗
      (memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [W_d]; ac_rfl)) hm_d
  obtain ⟨kd0, kd1, kd2, hm_kd⟩ := memRegion_24_exists_words3 (sp + 0x950#64) hm_kd
  have hm_bkd : s.mem ⊨ memRegion (sp + 0xae0#64) 32 ∗
      (memRegion (sp + 0xb00#64) 32 ∗ W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_kd
  obtain ⟨bkd0, bkd1, bkd2, bkd3, hm_bkd⟩ := memRegion_32_exists_words4 (sp + 0xae0#64) hm_bkd
  have hm_ikd : s.mem ⊨ memRegion (sp + 0xb00#64) 32 ∗
      (W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗
        words64At (sp + 0xae0#64) [bkd0, bkd1, bkd2, bkd3] ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_bkd
  obtain ⟨ikd0, ikd1, ikd2, ikd3, hm_ikd⟩ := memRegion_32_exists_words4 (sp + 0xb00#64) hm_ikd
  refine ⟨msgG, u0, ik0, ik1, ik2, ik3,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    k0, k1, k2, kd0, kd1, kd2, bk0, bk1, bk2, bk3, bkd0, bkd1, bkd2, bkd3,
    ikd0, ikd1, ikd2, ikd3, H_sm, H_ky, hw0, hmsg_len, hik, hbk, hpack_sm, hpack_ky, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [S_sc, W_sm, W_d, F_e6d]; ac_rfl)) hm_ikd

theorem words64At_entails_mr (a : BitVec 64) (ws : List (BitVec 64)) (n : Nat)
    (hn : 8 * ws.length = n) (hb : n ≤ 2 ^ 64) :
    words64At a ws ⊢ memRegion a n :=
  hn ▸ Pf.SegFrom.words64At_entails_memRegion ws a (hn.symm ▸ hb)

theorem bytes32_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) ⊢ memRegion a 32 := by
  obtain ⟨w0, w1, w2, w3, heq⟩ := bytes32_exists_words64At h
  rw [heq a]
  exact words64At_entails_mr a [w0, w1, w2, w3] 32 rfl (by decide)

def preKeyMsgCallFrame {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (items : PendingPreKey) (pkVal : BitVec 32) (draws : Nat) (sp : BitVec 64) (s0 : State) :
    SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
    ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
    buildPreKeyMsgScratchRest sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x678#64) 0x228 ∗
    memRegion (sp + 0x8a0#64) 24 ∗ memRegion (sp + 0x930#64) 0x20 ∗
    memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
    memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗
    memRegion x.ret 248 ∗ encCommonRest A ctl img x draws s0

theorem preKeyMsgNew_pre_pack {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' kyBoxPtr : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32)
    (msgG : SignalMessageGhost) (sm : SignalMessage) (ik0 ik1 ik2 ik3 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (k0 k1 k2 bk0 bk1 bk2 bk3 : BitVec 64)
    (H_sm H_ky : SepProp) (draws : Nat) (sp : BitVec 64) (s0 s1 : State)
    (hsp_eq : sp = s0.sp - 0xbe0#64) (hs1_sp : s1.sp = sp)
    (hik : ∀ a : BitVec 64,
      (a ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) = words64At a [ik0, ik1, ik2, ik3])
    (hbk : ∀ a : BitVec 64,
      (a ↦ₛ items.baseKey.bytes.toList) = words64At a [bk0, bk1, bk2, bk3])
    (hsm_rel : ∀ dst : BitVec 64,
      words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H_sm ⊢
        signalMessageAt A msgG dst sm)
    (hky_rel : ∀ dst : BitVec 64,
      words64At dst [k0, k1, k2] ∗ H_ky ⊢
        optKyberAt A dst kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))) :
    ((sp ↦₆₄ (sp + 0x8b8#64)) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
      ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
      words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
      words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      words64At (sp + 0x8a0#64) [k0, k1, k2] ∗
      words64At (sp + 0x8b8#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      words64At (sp + 0x950#64) [k0, k1, k2] ∗ words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗
      words64At (sp + 0xae0#64) [bk0, bk1, bk2, bk3] ∗
      words64At (sp + 0xb00#64) [ik0, ik1, ik2, ik3]) ∗
      buildPreKeyMsgRestFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
        H_sm H_ky s0 ⊢
      ((s1.sp ↦₆₄ (sp + 0x8b8#64)) ∗
        optKyberAt A (sp + 0x950#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) ∗
        signalMessageAt A msgG (sp + 0x8b8#64) sm ∗
        memRegion (sp + 0x580#64) 248 ∗ A.pool ∗ stackAt s1.sp preKeyMsgNewStack) ∗
      preKeyMsgCallFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k
        items pkVal draws sp s0 := by
  rw [hs1_sp]
  unfold buildPreKeyMsgRestFrame preKeyMsgCallFrame
  have h580 : memRegion (sp + 0x580#64) 248 =
      memRegion (sp + 0x580#64) 120 ∗ memRegion (sp + 0x5f8#64) 128 :=
    mr_cut_add sp 0x580 120 128 (by decide)
  rw [encCommon_eq_preKeyMsg A ctl img x draws s0, ← hsp_eq,
      otrAt_eq_ik_ver_rest A sp pqCap' pqPtr' otr' ik0 ik1 ik2 ik3 hik,
      hbk (sp + 0xae0#64), hik (sp + 0xb00#64), h580]
  have hw_ret := words64At_entails_mr (sp + 0x580#64)
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] 120 rfl (by decide)
  have hw_8a0 := words64At_entails_mr (sp + 0x8a0#64) [k0, k1, k2] 24 rfl (by decide)
  have hw_ab4 := words64At_entails_mr (sp + 0xab4#64) [bk0, bk1, bk2, bk3] 32 rfl (by decide)
  refine Entails.trans (Entails.of_eq (show _ =
      ((words64At (sp + 0x950#64) [k0, k1, k2] ∗ H_ky) ∗
        (words64At (sp + 0x8b8#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H_sm) ∗
        words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3]) ∗
      ((sp ↦₆₄ (sp + 0x8b8#64)) ∗ words64At (sp + 0xae0#64) [bk0, bk1, bk2, bk3] ∗
        words64At (sp + 0xb00#64) [ik0, ik1, ik2, ik3] ∗ memRegion (sp + 0x5f8#64) 128 ∗
        A.pool ∗ stackAt sp preKeyMsgNewStack ∗
        sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        (words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
          ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗ otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗ ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗
        ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x678#64) 0x228 ∗
        memRegion (sp + 0x930#64) 0x20 ∗ memRegion (sp + 0x968#64) 0x14c ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗
        memRegion x.ret 248 ∗ encCommonRest A ctl img x draws s0) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left
      (sepConj_mono (hky_rel (sp + 0x950#64))
        (sepConj_mono (hsm_rel (sp + 0x8b8#64))
          (sepConj_mono hw_ret (sepConj_mono hw_8a0 hw_ab4))))) ?_
  exact Entails.of_eq (by ac_rfl)

def cmCopyRestFrame {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (draws : Nat) (sp : BitVec 64) (H_psm : SepProp) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x678#64) 0x2b8 ∗
    memRegion (sp + 0x948#64) 0x238 ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x draws s0 ∗ H_psm

theorem cmCopy_pre_unpack {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32)
    (psm : PreKeySignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hm2 : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) psm) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k
        items pkVal draws sp s0 ∗ R) :
    ∃ (psmG : PreKeyMsgGhost)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
        w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 v0 v1 v2 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20
        d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 : BitVec 64) (H_psm : SepProp),
      w0 + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
          w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
          H_psm ⊢ preKeyMsgAt A psmG dst psm) ∧
      (s2.mem ⊨
        (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
            w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
          words64At (sp + 0x930#64) [v0, v1, v2] ∗
          words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
            d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30]) ∗
        (cmCopyRestFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
          H_psm s0 ∗ R)) := by
  unfold preKeyMsgCallFrame at hm2
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨psmG, hm2⟩ := hm2
  have hcm := preKeyEncryptScratch'_to_cmScratch sp (sp + 0x8b8#64)
    sess.localRegistrationId items.signedPreKeyId pkVal
  have hbk_ae0 := bytes32_entails_memRegion (sp + 0xae0#64) items.baseKey.bytes.toList
    (List.Vector.toList_length _)
  have hik_b00 := bytes32_entails_memRegion (sp + 0xb00#64)
    otr'.localIdentityKey.publicKey.bytes.toList (List.Vector.toList_length _)
  let F_core :=
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗ memRegion x.ret 248 ∗ R
  have hm2_sub : s2.mem ⊨
      (((sp ↦₆₄ (sp + 0x8b8#64)) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
        ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp) ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList)) ∗
      (preKeyMsgAt A psmG (sp + 0x580#64) psm ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x8b8#64) 120 ∗
        (A.pool ∗ stackAt sp preKeyMsgNewStack ∗ encCommonRest A ctl img x draws s0) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗ memRegion (sp + 0x678#64) 0x228 ∗
        memRegion (sp + 0x8a0#64) 24 ∗ memRegion (sp + 0x930#64) 0x20 ∗
        memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗ F_core) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [F_core]; ac_rfl)) hm2
  have hm2_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hcm (sepConj_mono hbk_ae0 hik_b00))) hm2_sub
  have h930 : memRegion (sp + 0x930#64) 0x20 =
      memRegion (sp + 0x930#64) 24 ∗ memRegion (sp + 0x948#64) 8 :=
    mr_cut_add sp 0x930 24 8 (by decide)
  have henc_psm : A.pool ∗ stackAt sp preKeyMsgNewStack ∗ encCommonRest A ctl img x draws s0 =
      encCommon A ctl img x draws s0 := by
    rw [hsp_eq, ← encCommon_eq_preKeyMsg A ctl img x draws s0]
  rw [henc_psm, h930] at hm2_mono
  have hmerge_678 :
      memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗
        memRegion (sp + 0x8b8#64) 120 = memRegion (sp + 0x678#64) 0x2b8 := by
    rw [mr_cut_add sp 0x678 0x228 0x90 (by decide), mr_cut_add sp 0x8a0 24 120 (by decide)]
  have hmerge_948 :
      memRegion (sp + 0x948#64) 8 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
        memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60 =
      memRegion (sp + 0x948#64) 0x238 := by
    rw [mr_cut_add sp 0x948 8 0x230 (by decide), mr_cut_add sp 0x950 24 0x218 (by decide),
        mr_cut_add sp 0x968 0x14c 0xcc (by decide), mr_cut_add sp 0xab4 32 0xac (by decide),
        mr_cut_add sp 0xad4 0xc 0xa0 (by decide), mr_cut_add sp 0xae0 32 0x80 (by decide),
        mr_cut_add sp 0xb00 32 0x60 (by decide)]
  have hm2_merged : s2.mem ⊨
      preKeyMsgAt A psmG (sp + 0x580#64) psm ∗
      (memRegion (sp + 0x930#64) 24 ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        (memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗
          memRegion (sp + 0x8b8#64) 120) ∗
        (memRegion (sp + 0x948#64) 8 ∗ memRegion (sp + 0x950#64) 24 ∗
          memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
          memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
          memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60) ∗
        cmScratch sp ∗ encCommon A ctl img x draws s0 ∗ F_core) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm2_mono
  rw [hmerge_678, hmerge_948] at hm2_merged
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    H_psm, hw0, hm2_psm, hpsm_rel⟩ :=
    preKeyMsgAt_relocate A psmG (sp + 0x580#64) psm hm2_merged
  let W_psm := words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]
  let F_e6e := cmCopyRestFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
    H_psm s0 ∗ R
  have hm2_930 : s2.mem ⊨ memRegion (sp + 0x930#64) 24 ∗
      (memRegion (sp + 0x370#64) 0xf8 ∗ W_psm ∗ F_e6e) := by
    dsimp only [W_psm, F_e6e]; unfold cmCopyRestFrame
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [F_core]; ac_rfl)) hm2_psm
  obtain ⟨v0, v1, v2, hm2_930⟩ := memRegion_24_exists_words3 (sp + 0x930#64) hm2_930
  have hm2_370 : s2.mem ⊨ memRegion (sp + 0x370#64) 248 ∗
      (W_psm ∗ words64At (sp + 0x930#64) [v0, v1, v2] ∗ F_e6e) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm2_930
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, hm2_370⟩ :=
    memRegion_248_exists_words31 (sp + 0x370#64) hm2_370
  exact ⟨psmG, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30,
    H_psm, hw0, hpsm_rel, Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [W_psm, F_e6e]; ac_rfl)) hm2_370⟩

theorem cmCopy_post_pack {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (psmG : PreKeyMsgGhost) (psm : PreKeySignalMessage)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
      w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : BitVec 64)
    (H_psm : SepProp) (draws : Nat) (sp : BitVec 64) (s0 : State)
    (hpsm_rel : ∀ dst : BitVec 64,
      words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
        w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        H_psm ⊢ preKeyMsgAt A psmG dst psm) :
    (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
      words64At (sp + 0x930#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]) ∗
      cmCopyRestFrame kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
        H_psm s0 ⊢
    cmSlots A sp sess taken otr' pqCap' pqPtr' k (.preKeySignalMessage psm) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0 := by
  unfold cmCopyRestFrame cmSlots takenSlots
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ⊢
        ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) :=
    Entails.sepExists_right ⟨prevCap, prevPtr, some G⟩ (Entails.refl _)
  have hcm_msg :
      words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        H_psm ⊢ apiEncResultAt A (sp + 0x370#64) (.ok (.preKeySignalMessage psm)) :=
    Entails.sepExists_right psmG (hpsm_rel (sp + 0x370#64))
  have hw_580 := words64At_entails_mr (sp + 0x580#64)
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
      w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]
    0xf8 rfl (by decide)
  have hw_930 := words64At_entails_mr (sp + 0x930#64) [w4, w5, w6] 24 rfl (by decide)
  have hmerge_46a :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 0xf8 ∗
        memRegion (sp + 0x678#64) 0x2b8 ∗ memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x948#64) 0x238 := by
    rw [mr_cut_add sp 0x46a 0x116 0x600 (by decide), mr_cut_add sp 0x580 0xf8 0x508 (by decide),
        mr_cut_add sp 0x678 0x2b8 0x250 (by decide), mr_cut_add sp 0x930 24 0x238 (by decide)]
  rw [hmerge_46a]
  refine Entails.trans (Entails.of_eq (show _ =
      (sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        (words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
          H_psm) ∗
        words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        words64At (sp + 0x930#64) [w4, w5, w6]) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x678#64) 0x2b8 ∗ memRegion (sp + 0x948#64) 0x238 ∗
        memRegion x.ret 248 ∗ encCommon A ctl img x draws s0) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono hrec_ex (sepConj_mono hcm_msg (sepConj_mono hw_580 hw_930)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem kyber_ciphertext_length_lt {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} (hr : RecordInScopeEnc r) (hcur : r.currentSession = some sess) :
    ∀ k, (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) = some k →
      k.ciphertext.length < 2 ^ 32 := by
  intro k hk
  rw [Option.map_eq_some_iff] at hk
  rcases hk with ⟨pk, hpk_some, rfl⟩
  exact (hr sess hcur).2.2.2 pk hpk_some

set_option linter.unusedVariables false in
/-- From `PreKeyEncryptRetState` at `+0x8c8` on `OTR::encrypt = .ok sm`, calls
`PreKeySignalMessage::new` and copies the 248-byte result to `sp + 0x370`, reaching `CmState` at
`+0xa70`. -/
theorem segPreKey_buildMessage_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (sm : SignalMessage)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hok : ((preKeyOtrGhost (s0.sp - 0xbe0#64 |> fun sp => x) (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm)
    (hret : PreKeyEncryptRetState kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          R s0 sf) := by
  rcases hret with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx22, hx24, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp_eq : sp = s0.sp - 0xbe0#64 := rfl
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have hok' : res.1 = .ok sm := hok
  have hentry : encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName :=
    encEntry_eq_fnAddr env
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x8c8#64 := by
    rw [hs_pc, hentry]
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  let R' := encStoreExtra kit st0 ikit ist0 x s0 ∗ R
  change s.mem ⊨
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
    signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
    optKyberAt A (sp + 0x8a0#64) kyBoxPtr
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
    memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗ R' at hm
  rw [hok'] at hm
  obtain ⟨msgG, u0, ik0, ik1, ik2, ik3,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    k0, k1, k2, kd0, kd1, kd2, bk0, bk1, bk2, bk3, bkd0, bkd1, bkd2, bkd3,
    ikd0, ikd1, ikd2, ikd3, H_sm, H_ky, hw0, hmsg_len, hik, hbk, hsm_rel, hky_rel, hm_e6d⟩ :=
    buildPreKeyMsg_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
      items pkVal sm (S.draws otr.pqrState x.rest) sp R' s0 s hm
  refine Pf.SegFrom.SegExit.of_sepWP hm_e6d
    (buildPreKeyMsg_step_bl hs_pc' hrun hsp hal hx22 hx25 hx26 hx29' hw0) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8,
      hs1_x19, hs1_x20, hs1_x22, _, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have ⟨hfl1, hsym1⟩ := Pf.SegFrom.callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = encEntry img + 18446744073709389144#64 := by
    rw [hs1_pc, hentry]
  let call : PreKeyMsgNewCall :=
    { ret := sp + 0x580#64, ver := res.2.sessionVersion, regId := sess.localRegistrationId,
      preKeyId := items.preKeyId, spk := items.signedPreKeyId, kyA := sp + 0x950#64,
      kyPtr := kyBoxPtr,
      kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload),
      bkA := sp + 0xae0#64, baseKey := items.baseKey, ikA := sp + 0xb00#64,
      ik := res.2.localIdentityKey, msgA := sp + 0x8b8#64, msgG := msgG, msg := sm }
  have hm1_sub : s1.mem ⊨
      (Pm1 ∗ buildPreKeyMsgRestFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp H_sm H_ky s0) ∗ R' :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1
  have hm1_pack := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm1)
        (preKeyMsgNew_pre_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
          items pkVal msgG sm ik0 ik1 ik2 ik3
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
          k0 k1 k2 bk0 bk1 bk2 bk3 H_sm H_ky (S.draws otr.pqrState x.rest) sp s0 s1
          hsp_eq hs1_sp hik hbk hsm_rel hky_rel)))
    hm1_sub
  have hcall_len : call.model.serialized.length < 2 ^ 42 :=
    call.model_serialized_length_lt hmsg_len
      (kyber_ciphertext_length_lt (env.scopeIn r hscope) hcur)
  have hcall_pure :
      (s1.readReg64 .x0).setWidth 8 = call.ver ∧ (s1.readReg64 .x1).setWidth 32 = call.regId ∧
      (s1.readReg64 .x2).setWidth 32 = (if call.preKeyId.isSome then 1#32 else 0#32) ∧
      (∀ v, call.preKeyId = some v → (s1.readReg64 .x3).setWidth 32 = v) ∧
      (s1.readReg64 .x4).setWidth 32 = call.spk ∧ s1.readReg64 .x5 = call.kyA ∧
      s1.readReg64 .x6 = call.bkA ∧ s1.readReg64 .x7 = call.ikA ∧
      s1.readReg64 .x8 = call.ret ∧ call.model.serialized.length < 2 ^ 42 :=
    ⟨hs1_x0, hs1_x1, hs1_x2.trans hx24, fun v hv => hs1_x3.trans (hpkVal v hv),
      hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8, hcall_len⟩
  have hm1_pre : s1.mem ⊨ (preKeyMsgNewSpec A).pre call s1 ∗
      (preKeyMsgCallFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R') := by
    unfold preKeyMsgNewSpec
    dsimp only [call]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcall_pure, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1_pack⟩
  have hpref01 : s0.trace <+: s1.trace := by
    rw [hs1_tr, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩
  refine Pf.SegFrom.SegExit.call (preKeyMsgNew_ok_at_enc env) call hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (preKeyMsgNewSpec A).onExit call code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      have hp : sf.mem ⊨ (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗
          (preKeyMsgCallFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
            items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ encStoreExtra kit st0 ikit ist0 x s0) ∗ R := by
        dsimp only [preKeyMsgNewSpec, R'] at hpost; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
      exact onPanic_of_alloc hpref01 hp)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := Pf.SegFrom.callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x22 : s2.readReg64 .x22 = sp + 0x8b8#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  unfold preKeyMsgNewSpec at hpost2
  dsimp only [call] at hpost2
  rw [hs1_sp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost2
  rcases hpost2 with ⟨hs2_tr, hm2⟩
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  have hm2' : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) call.model) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ res.2.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R' :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm2
  obtain ⟨psmG,
    pw0, pw1, pw2, pw3, pw4, pw5, pw6, pw7, pw8, pw9, pw10, pw11, pw12, pw13, pw14,
    pw15, pw16, pw17, pw18, pw19, pw20, pw21, pw22, pw23, pw24, pw25, pw26, pw27, pw28, pw29, pw30,
    v0, v1, v2,
    pd0, pd1, pd2, pd3, pd4, pd5, pd6, pd7, pd8, pd9, pd10, pd11, pd12, pd13, pd14,
    pd15, pd16, pd17, pd18, pd19, pd20, pd21, pd22, pd23, pd24, pd25, pd26, pd27, pd28, pd29, pd30,
    H_psm, hpw0, hpsm_rel, hm2_e6e⟩ :=
    cmCopy_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
      items pkVal call.model (S.draws otr.pqrState x.rest) sp R' s0 s2 hsp_eq hm2'
  refine Pf.SegFrom.SegExit.of_sepWP hm2_e6e
    (cmCopy_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x22 hs2_x25 hpw0) ?_
  intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := Pf.SegFrom.callInv_steps hfl2 hsym2 hsteps23 hL2
  have hs3_al : s3.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_sub : s3.mem ⊨
      (Pm3 ∗ cmCopyRestFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp H_psm s0) ∗ R' :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm3
  have hm3_cm := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm3)
        (cmCopy_post_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
          psmG call.model
          pw0 pw1 pw2 pw3 pw4 pw5 pw6 pw7 pw8 pw9 pw10 pw11 pw12 pw13 pw14
          pw15 pw16 pw17 pw18 pw19 pw20 pw21 pw22 pw23 pw24 pw25 pw26 pw27 pw28 pw29 pw30
          H_psm (S.draws otr.pqrState x.rest) sp s0 hpsm_rel)))
    hm3_sub
  have hsteps15 := stepsThroughEncrypt_of_preKey_ok hcur hscope hfrom hrem hpk hts hexp hlt hok'
  refine Pf.SegFrom.SegExit.next ⟨.preKeySignalMessage call.model, res.2, pqCap', pqPtr',
    hsteps15, ?_⟩
  refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
      hs3_vregs.trans ((hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs))⟩,
    hs3_tr.trans hs2_tr', ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩,
    hpt, hrest, hloc, hnow, hstk,
    Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [sp, call, PreKeyMsgNewCall.model, R']; ac_rfl)) hm3_cm⟩
  rw [hs3_pc, cmPC, hentry]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
