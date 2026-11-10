/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S1Sym
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem s1_err_stack_recombine (sp remA tag w0 w1 w2 w3 w4 : BitVec 64) :
    (memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ remA) ∗
     memRegion (sp + 0x38#64) 0x158 ∗
     ((sp + 0x190#64) ↦₆₄ errTag) ∗
     ((sp + 0x198#64) ↦₆₄ tag) ∗
     words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x1c8#64) 208 ∗
     memRegion (sp + 0x298#64) 0x268 ∗
     ((sp + 0x500#64) ↦₆₄ tag) ∗
     words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x530#64) 0x50) ⊢
    memRegion sp 1408 := by
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x30#64) remA)
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x190#64) errTag)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x198#64) tag)
      (sepConj_mono (words5At_entails_memRegion (sp + 0x1a0#64) w0 w1 w2 w3 w4)
      (sepConj_mono_right
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x500#64) tag)
      (sepConj_mono_left (words5At_entails_memRegion (sp + 0x508#64) w0 w1 w2 w3 w4))))))))))) ?_
  rw [show sp + 0x530#64 = (sp + 0x508#64) + 40#64 by bv_omega,
      ← memRegion_split (sp + 0x508#64) 40 0x50 (by decide),
      show sp + 0x508#64 = (sp + 0x500#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x500#64) 8 120 (by decide),
      show sp + 0x500#64 = (sp + 0x298#64) + BitVec.ofNat 64 0x268 by bv_omega,
      ← memRegion_split (sp + 0x298#64) 0x268 128 (by decide),
      show sp + 0x298#64 = (sp + 0x1c8#64) + 208#64 by bv_omega,
      ← memRegion_split (sp + 0x1c8#64) 208 744 (by decide),
      show sp + 0x1c8#64 = (sp + 0x1a0#64) + 40#64 by bv_omega,
      ← memRegion_split (sp + 0x1a0#64) 40 952 (by decide),
      show sp + 0x1a0#64 = (sp + 0x198#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x198#64) 8 992 (by decide),
      show sp + 0x198#64 = (sp + 0x190#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 8 1000 (by decide),
      show sp + 0x190#64 = (sp + 0x38#64) + BitVec.ofNat 64 0x158 by bv_omega,
      ← memRegion_split (sp + 0x38#64) 0x158 1008 (by decide),
      show sp + 0x38#64 = (sp + 0x30#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x30#64) 8 1352 (by decide),
      ← memRegion_split sp 0x30 1360 (by decide)]
  exact Entails.refl _

def signalMessageNoCounterAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_eq_counter_rest (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x68#64) ↦₃₂ m.counter) ∗ signalMessageNoCounterAt A g a m := by
  unfold signalMessageAt signalMessageNoCounterAt; ac_rfl

theorem exists_words32_of_trBodyAt {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {p : BitVec 64} {R : SepProp} {m : Memory}
    (hpad : trG.ratchet.senderPad.length = 100)
    (hm : m ⊨ trBodyAt p trG tr ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
       w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64)
      (H_tr : SepProp),
      (m ⊨ (words32At p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
              w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗ R) ∧
      (∀ q : BitVec 64,
        words32At q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr ⊢
        trBodyAt q trG tr) := by
  obtain ⟨bs, H_tr, hlen, hm', hent⟩ := relocBytes_trBodyAt trG tr hpad p R m hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, hwords⟩ :=
    exists_words32_of_length_256 hlen
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
    H_tr, by rwa [← hwords p], fun q => ?_⟩
  rw [← hwords q]
  exact hent q

theorem exists_words32_of_memRegion_256 {p : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion p 256 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64,
      m ⊨ words32At p d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗ R := by
  rw [memRegion_eq_exists_bytes p 256 (by decide), sepExists_sepConj_left,
      satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, hwords⟩ :=
    exists_words32_of_length_256 hlen
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    by rwa [← hwords p]⟩



namespace BS9

theorem elim_exists_words32_of_trBodyAt {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {p : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hpad : trG.ratchet.senderPad.length = 100)
    (hm : m ⊨ trBodyAt p trG tr ∗ R)
    (k : ∀ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64)
      (H_tr : SepProp),
      (m ⊨ (words32At p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
              w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗ R) →
      (∀ q : BitVec 64,
        words32At q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr ⊢
        trBodyAt q trG tr) → P) : P :=
  let ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
    H_tr, hm_w, hent_tr⟩ := exists_words32_of_trBodyAt hpad hm
  k w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr

theorem elim_exists_words32_of_memRegion_256 {p : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hm : m ⊨ memRegion p 256 ∗ R)
    (k : ∀ (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64),
      (m ⊨ words32At p d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗ R) → P) : P :=
  let ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, hm'⟩ :=
    exists_words32_of_memRegion_256 hm
  k d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 hm'

end BS9

theorem s1_ok_stack_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗ R) :
    ∃ (g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
       d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64)
      (g28 : BitVec 32) (g2ac : BitVec 8),
      m ⊨
        (((sp + 0x20#64) ↦₆₄ g20) ∗
         ((sp + 0x28#64) ↦₃₂ g28) ∗
         ((sp + 0x38#64) ↦₆₄ d_cap) ∗
         words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
         ((sp + 0x2ac#64) ↦₈ g2ac) ∗
         words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
         ((sp + 0x520#64) ↦₆₄ t4) ∗
         ((sp + 0x528#64) ↦₆₄ t5)) ∗
        (memRegion sp 0x20 ∗
         memRegion (sp + 0x2c#64) 4 ∗
         memRegion (sp + 0x140#64) 0x50 ∗
         memRegion (sp + 0x298#64) 8 ∗
         memRegion (sp + 0x2a8#64) 4 ∗
         memRegion (sp + 0x2ad#64) 0x253 ∗
         memRegion (sp + 0x530#64) 0x50) ∗ R := by
  rw [memRegion_split sp 0x20 0x10 (by decide),
      memRegion_split (sp + 0x20#64) 8 8 (by decide),
      show (sp + 0x20#64) + 8#64 = sp + 0x28#64 by bv_omega,
      memRegion_split (sp + 0x28#64) 4 4 (by decide),
      show (sp + 0x28#64) + 4#64 = sp + 0x2c#64 by bv_omega,
      memRegion_split (sp + 0x38#64) 8 0x150 (by decide),
      show (sp + 0x38#64) + 8#64 = sp + 0x40#64 by bv_omega,
      memRegion_split (sp + 0x40#64) 256 0x50 (by decide),
      show (sp + 0x40#64) + 256#64 = sp + 0x140#64 by bv_omega,
      memRegion_split (sp + 0x298#64) 8 0x2e0 (by decide),
      show (sp + 0x298#64) + 8#64 = sp + 0x2a0#64 by bv_omega,
      memRegion_split (sp + 0x2a0#64) 8 0x2d8 (by decide),
      show (sp + 0x2a0#64) + 8#64 = sp + 0x2a8#64 by bv_omega,
      memRegion_split (sp + 0x2a8#64) 4 0x2d4 (by decide),
      show (sp + 0x2a8#64) + 4#64 = sp + 0x2ac#64 by bv_omega,
      memRegion_split (sp + 0x2ac#64) 1 0x2d3 (by decide),
      show (sp + 0x2ac#64) + 1#64 = sp + 0x2ad#64 by bv_omega,
      memRegion_split (sp + 0x2ad#64) 0x253 0x80 (by decide),
      show (sp + 0x2ad#64) + BitVec.ofNat 64 0x253 = sp + 0x500#64 by bv_omega,
      memRegion_split (sp + 0x500#64) 48 0x50 (by decide),
      show (sp + 0x500#64) + 48#64 = sp + 0x530#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 0x20#64) 8 ∗
      (memRegion (sp + 0x28#64) 4 ∗
       memRegion (sp + 0x38#64) 8 ∗
       memRegion (sp + 0x40#64) 256 ∗
       memRegion (sp + 0x2a0#64) 8 ∗
       memRegion (sp + 0x2ac#64) 1 ∗
       memRegion (sp + 0x500#64) 48 ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨g20, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : m ⊨ memRegion (sp + 0x28#64) 4 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       memRegion (sp + 0x38#64) 8 ∗
       memRegion (sp + 0x40#64) 256 ∗
       memRegion (sp + 0x2a0#64) 8 ∗
       memRegion (sp + 0x2ac#64) 1 ∗
       memRegion (sp + 0x500#64) 48 ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨g28, hm2⟩ := exists_word32_of_memRegion_4 hm2
  have hm3 : m ⊨ memRegion (sp + 0x38#64) 8 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       memRegion (sp + 0x40#64) 256 ∗
       memRegion (sp + 0x2a0#64) 8 ∗
       memRegion (sp + 0x2ac#64) 1 ∗
       memRegion (sp + 0x500#64) 48 ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨d_cap, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm4 : m ⊨ memRegion (sp + 0x40#64) 256 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       memRegion (sp + 0x2a0#64) 8 ∗
       memRegion (sp + 0x2ac#64) 1 ∗
       memRegion (sp + 0x500#64) 48 ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine BS9.elim_exists_words32_of_memRegion_256 hm4
    fun d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 hm4 => ?_
  have hm5 : m ⊨ memRegion (sp + 0x2a0#64) 8 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       memRegion (sp + 0x2ac#64) 1 ∗
       memRegion (sp + 0x500#64) 48 ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨g2a0, hm5⟩ := exists_word64_of_memRegion_8 hm5
  have hm6 : m ⊨ memRegion (sp + 0x2ac#64) 1 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
       memRegion (sp + 0x500#64) 48 ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  obtain ⟨g2ac, hm6⟩ := exists_word8_of_memRegion_1 hm6
  have hm7 : m ⊨ memRegion (sp + 0x500#64) 48 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
       ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       (memRegion sp 0x20 ∗
        memRegion (sp + 0x2c#64) 4 ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x298#64) 8 ∗
        memRegion (sp + 0x2a8#64) 4 ∗
        memRegion (sp + 0x2ad#64) 0x253 ∗
        memRegion (sp + 0x530#64) 0x50) ∗ R) := by
    convert hm6 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, t3, t4, t5, hm7⟩ := exists_words6_of_memRegion_48 hm7
  have h500 :
      (((sp + 0x500#64) ↦₆₄ t0) ∗ words5At (sp + 0x500#64 + 8#64) t1 t2 t3 t4 t5) =
      (words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗
       ((sp + 0x528#64) ↦₆₄ t5)) := by
    unfold words5At words4At
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [h500] at hm7
  refine ⟨g20, d_cap, g2a0, t0, t1, t2, t3, t4, t5,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    g28, g2ac, ?_⟩
  convert hm7 using 1; sep_ac_rfl


namespace BS9

theorem elim_s1_ok_stack_extract {sp : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hm : m ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗ R)
    (k : ∀ (g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
       d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64)
      (g28 : BitVec 32) (g2ac : BitVec 8),
      (m ⊨
        (((sp + 0x20#64) ↦₆₄ g20) ∗
         ((sp + 0x28#64) ↦₃₂ g28) ∗
         ((sp + 0x38#64) ↦₆₄ d_cap) ∗
         words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
         ((sp + 0x2ac#64) ↦₈ g2ac) ∗
         words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
         ((sp + 0x520#64) ↦₆₄ t4) ∗
         ((sp + 0x528#64) ↦₆₄ t5)) ∗
        (memRegion sp 0x20 ∗
         memRegion (sp + 0x2c#64) 4 ∗
         memRegion (sp + 0x140#64) 0x50 ∗
         memRegion (sp + 0x298#64) 8 ∗
         memRegion (sp + 0x2a8#64) 4 ∗
         memRegion (sp + 0x2ad#64) 0x253 ∗
         memRegion (sp + 0x530#64) 0x50) ∗ R) → P) : P :=
  let ⟨g20, d_cap, g2a0, t0, t1, t2, t3, t4, t5,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    g28, g2ac, hm_stk2⟩ := s1_ok_stack_extract hm
  k g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
    g28 g2ac hm_stk2

end BS9

theorem s1_ok_stack_recombine (sp cap remA : BitVec 64) (b2ac : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    (memRegion (sp + 0x140#64) 0x50 ∗
     ((sp + 0x190#64) ↦₆₄ cap) ∗
     words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
       w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
     memRegion (sp + 0x298#64) 8 ∗
     ((sp + 0x2a0#64) ↦₆₄ remA) ∗
     memRegion (sp + 0x2a8#64) 4 ∗
     ((sp + 0x2ac#64) ↦₈ b2ac) ∗
     memRegion (sp + 0x2ad#64) 0x253 ∗
     words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
     ((sp + 0x520#64) ↦₆₄ w4) ∗
     ((sp + 0x528#64) ↦₆₄ w5) ∗
     memRegion (sp + 0x530#64) 0x50) ⊢
    memRegion (sp + 0x140#64) 0x440 := by
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x190#64) cap)
      (sepConj_mono
        (words32At_entails_memRegion (sp + 0x198#64)
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31)
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x2a0#64) remA)
      (sepConj_mono_right
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 0x2ac#64) b2ac)
      (sepConj_mono_right
      (sepConj_mono (words4At_entails_memRegion (sp + 0x500#64) w0 w1 w2 w3)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x520#64) w4)
      (sepConj_mono_left (pointsTo64_entails_memRegion (sp + 0x528#64) w5)))))))))))) ?_
  rw [show sp + 0x530#64 = (sp + 0x528#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x528#64) 8 0x50 (by decide),
      show sp + 0x528#64 = (sp + 0x520#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x520#64) 8 88 (by decide),
      show sp + 0x520#64 = (sp + 0x500#64) + 32#64 by bv_omega,
      ← memRegion_split (sp + 0x500#64) 32 96 (by decide),
      show sp + 0x500#64 = (sp + 0x2ad#64) + BitVec.ofNat 64 0x253 by bv_omega,
      ← memRegion_split (sp + 0x2ad#64) 0x253 128 (by decide),
      show sp + 0x2ad#64 = (sp + 0x2ac#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 0x2ac#64) 1 723 (by decide),
      show sp + 0x2ac#64 = (sp + 0x2a8#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x2a8#64) 4 724 (by decide),
      show sp + 0x2a8#64 = (sp + 0x2a0#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x2a0#64) 8 728 (by decide),
      show sp + 0x2a0#64 = (sp + 0x298#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x298#64) 8 736 (by decide),
      show sp + 0x298#64 = (sp + 0x198#64) + 256#64 by bv_omega,
      ← memRegion_split (sp + 0x198#64) 256 744 (by decide),
      show sp + 0x198#64 = (sp + 0x190#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 8 1000 (by decide),
      show sp + 0x190#64 = (sp + 0x140#64) + BitVec.ofNat 64 0x50 by bv_omega,
      ← memRegion_split (sp + 0x140#64) 0x50 1008 (by decide)]
  exact Entails.refl _

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
