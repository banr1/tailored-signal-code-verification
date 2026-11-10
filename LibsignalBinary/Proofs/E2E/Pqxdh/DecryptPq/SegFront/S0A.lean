/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
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

theorem exists_localGroupA_of_memRegion_32 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8),
      m ⊨ localGroupA a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗ R := by
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, heq⟩ := exists_localGroupA_of_length_32 hlen
  exact ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, heq a ▸ hm⟩

theorem exists_remoteGroupC_of_memRegion_32 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      BitVec 8)
      (w3 : BitVec 64) (b31 : BitVec 8),
      (∀ q : BitVec 64,
        remoteGroupC q w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3
          b31 ⊢
          memRegion q 32) ∧
      m ⊨ remoteGroupC a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 ∗ R := by
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
      b22, w3, b31, heq⟩ :=
    exists_remoteGroupC_of_length_32 hlen
  refine ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
      b22, w3, b31,
    fun q => ?_, heq a ▸ hm⟩
  rw [← heq q, ← hlen]
  exact pointsToBytes_entails_memRegion q bs

def sessionStateRestAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_eq_ik_rest (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      vecGhostAt A G.localIk ss ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      sessionStateRestAt A ss G st := by
  unfold sessionStateAt sessionStateRestAt
  ac_rfl

theorem sessionStateAt_ik_facts {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ sessionStateAt A ss G st ∗ R) :
    PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) := by
  unfold sessionStateAt at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact ⟨hm.1.1, hm.1.2.1⟩

theorem exists_words4_of_memRegion_32 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ r0 r1 r2 r3 : BitVec 64, m ⊨ words4At a r0 r1 r2 r3 ∗ R := by
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨r0, r1, r2, r3, heq⟩ := exists_words4_of_length_32 hlen
  exact ⟨r0, r1, r2, r3, heq a ▸ hm⟩

theorem exists_words8_of_memRegion_64 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 64 ∗ R) :
    ∃ r4 r5 r6 r7 r8 r9 r10 r11 : BitVec 64,
      m ⊨ words8At a r4 r5 r6 r7 r8 r9 r10 r11 ∗ R := by
  rw [memRegion_eq_exists_bytes a 64 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, heq⟩ := exists_words8_of_length_64 hlen
  exact ⟨r4, r5, r6, r7, r8, r9, r10, r11, heq a ▸ hm⟩

theorem tryDecryptStack_split_prologue (sp0 : BitVec 64) :
    let sp := sp0 - 1504#64
    stackAt sp0 rootStack =
      memRegion (sp0 - 96#64) 32 ∗
      memRegion (sp0 - 64#64) 64 ∗
      memRegion sp 8 ∗
      memRegion (sp + 8#64) 40 ∗
      memRegion (sp + 48#64) 8 ∗
      memRegion (sp + 56#64) 344 ∗
      memRegion (sp + 400#64) 33 ∗
      memRegion (sp + 433#64) 975 ∗
      stackAt sp localIdentityKeyStack ∗
      memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) := by
  dsimp only
  rw [stackAt_sub sp0 1504 rootStack (by decide) (by decide)]
  have hsub : memRegion (sp0 - BitVec.ofNat 64 rootStack) (rootStack - 1504) =
      stackAt (sp0 - 1504#64) tryDecryptSubStack := by
    unfold stackAt tryDecryptSubStack tryDecryptFrameSize rootStack
    exact congrArg (fun a => memRegion a (262144 - 1504)) (by bv_omega)
  rw [hsub, stackAt_tryDecryptSubStack_sub sp0 localIdentityKeyStack (by decide)]
  unfold stackAt
  change memRegion (sp0 - 1504#64) 1504 ∗
      (memRegion (sp0 - 1504#64 - BitVec.ofNat 64 localIdentityKeyStack) localIdentityKeyStack ∗
       memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) = _
  rw [memRegion_split (sp0 - 1504#64) 1408 96 (by decide),
      show sp0 - 1504#64 + 1408#64 = sp0 - 96#64 by bv_omega,
      memRegion_split (sp0 - 96#64) 32 64 (by decide),
      show sp0 - 96#64 + 32#64 = sp0 - 64#64 by bv_omega,
      memRegion_split (sp0 - 1504#64) 8 1400 (by decide),
      memRegion_split (sp0 - 1504#64 + 8#64) 40 1360 (by decide),
      show sp0 - 1504#64 + 8#64 + 40#64 = sp0 - 1504#64 + 48#64 by bv_omega,
      memRegion_split (sp0 - 1504#64 + 48#64) 8 1352 (by decide),
      show sp0 - 1504#64 + 48#64 + 8#64 = sp0 - 1504#64 + 56#64 by bv_omega,
      memRegion_split (sp0 - 1504#64 + 56#64) 344 1008 (by decide),
      show sp0 - 1504#64 + 56#64 + 344#64 = sp0 - 1504#64 + 400#64 by bv_omega,
      memRegion_split (sp0 - 1504#64 + 400#64) 33 975 (by decide),
      show sp0 - 1504#64 + 400#64 + 33#64 = sp0 - 1504#64 + 433#64 by bv_omega]
  sep_ac_rfl

theorem s0_prologue_extract {sp0 : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ stackAt sp0 rootStack ∗ R) :
    let sp := sp0 - 1504#64
    ∃ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48 : BitVec 64,
      m ⊨ (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗
           words8At (sp0 - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
           (sp ↦₆₄ w_sp0) ∗
           ((sp + 48#64) ↦₆₄ w_sp48) ∗
           memRegion (sp + 400#64) 33 ∗
           stackAt sp localIdentityKeyStack) ∗
          (memRegion (sp + 8#64) 40 ∗
           memRegion (sp + 56#64) 344 ∗
           memRegion (sp + 433#64) 975 ∗
           memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R) := by
  dsimp only
  let sp := sp0 - 1504#64
  rw [tryDecryptStack_split_prologue sp0] at hm
  have hm1 : m ⊨ memRegion (sp0 - 96#64) 32 ∗
      (memRegion (sp0 - 64#64) 64 ∗ memRegion sp 8 ∗ memRegion (sp + 48#64) 8 ∗
       memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, hm1⟩ := exists_words4_of_memRegion_32 hm1
  have hm2 : m ⊨ memRegion (sp0 - 64#64) 64 ∗
      (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ memRegion sp 8 ∗ memRegion (sp + 48#64) 8 ∗
       memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, hm2⟩ := exists_words8_of_memRegion_64 hm2
  have hm3 : m ⊨ memRegion sp 8 ∗
      (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ words8At (sp0 - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       memRegion (sp + 48#64) 8 ∗ memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨w_sp0, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm4 : m ⊨ memRegion (sp + 48#64) 8 ∗
      (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ words8At (sp0 - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    convert hm3 using 1; sep_ac_rfl
  obtain ⟨w_sp48, hm4⟩ := exists_word64_of_memRegion_8 hm4
  refine ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, w_sp0, w_sp48, ?_⟩
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem s0_step2_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion (sp + 433#64) 975 ∗ R) :
    ∃ (d0 d1 d2 d3 d4 d5 d6 : BitVec 8) (dw0 dw1 dw2 : BitVec 64) (db31 : BitVec 8)
      (u1104 : BitVec 64) (u1112 : BitVec 8),
      m ⊨ (localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
           ((sp + 1104#64) ↦₆₄ u1104) ∗
           ((sp + 1112#64) ↦₈ u1112)) ∗
          (memRegion (sp + 433#64) 1 ∗
           memRegion (sp + 434#64) 670 ∗
           memRegion (sp + 1113#64) 167 ∗
           memRegion (sp + 1312#64) 96 ∗ R) := by
  rw [memRegion_split (sp + 433#64) 1 974 (by decide),
      show sp + 433#64 + 1#64 = sp + 434#64 by bv_omega,
      memRegion_split (sp + 434#64) 670 304 (by decide),
      show sp + 434#64 + 670#64 = sp + 1104#64 by bv_omega,
      memRegion_split (sp + 1104#64) 8 296 (by decide),
      show sp + 1104#64 + 8#64 = sp + 1112#64 by bv_omega,
      memRegion_split (sp + 1112#64) 1 295 (by decide),
      show sp + 1112#64 + 1#64 = sp + 1113#64 by bv_omega,
      memRegion_split (sp + 1113#64) 167 128 (by decide),
      show sp + 1113#64 + 167#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 32 96 (by decide),
      show sp + 1280#64 + 32#64 = sp + 1312#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 1280#64) 32 ∗
      (memRegion (sp + 1104#64) 8 ∗ memRegion (sp + 1112#64) 1 ∗
       (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
        memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, hm1⟩ :=
    exists_localGroupA_of_memRegion_32 hm1
  have hm2 : m ⊨ memRegion (sp + 1104#64) 8 ∗
      (localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       memRegion (sp + 1112#64) 1 ∗
       (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
        memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1104, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : m ⊨ memRegion (sp + 1112#64) 1 ∗
      (localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗
       (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
        memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1112, hm3⟩ := exists_word8_of_memRegion_1 hm3
  refine ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, ?_⟩
  convert hm3 using 1; sep_ac_rfl

theorem s0_step2_recombine (sp : BitVec 64) (ik : IdentityKey) (w2 : BitVec 64) (b31 : BitVec 8) :
    (((sp + 400#64) ↦₈ 0#8) ∗
     ((sp + 401#64) ↦ₛ ik.publicKey.bytes.toList) ∗
     memRegion (sp + 433#64) 1 ∗
     memRegion (sp + 434#64) 670 ∗
     ((sp + 1104#64) ↦₆₄ w2) ∗
     ((sp + 1112#64) ↦₈ b31) ∗
     memRegion (sp + 1113#64) 167) ⊢
    memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 846 := by
  have hlen : ik.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  refine Entails.trans
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
    (sepConj_mono (hlen ▸ pointsToBytes_entails_memRegion (sp + 401#64) _)
    (sepConj_mono_right
    (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 1104#64) w2)
    (sepConj_mono_left (pointsTo8_entails_memRegion (sp + 1112#64) b31))))))) ?_
  rw [show sp + 1113#64 = (sp + 1112#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 1112#64) 1 167 (by decide),
      show sp + 1112#64 = (sp + 1104#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 1104#64) 8 168 (by decide),
      show sp + 1104#64 = (sp + 434#64) + 670#64 by bv_omega,
      ← memRegion_split (sp + 434#64) 670 176 (by decide),
      show sp + 433#64 = (sp + 401#64) + 32#64 by bv_omega,
      ← sepConj_assoc (memRegion (sp + 401#64) 32),
      ← memRegion_split (sp + 401#64) 32 1 (by decide),
      show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
      ← sepConj_assoc (memRegion (sp + 400#64) 1),
      ← memRegion_split (sp + 400#64) 1 33 (by decide)]
  exact Entails.refl _

theorem s0_step4_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗ R) :
    ∃ (u352 : BitVec 64) (u360 : BitVec 8) (u976 : BitVec 32) (u980 u981 : BitVec 8),
      m ⊨ (((sp + 352#64) ↦₆₄ u352) ∗
           ((sp + 360#64) ↦₈ u360) ∗
           ((sp + 976#64) ↦₃₂ u976) ∗
           ((sp + 980#64) ↦₈ u980) ∗
           ((sp + 981#64) ↦₈ u981)) ∗
          (memRegion (sp + 56#64) 296 ∗
           memRegion (sp + 361#64) 39 ∗
           memRegion (sp + 434#64) 542 ∗
           memRegion (sp + 982#64) 298 ∗ R) := by
  rw [memRegion_split (sp + 56#64) 296 48 (by decide),
      show sp + 56#64 + 296#64 = sp + 352#64 by bv_omega,
      memRegion_split (sp + 352#64) 8 40 (by decide),
      show sp + 352#64 + 8#64 = sp + 360#64 by bv_omega,
      memRegion_split (sp + 360#64) 1 39 (by decide),
      show sp + 360#64 + 1#64 = sp + 361#64 by bv_omega,
      memRegion_split (sp + 434#64) 542 304 (by decide),
      show sp + 434#64 + 542#64 = sp + 976#64 by bv_omega,
      memRegion_split (sp + 976#64) 4 300 (by decide),
      show sp + 976#64 + 4#64 = sp + 980#64 by bv_omega,
      memRegion_split (sp + 980#64) 1 299 (by decide),
      show sp + 980#64 + 1#64 = sp + 981#64 by bv_omega,
      memRegion_split (sp + 981#64) 1 298 (by decide),
      show sp + 981#64 + 1#64 = sp + 982#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 352#64) 8 ∗
      (memRegion (sp + 360#64) 1 ∗ memRegion (sp + 976#64) 4 ∗
       memRegion (sp + 980#64) 1 ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨u352, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : m ⊨ memRegion (sp + 360#64) 1 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ memRegion (sp + 976#64) 4 ∗
       memRegion (sp + 980#64) 1 ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u360, hm2⟩ := exists_word8_of_memRegion_1 hm2
  have hm3 : m ⊨ memRegion (sp + 976#64) 4 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
       memRegion (sp + 980#64) 1 ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u976, hm3⟩ := exists_word32_of_memRegion_4 hm3
  have hm4 : m ⊨ memRegion (sp + 980#64) 1 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
       ((sp + 976#64) ↦₃₂ u976) ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm3 using 1; sep_ac_rfl
  obtain ⟨u980, hm4⟩ := exists_word8_of_memRegion_1 hm4
  have hm5 : m ⊨ memRegion (sp + 981#64) 1 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
       ((sp + 976#64) ↦₃₂ u976) ∗ ((sp + 980#64) ↦₈ u980) ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨u981, hm5⟩ := exists_word8_of_memRegion_1 hm5
  refine ⟨u352, u360, u976, u980, u981, ?_⟩
  convert hm5 using 1; sep_ac_rfl

theorem s0_step4_to_memRegion_1352 (sp : BitVec 64) (ik : IdentityKey)
    (w0 : BitVec 32) (b4 b5 : BitVec 8) (w3 : BitVec 64) (b31 : BitVec 8) :
    (memRegion (sp + 56#64) 296 ∗
     ((sp + 352#64) ↦₆₄ w3) ∗
     ((sp + 360#64) ↦₈ b31) ∗
     memRegion (sp + 361#64) 39 ∗
     memRegion (sp + 400#64) 34 ∗
     memRegion (sp + 434#64) 542 ∗
     ((sp + 976#64) ↦₃₂ w0) ∗
     ((sp + 980#64) ↦₈ b4) ∗
     ((sp + 981#64) ↦₈ b5) ∗
     memRegion (sp + 982#64) 298 ∗
     ((sp + 1280#64) ↦ₛ ik.publicKey.bytes.toList) ∗
     memRegion (sp + 1312#64) 96) ⊢
    memRegion (sp + 56#64) 1352 := by
  have hlen : ik.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  refine Entails.trans
    (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 352#64) w3)
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 360#64) b31)
    (sepConj_mono_right
    (sepConj_mono_right
    (sepConj_mono_right
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 976#64) w0)
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 980#64) b4)
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 981#64) b5)
    (sepConj_mono_right
    (sepConj_mono_left (hlen ▸ pointsToBytes_entails_memRegion (sp + 1280#64) _)))))))))))) ?_
  rw [show sp + 1312#64 = (sp + 1280#64) + 32#64 by bv_omega,
      ← memRegion_split (sp + 1280#64) 32 96 (by decide),
      show sp + 1280#64 = (sp + 982#64) + 298#64 by bv_omega,
      ← memRegion_split (sp + 982#64) 298 128 (by decide),
      show sp + 982#64 = (sp + 981#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 981#64) 1 426 (by decide),
      show sp + 981#64 = (sp + 980#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 980#64) 1 427 (by decide),
      show sp + 980#64 = (sp + 976#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 976#64) 4 428 (by decide),
      show sp + 976#64 = (sp + 434#64) + 542#64 by bv_omega,
      ← memRegion_split (sp + 434#64) 542 432 (by decide),
      show sp + 434#64 = (sp + 400#64) + 34#64 by bv_omega,
      ← memRegion_split (sp + 400#64) 34 974 (by decide),
      show sp + 400#64 = (sp + 361#64) + 39#64 by bv_omega,
      ← memRegion_split (sp + 361#64) 39 1008 (by decide),
      show sp + 361#64 = (sp + 360#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 360#64) 1 1047 (by decide),
      show sp + 360#64 = (sp + 352#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 352#64) 8 1048 (by decide),
      show sp + 352#64 = (sp + 56#64) + 296#64 by bv_omega,
      ← memRegion_split (sp + 56#64) 296 1056 (by decide)]
  exact Entails.refl _



end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
