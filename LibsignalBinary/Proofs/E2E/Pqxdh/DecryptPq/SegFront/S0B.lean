/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0A
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

private theorem tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)


theorem s0_step5_some_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗ R) :
    ∃ (u400 : BitVec 64) (u408 : BitVec 8)
      (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19
        db20 db21 db22 : BitVec 8)
      (dw3 : BitVec 64) (db31 : BitVec 8),
      m ⊨ (((sp + 400#64) ↦₆₄ u400) ∗
           ((sp + 408#64) ↦₈ u408) ∗
           remoteGroupD (sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
             db17 db18 db19 db20 db21 db22 dw3 db31) ∗
          (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R) := by
  rw [memRegion_split (sp + 400#64) 8 26 (by decide),
      show sp + 400#64 + 8#64 = sp + 408#64 by bv_omega,
      memRegion_split (sp + 408#64) 1 25 (by decide),
      show sp + 408#64 + 1#64 = sp + 409#64 by bv_omega,
      memRegion_split (sp + 56#64) 32 264 (by decide),
      show sp + 56#64 + 32#64 = sp + 88#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 400#64) 8 ∗
      (memRegion (sp + 408#64) 1 ∗ memRegion (sp + 56#64) 32 ∗
       (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨u400, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : m ⊨ memRegion (sp + 408#64) 1 ∗
      (((sp + 400#64) ↦₆₄ u400) ∗ memRegion (sp + 56#64) 32 ∗
       (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u408, hm2⟩ := exists_word8_of_memRegion_1 hm2
  have hm3 : m ⊨ memRegion (sp + 56#64) 32 ∗
      (((sp + 400#64) ↦₆₄ u400) ∗ ((sp + 408#64) ↦₈ u408) ∗
       (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16, db17, db18,
      db19, db20, db21, db22, dw3, db31, _, hm3⟩ :=
    exists_remoteGroupC_of_memRegion_32 hm3
  rw [remoteGroupC_eq_remoteGroupD] at hm3
  refine ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16,
      db17, db18, db19, db20, db21, db22, dw3, db31, ?_⟩
  convert hm3 using 1; sep_ac_rfl

theorem s0_step5_some_recombine (sp : BitVec 64) (locIk remIk : IdentityKey)
    (w0 : BitVec 32) (b4 b5 b6 : BitVec 8) (w401 w3 : BitVec 64) (b31 : BitVec 8) :
    (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
     memRegion (sp + 88#64) 264 ∗
     ((sp + 352#64) ↦₆₄ w3) ∗
     ((sp + 360#64) ↦₈ b31) ∗
     memRegion (sp + 361#64) 39 ∗
     ((sp + 400#64) ↦₈ b6) ∗
     ((sp + 401#64) ↦₆₄ w401) ∗
     memRegion (sp + 409#64) 25 ∗
     memRegion (sp + 434#64) 542 ∗
     ((sp + 976#64) ↦₃₂ w0) ∗
     ((sp + 980#64) ↦₈ b4) ∗
     ((sp + 981#64) ↦₈ b5) ∗
     memRegion (sp + 982#64) 298 ∗
     ((sp + 1280#64) ↦ₛ locIk.publicKey.bytes.toList) ∗
     memRegion (sp + 1312#64) 96) ⊢
    memRegion (sp + 56#64) 1352 := by
  have hrem_len : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have h56 : ((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ memRegion (sp + 88#64) 264 ⊢
      memRegion (sp + 56#64) 296 := by
    refine Entails.trans (sepConj_mono_left (hrem_len ▸ pointsToBytes_entails_memRegion (sp +
        56#64) _)) ?_
    rw [show sp + 88#64 = (sp + 56#64) + 32#64 by bv_omega,
        ← memRegion_split (sp + 56#64) 32 264 (by decide)]
    exact Entails.refl _
  have h400 : ((sp + 400#64) ↦₈ b6) ∗ ((sp + 401#64) ↦₆₄ w401) ∗ memRegion (sp + 409#64) 25 ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) b6)
        (sepConj_mono_left (pointsTo64_entails_memRegion (sp + 401#64) w401))) ?_
    rw [show sp + 409#64 = (sp + 401#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 8 25 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]
    exact Entails.refl _
  rw [← sepConj_assoc ((sp + 56#64) ↦ₛ _),
      ← sepConj_assoc ((sp + 401#64) ↦₆₄ _),
      ← sepConj_assoc ((sp + 400#64) ↦₈ _)]
  refine Entails.trans
    (sepConj_mono h56
    (sepConj_mono_right
    (sepConj_mono_right
    (sepConj_mono_right
    (sepConj_mono_left h400))))) ?_
  exact s0_step4_to_memRegion_1352 sp locIk w0 b4 b5 w3 b31

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
