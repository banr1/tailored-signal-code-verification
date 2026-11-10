/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Post-`try_decrypt_with_state` Dispatch and Error-Tail Assembly for Stage P3

Layout and framing helpers for the post-`try_decrypt_with_state` (`+0x1cd8#64`) success path
(`-> +0x34dc#64`), duplicate-message error tail, and general `SignalProtocolError` cleanup path of
`message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace P3P4

abbrev dropSessionStructure2Stack := dropSessionStructureLocal2Stack
abbrev dropSessionStructure2Spec := dropSessionStructureLocal2Spec

/-! ## 1. Byte, `.rodata`, `sessionStateAt`, `vecResultAt`, and `speAt` Layout Helpers -/

theorem SepWPp.drop_frame {prog : Program} {ret : BitVec 64} {s : State} {P_all P_drop P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hP : P_all = P_drop ∗ P)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P_all Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL
theorem SepWPp.bind_sepWPp_frame_raw {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {Q_mid : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hpcm hrunm hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim
theorem sessionStateAt_unpack_head_tail (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G st (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionHeap A G st := by
  rw [sessionStateAt_eq_inline_sep_heap A ss G st]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨_, hinl⟩
  obtain ⟨bs336, hlen336, rfl⟩ := sessionInline_exists_tail hinl
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have h8 : ss + BitVec.ofNat 64 8 = ss + 8#64 := rfl
  rw [h8]
  refine Entails.trans (sepConj_mono_right (sessionHeap_localIk_cap_lt A G st)) ?_
  have hpull :
      (((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336)) ∗
        (⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ sessionHeap A G st)) =
      (⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionHeap A G st) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hcap
  refine Entails.sepExists_right bs336 ?_
  exact Entails.pure_right ⟨hlen336, hcap, hinl⟩ (Entails.refl _)
theorem sessionStateAt_pack_head_tail (A : RustAlloc) (dst : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {bs336 : List (BitVec 8)}
    (h : SessionInline G st (unpack64 G.localIk.cap ++ bs336)) :
    ((dst ↦₆₄ G.localIk.cap) ∗ ((dst + 8#64) ↦ₛ bs336) ∗ sessionHeap A G st) ⊢
      sessionStateAt A dst G st := by
  have h8 : dst + 8#64 = dst + BitVec.ofNat 64 (unpack64 G.localIk.cap).length := rfl
  rw [pointsTo64_eq_pointsToBytes, h8, ← sepConj_assoc, ← pointsToBytes_append]
  exact sessionStateAt_of_bytes A dst G st h
theorem cap_ne_noneCap_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap ≠ 0xffffffffffffffff#64 := by
  intro heq
  subst heq
  revert h
  decide
/-- Upgrade `sessionStateAt` (from `LibsignalSession2Repr`) to `sessionStateReprAt` (from
    `LibsignalSession3Repr`). -/
theorem sessionStateAt_entails_sessionAt (A : RustAlloc) (p : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8)))
    (h : PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
      G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
      (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat) :
    sessionStateAt A p G s.state ⊢ sessionStateReprAt A p G s := by
  unfold sessionStateReprAt
  exact Entails.pure_right h (Entails.refl _)
theorem repack20_32_64_64_to_64_64_32 (a : BitVec 64) (w0 : BitVec 32) (w1 w2 : BitVec 64) :
    (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₆₄ w2) =
      (a ↦₆₄ (w1.extractLsb' 0 32 ++ w0)) ∗
      ((a + 8#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((a + 16#64) ↦₃₂ w2.extractLsb' 32 32) := by
  rw [pointsTo64_split32 (a + 4#64) w1, pointsTo64_split32 (a + 12#64) w2,
      ← pointsTo32_pair a w0 (w1.extractLsb' 0 32),
      ← pointsTo32_pair (a + 8#64) (w1.extractLsb' 32 32) (w2.extractLsb' 0 32)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem memRegion20_from_32_64_64 (a : BitVec 64) :
    memRegion a 20 =
      (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ u0 : BitVec 32,
        (a ↦₃₂ u0) ∗ ((a + 0x4#64) ↦₆₄ w1) ∗ ((a + 0xc#64) ↦₆₄ w2)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 16) (b' := a + 0x4#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four a,
      ProofLib.memRegion_cells (a + 0x4#64) 2 (by decide)]
  simp only [cells, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
theorem sp370_36_err_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 =
      (∃∗ u_38c : BitVec 64, ∃∗ u_384 : BitVec 64, ∃∗ u_380 : BitVec 32,
       ∃∗ u_378 : BitVec 64, ∃∗ u_370 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u_370) ∗ ((sp + 0x378#64) ↦₆₄ u_378) ∗
        ((sp + 0x380#64) ↦₃₂ u_380) ∗ ((sp + 0x384#64) ↦₆₄ u_384) ∗
          ((sp + 0x38c#64) ↦₆₄ u_38c)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x370#64) (n := 8) (k := 28)
        (b' := sp + 0x378#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x378#64) (n := 8) (k := 20)
        (b' := sp + 0x380#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x380#64) (n := 4) (k := 16)
        (b' := sp + 0x384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x384#64) (n := 8) (k := 8)
        (b' := sp + 0x38c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x370#64),
      ProofLib.memRegion_eight (sp + 0x378#64),
      ProofLib.memRegion_four (sp + 0x380#64),
      ProofLib.memRegion_eight (sp + 0x384#64),
      ProofLib.memRegion_eight (sp + 0x38c#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
theorem sp370_36_err_fold (sp u_370 u_378 u_384 u_38c : BitVec 64) (u_380 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ u_370) ∗ ((sp + 0x378#64) ↦₆₄ u_378) ∗
    ((sp + 0x380#64) ↦₃₂ u_380) ∗ ((sp + 0x384#64) ↦₆₄ u_384) ∗ ((sp + 0x38c#64) ↦₆₄ u_38c) ⊢
      memRegion (sp + 0x370#64) 36 := by
  rw [sp370_36_err_split_eq sp]
  exact Entails.sepExists_right u_38c (Entails.sepExists_right u_384
    (Entails.sepExists_right u_380 (Entails.sepExists_right u_378
      (Entails.sepExists_right u_370 (Entails.refl _)))))
theorem memRegion17_split_eq (a : BitVec 64) :
    memRegion a 17 =
      (∃∗ u10 : BitVec 8, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((a + 0x0#64) ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u8) ∗ ((a + 0x10#64) ↦₈ u10)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 9)
        (b' := a + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x8#64) (n := 8) (k := 1)
        (b' := a + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 0x8#64),
      ProofLib.memRegion_one (a + 0x10#64),
      BitVec.add_zero]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
theorem dfPtr_words_eq_decryptionFailedStr (dfPtr : BitVec 64) :
    ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗ ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
    ((dfPtr + 0x10#64) ↦₈ 0x64#8) =
      (dfPtr ↦ₛ utf8 "decryption failed") := by
  have hstr : utf8 "decryption failed" =
      unpack64 0x6974707972636564#64 ++
      (unpack64 0x656c696166206e6f#64 ++ [0x64#8]) := by decide +kernel
  rw [hstr, pointsToBytes_append, pointsToBytes_append, pointsToBytes_singleton,
      unpack64_length, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem dfPtr_decryptionFailed_entails_memRegion17 (dfPtr : BitVec 64) :
    (dfPtr ↦ₛ utf8 "decryption failed") ⊢ memRegion dfPtr 17 := by
  have hlen : (utf8 "decryption failed").length = 17 := by decide +kernel
  rw [← hlen]
  exact pointsToBytes_entails_memRegion dfPtr (utf8 "decryption failed")
theorem cell_split_head8 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₈ v.extractLsb' 0 8) ∗ ((a + 1#64) ↦ₛ (unpack64 v).drop 1)) := by
  conv_lhs =>
    rw [pointsTo64_eq_pointsToBytes,
        show unpack64 v = v.extractLsb' 0 8 :: (unpack64 v).drop 1 from rfl,
        pointsToBytes_cons]
theorem cell_join_head8 (b0 : BitVec 8) (v : BitVec 64) :
    ∃ w : BitVec 64,
      unpack64 w = b0 :: (unpack64 v).drop 1 ∧
      ∀ a : BitVec 64, ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ (unpack64 v).drop 1)) = (a ↦₆₄ w) := by
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := b0 :: (unpack64 v).drop 1) rfl
  refine ⟨w, hw.symm, fun a => ?_⟩
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons]
theorem tail7_word8_entails_memRegion15 (a : BitVec 64) (v w : BitVec 64) :
    ((a + 1#64) ↦ₛ (unpack64 v).drop 1) ∗ ((a + 8#64) ↦₆₄ w) ⊢
      memRegion (a + 1#64) 15 := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 7) (k := 8)
        (b' := a + 8#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono ?_ (pointsTo64_entails_memRegion (a + 8#64) w)
  have hlen : ((unpack64 v).drop 1).length = 7 := by simp [unpack64_length]
  simpa [hlen] using pointsToBytes_entails_memRegion (a + 1#64) ((unpack64 v).drop 1)
theorem memRegion48_words6_split_eq (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ((a + 0x0#64) ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u1) ∗ ((a + 0x10#64) ↦₆₄ u2) ∗
        ((a + 0x18#64) ↦₆₄ u3) ∗ ((a + 0x20#64) ↦₆₄ u4) ∗ ((a + 0x28#64) ↦₆₄ u5)) := by
  rw [ProofLib.memRegion_cells a 6 (by decide)]
  simp only [cells, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
theorem words6_entails_memRegion48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 0x0#64) ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) ∗
    ((a + 0x18#64) ↦₆₄ w3) ∗ ((a + 0x20#64) ↦₆₄ w4) ∗ ((a + 0x28#64) ↦₆₄ w5) ⊢
      memRegion a 48 := by
  rw [memRegion48_words6_split_eq a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))
theorem memRegion32_words4_split_eq (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((a + 0x0#64) ↦₆₄ u0) ∗ ((a + 0x8#64) ↦₆₄ u1) ∗
        ((a + 0x10#64) ↦₆₄ u2) ∗ ((a + 0x18#64) ↦₆₄ u3)) := by
  rw [ProofLib.memRegion_cells a 4 (by decide)]
  simp only [cells, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
theorem words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    ((a + 0x0#64) ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) ∗
      ((a + 0x18#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion32_words4_split_eq a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))
theorem words5_entails_memRegion40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    ((a + 0x8#64) ↦₆₄ w0) ∗ ((a + 0x10#64) ↦₆₄ w1) ∗ ((a + 0x18#64) ↦₆₄ w2) ∗
    ((a + 0x20#64) ↦₆₄ w3) ∗ ((a + 0x28#64) ↦₆₄ w4) ⊢
      memRegion (a + 0x8#64) 40 := by
  rw [ProofLib.memRegion_split' (b := a + 0x8#64) (n := 8) (k := 32)
        (b' := a + 0x10#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion (a + 0x8#64) w0) ?_
  simpa only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using
    words4_entails_memRegion32 (a + 0x10#64) w1 w2 w3 w4
theorem vecU8Buf_entails_pointsToBytes (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
  :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Buf
  apply Entails.pure_left; rintro ⟨hle, hlt, hnz⟩
  refine Entails.pure_right ⟨hle, hlt, hnz⟩ ?_
  by_cases hc : cap = 0
  · subst hc
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · have hc64 : ¬cap = 0#64 := hc
    simp only [hc, hc64, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)
theorem decResultAt_ok_unpack (A : RustAlloc) (r : BitVec 64) (pt : List (BitVec 8)) :
    vecResultAt A r (.ok pt) ⊢
      ∃∗ ptCap : BitVec 64, ∃∗ ptPtr : BitVec 64,
        ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝ ∗
        (r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 0x8#64) ↦₆₄ ptCap) ∗
        ((r + 0x10#64) ↦₆₄ ptPtr) ∗ ((r + 0x18#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (r + 0x20#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
        (if ptCap = 0#64 then emp
         else A.live ptPtr ptCap.toNat 1 ∗
           memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := by
  unfold vecResultAt vecU8 vecU8At vecHeader okTagVec
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro ptCap
  apply Entails.sepExists_elim; intro ptPtr
  refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
  have hbuf := vecU8Buf_entails_pointsToBytes A ptCap ptPtr pt
  unfold vecU8Buf at hbuf
  have h1 :
      (r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 0x8#64) ↦₆₄ ptCap) ∗
      ((r + 0x10#64) ↦₆₄ ptPtr) ∗ ((r + 0x18#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      (⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0⌝ ∗
       (if ptCap = 0 then emp
        else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length))) ∗
      memRegion (r + 0x20#64) 16 ⊢
      (r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 0x8#64) ↦₆₄ ptCap) ∗
      ((r + 0x10#64) ↦₆₄ ptPtr) ∗ ((r + 0x18#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      (⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝ ∗ (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length))) ∗
      memRegion (r + 0x20#64) 16 :=
    sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hbuf))))
  rw [← sepConj_assoc (⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0⌝)]
  exact Entails.trans h1 (Entails.of_eq (by ac_rfl))

/-! ## 2. Error-Tail Common and Duplicate-Message Error Helpers -/
theorem entails_replace_sub {A B F P Q : SepProp}
    (hab : A ⊢ B) (h1 : P = A ∗ F) (h2 : B ∗ F = Q) : P ⊢ Q := by
  rw [h1, ← h2]
  exact sepConj_mono_left hab
private theorem SepWPp.call_frame_inImage_nopanic {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]
  rw [hspec, pure_sepConj_pure_assoc]
/-! ## 3. Non-Duplicate Error Path Helpers -/
theorem extractLsb0_8_of_unpack64_cons {w : BitVec 64} {b0 : BitVec 8} {tl : List (BitVec 8)}
    (h : unpack64 w = b0 :: tl) : w.extractLsb' 0 8 = b0 := by
  have h0 : (unpack64 w).head? = some b0 := by rw [h]; rfl
  simpa [unpack64] using h0
theorem recordError_preKey_of_speTag_ne_speWord23 {e : SignalProtocolError}
    (hne : e ≠ .panic) (htag : speTag e ≠ speWord 23) :
    SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed := by
  cases e with
  | duplicatedMessage _ _ => exact absurd rfl htag
  | panic => exact absurd rfl hne
  | _ => rfl
theorem speTag_ne_ok_of_ne_panic {e : SignalProtocolError} (hne : e ≠ .panic) :
    speTag e ≠ 0xfffffffffffffffe#64 := by
  cases e <;> first | exact absurd rfl hne | (dsimp [speTag, speWord]; decide)
theorem recordResultAt_preKey_decryptionFailed_intro (A : RustAlloc) (r p : BitVec 64)
    (hp : p ≠ 0) :
    (r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₆₄ 17#64) ∗ ((r + 16#64) ↦₆₄ p) ∗
    ((r + 24#64) ↦₆₄ 17#64) ∗ ((r + 32#64) ↦₈ msgTypeByte .preKey) ∗
    memRegion (r + 33#64) 15 ∗ A.live p 17 1 ∗ (p ↦ₛ decryptionFailedStr) ⊢
    recordResultAt A r (.error (.invalidMessage .preKey .decryptionFailed)) := by
  have hlen : decryptionFailedStr.length = 17 := by decide +kernel
  have hvec :
      ((r + 8#64) ↦₆₄ 17#64) ∗ ((r + 16#64) ↦₆₄ p) ∗ ((r + 24#64) ↦₆₄ 17#64) ∗
      A.live p 17 1 ∗ (p ↦ₛ decryptionFailedStr) ⊢
      vecU8 A (r + 8#64) decryptionFailedStr := by
    unfold vecU8 vecU8At vecHeader
    refine Entails.sepExists_right 17#64 (Entails.sepExists_right p ?_)
    have hcond : (17 ≤ 17 ∧ 17 < 2 ^ 63 ∧ p ≠ 0#64) = True :=
      propext ⟨fun _ => trivial, fun _ => ⟨by decide, by decide, hp⟩⟩
    have h17_ne : ((17#64 : BitVec 64) = 0#64) = False := propext ⟨by decide, False.elim⟩
    have hcap17 : (17#64 : BitVec 64).toNat = 17 := rfl
    simp only [hlen, hcap17, hcond, pure_true, emp_sepConj, h17_ne, ite_false,
      Nat.sub_self, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      memRegion_zero, sepConj_emp, sepConj_assoc]
    exact Entails.refl _
  dsimp only [recordResultAt]
  exact entails_replace_sub hvec (by sep_focus) (eq_of_sep_emp (by sep_focus))
theorem words6At_preKey_decryptionFailed_entails_recordResultAt (A : RustAlloc)
    (outPtr dfPtr w3 w4 : BitVec 64) (hdf_ne : dfPtr ≠ 0) (hw3 : w3.extractLsb' 0 8 = 3#8) :
    words6At outPtr 0x8000000000000018#64 17#64 dfPtr 17#64 w3 w4 ∗
    A.live dfPtr 17 1 ∗ (dfPtr ↦ₛ utf8 "decryption failed") ⊢
    recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) := by
  have h1 :
      words6At outPtr 0x8000000000000018#64 17#64 dfPtr 17#64 w3 w4 ∗
      A.live dfPtr 17 1 ∗ (dfPtr ↦ₛ utf8 "decryption failed") =
      (((outPtr + 32#64) ↦₆₄ w3) ∗ ((outPtr + 40#64) ↦₆₄ w4)) ∗
      ((outPtr ↦₆₄ speWord 24) ∗ ((outPtr + 8#64) ↦₆₄ 17#64) ∗
       ((outPtr + 16#64) ↦₆₄ dfPtr) ∗ ((outPtr + 24#64) ↦₆₄ 17#64) ∗
       A.live dfPtr 17 1 ∗ (dfPtr ↦ₛ decryptionFailedStr)) := by
    unfold words6At speWord decryptionFailedStr
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact eq_of_sep_emp (by sep_focus)
  rw [h1, cell_split_head8 (outPtr + 32#64) w3, hw3]
  have htail := tail7_word8_entails_memRegion15 (outPtr + 32#64) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at htail
  have h2 :
      (((outPtr + 32#64) ↦₈ 3#8) ∗ ((outPtr + 33#64) ↦ₛ (unpack64 w3).drop 1) ∗
       ((outPtr + 40#64) ↦₆₄ w4)) ∗ ((outPtr ↦₆₄ speWord 24) ∗ ((outPtr + 8#64) ↦₆₄ 17#64) ∗
       ((outPtr + 16#64) ↦₆₄ dfPtr) ∗ ((outPtr + 24#64) ↦₆₄ 17#64) ∗
       A.live dfPtr 17 1 ∗ (dfPtr ↦ₛ decryptionFailedStr)) ⊢
      (outPtr ↦₆₄ speWord 24) ∗ ((outPtr + 8#64) ↦₆₄ 17#64) ∗
      ((outPtr + 16#64) ↦₆₄ dfPtr) ∗ ((outPtr + 24#64) ↦₆₄ 17#64) ∗
      ((outPtr + 32#64) ↦₈ msgTypeByte .preKey) ∗
      memRegion (outPtr + 33#64) 15 ∗ A.live dfPtr 17 1 ∗ (dfPtr ↦ₛ decryptionFailedStr) := by
    dsimp only [msgTypeByte]
    exact entails_replace_sub htail (by sep_focus) (eq_of_sep_emp (by sep_focus))
  exact Entails.trans (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h2)
    (recordResultAt_preKey_decryptionFailed_intro A outPtr dfPtr hdf_ne)
private theorem growOneSpe_pre_zero_eq (A : RustAlloc) (s : State) (v ptr : BitVec 64)
    (hx0 : s.readReg64 .x0 = v) (hptr : ptr ≠ 0) :
    (growOneSpeSpec A).pre (v, 0#64, ptr, []) s =
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have hp : (s.readReg64 .x0 = v ∧ ([] : List (BitVec 8)).length = (0#64 : BitVec 64).toNat * 48 ∧
      ptr ≠ 0 ∧ max (2 * (0#64 : BitVec 64).toNat) 4 * 48 + 8 ≤ 2 ^ 63) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hx0, rfl, hptr, by decide⟩⟩
  have hif : ((0#64 : BitVec 64) = 0) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩
  simp only [hp, pure_true, hif, ite_true, emp_sepConj, sepConj_emp, sepConj_assoc]
private theorem growOneSpe_post_zero_eq (A : RustAlloc) (s0 sf : State) (v ptr : BitVec 64) :
    (growOneSpeSpec A).post (v, 0#64, ptr, []) s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗
      ∃∗ p' : BitVec 64,
        ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' 192 8 ∗ memRegion p' 192 ∗ A.pool ∗ stackAt s0.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.sub_zero, show max 0 4 = 4 from rfl,
    show 4 * 48 = 192 from rfl, show ([] : List (BitVec 8)).length = 0 from rfl,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, pointsToBytes_nil,
    emp_sepConj, sepConj_emp, sepConj_assoc]
/-- Shared precondition frame for `stageP3_sub5_err_nondup_ok` and `stageP3_sub5_err_ok`. -/
def stageP3ErrPre (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
  stackAt s.sp growOneSpeStack
/-- Shared postcondition heap for `stageP3_sub5_err_nondup_ok` and `stageP3_sub5_err_ok`. -/
def stageP3ErrPost (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr prevStatesPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  recordResultAt A outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack
/-! ## 4. Stage P3 Post-Decrypt Dispatch Helpers -/
/-- Precondition at `+0x1cd8#64` for `stageP3_sub5_dispatch_ok`. -/
def stageP3DispatchPre (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  vecResultAt A (s.sp + 0x270#64) res ∗ sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
  stackAt s.sp growOneSpeStack
/-- Mid-state heap at `+0x34dc#64` after `stageP3_sub5_decResult_ok` on `res = .ok pt`. -/
def stageP3DispatchOkMid (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack
end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
