/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Shared Word-Extraction, Stack-Frame, and Writeback Helpers for `<States>::recv`

Word-grid split/merge lemmas, stack-frame layouts (`4,240`-byte frame), `Relocatable` `memcpy` rule,
and shared `Ok(V1Recv)` writeback epilogue (`0x59e88..0x59ff0`, `+18996 -> +19356`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem bv_sub_sub_recv (x y z : BitVec 64) : (x - y) - z = x - (y + z) := by bv_omega

theorem bv_add_lit_add_lit_recv (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append

/-! ## 8-Byte Packing & `Words10` / `Words5x10` / `Words63` Definitions -/

def pack64Le (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

theorem unpack64_pack64Le (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (pack64Le b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [unpack64, pack64Le, List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
          by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem exists_word_of_length_8 (bs : List (BitVec 8)) (h : bs.length = 8) :
    ∃ w : BitVec 64, bs = unpack64 w :=
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    ⟨pack64Le b0 b1 b2 b3 b4 b5 b6 b7, (unpack64_pack64Le b0 b1 b2 b3 b4 b5 b6 b7).symm⟩

theorem exists_word_cons_of_length_add_8 {k : Nat} (bs : List (BitVec 8)) (h : bs.length = 8 + k) :
    ∃ (w : BitVec 64) (rest : List (BitVec 8)),
      rest.length = k ∧ bs = unpack64 w ++ rest := by
  have htake : (bs.take 8).length = 8 := by simp [h]
  have hdrop : (bs.drop 8).length = k := by simp [h]
  obtain ⟨w, hw⟩ := exists_word_of_length_8 (bs.take 8) htake
  exact ⟨w, bs.drop 8, hdrop, by rw [← hw, List.take_append_drop]⟩

@[simp]
theorem wordsBytes_append (ws1 ws2 : List (BitVec 64)) :
    wordsBytes (ws1 ++ ws2) = wordsBytes ws1 ++ wordsBytes ws2 := by
  induction ws1 with
  | nil => rfl
  | cons w ws1 ih => simp only [List.cons_append, wordsBytes_cons, ih, List.append_assoc]

/-- 10-word (`80`-byte) tuple. -/
structure Words10 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64

def words10List (b : Words10) : List (BitVec 64) :=
  [b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7, b.w8, b.w9]

@[simp]
theorem length_words10List (b : Words10) : (words10List b).length = 10 := rfl

def words10At (a : BitVec 64) (b : Words10) : SepProp :=
  (a ↦₆₄ b.w0) ∗ ((a + 8#64) ↦₆₄ b.w1) ∗ ((a + 16#64) ↦₆₄ b.w2) ∗ ((a + 24#64) ↦₆₄ b.w3) ∗
  ((a + 32#64) ↦₆₄ b.w4) ∗ ((a + 40#64) ↦₆₄ b.w5) ∗ ((a + 48#64) ↦₆₄ b.w6) ∗ ((a + 56#64) ↦₆₄ b.w7) ∗
  ((a + 64#64) ↦₆₄ b.w8) ∗ ((a + 72#64) ↦₆₄ b.w9)

theorem words10At_eq_wordsAt (a : BitVec 64) (b : Words10) :
    words10At a b = wordsAt a (words10List b) := by
  unfold words10At words10List
  rw [wordsAt_10]

theorem exists_words10_of_length_add_80 {k : Nat} (bs : List (BitVec 8)) (h : bs.length = 80 + k) :
    ∃ (b : Words10) (rest : List (BitVec 8)),
      rest.length = k ∧ bs = wordsBytes (words10List b) ++ rest := by
  obtain ⟨w0, r1, hr1, h0⟩ := exists_word_cons_of_length_add_8 (k := 72 + k) bs (by omega)
  obtain ⟨w1, r2, hr2, h1⟩ := exists_word_cons_of_length_add_8 (k := 64 + k) r1 (by omega)
  obtain ⟨w2, r3, hr3, h2⟩ := exists_word_cons_of_length_add_8 (k := 56 + k) r2 (by omega)
  obtain ⟨w3, r4, hr4, h3⟩ := exists_word_cons_of_length_add_8 (k := 48 + k) r3 (by omega)
  obtain ⟨w4, r5, hr5, h4⟩ := exists_word_cons_of_length_add_8 (k := 40 + k) r4 (by omega)
  obtain ⟨w5, r6, hr6, h5⟩ := exists_word_cons_of_length_add_8 (k := 32 + k) r5 (by omega)
  obtain ⟨w6, r7, hr7, h6⟩ := exists_word_cons_of_length_add_8 (k := 24 + k) r6 (by omega)
  obtain ⟨w7, r8, hr8, h7⟩ := exists_word_cons_of_length_add_8 (k := 16 + k) r7 (by omega)
  obtain ⟨w8, r9, hr9, h8⟩ := exists_word_cons_of_length_add_8 (k := 8 + k) r8 (by omega)
  obtain ⟨w9, r10, hr10, h9⟩ := exists_word_cons_of_length_add_8 (k := k) r9 hr9
  refine ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩, r10, hr10, ?_⟩
  simp only [words10List, wordsBytes, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, List.append_assoc,
    List.nil_append]

/-- `5 × Words10` (`400`-byte) tuple for `PolyEncoder` / `PolyDecoder`. -/
structure Words5x10 where
  b0 : Words10
  b1 : Words10
  b2 : Words10
  b3 : Words10
  b4 : Words10

def words5x10List (p : Words5x10) : List (BitVec 64) :=
  words10List p.b0 ++ words10List p.b1 ++ words10List p.b2 ++ words10List p.b3 ++ words10List p.b4

@[simp]
theorem length_words5x10List (p : Words5x10) : (words5x10List p).length = 50 := rfl

theorem exists_words5x10_of_length_400 (bs : List (BitVec 8)) (h : bs.length = 400) :
    ∃ p : Words5x10, bs = wordsBytes (words5x10List p) := by
  obtain ⟨u, rfl⟩ := exists_words50_of_length_400 h
  refine ⟨⟨⟨u.c0.w0, u.c0.w1, u.c0.w2, u.c0.w3, u.c0.w4, u.c0.w5, u.c0.w6, u.c0.w7, u.c0.w8, u.c0.w9⟩,
           ⟨u.c0.w10, u.c0.w11, u.c0.w12, u.c0.w13, u.c0.w14, u.c0.w15, u.c1.w0, u.c1.w1, u.c1.w2, u.c1.w3⟩,
           ⟨u.c1.w4, u.c1.w5, u.c1.w6, u.c1.w7, u.c1.w8, u.c1.w9, u.c1.w10, u.c1.w11, u.c1.w12, u.c1.w13⟩,
           ⟨u.c1.w14, u.c1.w15, u.c2.w0, u.c2.w1, u.c2.w2, u.c2.w3, u.c2.w4, u.c2.w5, u.c2.w6, u.c2.w7⟩,
           ⟨u.c2.w8, u.c2.w9, u.c2.w10, u.c2.w11, u.c2.w12, u.c2.w13, u.c2.w14, u.c2.w15, u.w48, u.w49⟩⟩, ?_⟩
  simp only [Words50.toBytes, Words16.toList, words5x10List, words10List,
    wordsBytes_append, wordsBytes_cons, wordsBytes_nil, List.append_assoc, List.append_nil]

theorem exists_vecWords_376_of_length_400 (bs : List (BitVec 8)) (h : bs.length = 400) :
    ∃ (v : VecWords) (tailBytes : List (BitVec 8)),
      tailBytes.length = 376 ∧ bs = wordsBytes (vecWordsList v) ++ tailBytes := by
  obtain ⟨w0, r1, hr1, h0⟩ := exists_word_cons_of_length_add_8 (k := 392) bs h
  obtain ⟨w1, r2, hr2, h1⟩ := exists_word_cons_of_length_add_8 (k := 384) r1 hr1
  obtain ⟨w2, r3, hr3, h2⟩ := exists_word_cons_of_length_add_8 (k := 376) r2 hr2
  refine ⟨⟨w0, w1, w2⟩, r3, hr3, ?_⟩
  simp only [vecWordsList, wordsBytes, h0, h1, h2, List.append_assoc, List.nil_append]

theorem relocatable_400_extract_words5x10 {F : BitVec 64 → SepProp}
    (hF : Relocatable 400 F) (a : BitVec 64) :
    F a ⊢
      ∃∗ p : Words5x10,
        wordsAt a (words5x10List p) ∗
        relocatedHeap F (wordsBytes (words5x10List p)) := by
  refine Entails.trans (hF a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨p, rfl⟩ := exists_words5x10_of_length_400 bs hlen
  rw [← wordsAt_eq_pointsToBytes]
  exact Entails.sepExists_right p (Entails.refl _)

theorem relocatable_400_extract_words3_376 {F : BitVec 64 → SepProp}
    (hF : Relocatable 400 F) (a : BitVec 64) :
    F a ⊢
      ∃∗ v : VecWords, ∃∗ tailBytes : List (BitVec 8),
        ⌜tailBytes.length = 376⌝ ∗
        wordsAt a (vecWordsList v) ∗
        ((a + 24#64) ↦ₛ tailBytes) ∗
        relocatedHeap F (wordsBytes (vecWordsList v) ++ tailBytes) := by
  refine Entails.trans (hF a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨v, tailBytes, htail, rfl⟩ := exists_vecWords_376_of_length_400 bs hlen
  rw [pointsToBytes_append a (wordsBytes (vecWordsList v)) tailBytes,
      length_wordsBytes, length_vecWordsList, ← wordsAt_eq_pointsToBytes]
  refine Entails.sepExists_right v (Entails.sepExists_right tailBytes ?_)
  refine Entails.pure_right htail ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## `Words63` (`504`B) Representation and Extraction/Recomposition Lemmas -/

theorem pointsTo128_eq_pair64_recv (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) =
      (a ↦₆₄ q.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ q.extractLsb' 64 64) := by
  have h : q.extractLsb' 64 64 ++ q.extractLsb' 0 64 = q := by bv_kernel
  rw [EncoderFromPb.pointsTo64_pair_eq_pointsTo128, h]

/-- 63-word (`504`-byte) state tuple, with bytes `480..496` (`+0x1e0`) represented as a 128-bit
    SIMD quadword `q60` to match the `ldr q0` / `str q0` instructions directly. -/
structure Words63 where
  b0 : Words10
  b1 : Words10
  b2 : Words10
  b3 : Words10
  b4 : Words10
  b5 : Words10
  q60 : BitVec 128
  w62 : BitVec 64

def words63List (w : Words63) : List (BitVec 64) :=
  words10List w.b0 ++ words10List w.b1 ++ words10List w.b2 ++
  words10List w.b3 ++ words10List w.b4 ++ words10List w.b5 ++
  [w.q60.extractLsb' 0 64, w.q60.extractLsb' 64 64, w.w62]

@[simp]
theorem length_words63List (w : Words63) : (words63List w).length = 63 := rfl

def words63At (a : BitVec 64) (w : Words63) : SepProp :=
  words10At a w.b0 ∗
  words10At (a + 80#64) w.b1 ∗
  words10At (a + 160#64) w.b2 ∗
  words10At (a + 240#64) w.b3 ∗
  words10At (a + 320#64) w.b4 ∗
  words10At (a + 400#64) w.b5 ∗
  ((a + 480#64) ↦₁₂₈ w.q60) ∗
  ((a + 496#64) ↦₆₄ w.w62)

theorem words63At_eq_wordsAt (a : BitVec 64) (w : Words63) :
    words63At a w = wordsAt a (words63List w) := by
  unfold words63At words63List
  simp only [List.append_assoc, wordsAt_append, length_words10List,
    ← words10At_eq_wordsAt, pointsTo128_eq_pair64_recv, wordsAt, sepConj_emp,
    bv_add_lit_add_lit_recv, sepConj_assoc]

theorem words63At_entails_memRegion (a : BitVec 64) (w : Words63) :
    words63At a w ⊢ memRegion a 504 := by
  rw [words63At_eq_wordsAt]
  exact wordsAt_entails_memRegion (words63List w) a 504 rfl

theorem recompose63 {F_pred : BitVec 64 → SepProp} (dst : BitVec 64) (w : Words63) :
    words63At dst w ∗ relocatedHeap F_pred (wordsBytes (words63List w)) ⊢ F_pred dst := by
  rw [words63At_eq_wordsAt, wordsAt_eq_pointsToBytes]
  exact relocatedHeap_recompose F_pred (wordsBytes (words63List w)) dst

theorem recompose63_376 {F_pred : BitVec 64 → SepProp} (dst : BitVec 64) (w : Words63)
    (tailBytes : List (BitVec 8)) :
    words63At dst w ∗ ((dst + 504#64) ↦ₛ tailBytes) ∗
      relocatedHeap F_pred (wordsBytes (words63List w) ++ tailBytes) ⊢ F_pred dst := by
  rw [words63At_eq_wordsAt, wordsAt_eq_pointsToBytes, ← sepConj_assoc]
  have happ : (dst ↦ₛ wordsBytes (words63List w)) ∗ ((dst + 504#64) ↦ₛ tailBytes) =
      (dst ↦ₛ (wordsBytes (words63List w) ++ tailBytes)) := by
    rw [pointsToBytes_append dst (wordsBytes (words63List w)) tailBytes,
        length_wordsBytes, length_words63List]
  rw [happ]
  exact relocatedHeap_recompose F_pred (wordsBytes (words63List w) ++ tailBytes) dst

theorem memRegion_80_entails_words10At (a : BitVec 64) :
    memRegion a 80 ⊢ ∃∗ b : Words10, words10At a b := by
  refine Entails.trans (cells_10_unfold a) ?_
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w7
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9
  let b : Words10 := ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩
  refine Entails.sepExists_right b ?_
  rw [words10At_eq_wordsAt]
  exact Entails.refl _

theorem memRegion_16_entails_128_recv (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ q : BitVec 128, (a ↦₁₂₈ q) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  rw [EncoderFromPb.pointsTo64_pair_eq_pointsTo128 a w0 w1]
  exact Entails.sepExists_right (w1 ++ w0) (Entails.refl _)

theorem memRegion_504_entails_words63At (a : BitVec 64) :
    memRegion a 504 ⊢ ∃∗ w : Words63, words63At a w := by
  rw [ProofLib.memRegion_split' (b := a) (n := 80) (k := 424) (b' := a + 80#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 80) (k := 344) (b' := a + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 160#64) (n := 80) (k := 264) (b' := a + 240#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 240#64) (n := 80) (k := 184) (b' := a + 320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 320#64) (n := 80) (k := 104) (b' := a + 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 400#64) (n := 80) (k := 24) (b' := a + 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 480#64) (n := 16) (k := 8) (b' := a + 496#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 496#64)]
  refine Entails.trans (sepConj_mono (memRegion_80_entails_words10At a)
    (sepConj_mono (memRegion_80_entails_words10At (a + 80#64))
      (sepConj_mono (memRegion_80_entails_words10At (a + 160#64))
        (sepConj_mono (memRegion_80_entails_words10At (a + 240#64))
          (sepConj_mono (memRegion_80_entails_words10At (a + 320#64))
            (sepConj_mono (memRegion_80_entails_words10At (a + 400#64))
              (sepConj_mono_left (memRegion_16_entails_128_recv (a + 480#64))))))))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b1
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b2
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b3
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b4
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b5
  rw [← sepConj_assoc, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w62
  rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q60
  simp only [sepConj_assoc]
  exact Entails.sepExists_right ⟨b0, b1, b2, b3, b4, b5, q60, w62⟩ (Entails.refl _)

/-! ## State Extraction Lemmas for `KeysSampled`, `Ct1Received`, `HeaderSent`, `EkSentCt1Received` -/

def mkWords63_50_13 (p : Words5x10) (g : FourVecWords) (ep : BitVec 64) : Words63 :=
  { b0 := p.b0
    b1 := p.b1
    b2 := p.b2
    b3 := p.b3
    b4 := p.b4
    b5 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.rest.v1.w0, g.rest.v1.w1, g.rest.v1.w2,
           g.rest.auth.v1.w0, g.rest.auth.v1.w1, g.rest.auth.v1.w2, g.rest.auth.v2.w0⟩
    q60 := g.rest.auth.v2.w2 ++ g.rest.auth.v2.w1
    w62 := ep }

theorem words63List_mkWords63_50_13 (p : Words5x10) (g : FourVecWords) (ep : BitVec 64) :
    words5x10List p ++ ekSentCt1ReceivedWordsList g ep = words63List (mkWords63_50_13 p g ep) := by
  simp only [words63List, mkWords63_50_13, words5x10List, words10List,
    ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList, authWordsList, vecWordsList,
    Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append, List.append_assoc,
    List.cons_append, List.nil_append]

theorem chunkedKeysSampledAt_extract63 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    chunkedKeysSampledAt A a st ⊢
      ∃∗ w : Words63,
        ⌜w.w62 = st.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) := by
  unfold chunkedKeysSampledAt
  refine Entails.trans (sepConj_mono
    (relocatable_400_extract_words5x10 (Relocatable.of_polyEncoderAt A st.sending_hdr) a)
    (unchunkedHeaderSentAt_extract A (a + 400#64) st.uc)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  let w := mkWords63_50_13 p g st.uc.epoch
  refine Entails.sepExists_right w (Entails.pure_right rfl ?_)
  rw [words63At_eq_wordsAt, ← words63List_mkWords63_50_13]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem chunkedCt1ReceivedAt_extract63 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    chunkedCt1ReceivedAt A a st ⊢
      ∃∗ w : Words63,
        ⌜w.w62 = st.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) := by
  unfold chunkedCt1ReceivedAt
  refine Entails.trans (sepConj_mono
    (relocatable_400_extract_words5x10 (Relocatable.of_polyEncoderAt A st.sending_ek) a)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 400#64) st.uc)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  let w := mkWords63_50_13 p g st.uc.epoch
  refine Entails.sepExists_right w (Entails.pure_right rfl ?_)
  rw [words63At_eq_wordsAt, ← words63List_mkWords63_50_13]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

def mkWords63_13_50 (g : FourVecWords) (ep : BitVec 64) (p : Words5x10) : Words63 :=
  { b0 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.rest.v1.w0, g.rest.v1.w1, g.rest.v1.w2,
           g.rest.auth.v1.w0, g.rest.auth.v1.w1, g.rest.auth.v1.w2, g.rest.auth.v2.w0⟩
    b1 := ⟨g.rest.auth.v2.w1, g.rest.auth.v2.w2, ep,
           p.b0.w0, p.b0.w1, p.b0.w2, p.b0.w3, p.b0.w4, p.b0.w5, p.b0.w6⟩
    b2 := ⟨p.b0.w7, p.b0.w8, p.b0.w9,
           p.b1.w0, p.b1.w1, p.b1.w2, p.b1.w3, p.b1.w4, p.b1.w5, p.b1.w6⟩
    b3 := ⟨p.b1.w7, p.b1.w8, p.b1.w9,
           p.b2.w0, p.b2.w1, p.b2.w2, p.b2.w3, p.b2.w4, p.b2.w5, p.b2.w6⟩
    b4 := ⟨p.b2.w7, p.b2.w8, p.b2.w9,
           p.b3.w0, p.b3.w1, p.b3.w2, p.b3.w3, p.b3.w4, p.b3.w5, p.b3.w6⟩
    b5 := ⟨p.b3.w7, p.b3.w8, p.b3.w9,
           p.b4.w0, p.b4.w1, p.b4.w2, p.b4.w3, p.b4.w4, p.b4.w5, p.b4.w6⟩
    q60 := p.b4.w8 ++ p.b4.w7
    w62 := p.b4.w9 }

theorem words63List_mkWords63_13_50 (g : FourVecWords) (ep : BitVec 64) (p : Words5x10) :
    ekSentCt1ReceivedWordsList g ep ++ words5x10List p = words63List (mkWords63_13_50 g ep p) := by
  simp only [words63List, mkWords63_13_50, words5x10List, words10List,
    ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList, authWordsList, vecWordsList,
    Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append, List.append_assoc,
    List.cons_append, List.nil_append]

theorem chunkedEkSentCt1ReceivedAt_extract63 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    chunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ w : Words63,
        ⌜w.b1.w2 = st.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) := by
  unfold chunkedEkSentCt1ReceivedAt
  refine Entails.trans (sepConj_mono
    (unchunkedEkSentCt1ReceivedAt_extract A a st.uc)
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_ct2) (a + 104#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  let w := mkWords63_13_50 g st.uc.epoch p
  refine Entails.sepExists_right w (Entails.pure_right rfl ?_)
  rw [words63At_eq_wordsAt, ← words63List_mkWords63_13_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

def mkWords63_50_10_3 (p : Words5x10) (g : ThreeVecWords) (ep : BitVec 64) (v : VecWords) : Words63 :=
  { b0 := p.b0
    b1 := p.b1
    b2 := p.b2
    b3 := p.b3
    b4 := p.b4
    b5 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.auth.v1.w0, g.auth.v1.w1, g.auth.v1.w2,
           g.auth.v2.w0, g.auth.v2.w1, g.auth.v2.w2, ep⟩
    q60 := v.w1 ++ v.w0
    w62 := v.w2 }

theorem words63List_mkWords63_50_10_3 (p : Words5x10) (g : ThreeVecWords) (ep : BitVec 64) (v : VecWords) :
    (words5x10List p ++ ekSentWordsList g ep) ++ vecWordsList v =
      words63List (mkWords63_50_10_3 p g ep v) := by
  simp only [words63List, mkWords63_50_10_3, words5x10List, words10List,
    ekSentWordsList, ct2SentWordsList, authWordsList, vecWordsList,
    Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append, List.append_assoc,
    List.cons_append, List.nil_append]

theorem chunkedHeaderSentAt_extract63_376 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderSentAt A a st ⊢
      ∃∗ w : Words63, ∃∗ tailBytes : List (BitVec 8),
        ⌜w.b5.w9 = st.uc.epoch ∧ tailBytes.length = 376⌝ ∗
        words63At a w ∗
        ((a + 504#64) ↦ₛ tailBytes) ∗
        relocatedHeap (fun dst => chunkedHeaderSentAt A dst st)
          (wordsBytes (words63List w) ++ tailBytes) := by
  unfold chunkedHeaderSentAt
  have h12 : polyEncoderAt A a st.sending_ek ∗ unchunkedEkSentAt A (a + 400#64) st.uc ⊢
      ∃∗ p : Words5x10, ∃∗ g : ThreeVecWords,
        wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) := by
    refine Entails.trans (sepConj_mono
      (relocatable_400_extract_words5x10 (Relocatable.of_polyEncoderAt A st.sending_ek) a)
      (unchunkedEkSentAt_extract A (a + 400#64) st.uc)) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
    exact Entails.sepExists_right p (Entails.sepExists_right g (wordsExtract_sepConj rfl (fun _ => rfl)))
  refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm) ?_
  refine Entails.trans (sepConj_mono h12
    (relocatable_400_extract_words3_376 (Relocatable.of_polyDecoderAt A st.receiving_ct1) (a + 480#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro v
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro tailBytes
  rw [sepConj_left_comm (wordsAt a _ ∗ _)]
  apply Entails.pure_left; intro htail
  let w := mkWords63_50_10_3 p g st.uc.epoch v
  refine Entails.sepExists_right w (Entails.sepExists_right tailBytes ?_)
  refine Entails.pure_right ⟨rfl, htail⟩ ?_
  have hw_eq := words63List_mkWords63_50_10_3 p g st.uc.epoch v
  have hwords_a :
      wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗ wordsAt (a + 480#64) (vecWordsList v) =
      words63At a w := by
    rw [words63At_eq_wordsAt a w, ← hw_eq,
        wordsAt_append (words5x10List p ++ ekSentWordsList g st.uc.epoch) (vecWordsList v)]
    simp only [List.length_append, length_words5x10List, length_ekSentWordsList]
  have ha504 : (a + 480#64) + 24#64 = a + 504#64 := by bv_omega
  rw [ha504]
  have hreord :
      (wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))) ∗
      wordsAt (a + 480#64) (vecWordsList v) ∗
      ((a + 504#64) ↦ₛ tailBytes) ∗
      relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
        (wordsBytes (vecWordsList v) ++ tailBytes) =
      (wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗ wordsAt (a + 480#64) (vecWordsList v)) ∗
      ((a + 504#64) ↦ₛ tailBytes) ∗
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
        (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
        (wordsBytes (vecWordsList v) ++ tailBytes)) := by ac_rfl
  rw [hreord, hwords_a]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine relocatedHeap_intro _ fun dst => ?_
  rw [← hw_eq, wordsBytes_append, List.append_assoc,
      pointsToBytes_append dst (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))
        (wordsBytes (vecWordsList v) ++ tailBytes),
      length_wordsBytes]
  simp only [List.length_append, length_words5x10List, length_ekSentWordsList]
  have hdst_reord :
      ((dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       ((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes))) ∗
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
        (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
        (wordsBytes (vecWordsList v) ++ tailBytes)) =
      ((dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
        (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))) ∗
      (((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
        (wordsBytes (vecWordsList v) ++ tailBytes)) := by ac_rfl
  rw [hdst_reord, ← sepConj_assoc (polyEncoderAt A dst st.sending_ek)]
  exact sepConj_mono (relocatedHeap_recompose _ _ dst) (relocatedHeap_recompose _ _ (dst + 480#64))

/-! ## Stack Frame and Output Sret Split/Rejoin Helpers -/

/-- 63-word (`504`-byte) stack spill region at `[fsp + 8 .. fsp + 512)` (`0x008..0x200`),
    plus the 4 slots at `[fsp + 512 .. fsp + 568)` (`0x200..0x238`) and `[fsp + 960 .. fsp + 976)` (`0x3c0..0x3d0`). -/
structure SendEkSpills where
  b0 : Words10
  b1 : Words10
  b2 : Words10
  b3 : Words10
  b4 : Words10
  b5 : Words10
  w60 : BitVec 64
  w61 : BitVec 64
  w62 : BitVec 64
  q200 : BitVec 128
  q210 : BitVec 128
  q220 : BitVec 128
  w230 : BitVec 64
  q3c0 : BitVec 128

def sendEkSpillsAt (fsp : BitVec 64) (sp : SendEkSpills) : SepProp :=
  words10At (fsp + 8#64) sp.b0 ∗
  words10At (fsp + 88#64) sp.b1 ∗
  words10At (fsp + 168#64) sp.b2 ∗
  words10At (fsp + 248#64) sp.b3 ∗
  words10At (fsp + 328#64) sp.b4 ∗
  words10At (fsp + 408#64) sp.b5 ∗
  ((fsp + 488#64) ↦₆₄ sp.w60) ∗
  ((fsp + 496#64) ↦₆₄ sp.w61) ∗
  ((fsp + 504#64) ↦₆₄ sp.w62) ∗
  ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗
  ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
  ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗
  ((fsp + 560#64) ↦₆₄ sp.w230) ∗
  ((fsp + 960#64) ↦₁₂₈ sp.q3c0)

def sendEkUnusedAt (fsp : BitVec 64) : SepProp :=
  memRegion fsp 8 ∗
  memRegion (fsp + 568#64) 8 ∗
  memRegion (fsp + 952#64) 8 ∗
  memRegion (fsp + 2736#64) 1408

theorem memRegion_560_entails_spills_prefix (a : BitVec 64) :
    memRegion a 560 ⊢
      ∃∗ b0 : Words10, ∃∗ b1 : Words10, ∃∗ b2 : Words10,
      ∃∗ b3 : Words10, ∃∗ b4 : Words10, ∃∗ b5 : Words10,
      ∃∗ w60 : BitVec 64, ∃∗ w61 : BitVec 64, ∃∗ w62 : BitVec 64,
      ∃∗ q200 : BitVec 128, ∃∗ q210 : BitVec 128, ∃∗ q220 : BitVec 128,
      ∃∗ w230 : BitVec 64,
        words10At a b0 ∗
        words10At (a + 80#64) b1 ∗
        words10At (a + 160#64) b2 ∗
        words10At (a + 240#64) b3 ∗
        words10At (a + 320#64) b4 ∗
        words10At (a + 400#64) b5 ∗
        ((a + 480#64) ↦₆₄ w60) ∗
        ((a + 488#64) ↦₆₄ w61) ∗
        ((a + 496#64) ↦₆₄ w62) ∗
        ((a + 504#64) ↦₁₂₈ q200) ∗
        ((a + 520#64) ↦₁₂₈ q210) ∗
        ((a + 536#64) ↦₁₂₈ q220) ∗
        ((a + 552#64) ↦₆₄ w230) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 80) (k := 480) (b' := a + 80#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 80) (k := 400) (b' := a + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 160#64) (n := 80) (k := 320) (b' := a + 240#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 240#64) (n := 80) (k := 240) (b' := a + 320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 320#64) (n := 80) (k := 160) (b' := a + 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 400#64) (n := 80) (k := 80) (b' := a + 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 480#64) (n := 8) (k := 72) (b' := a + 488#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 488#64) (n := 8) (k := 64) (b' := a + 496#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 496#64) (n := 8) (k := 56) (b' := a + 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 504#64) (n := 16) (k := 40) (b' := a + 520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 520#64) (n := 16) (k := 24) (b' := a + 536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 536#64) (n := 16) (k := 8) (b' := a + 552#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 480#64),
      ProofLib.memRegion_eight (a + 488#64),
      ProofLib.memRegion_eight (a + 496#64),
      ProofLib.memRegion_eight (a + 552#64)]
  refine Entails.trans (sepConj_mono (memRegion_80_entails_words10At a)
    (sepConj_mono (memRegion_80_entails_words10At (a + 80#64))
      (sepConj_mono (memRegion_80_entails_words10At (a + 160#64))
        (sepConj_mono (memRegion_80_entails_words10At (a + 240#64))
          (sepConj_mono (memRegion_80_entails_words10At (a + 320#64))
            (sepConj_mono (memRegion_80_entails_words10At (a + 400#64))
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (memRegion_16_entails_128_recv (a + 504#64))
                  (sepConj_mono (memRegion_16_entails_128_recv (a + 520#64))
                    (sepConj_mono_left (memRegion_16_entails_128_recv (a + 536#64)))))))))))))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b1
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b2
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b3
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b4
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b5
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w60
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w61
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w62
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q200
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q210
  rw [← sepConj_assoc, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w230
  rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q220
  simp only [sepConj_assoc]
  exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.sepExists_right b2
    (Entails.sepExists_right b3 (Entails.sepExists_right b4 (Entails.sepExists_right b5
      (Entails.sepExists_right w60 (Entails.sepExists_right w61 (Entails.sepExists_right w62
        (Entails.sepExists_right q200 (Entails.sepExists_right q210 (Entails.sepExists_right q220
          (Entails.sepExists_right w230 (Entails.refl _)))))))))))))

theorem words10At_entails_memRegion_80 (a : BitVec 64) (b : Words10) :
    words10At a b ⊢ memRegion a 80 := by
  rw [words10At_eq_wordsAt]
  exact wordsAt_entails_memRegion (words10List b) a 80 rfl

theorem pointsTo128_entails_memRegion_16 (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) ⊢ memRegion a 16 := by
  rw [pointsTo128_eq_pair64_recv,
      ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono
    (ProofLib.pointsTo64_entails_memRegion a _)
    (ProofLib.pointsTo64_entails_memRegion (a + 8#64) _)

theorem memRegion_4144_entails_sendEkFrame (fsp : BitVec 64) :
    memRegion fsp 4144 ⊢
      ∃∗ sp : SendEkSpills,
        sendEkSpillsAt fsp sp ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗
        sendEkUnusedAt fsp := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 4136) (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 560) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 16) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 880) (k := 1408) (b' := fsp + 2736#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono (memRegion_560_entails_spills_prefix (fsp + 8#64))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 960#64)))))))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b4
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b5
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w60
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w61
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w62
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro q200
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro q210
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro q220
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w230
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro q3c0
  refine Entails.sepExists_right ⟨b0, b1, b2, b3, b4, b5, w60, w61, w62, q200, q210, q220, w230, q3c0⟩ ?_
  unfold sendEkSpillsAt sendEkUnusedAt
  simp only [bv_add_lit_add_lit_recv,
    show BitVec.ofNat 64 (8 + 80) = 88#64 from rfl,
    show BitVec.ofNat 64 (8 + 160) = 168#64 from rfl,
    show BitVec.ofNat 64 (8 + 240) = 248#64 from rfl,
    show BitVec.ofNat 64 (8 + 320) = 328#64 from rfl,
    show BitVec.ofNat 64 (8 + 400) = 408#64 from rfl,
    show BitVec.ofNat 64 (8 + 480) = 488#64 from rfl,
    show BitVec.ofNat 64 (8 + 488) = 496#64 from rfl,
    show BitVec.ofNat 64 (8 + 496) = 504#64 from rfl,
    show BitVec.ofNat 64 (8 + 504) = 512#64 from rfl,
    show BitVec.ofNat 64 (8 + 520) = 528#64 from rfl,
    show BitVec.ofNat 64 (8 + 536) = 544#64 from rfl,
    show BitVec.ofNat 64 (8 + 552) = 560#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

theorem sendEkFrame_entails_memRegion_4144 (fsp : BitVec 64) (sp : SendEkSpills) :
    sendEkSpillsAt fsp sp ∗
    memRegion (fsp + 576#64) 376 ∗
    memRegion (fsp + 976#64) 880 ∗
    memRegion (fsp + 1856#64) 880 ∗
    sendEkUnusedAt fsp ⊢
      memRegion fsp 4144 := by
  have h560 :
      words10At (fsp + 8#64) sp.b0 ∗
      words10At (fsp + 88#64) sp.b1 ∗
      words10At (fsp + 168#64) sp.b2 ∗
      words10At (fsp + 248#64) sp.b3 ∗
      words10At (fsp + 328#64) sp.b4 ∗
      words10At (fsp + 408#64) sp.b5 ∗
      ((fsp + 488#64) ↦₆₄ sp.w60) ∗
      ((fsp + 496#64) ↦₆₄ sp.w61) ∗
      ((fsp + 504#64) ↦₆₄ sp.w62) ∗
      ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗
      ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
      ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗
      ((fsp + 560#64) ↦₆₄ sp.w230) ⊢ memRegion (fsp + 8#64) 560 := by
    rw [ProofLib.memRegion_split' (b := fsp + 8#64) (n := 80) (k := 480) (b' := fsp + 88#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 88#64) (n := 80) (k := 400) (b' := fsp + 168#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 168#64) (n := 80) (k := 320) (b' := fsp + 248#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 248#64) (n := 80) (k := 240) (b' := fsp + 328#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 328#64) (n := 80) (k := 160) (b' := fsp + 408#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 408#64) (n := 80) (k := 80) (b' := fsp + 488#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 488#64) (n := 8) (k := 72) (b' := fsp + 496#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 496#64) (n := 8) (k := 64) (b' := fsp + 504#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 504#64) (n := 8) (k := 56) (b' := fsp + 512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 512#64) (n := 16) (k := 40) (b' := fsp + 528#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 528#64) (n := 16) (k := 24) (b' := fsp + 544#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 544#64) (n := 16) (k := 8) (b' := fsp + 560#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (words10At_entails_memRegion_80 _ _)
      (sepConj_mono (words10At_entails_memRegion_80 _ _)
        (sepConj_mono (words10At_entails_memRegion_80 _ _)
          (sepConj_mono (words10At_entails_memRegion_80 _ _)
            (sepConj_mono (words10At_entails_memRegion_80 _ _)
              (sepConj_mono (words10At_entails_memRegion_80 _ _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo128_entails_memRegion_16 _ _)
                        (sepConj_mono (pointsTo128_entails_memRegion_16 _ _)
                          (sepConj_mono (pointsTo128_entails_memRegion_16 _ _)
                            (ProofLib.pointsTo64_entails_memRegion _ _))))))))))))
  unfold sendEkSpillsAt sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 4136) (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 560) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 16) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 880) (k := 1408) (b' := fsp + 2736#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗
    ((words10At (fsp + 8#64) sp.b0 ∗
      words10At (fsp + 88#64) sp.b1 ∗
      words10At (fsp + 168#64) sp.b2 ∗
      words10At (fsp + 248#64) sp.b3 ∗
      words10At (fsp + 328#64) sp.b4 ∗
      words10At (fsp + 408#64) sp.b5 ∗
      ((fsp + 488#64) ↦₆₄ sp.w60) ∗
      ((fsp + 496#64) ↦₆₄ sp.w61) ∗
      ((fsp + 504#64) ↦₆₄ sp.w62) ∗
      ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗
      ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
      ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗
      ((fsp + 560#64) ↦₆₄ sp.w230)) ∗
     (memRegion (fsp + 568#64) 8 ∗
      (memRegion (fsp + 576#64) 376 ∗
       (memRegion (fsp + 952#64) 8 ∗
        (((fsp + 960#64) ↦₁₂₈ sp.q3c0) ∗
         (memRegion (fsp + 976#64) 880 ∗
          (memRegion (fsp + 1856#64) 880 ∗
           memRegion (fsp + 2736#64) 1408))))))) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono h560
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 960#64) sp.q3c0))))))

attribute [local arm64_norm, local wp_norm]
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48

@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_8_recv (sp : BitVec 64) : (sp - 96#64) + 8#64 = sp - 88#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8_recv (sp : BitVec 64) : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_64_add_8_recv (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_48_add_8_recv (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_32_add_8_recv (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_16_add_8_recv (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_96_recv (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega

/-- Shared epilogue `0x59fd0..0x59ff0` (`+19324 -> +19356`):
    restores `sp`, `x19..x30`, and returns to `s0.readReg64 .x30`. -/
theorem states_recv_epilogue_59fd0 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  states_recv_fetches_range b (Rust.withPanics ext) 19324 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_conv_pre => dsimp only [statesRecvSavedCells]
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' ⊢
  wp_steps
  subst hsp0
  refine SepWP.fold (F := P_rest) (stack_restore_statesRecv s0) ?_ ?_
  · unfold statesRecvSavedCells
    ac_rfl
  · wp_done

/-- Framed `memcpy` call rule that relocates any `Relocatable n F` predicate from `src` to `dst`,
    leaving `memRegion src n` at `src`, and forwards `CalleeSavedPreserved s sf`. -/
theorem call_memcpy_relocate_cs {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- The 63 words (`504` bytes) written to `words63At (outA + 8#64)` by the shared
    `Ok(V1Recv)` writeback block `0x59e88..0x59fa0` from register state `s` and
    stack spills `sp : SendEkSpills`. -/
def writebackWords63 (s : State) (sp : SendEkSpills) : Words63 :=
  { b0 := ⟨s.readReg64 .x1, s.readReg64 .x8, sp.w61, sp.b5.w6, sp.b4.w6,
           sp.b4.w5, sp.w62, sp.b3.w5, sp.b5.w3, sp.b5.w0⟩
    b1 := ⟨sp.b4.w3, sp.b4.w7, sp.b4.w1, sp.b3.w6, sp.b5.w2,
           s.readReg64 .x23, s.readReg64 .x27, sp.b5.w4, sp.b3.w2, sp.b4.w2⟩
    b2 := ⟨sp.b4.w8, sp.b3.w3, sp.b4.w4, sp.b4.w9, sp.b5.w7,
           sp.b3.w7, sp.b4.w0, sp.b3.w4, sp.b3.w9, s.readReg64 .x3⟩
    b3 := ⟨sp.b3.w8, s.readReg64 .x24, s.readReg64 .x25, s.readReg64 .x12, s.readReg64 .x11,
           s.readReg64 .x10, s.readReg64 .x15, s.readReg64 .x28, s.readReg64 .x7, s.readReg64 .x0⟩
    b4 := ⟨s.readReg64 .x6, s.readReg64 .x30, s.readReg64 .x21, s.readReg64 .x9, sp.b5.w1,
           s.readReg64 .x17, sp.b5.w8, s.readReg64 .x26, s.readReg64 .x5, s.readReg64 .x4⟩
    b5 := ⟨sp.b5.w5, s.readReg64 .x22, s.readReg64 .x13, s.readReg64 .x14, sp.b5.w9,
           s.readReg64 .x16, sp.w60, s.readReg64 .x2, sp.b3.w0, s.readReg64 .x20⟩
    q60 := sp.q3c0
    w62 := sp.b3.w1 }

theorem memRegion_32_entails_q2 (a : BitVec 64) :
    memRegion a 32 ⊢ ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) := by
  rw [ProofLib.memRegion_split a 16 16 (by decide)]
  refine Entails.trans (sepConj_mono (memRegion_16_entails_128_recv a)
    (memRegion_16_entails_128_recv (a + 16#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q0
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro q1
  exact Entails.sepExists_right q0 (Entails.sepExists_right q1 (Entails.refl _))

theorem q2_entails_memRegion_32 (a : BitVec 64) (q0 q1 : BitVec 128) :
    (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ⊢ memRegion a 32 := by
  rw [ProofLib.memRegion_split a 16 16 (by decide)]
  exact sepConj_mono (pointsTo128_entails_memRegion_16 a q0)
    (pointsTo128_entails_memRegion_16 (a + 16#64) q1)

theorem memRegion_40_entails_q2_w1 (a : BitVec 64) :
    memRegion a 40 ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ w2 : BitVec 64,
        (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ∗ ((a + 32#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 32 8 (by decide), ProofLib.memRegion_eight (a + 32#64)]
  refine Entails.trans (sepConj_mono_left (memRegion_32_entails_q2 a)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q0
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w2
  simp only [sepConj_assoc]
  exact Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right w2 (Entails.refl _)))

theorem q2_w1_entails_memRegion_40 (a : BitVec 64) (q0 q1 : BitVec 128) (w2 : BitVec 64) :
    (a ↦₁₂₈ q0) ∗ ((a + 16#64) ↦₁₂₈ q1) ∗ ((a + 32#64) ↦₆₄ w2) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split a 32 8 (by decide), ← sepConj_assoc]
  exact sepConj_mono (q2_entails_memRegion_32 a q0 q1)
    (ProofLib.pointsTo64_entails_memRegion (a + 32#64) w2)

theorem memRegion_32_entails_w2_q1 (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ q2 : BitVec 128,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₁₂₈ q2) := by
  rw [ProofLib.memRegion_split a 8 24 (by decide), ProofLib.memRegion_eight a, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (memRegion_16_entails_128_recv (a + 16#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro q2
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right q2 (Entails.refl _)))

theorem memRegion_960_entails_writebackOut (outA : BitVec 64) :
    memRegion outA v1RecvSize ⊢
      ∃∗ v0 : BitVec 64, ∃∗ w : Words63,
      ∃∗ q888 : BitVec 128, ∃∗ q904 : BitVec 128,
      ∃∗ w920 : BitVec 64, ∃∗ w928 : BitVec 64,
      ∃∗ w936 : BitVec 64, ∃∗ q944 : BitVec 128,
        (outA ↦₆₄ v0) ∗
        words63At (outA + 8#64) w ∗
        memRegion (outA + 512#64) 376 ∗
        ((outA + 888#64) ↦₁₂₈ q888) ∗
        ((outA + 904#64) ↦₁₂₈ q904) ∗
        ((outA + 920#64) ↦₆₄ w920) ∗
        ((outA + 928#64) ↦₆₄ w928) ∗
        ((outA + 936#64) ↦₆₄ w936) ∗
        ((outA + 944#64) ↦₁₂₈ q944) := by
  unfold v1RecvSize
  rw [ProofLib.memRegion_split outA 8 952 (by decide),
      ProofLib.memRegion_eight outA, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v0
  rw [ProofLib.memRegion_split' (b := outA + 8#64) (n := 504) (k := 448)
        (b' := outA + 512#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (memRegion_504_entails_words63At (outA + 8#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w
  rw [ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 72)
        (b' := outA + 888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 888#64) (n := 40) (k := 32)
        (b' := outA + 928#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_40_entails_q2_w1 (outA + 888#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro q888
  apply Entails.sepExists_elim; intro q904
  apply Entails.sepExists_elim; intro w920
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (memRegion_32_entails_w2_q1 (outA + 928#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro w928
  apply Entails.sepExists_elim; intro w936
  apply Entails.sepExists_elim; intro q944
  exact Entails.sepExists_right v0 (Entails.sepExists_right w
    (Entails.sepExists_right q888 (Entails.sepExists_right q904
      (Entails.sepExists_right w920 (Entails.sepExists_right w928
        (Entails.sepExists_right w936 (Entails.sepExists_right q944 (Entails.refl _))))))))

set_option maxHeartbeats 1200000 in
/-- Shared `Ok(V1Recv)` writeback + epilogue `0x59e88..0x59ff0` (`+18996 -> +19356`):
    - Stores `sp.b2.w7` to `[outA + 0]` and `writebackWords63 s sp` (`504`B) to `[outA + 8 .. outA + 512)`.
    - Calls `memcpy(outA + 512#64, (s0.sp - 4240#64) + 576#64, 376)` at `0x59fa4` to relocate `F_tail`.
    - Writes `40`B at `[outA + 888 .. outA + 928)` (folded into `memRegion (outA + 888#64) 40`) and
      `32`B at `[outA + 928 .. outA + 960)` (`sp.b2.w8`, `s.readReg64 .x20`, `sp.q200`).
    - Folds the `4144`B stack frame and executes `0x59fd0..0x59ff0` to return to `s0.readReg64 .x30`. -/
theorem states_recv_writeback_59e88 {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          (outA ↦₆₄ sp.b2.w7) ∗
          words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗
          memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  have hepilogue := @states_recv_epilogue_59fd0 b ext s0
  states_recv_fetches_range b (Rust.withPanics ext) 18996 328
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  refine SepWP.fold (memRegion_960_entails_writebackOut outA) (by sep_focus) ?_
  wp_pull_exists; rename_i v0 w_init q888 q904 w920 w928 w936 q944
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine call_memcpy_relocate_cs (ret_pc := entry + 19284#64)
    hmemcpy_raw hrel (outA + 512#64) (sp0 - 3664#64)
    rfl hrun hsp hfsp_align rfl htr rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans hx19
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 := hcs1.2.1
  wp_steps
  subst hsp0
  refine SepWP.fold
    (F := P_rest ∗
      (outA ↦₆₄ sp.b2.w7) ∗
      words63At (outA + 8#64) (writebackWords63 s sp) ∗
      F_tail (outA + 512#64) ∗
      ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
      ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
      ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      statesRecvSavedCells s0)
    (sepConj_mono (q2_w1_entails_memRegion_40 (outA + 888#64) sp.q210 sp.q220 sp.w230)
      (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp))
    ?_ ?_
  · dsimp only [words63At, writebackWords63, sendEkSpillsAt, words10At, Reg.x0, Reg.x1, Reg.x2,
      Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13,
      Reg.x14, Reg.x15, Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.x30]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion (outA + 888#64) 40 ∗ memRegion (s0.sp - 4240#64) 4144) ∗
        (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0) =
        (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hepilogue _
        (P_rest ∗
          (outA ↦₆₄ sp.b2.w7) ∗
          words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗
          memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200))
        rfl ?_ ?_ hsp_align ?_)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · exact hrun1
    · exact hsp1
    · exact htr1

end CryptoVerification.SpqrV1.States.Recv
