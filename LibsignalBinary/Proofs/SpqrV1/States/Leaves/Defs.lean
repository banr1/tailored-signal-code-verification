/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# SPQR V1 Chunked Braid Leaf Transitions: Shared Definitions & Send-Leaf Specifications

**Checked by Lean.**

Symbol names, instruction decode trees (`spqrStatesLeavesBin`), address-independent relocation
combinators (`relocatedHeap`, `Relocatable`), word-tuple extraction predicates, and separation-logic
specifications for `<Ct2Sampled>::recv_next_epoch`, `<EkReceivedCt1Sampled>::send_ct1_chunk`,
`<Ct2Sampled>::send_ct2_chunk`, `<HeaderSent>::send_ek_chunk`, `<Ct1Received>::send_ek_chunk`,
and `<Ct1Sampled>::send_ct1_chunk`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Symbol Names and Offsets -/

abbrev ct2SampledRecvNextEpochName : String :=
  "<spqr::v1::chunked::send_ct::Ct2Sampled>::recv_next_epoch"

abbrev ekReceivedCt1SampledSendCt1ChunkName : String :=
  "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::send_ct1_chunk"

abbrev ct2SampledSendCt2ChunkName : String :=
  "<spqr::v1::chunked::send_ct::Ct2Sampled>::send_ct2_chunk"

abbrev headerSentSendEkChunkName : String :=
  "<spqr::v1::chunked::send_ek::HeaderSent>::send_ek_chunk"

abbrev ct1ReceivedSendEkChunkName : String :=
  "<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk"

abbrev ct1SampledSendCt1ChunkName : String :=
  "<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk"

@[simp, arm64_norm] theorem ct2SampledRecvNextEpoch_fnOff :
    libsignalSessionCode.fnOff ct2SampledRecvNextEpochName = 0x5a664 :=
  libsignalSessionCode_fnOff_0x5a664

@[simp, arm64_norm] theorem ekReceivedCt1SampledSendCt1Chunk_fnOff :
    libsignalSessionCode.fnOff ekReceivedCt1SampledSendCt1ChunkName = 0x58dd8 :=
  libsignalSessionCode_fnOff_0x58dd8

@[simp, arm64_norm] theorem ct2SampledSendCt2Chunk_fnOff :
    libsignalSessionCode.fnOff ct2SampledSendCt2ChunkName = 0x5a5dc :=
  libsignalSessionCode_fnOff_0x5a5dc

@[simp, arm64_norm] theorem headerSentSendEkChunk_fnOff :
    libsignalSessionCode.fnOff headerSentSendEkChunkName = 0x58468 :=
  libsignalSessionCode_fnOff_0x58468

@[simp, arm64_norm] theorem ct1ReceivedSendEkChunk_fnOff :
    libsignalSessionCode.fnOff ct1ReceivedSendEkChunkName = 0x58e58 :=
  libsignalSessionCode_fnOff_0x58e58

@[simp, arm64_norm] theorem ct1SampledSendCt1Chunk_fnOff :
    libsignalSessionCode.fnOff ct1SampledSendCt1ChunkName = 0x583c4 :=
  libsignalSessionCode_fnOff_0x583c4

/-! ## 2. SIMD 128-Bit Concatenation / Extraction & Word-Slice Bridge Lemmas -/

@[simp, arm64_norm, wp_norm]
theorem extractLsb'_0_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[simp, arm64_norm, wp_norm]
theorem extractLsb'_64_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

/-- Byte list representation of a list of 64-bit little-endian words. -/
def wordsBytes : List (BitVec 64) → List (BitVec 8)
  | [] => []
  | w :: ws => unpack64 w ++ wordsBytes ws

@[simp]
theorem wordsBytes_nil : wordsBytes [] = [] := rfl

@[simp]
theorem wordsBytes_cons (w : BitVec 64) (ws : List (BitVec 64)) :
    wordsBytes (w :: ws) = unpack64 w ++ wordsBytes ws := rfl

@[simp]
theorem length_wordsBytes : ∀ ws : List (BitVec 64), (wordsBytes ws).length = 8 * ws.length
  | [] => rfl
  | w :: ws => by
    simp only [wordsBytes_cons, List.length_append, unpack64_length, length_wordsBytes ws,
      List.length_cons]
    omega

/-- Contiguous 64-bit word cells starting at `a`. -/
def wordsAt (a : BitVec 64) : List (BitVec 64) → SepProp
  | [] => emp
  | w :: ws => (a ↦₆₄ w) ∗ wordsAt (a + 8#64) ws

theorem wordsAt_eq_pointsToBytes :
    ∀ (ws : List (BitVec 64)) (a : BitVec 64),
      wordsAt a ws = (a ↦ₛ wordsBytes ws)
  | [], a => by
    simp only [wordsAt, wordsBytes, pointsToBytes_nil]
  | w :: ws, a => by
    simp only [wordsAt, wordsBytes_cons]
    rw [pointsToBytes_append a (unpack64 w) (wordsBytes ws), unpack64_length,
        ← pointsTo64_eq_pointsToBytes a w,
        wordsAt_eq_pointsToBytes ws (a + BitVec.ofNat 64 8)]

/-! ## 3. Instruction Decode Trees (`spqrStatesLeavesBin`) -/

gen_decodes libsignalSessionCode_tree spqrStatesLeavesBin [
  0x583c4 → 0x58464,
  0x58468 → 0x58500,
  0x58dd8 → 0x58e54,
  0x58e58 → 0x58ef8,
  0x5a5dc → 0x5a660,
  0x5a664 → 0x5a6dc
]

/-! ## 4. Address-Independent Relocation Combinators (`relocatedHeap`, `Relocatable`) -/

theorem wordsAt_entails_memRegion (ws : List (BitVec 64)) (a : BitVec 64) (n : Nat)
    (hn : 8 * ws.length = n) :
    wordsAt a ws ⊢ memRegion a n := by
  rw [wordsAt_eq_pointsToBytes, ← hn, ← length_wordsBytes ws]
  exact pointsToBytes_entails_memRegion a (wordsBytes ws)

theorem wordsAt_append (ws1 ws2 : List (BitVec 64)) (a : BitVec 64) :
    wordsAt a (ws1 ++ ws2) =
      wordsAt a ws1 ∗ wordsAt (a + BitVec.ofNat 64 (8 * ws1.length)) ws2 := by
  induction ws1 generalizing a with
  | nil => simp [wordsAt, emp_sepConj]
  | cons w ws1 ih =>
    simp only [List.cons_append, wordsAt, ih (a + 8#64)]
    have haddr : (a + 8#64) + BitVec.ofNat 64 (8 * ws1.length) =
        a + BitVec.ofNat 64 (8 * (w :: ws1).length) := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
      bv_omega
    rw [haddr]
    ac_rfl

/-- Address-independent heap resource for relocating a `SepProp` family `F : BitVec 64 → SepProp`
    along with its inline byte slice `bs`. -/
def relocatedHeap (F : BitVec 64 → SepProp) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ P : SepProp, ⌜∀ dst : BitVec 64, (dst ↦ₛ bs) ∗ P ⊢ F dst⌝ ∗ P

theorem relocatedHeap_intro {F : BitVec 64 → SepProp} {bs : List (BitVec 8)} (P : SepProp)
    (h : ∀ dst : BitVec 64, (dst ↦ₛ bs) ∗ P ⊢ F dst) :
    P ⊢ relocatedHeap F bs :=
  Entails.sepExists_right P (Entails.pure_right h (Entails.refl P))

theorem relocatedHeap_recompose (F : BitVec 64 → SepProp) (bs : List (BitVec 8)) (dst : BitVec 64) :
    (dst ↦ₛ bs) ∗ relocatedHeap F bs ⊢ F dst := by
  unfold relocatedHeap
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro h
  exact h dst

/-- `Relocatable n F` means that for any `src`, `F src` decomposes into an `n`-byte slice
    `(src ↦ₛ bs)` (`bs.length = n`) and `relocatedHeap F bs`. -/
def Relocatable (n : Nat) (F : BitVec 64 → SepProp) : Prop :=
  ∀ src : BitVec 64,
    F src ⊢ ∃∗ bs : List (BitVec 8),
      ⌜bs.length = n⌝ ∗ (src ↦ₛ bs) ∗ relocatedHeap F bs

theorem Relocatable.congr {n m : Nat} {F G : BitVec 64 → SepProp}
    (hnm : n = m) (hFG : ∀ a, F a = G a) (hF : Relocatable n F) : Relocatable m G := by
  subst hnm
  have heq : F = G := funext hFG
  exact heq ▸ hF

theorem Relocatable.pointsTo64 (w : BitVec 64) : Relocatable 8 (fun a => a ↦₆₄ w) := by
  intro src; dsimp only
  refine Entails.sepExists_right (unpack64 w) ?_
  refine Entails.pure_right (unpack64_length w) ?_
  rw [pointsTo64_eq_pointsToBytes src w]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ unpack64 w)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, pointsTo64_eq_pointsToBytes dst w]
  exact Entails.refl _

theorem Relocatable.pointsTo32 (w : BitVec 32) : Relocatable 4 (fun a => a ↦₃₂ w) := by
  intro src; dsimp only
  refine Entails.sepExists_right (unpack32 w) ?_
  refine Entails.pure_right (unpack32_length w) ?_
  rw [pointsTo32_eq_pointsToBytes src w]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ unpack32 w)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, pointsTo32_eq_pointsToBytes dst w]
  exact Entails.refl _

theorem Relocatable.pointsTo8 (b : BitVec 8) : Relocatable 1 (fun a => a ↦₈ b) := by
  intro src; dsimp only
  refine Entails.sepExists_right [b] ?_
  refine Entails.pure_right rfl ?_
  rw [← pointsToBytes_singleton src b]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ [b])]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, pointsToBytes_singleton dst b]
  exact Entails.refl _

theorem Relocatable.of_memRegion (n : Nat) (hn : n ≤ 2 ^ 64 := by decide) :
    Relocatable n (fun a => memRegion a n) := by
  intro src; dsimp only
  rw [memRegion_eq_exists_bytes src n hn]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs ?_
  refine Entails.pure_right hlen ?_
  conv_lhs => rw [← sepConj_emp (src ↦ₛ bs)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, ← hlen]
  exact pointsToBytes_entails_memRegion dst bs

theorem Relocatable.pure_left {n : Nat} (P : Prop) {F : BitVec 64 → SepProp}
    (hF : P → Relocatable n F) : Relocatable n (fun a => ⌜P⌝ ∗ F a) := by
  intro src; dsimp only
  apply Entails.pure_left; intro hP
  refine Entails.trans (hF hP src) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  refine sepConj_mono_right (relocatedHeap_intro (relocatedHeap F bs) fun dst => ?_)
  exact Entails.pure_right hP (relocatedHeap_recompose F bs dst)

theorem Relocatable.sepConj {n k m : Nat} {off : BitVec 64} {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 n) (hm : n + k = m)
    (hF : Relocatable n F) (hG : Relocatable k G) :
    Relocatable m (fun a => F a ∗ G (a + off)) := by
  intro src; dsimp only
  refine Entails.trans (sepConj_mono (hF src) (hG (src + off))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  rw [sepConj_assoc (⌜bs1.length = n⌝)]
  apply Entails.pure_left; intro hlen1
  rw [sepConj_left_comm ((src ↦ₛ bs1) ∗ relocatedHeap F bs1)]
  apply Entails.pure_left; intro hlen2
  refine Entails.sepExists_right (bs1 ++ bs2) ?_
  have hlen12 : (bs1 ++ bs2).length = m := by rw [List.length_append, hlen1, hlen2, hm]
  refine Entails.pure_right hlen12 ?_
  have hsplit_src : (src ↦ₛ (bs1 ++ bs2)) = (src ↦ₛ bs1) ∗ ((src + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append src bs1 bs2, hlen1, ← hoff]
  have hreord :
      ((src ↦ₛ bs1) ∗ relocatedHeap F bs1) ∗ ((src + off) ↦ₛ bs2) ∗ relocatedHeap G bs2 =
        ((src ↦ₛ bs1) ∗ ((src + off) ↦ₛ bs2)) ∗ (relocatedHeap F bs1 ∗ relocatedHeap G bs2) := by ac_rfl
  rw [hreord, ← hsplit_src]
  refine sepConj_mono_right (relocatedHeap_intro (relocatedHeap F bs1 ∗ relocatedHeap G bs2) fun dst => ?_)
  have hsplit_dst : (dst ↦ₛ (bs1 ++ bs2)) = (dst ↦ₛ bs1) ∗ ((dst + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append dst bs1 bs2, hlen1, ← hoff]
  have hreord_dst :
      ((dst ↦ₛ bs1) ∗ ((dst + off) ↦ₛ bs2)) ∗ (relocatedHeap F bs1 ∗ relocatedHeap G bs2) =
        ((dst ↦ₛ bs1) ∗ relocatedHeap F bs1) ∗ (((dst + off) ↦ₛ bs2) ∗ relocatedHeap G bs2) := by ac_rfl
  rw [hsplit_dst, hreord_dst]
  exact sepConj_mono (relocatedHeap_recompose F bs1 dst) (relocatedHeap_recompose G bs2 (dst + off))

theorem Relocatable.vecOf {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (xs : List α) :
    Relocatable 24 (fun a => vecOf A stride align elem a xs) := by
  intro src
  dsimp only [RustHeap.vecOf, RustHeap.vecAt, RustHeap.vecHeader]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  have hhdr : Relocatable 24 (fun a =>
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length)) := by
    have h23 := Relocatable.sepConj (off := 8#64) (m := 16) rfl rfl
      (Relocatable.pointsTo64 ptr) (Relocatable.pointsTo64 (BitVec.ofNat 64 xs.length))
    have h123 := Relocatable.sepConj (off := 8#64) (m := 24) rfl rfl
      (Relocatable.pointsTo64 cap) h23
    refine Relocatable.congr rfl (fun a => ?_) h123
    rw [BitVec.add_assoc a 8#64 8#64]
    rfl
  let Rest := vecBuf A stride align elem cap ptr xs
  refine Entails.trans (sepConj_mono_left (hhdr src)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_assoc (⌜bs.length = 24⌝)]
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  rw [sepConj_assoc (src ↦ₛ bs)]
  refine sepConj_mono_right (relocatedHeap_intro (relocatedHeap _ bs ∗ Rest) fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [← sepConj_assoc (dst ↦ₛ bs)]
  exact sepConj_mono_left (relocatedHeap_recompose _ bs dst)

theorem Relocatable.arrayAt {α : Type} {stride : Nat} {elem : α → BitVec 64 → SepProp}
    (h : ∀ x : α, Relocatable stride (fun a => elem x a))
    (xs : List α) (m : Nat) (hm : stride * xs.length = m) :
    Relocatable m (fun a => RustHeap.arrayAt elem stride a xs) := by
  induction xs generalizing m with
  | nil =>
    subst hm
    intro src
    simp only [RustHeap.arrayAt, Nat.mul_zero]
    refine Entails.sepExists_right [] (Entails.pure_right rfl ?_)
    rw [pointsToBytes_nil, emp_sepConj]
    exact relocatedHeap_intro emp fun dst => by rw [pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
  | cons x xs ih =>
    have htl := ih (stride * xs.length) rfl
    have hcons := Relocatable.sepConj (off := BitVec.ofNat 64 stride) (m := m) rfl
      (by simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hm; omega)
      (h x) htl
    exact Relocatable.congr rfl (fun _ => rfl) hcons

theorem Relocatable.of_polyEncoderAt (A : RustAlloc) (enc : PolyEncoder) :
    Relocatable 400 (fun a => polyEncoderAt A a enc) := by
  have hstate : Relocatable 392 (fun a => encoderStateAt A a enc.s) := by
    cases hs : enc.s with
    | points pts =>
      dsimp only [encoderStateAt]
      refine Relocatable.pure_left
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555))
        fun ⟨hlen, _⟩ => ?_
      have harr : Relocatable 384 (fun a => pointListOf A a pts) :=
        Relocatable.arrayAt (elem := fun pt addr => pointOf A addr pt)
          (fun pt => Relocatable.vecOf A gf16Stride gf16Align gf16At pt.value)
          pts 384 (by rw [hlen]; rfl)
      exact Relocatable.sepConj (off := polyEncoderVecsOff) (m := 392) rfl rfl
        (Relocatable.pointsTo64 polyEncoderPointsTag) harr
    | polys ps =>
      dsimp only [encoderStateAt]
      refine Relocatable.pure_left (ps.length = NUM_POLYS) fun hlen => ?_
      have harr : Relocatable 384 (fun a => polyListOf A a ps) :=
        Relocatable.arrayAt (elem := fun p addr => polyOf A addr p)
          (fun p => Relocatable.vecOf A gf16Stride gf16Align gf16At p.coefficients)
          ps 384 (by rw [hlen]; rfl)
      exact Relocatable.sepConj (off := polyEncoderVecsOff) (m := 392) rfl rfl
        (Relocatable.pointsTo64 polyEncoderPolysTag) harr
  have hfull := Relocatable.sepConj (off := 392#64) (m := 400) rfl rfl hstate
    (Relocatable.sepConj (off := 4#64) (m := 8) rfl rfl
      (Relocatable.pointsTo32 enc.idx) (Relocatable.of_memRegion 4))
  refine Relocatable.congr rfl (fun a => ?_) hfull
  unfold polyEncoderAt polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  have h1 : a + 392#64 = a + 0x188#64 := rfl
  have h2 : (a + 392#64) + 4#64 = a + 0x18c#64 := by bv_omega
  rw [h1, h2]

theorem Relocatable.of_polyDecoderAt (A : RustAlloc) (dec : PolyDecoder) :
    Relocatable 400 (fun a => polyDecoderAt A a dec) := by
  unfold Poly.polyDecoderAt
  refine Relocatable.pure_left (dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64) fun ⟨hlen, _⟩ => ?_
  have harr : Relocatable 384 (fun a => sortedSetPtListOf A a dec.pts) :=
    Relocatable.arrayAt (elem := fun s addr => sortedSetPtOf A addr s)
      (fun s => Relocatable.vecOf A ptStride ptAlign ptAt s.vec)
      dec.pts 384 (by rw [hlen]; rfl)
  have htail2 : Relocatable 8 (fun a =>
      ((a + 0#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (a + 1#64) 7) := by
    have h := Relocatable.sepConj (off := 1#64) (m := 8) rfl rfl
      (Relocatable.pointsTo8 (boolByte dec.isComplete)) (Relocatable.of_memRegion 7)
    refine Relocatable.congr rfl (fun a => ?_) h
    rw [BitVec.add_zero]
  have htail16 := Relocatable.sepConj (off := 8#64) (m := 16) rfl rfl
    (Relocatable.pointsTo64 (BitVec.ofNat 64 dec.ptsNeeded)) htail2
  have hfull := Relocatable.sepConj (off := 384#64) (m := 400) rfl rfl harr htail16
  refine Relocatable.congr rfl (fun a => ?_) hfull
  unfold polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  have h1 : a + 384#64 = a + 0x180#64 := rfl
  have h2 : ((a + 384#64) + 8#64) + 0#64 = a + 0x188#64 := by bv_omega
  have h3 : ((a + 384#64) + 8#64) + 1#64 = a + 0x189#64 := by bv_omega
  rw [h2, h3, h1]

/-! ## 5. Word-Tuple Extraction Combinators & Representation Predicates -/

@[simp]
theorem wordsAt_nil (a : BitVec 64) : wordsAt a [] = emp := rfl

theorem wordsAt_cons_off (base off : BitVec 64) (w : BitVec 64) (ws : List (BitVec 64)) :
    wordsAt (base + off) (w :: ws) =
      ((base + off) ↦₆₄ w) ∗ wordsAt (base + (off + 8#64)) ws := by
  simp only [wordsAt, BitVec.add_assoc]

theorem relocatedHeap_congr {F G : BitVec 64 → SepProp} {bs : List (BitVec 8)}
    (hFG : ∀ a, F a = G a) :
    relocatedHeap F bs ⊢ relocatedHeap G bs := by
  have heq : F = G := funext hFG
  exact heq ▸ Entails.refl _

theorem relocatedHeap_words_sepConj {F G : BitVec 64 → SepProp}
    (ws1 ws2 : List (BitVec 64)) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (8 * ws1.length)) :
    relocatedHeap F (wordsBytes ws1) ∗ relocatedHeap G (wordsBytes ws2) ⊢
      relocatedHeap (fun a => F a ∗ G (a + off)) (wordsBytes (ws1 ++ ws2)) := by
  refine relocatedHeap_intro (relocatedHeap F (wordsBytes ws1) ∗ relocatedHeap G (wordsBytes ws2)) fun dst => ?_
  rw [← wordsAt_eq_pointsToBytes, wordsAt_append, ← hoff, wordsAt_eq_pointsToBytes, wordsAt_eq_pointsToBytes]
  have hreord :
      ((dst ↦ₛ wordsBytes ws1) ∗ ((dst + off) ↦ₛ wordsBytes ws2)) ∗
        (relocatedHeap F (wordsBytes ws1) ∗ relocatedHeap G (wordsBytes ws2)) =
      ((dst ↦ₛ wordsBytes ws1) ∗ relocatedHeap F (wordsBytes ws1)) ∗
        (((dst + off) ↦ₛ wordsBytes ws2) ∗ relocatedHeap G (wordsBytes ws2)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono (relocatedHeap_recompose F _ dst) (relocatedHeap_recompose G _ (dst + off))

theorem wordsExtract_sepConj {F G H : BitVec 64 → SepProp}
    {ws1 ws2 : List (BitVec 64)} {a off : BitVec 64}
    (hoff : off = BitVec.ofNat 64 (8 * ws1.length))
    (hH : ∀ dst, F dst ∗ G (dst + off) = H dst) :
    (wordsAt a ws1 ∗ relocatedHeap F (wordsBytes ws1)) ∗
      (wordsAt (a + off) ws2 ∗ relocatedHeap G (wordsBytes ws2)) ⊢
    wordsAt a (ws1 ++ ws2) ∗ relocatedHeap H (wordsBytes (ws1 ++ ws2)) := by
  rw [wordsAt_append, ← hoff]
  have hreord :
      (wordsAt a ws1 ∗ relocatedHeap F (wordsBytes ws1)) ∗
        (wordsAt (a + off) ws2 ∗ relocatedHeap G (wordsBytes ws2)) =
      (wordsAt a ws1 ∗ wordsAt (a + off) ws2) ∗
        (relocatedHeap F (wordsBytes ws1) ∗ relocatedHeap G (wordsBytes ws2)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right
    (Entails.trans (relocatedHeap_words_sepConj ws1 ws2 off hoff) (relocatedHeap_congr hH))

theorem emp_entails_relocatedHeap_word (w : BitVec 64) :
    emp ⊢ relocatedHeap (fun a => a ↦₆₄ w) (wordsBytes [w]) := by
  refine relocatedHeap_intro emp fun dst => ?_
  rw [sepConj_emp, ← wordsAt_eq_pointsToBytes]
  simp only [wordsAt, sepConj_emp]
  exact Entails.refl _

theorem word_extract (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ wordsAt a [w] ∗ relocatedHeap (fun dst => dst ↦₆₄ w) (wordsBytes [w]) := by
  simp only [wordsAt, sepConj_emp]
  conv_lhs => rw [← sepConj_emp (a ↦₆₄ w)]
  exact sepConj_mono_right (emp_entails_relocatedHeap_word w)

/-- 3-word header tuple `(cap, ptr, len)` of a `Vec<u8>`. -/
structure VecWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64

def vecWordsList (v : VecWords) : List (BitVec 64) :=
  [v.w0, v.w1, v.w2]

@[simp]
theorem length_vecWordsList (v : VecWords) : (vecWordsList v).length = 3 := rfl

theorem vecU8_extract (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v ?_
  have hhdr : ∀ dst : BitVec 64,
      ((dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) =
      wordsAt dst (vecWordsList v) := by
    intro dst
    simp only [vecWordsList, wordsAt, sepConj_emp]
    have h16 : (dst + 8#64) + 8#64 = dst + 16#64 := by bv_omega
    rw [h16]
  rw [hhdr a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [hhdr dst, wordsAt_eq_pointsToBytes]
  exact Entails.refl _

/-- 6-word header tuple for `Authenticator` (`root_key`, `mac_key`). -/
structure AuthWords where
  v1 : VecWords
  v2 : VecWords

def authWordsList (g : AuthWords) : List (BitVec 64) :=
  [g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2]

@[simp]
theorem length_authWordsList (g : AuthWords) : (authWordsList g).length = 6 := rfl

theorem authenticatorAt_extract (A : RustAlloc) (a : BitVec 64) (auth : Authenticator) :
    authenticatorAt A a auth ⊢
      ∃∗ g : AuthWords,
        wordsAt a (authWordsList g) ∗
        relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) := by
  unfold authenticatorAt
  refine Entails.trans (sepConj_mono (vecU8_extract A a auth.rootKey) (vecU8_extract A (a + 0x18#64) auth.macKey)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro v2
  refine Entails.sepExists_right ⟨v1, v2⟩ ?_
  exact wordsExtract_sepConj rfl (fun _ => rfl)

/-! ### Word-List Extraction for `unchunked::*` States -/

def ct2SentWordsList (g : AuthWords) (ep : BitVec 64) : List (BitVec 64) :=
  authWordsList g ++ [ep]

@[simp]
theorem length_ct2SentWordsList (g : AuthWords) (ep : BitVec 64) :
    (ct2SentWordsList g ep).length = 7 := rfl

theorem unchunkedCt2SentAt_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) :
    unchunkedCt2SentAt A a st ⊢
      ∃∗ g : AuthWords,
        wordsAt a (ct2SentWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst st)
          (wordsBytes (ct2SentWordsList g st.epoch)) := by
  unfold unchunkedCt2SentAt
  refine Entails.trans (sepConj_mono (authenticatorAt_extract A a st.auth) (word_extract (a + 48#64) st.epoch)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  exact wordsExtract_sepConj rfl (fun _ => rfl)

structure ThreeVecWords where
  v1 : VecWords
  auth : AuthWords

def ekSentWordsList (g : ThreeVecWords) (ep : BitVec 64) : List (BitVec 64) :=
  vecWordsList g.v1 ++ ct2SentWordsList g.auth ep

@[simp]
theorem length_ekSentWordsList (g : ThreeVecWords) (ep : BitVec 64) :
    (ekSentWordsList g ep).length = 10 := rfl

theorem unchunkedEkSentAt_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A a st ⊢
      ∃∗ g : ThreeVecWords,
        wordsAt a (ekSentWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedEkSentAt A dst st)
          (wordsBytes (ekSentWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st2 : Unchunked.SendCt.Ct2Sent (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.dk⟩⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedCt2SentAt A (dst + 24#64) st2 =
        unchunkedEkSentAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.dk) ∗
        (((dst + 24#64) + 48#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.dk ∗
        ((dst + 72#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract A a r0)
    (unchunkedCt2SentAt_extract A (a + 24#64) st2)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro auth
  refine Entails.sepExists_right ⟨v1, auth⟩ ?_
  exact wordsExtract_sepConj rfl heq

structure FourVecWords where
  v1 : VecWords
  rest : ThreeVecWords

def ekSentCt1ReceivedWordsList (g : FourVecWords) (ep : BitVec 64) : List (BitVec 64) :=
  vecWordsList g.v1 ++ ekSentWordsList g.rest ep

@[simp]
theorem length_ekSentCt1ReceivedWordsList (g : FourVecWords) (ep : BitVec 64) :
    (ekSentCt1ReceivedWordsList g ep).length = 13 := rfl

theorem unchunkedEkSentCt1ReceivedAt_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ g : FourVecWords,
        wordsAt a (ekSentCt1ReceivedWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
          (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st3 : Unchunked.SendEk.EkSent (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.dk⟩, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentAt A (dst + 24#64) st3 =
        unchunkedEkSentCt1ReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.dk) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ct1 ∗ (((dst + 24#64) + 72#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.dk ∗
        vecU8 A (dst + 72#64) st.ct1 ∗ ((dst + 96#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract A a r0)
    (unchunkedEkSentAt_extract A (a + 24#64) st3)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  refine Entails.sepExists_right ⟨v1, rest⟩ ?_
  exact wordsExtract_sepConj rfl heq

theorem unchunkedHeaderSentAt_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.HeaderSent (spqrAuthApi F)) :
    unchunkedHeaderSentAt A a st ⊢
      ∃∗ g : FourVecWords,
        wordsAt a (ekSentCt1ReceivedWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedHeaderSentAt A dst st)
          (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) :=
  unchunkedEkSentCt1ReceivedAt_extract A a (unchunkedHeaderSentToEkSentCt1Received st)

structure FiveVecWords where
  v1 : VecWords
  rest : FourVecWords

def fiveVecWordsList (g : FiveVecWords) (ep : BitVec 64) : List (BitVec 64) :=
  vecWordsList g.v1 ++ ekSentCt1ReceivedWordsList g.rest ep

@[simp]
theorem length_fiveVecWordsList (g : FiveVecWords) (ep : BitVec 64) :
    (fiveVecWordsList g ep).length = 16 := rfl

theorem unchunkedCt1SentEkReceivedAt_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A a st ⊢
      ∃∗ g : FiveVecWords,
        wordsAt a (fiveVecWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst st)
          (wordsBytes (fiveVecWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st4 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.es⟩, st.ek, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentCt1ReceivedAt A (dst + 24#64) st4 =
        unchunkedCt1SentEkReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.es) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ek ∗ vecU8 A ((dst + 24#64) + 72#64) st.ct1 ∗
        (((dst + 24#64) + 96#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.es ∗
        vecU8 A (dst + 72#64) st.ek ∗ vecU8 A (dst + 96#64) st.ct1 ∗
        ((dst + 120#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64, BitVec.add_assoc dst 24#64 96#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract A a r0)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 24#64) st4)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  refine Entails.sepExists_right ⟨v1, rest⟩ ?_
  exact wordsExtract_sepConj rfl heq

theorem unchunkedCt1SentAt_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A a st ⊢
      ∃∗ g : FiveVecWords,
        wordsAt a (fiveVecWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt1SentAt A dst st)
          (wordsBytes (fiveVecWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st4 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.hdr⟩, st.es, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentCt1ReceivedAt A (dst + 24#64) st4 =
        unchunkedCt1SentAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.hdr) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.es ∗ vecU8 A ((dst + 24#64) + 72#64) st.ct1 ∗
        (((dst + 24#64) + 96#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.hdr ∗
        vecU8 A (dst + 72#64) st.es ∗ vecU8 A (dst + 96#64) st.ct1 ∗
        ((dst + 120#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64, BitVec.add_assoc dst 24#64 96#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract A a r0)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 24#64) st4)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  refine Entails.sepExists_right ⟨v1, rest⟩ ?_
  exact wordsExtract_sepConj rfl heq

/-! ## 6. Target Specifications -/

/-- Ghost arguments for `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, 31 insns). -/
structure Ct2SampledRecvNextEpochGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)
  epoch : Epoch
  out : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)

/-- Specification of `<spqr::v1::chunked::send_ct::Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, 31 insns). -/
def ct2SampledRecvNextEpochSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct2SampledRecvNextEpochGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧ s.readReg64 .x2 = x.epoch ∧
      x.st.recv_next_epoch x.epoch = .ok x.out⌝ ∗
      memRegion x.outA 56 ∗
      chunkedCt2SampledAt A x.stA x.st ∗
      A.pool ∗ stackAt s.sp (dropGluePoly16Stack + 32)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedKeysUnsampledAt A x.outA x.out ∗
      memRegion x.stA 456 ∗
      A.pool ∗ stackAt s0.sp (dropGluePoly16Stack + 32)

/-- Ghost arguments for `<EkReceivedCt1Sampled>::send_ct1_chunk` (`0x5e1d0`, 32 insns). -/
structure EkReceivedCt1SampledSendCt1ChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)
  outSt : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::send_ct1_chunk` (`0x5e1d0`, 32 insns). -/
def ekReceivedCt1SampledSendCt1ChunkSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (528 + chunkSize) ∗
      chunkedEkReceivedCt1SampledAt A x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 960)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedEkReceivedCt1SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 528#64) x.chunk ∗
      memRegion x.stA 528 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 960)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost arguments for `<Ct2Sampled>::send_ct2_chunk` (`0x5f9d4`, 34 insns). -/
structure Ct2SampledSendCt2ChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)
  outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ct::Ct2Sampled>::send_ct2_chunk` (`0x5f9d4`, 34 insns). -/
def ct2SampledSendCt2ChunkSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (Ct2SampledSendCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct2_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (456 + chunkSize) ∗
      chunkedCt2SampledAt A x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 896)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt2SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 456#64) x.chunk ∗
      memRegion x.stA 456 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 896)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost arguments for `<HeaderSent>::send_ek_chunk` (`0x5d860`, 39 insns). -/
structure HeaderSentSendEkChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)
  outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ek::HeaderSent>::send_ek_chunk` (`0x5d860`, 39 insns). -/
def headerSentSendEkChunkSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (HeaderSentSendEkChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (880 + chunkSize) ∗
      chunkedHeaderSentAt A x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 1328)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedHeaderSentAt A x.outA x.outSt ∗
      chunkAt (x.outA + 880#64) x.chunk ∗
      memRegion x.stA 880 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 1328)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost arguments for `<Ct1Received>::send_ek_chunk` (`0x5e250`, 41 insns). -/
structure Ct1ReceivedSendEkChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)
  outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk` (`0x5e250`, 41 insns). -/
def ct1ReceivedSendEkChunkSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (Ct1ReceivedSendEkChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 944)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt1ReceivedAt A x.outA x.outSt ∗
      chunkAt (x.outA + 504#64) x.chunk ∗
      memRegion x.stA 504 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 944)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost arguments for `<Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`, 41 insns). -/
structure Ct1SampledSendCt1ChunkGhost (F : ShaCompress) where
  outA : BitVec 64
  stA : BitVec 64
  st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)
  outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`, 41 insns). -/
def ct1SampledSendCt1ChunkSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (Ct1SampledSendCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (928 + chunkSize) ∗
      chunkedCt1SampledAt A x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 1376)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt1SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 928#64) x.chunk ∗
      memRegion x.stA 928 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 1376)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 7. `Relocatable` for `unchunked::*` & `chunked::*` States and Pure Inversion Lemmas -/

theorem Relocatable.of_wordsExtract {α : Type} {n : Nat} {F : BitVec 64 → SepProp}
    {ws : α → List (BitVec 64)}
    (hlen : ∀ g : α, 8 * (ws g).length = n)
    (hext : ∀ a : BitVec 64, F a ⊢
      ∃∗ g : α, wordsAt a (ws g) ∗ relocatedHeap F (wordsBytes (ws g))) :
    Relocatable n F := by
  intro src
  refine Entails.trans (hext src) ?_
  apply Entails.sepExists_elim; intro g
  rw [wordsAt_eq_pointsToBytes]
  refine Entails.sepExists_right (wordsBytes (ws g)) ?_
  exact Entails.pure_right (by rw [length_wordsBytes, hlen g]) (Entails.refl _)

theorem Relocatable.of_unchunkedCt2SentAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) :
    Relocatable 56 (fun a => unchunkedCt2SentAt A a st) :=
  Relocatable.of_wordsExtract (fun _ => rfl) (fun a => unchunkedCt2SentAt_extract A a st)

theorem Relocatable.of_unchunkedEkSentAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    Relocatable 80 (fun a => unchunkedEkSentAt A a st) :=
  Relocatable.of_wordsExtract (fun _ => rfl) (fun a => unchunkedEkSentAt_extract A a st)

theorem Relocatable.of_unchunkedEkSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    Relocatable 104 (fun a => unchunkedEkSentCt1ReceivedAt A a st) :=
  Relocatable.of_wordsExtract (fun _ => rfl) (fun a => unchunkedEkSentCt1ReceivedAt_extract A a st)

theorem Relocatable.of_unchunkedCt1SentEkReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    Relocatable 128 (fun a => unchunkedCt1SentEkReceivedAt A a st) :=
  Relocatable.of_wordsExtract (fun _ => rfl) (fun a => unchunkedCt1SentEkReceivedAt_extract A a st)

theorem Relocatable.of_unchunkedCt1SentAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    Relocatable 128 (fun a => unchunkedCt1SentAt A a st) :=
  Relocatable.of_wordsExtract (fun _ => rfl) (fun a => unchunkedCt1SentAt_extract A a st)

theorem Relocatable.of_chunkedCt2SampledAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 456 (fun a => chunkedCt2SampledAt A a st) :=
  Relocatable.sepConj (off := 400#64) (m := 456) rfl rfl
    (Relocatable.of_polyEncoderAt A st.sending_ct2)
    (Relocatable.of_unchunkedCt2SentAt A st.uc)

theorem Relocatable.of_chunkedEkReceivedCt1SampledAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 528 (fun a => chunkedEkReceivedCt1SampledAt A a st) :=
  Relocatable.sepConj (off := 400#64) (m := 528) rfl rfl
    (Relocatable.of_polyEncoderAt A st.sending_ct1)
    (Relocatable.of_unchunkedCt1SentEkReceivedAt A st.uc)

theorem Relocatable.of_chunkedCt1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedCt1ReceivedAt A a st) :=
  Relocatable.sepConj (off := 400#64) (m := 504) rfl rfl
    (Relocatable.of_polyEncoderAt A st.sending_ek)
    (Relocatable.of_unchunkedEkSentCt1ReceivedAt A st.uc)

theorem Relocatable.of_chunkedHeaderSentAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    Relocatable 880 (fun a => chunkedHeaderSentAt A a st) := by
  have h23 := Relocatable.sepConj (off := 80#64) (m := 480) rfl rfl
    (Relocatable.of_unchunkedEkSentAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ct1)
  have h123 := Relocatable.sepConj (off := 400#64) (m := 880) rfl rfl
    (Relocatable.of_polyEncoderAt A st.sending_ek) h23
  refine Relocatable.congr rfl (fun a => ?_) h123
  unfold chunkedHeaderSentAt
  rw [BitVec.add_assoc a 400#64 80#64]; rfl

theorem Relocatable.of_chunkedCt1SampledAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 928 (fun a => chunkedCt1SampledAt A a st) := by
  have h23 := Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
    (Relocatable.of_unchunkedCt1SentAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ek)
  have h123 := Relocatable.sepConj (off := 400#64) (m := 928) rfl rfl
    (Relocatable.of_polyEncoderAt A st.sending_ct1) h23
  refine Relocatable.congr rfl (fun a => ?_) h123
  unfold chunkedCt1SampledAt
  rw [BitVec.add_assoc a 400#64 128#64]; rfl

theorem ct2Sampled_recv_next_epoch_ok {F : ShaCompress}
    {st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)} {epoch : Epoch}
    {out : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)}
    (h : st.recv_next_epoch epoch = .ok out) :
    st.uc.epoch ≠ BitVec.allOnes 64 ∧ st.uc.epoch + 1#64 = epoch ∧
      out = { uc := { epoch := epoch, auth := st.uc.auth } } := by
  unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch at h
  dsimp [Bind.bind, Except.bind] at h
  cases huc : st.uc.recv_next_epoch epoch with
  | error e => rw [huc] at h; contradiction
  | ok u =>
    rw [huc] at h
    cases h
    unfold Unchunked.SendCt.Ct2Sent.recv_next_epoch at huc
    dsimp only at huc
    split at huc
    · contradiction
    · rename_i hne1
      split at huc
      · contradiction
      · rename_i hne2
        cases huc
        have h1 : st.uc.epoch ≠ BitVec.allOnes 64 := by
          intro heq; exact hne1 (beq_iff_eq.mpr heq)
        have h2 : st.uc.epoch + 1#64 = epoch := by
          by_contra hne
          exact hne2 (bne_iff_ne.mpr hne)
        exact ⟨h1, h2, by rw [h2]⟩

private theorem mapError_ok_inv {ε ε' α : Type} {f : ε → ε'} {r : Except ε α} {v : α}
    (h : r.mapError f = .ok v) : r = .ok v := by
  cases r with
  | error e => contradiction
  | ok a => cases h; rfl

theorem ekReceivedCt1Sampled_send_ct1_chunk_ok {F : ShaCompress}
    {st outSt : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    (h : st.send_ct1_chunk = .ok (outSt, chunk)) :
    st.sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk) ∧
      outSt = { uc := st.uc, sending_ct1 := outSt.sending_ct1 } := by
  unfold Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at h
  dsimp [spqrPolyApi, Bind.bind, Except.bind] at h
  cases hnc : st.sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic with
  | error e => rw [hnc] at h; contradiction
  | ok p =>
    rw [hnc] at h
    rcases p with ⟨enc', ch⟩
    cases h
    exact ⟨mapError_ok_inv hnc, rfl⟩

theorem ct2Sampled_send_ct2_chunk_ok {F : ShaCompress}
    {st outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    (h : st.send_ct2_chunk = .ok (outSt, chunk)) :
    st.sending_ct2.nextChunk = .ok (outSt.sending_ct2, chunk) ∧
      outSt = { uc := st.uc, sending_ct2 := outSt.sending_ct2 } := by
  unfold Chunked.SendCt.Ct2Sampled.send_ct2_chunk at h
  dsimp [spqrPolyApi, Bind.bind, Except.bind] at h
  cases hnc : st.sending_ct2.nextChunk.mapError PolyPanic.toSpqrPanic with
  | error e => rw [hnc] at h; contradiction
  | ok p =>
    rw [hnc] at h
    rcases p with ⟨enc', ch⟩
    cases h
    exact ⟨mapError_ok_inv hnc, rfl⟩

theorem headerSent_send_ek_chunk_ok {F : ShaCompress}
    {st outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    (h : st.send_ek_chunk = .ok (outSt, chunk)) :
    st.sending_ek.nextChunk = .ok (outSt.sending_ek, chunk) ∧
      outSt = { uc := st.uc, sending_ek := outSt.sending_ek, receiving_ct1 := st.receiving_ct1 } := by
  unfold Chunked.SendEk.HeaderSent.send_ek_chunk at h
  dsimp [spqrPolyApi, Bind.bind, Except.bind] at h
  cases hnc : st.sending_ek.nextChunk.mapError PolyPanic.toSpqrPanic with
  | error e => rw [hnc] at h; contradiction
  | ok p =>
    rw [hnc] at h
    rcases p with ⟨enc', ch⟩
    cases h
    exact ⟨mapError_ok_inv hnc, rfl⟩

theorem ct1Received_send_ek_chunk_ok {F : ShaCompress}
    {st outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    (h : st.send_ek_chunk = .ok (outSt, chunk)) :
    st.sending_ek.nextChunk = .ok (outSt.sending_ek, chunk) ∧
      outSt = { uc := st.uc, sending_ek := outSt.sending_ek } := by
  unfold Chunked.SendEk.Ct1Received.send_ek_chunk at h
  dsimp [spqrPolyApi, Bind.bind, Except.bind] at h
  cases hnc : st.sending_ek.nextChunk.mapError PolyPanic.toSpqrPanic with
  | error e => rw [hnc] at h; contradiction
  | ok p =>
    rw [hnc] at h
    rcases p with ⟨enc', ch⟩
    cases h
    exact ⟨mapError_ok_inv hnc, rfl⟩

theorem ct1Sampled_send_ct1_chunk_ok {F : ShaCompress}
    {st outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    (h : st.send_ct1_chunk = .ok (outSt, chunk)) :
    st.sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk) ∧
      outSt = { uc := st.uc, sending_ct1 := outSt.sending_ct1, receiving_ek := st.receiving_ek } := by
  unfold Chunked.SendCt.Ct1Sampled.send_ct1_chunk at h
  dsimp [spqrPolyApi, Bind.bind, Except.bind] at h
  cases hnc : st.sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic with
  | error e => rw [hnc] at h; contradiction
  | ok p =>
    rw [hnc] at h
    rcases p with ⟨enc', ch⟩
    cases h
    exact ⟨mapError_ok_inv hnc, rfl⟩

end CryptoVerification.SpqrV1.States.Leaves
