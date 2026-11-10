/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInner
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Inner Chunk Loop and Outer Slot Steps

**Checked by Lean.**

Proves the 4-byte big-endian point decoding loop (`+304..+672`), outer-iteration completion
(`+672 → +204 / +876`), OOM panic block (`+1288`), and valid / invalid outer-loop steps (`+204`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Drop (vecPtOf vecPtListOf
  sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf)
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L37a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm]
  fp_add_448_sub_32 fp_add_448_sub_32_int
  fp_add_448_sub_24 fp_add_448_sub_24_int
  fp_add_448_sub_16 fp_add_448_sub_16_int
  truncate16_truncate32 and_ffff_truncate32 and_ffff_zeroExtend64_truncate32
  ofNat_add_one madd_24_eq

@[simp, local arm64_norm, local wp_norm]
theorem fsp_add_416_add_8 (fsp : BitVec 64) :
    fsp + 416#64 + 8#64 = fsp + 424#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fsp_add_416_add_16 (fsp : BitVec 64) :
    fsp + 416#64 + 16#64 = fsp + 432#64 := by bv_omega

/-! ## 4-Byte Big-Endian Point Decoding and Inner Loop (`+304 -> +672`) -/

theorem pointsToBytes_four_cons (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    (a ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) =
      (a ↦₃₂ (b3 ++ (b2 ++ (b1 ++ b0)))) ∗ ((a + 4#64) ↦ₛ rest) := by
  rw [pointsTo32_eq_pointsToBytes]
  have hsplit : (b0 :: b1 :: b2 :: b3 :: rest) = [b0, b1, b2, b3] ++ rest := rfl
  conv_lhs => rw [hsplit, pointsToBytes_append]
  dsimp only [List.length_cons, List.length_nil]
  congr 2
  simp only [unpack32, List.cons.injEq, and_true]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

/-- Single 4-byte chunk step (`0x62c4c..0x62c44`, `entry + 304#64` to `entry + 296#64`). -/
theorem fromPb_inner_step_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64} (hA : AllocContracts b A ext)
    (fsp cap ptr chunkPtr : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) (s : SortedSetPt)
    (hlt_cap : s.vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hlen : s.vec.length ≤ 65536)
    (st : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 304#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (hx19 : st.readReg64 .x19 = 1#64)
    (hx22 : st.readReg64 .x22 = ptr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length)
    (hx28 : st.readReg64 .x28 = chunkPtr)
    (hx29 : st.readReg64 .x29 = fsp + 448#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = st.sp →
      sf.trace = st.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = st.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64
        (bsearchPush s { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }).vec.length →
      sf.readReg64 .x28 = chunkPtr + 4#64 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr
          (bsearchPush s { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }) ∗
          (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗
          stackAt st.sp 0 ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗
        (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗
        stackAt st.sp 0 ∗ P)
      post := by
  let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
  have hpush := @fromPb_bsearchPush_at_320_sepWP b A ext target_pc hA fsp cap ptr s pt
    hlt_cap hcap hlen
  from_pb_fetches_range b (Rust.withPanics ext) 304 16
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpush hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  rw [pointsToBytes_four_cons chunkPtr b0 b1 b2 b3 rest]
  wp_steps 4
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hpush _ ((chunkPtr ↦₃₂ (b3 ++ (b2 ++ (b1 ++ b0)))) ∗ ((chunkPtr + 4#64) ↦ₛ rest) ∗ P) _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [wp_norm, arm64_norm] using hsp_al)
      (by simp [wp_norm, arm64_norm, hx19])
      (by dsimp only [pt, GF16.new]; simp only [wp_norm, arm64_norm, rev16_64, u16FromBeBytes]; bv_robdd)
      (by simp [wp_norm, arm64_norm, hx22])
      (by simp [wp_norm, arm64_norm, hx26])
      (by dsimp only [pt, GF16.new]; simp only [wp_norm, arm64_norm, rev16_64, u16FromBeBytes]; bv_robdd)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_))
  have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm] using hsp_f
  refine SepWP.weaken_pre
    (P' := tempVecPtAt A fsp cap ptr (bsearchPush s pt) ∗
      (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗ stackAt st.sp 0 ∗ P)
    (by rw [pointsToBytes_four_cons chunkPtr b0 b1 b2 b3 rest]; exact Entails.of_eq (by ac_rfl)) ?_
  apply hnext sf hpc_f hrun_f hsp_f'
  · simpa [wp_norm, arm64_norm] using htr_f
  · exact hx19_f
  · simpa [wp_norm, arm64_norm] using hx21_f
  · exact hx22_f
  · simpa [wp_norm, arm64_norm] using hx24_f
  · simpa [wp_norm, arm64_norm] using hx25_f
  · exact hx26_f
  · simpa [wp_norm, arm64_norm, hx28] using hx28_f
  · exact hx29_f
  · simpa [wp_norm, arm64_norm] using hvregs_f

theorem bv64_mul4_succ_sub_four (n : Nat) :
    BitVec.ofNat 64 (4 * (n + 1)) - 4#64 = BitVec.ofNat 64 (4 * n) := by
  have h : 4 * (n + 1) = 4 * n + 4 := by omega
  rw [h, BitVec.ofNat_add]
  bv_omega

/-- Multi-chunk inner loop (`0x62c4c..0x62dbc`, `entry + 304#64` to `entry + 672#64`). -/
theorem fromPb_inner_loop_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64} (hA : AllocContracts b A ext)
    (fsp cap ptr : BitVec 64)
    (hcap : cap.toNat * 4 < 2 ^ 63) :
    ∀ (n : Nat) (rem : List (BitVec 8)) (chunkPtr : BitVec 64) (s : SortedSetPt)
      (st : State) (P : SepProp) (post : State → SepProp → Prop),
      rem.length = 4 * (n + 1) →
      s.vec.length + (n + 1) ≤ cap.toNat →
      SortedSetPtStrictSorted s →
      st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 304#64 →
      st.status = .Running →
      st.spAligned = true →
      st.readReg64 .x19 = 1#64 →
      st.readReg64 .x21 = BitVec.ofNat 64 (4 * (n + 1)) →
      st.readReg64 .x22 = ptr →
      st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length →
      st.readReg64 .x28 = chunkPtr →
      st.readReg64 .x29 = fsp + 448#64 →
      (∀ sf : State,
        sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 672#64 →
        sf.status = .Running →
        sf.sp = st.sp →
        sf.trace = st.trace →
        sf.readReg64 .x19 = 1#64 →
        sf.readReg64 .x22 = ptr →
        sf.readReg64 .x24 = st.readReg64 .x24 →
        sf.readReg64 .x25 = st.readReg64 .x25 →
        sf.readReg64 .x26 = BitVec.ofNat 64 (pushChunks4Total rem s).vec.length →
        sf.readReg64 .x29 = fsp + 448#64 →
        calleeSavedVRegs sf = calleeSavedVRegs st →
        SepWP (tripleRatchetProgAtExt b ext) target_pc sf
          (tempVecPtAt A fsp cap ptr (pushChunks4Total rem s) ∗
            (chunkPtr ↦ₛ rem) ∗
            stackAt st.sp 0 ∗ P)
          post) →
      SepWP (tripleRatchetProgAtExt b ext) target_pc st
        (tempVecPtAt A fsp cap ptr s ∗
          (chunkPtr ↦ₛ rem) ∗
          stackAt st.sp 0 ∗ P)
        post := by
  intro n
  induction n with
  | zero =>
    intro rem chunkPtr s st P post hrem_len hle_cap hsort hpc hrun hsp_al
      hx19 hx21 hx22 hx26 hx28 hx29 hnext
    rcases rem with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
    · simp at hrem_len
    · simp at hrem_len
    · simp at hrem_len
    · simp at hrem_len
    · let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
      have ⟨hpush_bsearch, _⟩ := bsearchPush_eq_push s pt hsort
      have hpush_eq : pushChunks4Total [b0, b1, b2, b3] s = bsearchPush s pt := by
        unfold pushChunks4Total
        exact hpush_bsearch.symm
      have hlen : s.vec.length ≤ 65536 := ptListStrictSorted_length_le hsort
      rw [hpush_eq] at hnext
      refine fromPb_inner_step_sepWP hA fsp cap ptr chunkPtr b0 b1 b2 b3 [] s
        (by omega) hcap hlen st P post hpc hrun hsp_al hx19 hx22 hx26 hx28 hx29 ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1
      from_pb_fetches_range b (Rust.withPanics ext) 296 8
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc1 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      have hx21_s1 : s1.readReg64 (Reg.gpr 21#5) = 4#64 := hx21_1.trans hx21
      wp_steps 2
      apply hnext <;> simp [wp_norm, arm64_norm, pt, *]
    · simp at hrem_len
  | succ n ih =>
    intro rem chunkPtr s st P post hrem_len hle_cap hsort hpc hrun hsp_al
      hx19 hx21 hx22 hx26 hx28 hx29 hnext
    rcases rem with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
    · simp at hrem_len
    · simp at hrem_len; omega
    · simp at hrem_len; omega
    · simp at hrem_len; omega
    · have hrest_len : rest.length = 4 * (n + 1) := by simp at hrem_len; omega
      let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
      have ⟨hpush_bsearch, hsort'⟩ := bsearchPush_eq_push s pt hsort
      have hpush_step :
          pushChunks4Total (b0 :: b1 :: b2 :: b3 :: rest) s =
            pushChunks4Total rest (bsearchPush s pt) := by
        change pushChunks4Total rest (s.push pt).1 = pushChunks4Total rest (bsearchPush s pt)
        rw [← hpush_bsearch]
      have hlen : s.vec.length ≤ 65536 := ptListStrictSorted_length_le hsort
      rw [hpush_step] at hnext
      refine fromPb_inner_step_sepWP hA fsp cap ptr chunkPtr b0 b1 b2 b3 rest s
        (by omega) hcap hlen st P post hpc hrun hsp_al hx19 hx22 hx26 hx28 hx29 ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1
      have hsub4 : BitVec.ofNat 64 (4 * (n + 1 + 1)) - 4#64 = BitVec.ofNat 64 (4 * (n + 1)) :=
        bv64_mul4_succ_sub_four (n + 1)
      have hne0 : (BitVec.ofNat 64 (4 * (n + 1)) == 0#64) = false :=
        ofNat_beq_zero_false (by omega) (by omega)
      have hx21_s1 : s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (4 * (n + 1 + 1)) := hx21_1.trans hx21
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
      from_pb_fetches_range b (Rust.withPanics ext) 296 8
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at ih hpc1 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      wp_steps 2
      have hpush_len : (bsearchPush s pt).vec.length ≤ s.vec.length + 1 := by
        rw [hpush_bsearch]
        exact push_vec_length_le_succ s pt
      rw [pointsToBytes_four_cons chunkPtr b0 b1 b2 b3 rest]
      rw [← hsp1]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (ih rest (chunkPtr + 4#64) (bsearchPush s pt) _
          ((chunkPtr ↦₃₂ (b3 ++ (b2 ++ (b1 ++ b0)))) ∗ P) post
          hrest_len (by omega) hsort'
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun1])
          (by simpa [wp_norm, arm64_norm] using hsp1_al)
          (by simp [wp_norm, arm64_norm, hx19_1])
          (by simp [wp_norm, arm64_norm, hx21_s1, hsub4])
          (by simp [wp_norm, arm64_norm, hx22_1])
          (by simp [wp_norm, arm64_norm, pt, hx26_1])
          (by simp [wp_norm, arm64_norm, hx28_1])
          (by simp [wp_norm, arm64_norm, hx29_1])
          (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx22_f hx24_f hx25_f hx26_f hx29_f hvregs_f => ?_))
      have hsp_f' : sf.sp = st.sp := by
        simpa [wp_norm, arm64_norm, hsp1] using hsp_f
      rw [← hsp_f, hsp_f']
      refine SepWP.weaken_pre
        (P' := tempVecPtAt A fsp cap ptr (pushChunks4Total rest (bsearchPush s pt)) ∗
          (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗ stackAt st.sp 0 ∗ P)
        (by rw [pointsToBytes_four_cons chunkPtr b0 b1 b2 b3 rest]; exact Entails.of_eq (by ac_rfl)) ?_
      apply hnext sf hpc_f hrun_f hsp_f'
      · simpa [wp_norm, arm64_norm, htr1] using htr_f
      · exact hx19_f
      · exact hx22_f
      · rw [hx24_f]; simpa [wp_norm, arm64_norm] using hx24_1
      · rw [hx25_f]; simpa [wp_norm, arm64_norm] using hx25_1
      · exact hx26_f
      · exact hx29_f
      · rw [hvregs_f]; simpa [wp_norm, arm64_norm] using hvregs_1

/-! ## Empty Slot Predicates and `tempVecPtAt` Conversion -/

/-- A 24-byte `Default::default()` `SortedSet<Pt>` header `(cap = 0, ptr = 2, len = 0)`. -/
def emptySlotAt (addr : BitVec 64) : SepProp :=
  (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 2#64) ∗ ((addr + 16#64) ↦₆₄ 0#64)

/-- `n` consecutive `emptySlotAt` headers starting at `base`. -/
def emptySlotsAt (base : BitVec 64) (n : Nat) : SepProp :=
  arrayAt (fun _ a => emptySlotAt a) 24 base (List.replicate n ())

theorem emptySlotsAt_zero (base : BitVec 64) :
    emptySlotsAt base 0 = emp := by
  simp [emptySlotsAt, arrayAt]

theorem emptySlotsAt_succ (base : BitVec 64) (n : Nat) :
    emptySlotsAt base (n + 1) =
      emptySlotAt base ∗ emptySlotsAt (base + 24#64) n := by
  simp [emptySlotsAt, List.replicate_succ, arrayAt_cons]

theorem emptySlotsAt_off_succ (base : BitVec 64) (i n : Nat) :
    emptySlotsAt (base + BitVec.ofNat 64 (24 * i)) (n + 1) =
      emptySlotAt (base + BitVec.ofNat 64 (24 * i)) ∗
        emptySlotsAt (base + BitVec.ofNat 64 (24 * (i + 1))) n := by
  rw [emptySlotsAt_succ, off_24_succ]

theorem emptySlotAt_entails_sortedSetPtOf (A : RustAlloc) (addr : BitVec 64) :
    emptySlotAt addr ⊢ sortedSetPtOf A addr { vec := [] } := by
  rw [sortedSetPtOf_eq_vecPtOf]
  refine Entails.trans ?_ (vecPtOf_intro A addr 0#64 2#64 [])
  unfold emptySlotAt vecPtTail
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 4 < 2 ^ 63 ∧
      0 * 4 < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 := by decide
  dsimp only [List.length_nil, arrayAt_nil, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_emp, emp_sepConj]
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem emptySlotsAt_entails_sortedSetPtListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      emptySlotsAt base n ⊢ sortedSetPtListOf A base (List.replicate n { vec := [] })
  | 0, base => by
    simp [emptySlotsAt, sortedSetPtListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    rw [emptySlotsAt_succ]
    change emptySlotAt base ∗ emptySlotsAt (base + 24#64) n ⊢
      sortedSetPtOf A base { vec := [] } ∗
        sortedSetPtListOf A (base + 24#64) (List.replicate n { vec := [] })
    exact sepConj_mono (emptySlotAt_entails_sortedSetPtOf A base)
      (emptySlotsAt_entails_sortedSetPtListOf A n (base + 24#64))

theorem tempVecPtAt_into_sortedSetPtOf (A : RustAlloc) (fsp addr cap ptr : BitVec 64)
    (s : SortedSetPt)
    (hle : s.vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hpos : 0 < cap.toNat) (hptr : ptr ≠ 0) :
    (tempVecPtAt A fsp cap ptr s ∗
      (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
      ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ⊢
      sortedSetPtOf A addr s ∗
        ((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 424#64) ↦₆₄ ptr) ∗
        ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) := by
  rw [sortedSetPtOf_eq_vecPtOf]
  unfold tempVecPtAt ptSliceAt
  rw [fsp_add_416_add_8, fsp_add_416_add_16]
  have hcap_ne : cap ≠ 0 := by
    intro hc; subst hc
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    omega
  have hp : s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧
      s.vec.length * 4 < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hle, hcap, by omega, hptr⟩
  have htail :
      (A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)) ⊢
      vecPtTail A cap ptr s.vec.length := by
    unfold vecPtTail
    simp only [hcap_ne, ↓reduceIte]
    exact Entails.pure_right hp (Entails.refl _)
  have hintro := Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right htail))))
    (vecPtOf_intro A addr cap ptr s.vec)
  refine Entails.trans ?_ (sepConj_mono_left hintro)
  exact Entails.of_eq (by ac_rfl)

abbrev fromPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[irreducible] noncomputable def fromPbEntry (b : BitVec 64) (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName

theorem fromPbEntry_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    fromPbEntry b ext = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName := by
  unfold fromPbEntry; rfl

theorem fromPbEntry_raw_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = fromPbEntry b ext := by
  unfold fromPbEntry; rfl

/-! ## Outer Loop Iteration (`+204 -> +672 -> +204 / +876`) -/

/-- Finish one outer-loop iteration (`+672..+688 -> +172..+200`):
    moves the newly constructed `SortedSet<Pt>` from `[fsp + 416..440]` into slot `i` at
    `fsp + 32 + 24 * i`, increments `x25 = i + 1`, and branches to `+876` if `i + 1 = 16` or
    falls through to `+204` if `i + 1 < 16`. -/
theorem fromPb_finish_iter_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i remLen : Nat) (htot : i + (remLen + 1) = 16)
    (cap_v ptr_v : BitVec 64) (v : SortedSetPt)
    (st : State) (P : SepProp)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 672#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = fsp)
    (hx24 : st.readReg64 .x24 = 16#64)
    (hx25 : st.readReg64 .x25 = BitVec.ofNat 64 i)
    (hx29 : st.readReg64 .x29 = fsp + 448#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if i + 1 = 16 then
        (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64)
      st
      (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 416#64) ↦₆₄ cap_v) ∗ ((fsp + 424#64) ↦₆₄ ptr_v) ∗
        ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 v.vec.length) ∗
        emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
        P)
      (fun sf P_f =>
        (P_f ⊢
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ cap_v) ∗ ((fsp + 424#64) ↦₆₄ ptr_v) ∗
            ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 v.vec.length) ∗
            (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_v) ∗
              (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_v) ∗
              (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 v.vec.length)) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
            P) ∧
        sf.sp = fsp ∧
        sf.trace = st.trace ∧
        sf.readReg64 .x19 = 24#64 ∧
        sf.readReg64 .x21 = ptsPtr ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = BitVec.ofNat 64 (i + 1) ∧
        sf.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs st) := by
  subst hsp
  from_pb_fetches_range b (Rust.withPanics ext) 672 20
  from_pb_fetches_range b (Rust.withPanics ext) 172 32
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  rw [emptySlotsAt_off_succ (st.sp + 32#64) i remLen]
  unfold emptySlotAt
  have hmadd_slot :
      st.sp + 32#64 + BitVec.ofNat 64 i * 24#64 = st.sp + 32#64 + BitVec.ofNat 64 (24 * i) :=
    bv64_madd24_ofNat (st.sp + 32#64) (by omega)
  by_cases hdone : i + 1 = 16
  · have hi1_beq : (BitVec.ofNat 64 (i + 1) == 16#64) = true := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps 13
    simp only [sepConj_assoc]
    wp_done
  · have hi1_lt : i + 1 < 16 := by omega
    have hi1_beq : (BitVec.ofNat 64 (i + 1) == 16#64) = false := ofNat_beq_16_false hi1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps 13
    simp only [sepConj_assoc]
    wp_done

/-- Corollary of `fromPb_finish_iter_sepWP` that directly converts `tempVecPtAt A fsp cap_v ptr_v v`
    into `sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) v`. -/
theorem fromPb_finish_iter_tempVecPtAt_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i remLen : Nat) (htot : i + (remLen + 1) = 16)
    (cap_v ptr_v : BitVec 64) (v : SortedSetPt)
    (hle : v.vec.length ≤ cap_v.toNat) (hcap : cap_v.toNat * 4 < 2 ^ 63)
    (hpos : 0 < cap_v.toNat) (hptr : ptr_v ≠ 0)
    (st : State) (P : SepProp)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 672#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = fsp)
    (hx24 : st.readReg64 .x24 = 16#64)
    (hx25 : st.readReg64 .x25 = BitVec.ofNat 64 i)
    (hx29 : st.readReg64 .x29 = fsp + 448#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if i + 1 = 16 then
        (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64)
      st
      (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        tempVecPtAt A fsp cap_v ptr_v v ∗
        emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
        P)
      (fun sf P_f =>
        (P_f ⊢
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ cap_v) ∗ ((fsp + 424#64) ↦₆₄ ptr_v) ∗
            ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 v.vec.length) ∗
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) v ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
            P) ∧
        sf.sp = fsp ∧
        sf.trace = st.trace ∧
        sf.readReg64 .x19 = 24#64 ∧
        sf.readReg64 .x21 = ptsPtr ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = BitVec.ofNat 64 (i + 1) ∧
        sf.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs st) := by
  have hsplit_tmp :
      tempVecPtAt A fsp cap_v ptr_v v =
        ((fsp + 416#64) ↦₆₄ cap_v) ∗ ((fsp + 424#64) ↦₆₄ ptr_v) ∗
        ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 v.vec.length) ∗
        (ptSliceAt ptr_v v.vec ∗ A.live ptr_v (cap_v.toNat * 4) 2 ∗
          memRegion (ptr_v + BitVec.ofNat 64 (v.vec.length * 4)) ((cap_v.toNat - v.vec.length) * 4)) := by
    unfold tempVecPtAt
    rw [fsp_add_416_add_8, fsp_add_416_add_16]
    ac_rfl
  have hfin := fromPb_finish_iter_sepWP (A := A) fsp ptsPtr hfsp_align i remLen htot cap_v ptr_v v st
    ((ptSliceAt ptr_v v.vec ∗ A.live ptr_v (cap_v.toNat * 4) 2 ∗
      memRegion (ptr_v + BitVec.ofNat 64 (v.vec.length * 4)) ((cap_v.toNat - v.vec.length) * 4)) ∗ P)
    hpc hrun hsp hx24 hx25 hx29
  refine SepWP.weaken_pre (by rw [hsplit_tmp]; exact Entails.of_eq (by ac_rfl))
    (SepWP.mono hfin fun sf P_f _ _ ⟨hent, hregs⟩ => ⟨?_, hregs⟩)
  refine Entails.trans hent ?_
  have hinto := tempVecPtAt_into_sortedSetPtOf A fsp (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
    cap_v ptr_v v hle hcap hpos hptr
  rw [hsplit_tmp] at hinto
  refine Entails.trans (Entails.of_eq (show
    ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
      ((fsp + 416#64) ↦₆₄ cap_v) ∗ ((fsp + 424#64) ↦₆₄ ptr_v) ∗
      ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 v.vec.length) ∗
      (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_v) ∗
        (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_v) ∗
        (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 v.vec.length)) ∗
      emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
      ((ptSliceAt ptr_v v.vec ∗ A.live ptr_v (cap_v.toNat * 4) 2 ∗
        memRegion (ptr_v + BitVec.ofNat 64 (v.vec.length * 4)) ((cap_v.toNat - v.vec.length) * 4)) ∗ P) =
    ((((fsp + 416#64) ↦₆₄ cap_v) ∗ ((fsp + 424#64) ↦₆₄ ptr_v) ∗
      ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 v.vec.length) ∗
      (ptSliceAt ptr_v v.vec ∗ A.live ptr_v (cap_v.toNat * 4) 2 ∗
        memRegion (ptr_v + BitVec.ofNat 64 (v.vec.length * 4)) ((cap_v.toNat - v.vec.length) * 4))) ∗
      ((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_v) ∗
      (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_v) ∗
      (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 v.vec.length)) ∗
      (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗ P) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hinto) ?_
  exact Entails.of_eq (by ac_rfl)

theorem bv64_lsr2_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem and_neg4_of_mod4_zero {n : Nat} (hmod : n % 4 = 0) :
    (BitVec.ofNat 64 n) &&& 18446744073709551612#64 = BitVec.ofNat 64 n := by
  have hdiv : n = (n / 4) * 4 := by omega
  rw [hdiv, BitVec.ofNat_mul]
  change (BitVec.ofNat 64 (n / 4) * 4#64) &&& 18446744073709551612#64 =
    BitVec.ofNat 64 (n / 4) * 4#64
  bv_kernel

theorem and_3_of_mod4 {n : Nat} (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n) &&& 3#64 == 0#64) = decide (n % 4 = 0) := by
  have h1 : (BitVec.ofNat 64 n) &&& 3#64 = BitVec.ofNat 64 (n % 4) := by
    apply BitVec.eq_of_toNat_eq
    have h3 : (3#64 : BitVec 64).toNat = 2 ^ 2 - 1 := rfl
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h3,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n % 4 < 2 ^ 64)]
  rw [h1]
  by_cases hm : n % 4 = 0
  · simp [hm]
  · simp only [hm, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n % 4 < 2 ^ 64)] at ht
    exact hm ht

/-! ## `vecU8` Expose / Reassemble -/

/-- Remaining buffer and allocator block of a `Vec<u8>` after splitting out `(ptr ↦ₛ bs)`. -/
def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 len) (cap.toNat - len))

theorem vecU8_expose (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          vecU8Tail A cap ptr bs.length := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecU8Tail
  refine Entails.trans (Entails.of_eq (show
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  have hlen : bs.length < 2 ^ 63 := by omega
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl))
  apply Entails.pure_right ⟨hlen, hptr⟩
  apply Entails.pure_right ⟨hle, hcap, hptr⟩
  by_cases hc : cap = 0
  · subst hc
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8_intro (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      vecU8Tail A cap ptr bs.length) ⊢
    vecU8 A v bs := by
  refine Entails.trans ?_ (vecU8At_entails_vecU8 A v cap ptr bs)
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecU8Tail
  refine Entails.trans (Entails.of_eq (show
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl))
  apply Entails.pure_right ⟨hle, hcap, hptr⟩
  by_cases hc : cap = 0
  · subst hc
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem tempVecPtAt_empty_intro (A : RustAlloc) (fsp : BitVec 64) (n : Nat) (ptr : BitVec 64)
    (hn : 4 * (n + 1) < 2 ^ 63) :
    (((fsp + 416#64) ↦₆₄ BitVec.ofNat 64 (n + 1)) ∗
      ((fsp + 424#64) ↦₆₄ ptr) ∗
      ((fsp + 432#64) ↦₆₄ 0#64) ∗
      A.live ptr (4 * (n + 1)) 2 ∗
      memRegion ptr (4 * (n + 1))) =
    tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr { vec := [] } := by
  unfold tempVecPtAt ptSliceAt
  rw [fsp_add_416_add_8, fsp_add_416_add_16]
  have htoNat : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmul : (n + 1) * 4 = 4 * (n + 1) := by omega
  dsimp only [List.length_nil]
  simp only [htoNat, Nat.sub_zero, hmul, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, arrayAt_nil, sepConj_emp]
  ac_rfl

theorem stackAt_zero_of_aligned {sp : BitVec 64} (hal : (sp &&& 15#64 == 0#64) = true) :
    stackAt sp 0 = emp := by
  unfold stackAt
  simp [hal, ProofLib.memRegion_zero]

theorem stackAt_split_zero_right {sp : BitVec 64} (hal : (sp &&& 15#64 == 0#64) = true) (sz : Nat) :
    stackAt sp sz = stackAt sp sz ∗ stackAt sp 0 := by
  rw [stackAt_zero_of_aligned hal, sepConj_emp]

/-! ## OOM Panic Helper (`+0x508 = +1288`) and Outer Loop (`+204`) -/

/-- OOM panic block at `+0x508` (`+1288..+1296`: `mov w0, #2; mov x1, x23; bl handle_error`). -/
theorem decoder_from_pb_panic_1288 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1288#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := fromPbDecName) (k := num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" "alloc::raw_vec::handle_error"))
  from_pb_fetches_range b (Rust.withPanics ext) 1288 12
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [fromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-- One valid outer-loop iteration (`+204 -> +876` if `i + 1 = 16` else `+204`,
    when `pts.length % 4 = 0`):
    checks `pts.length % 4 == 0`, either jumps to `+660` (when `pts = []`) or allocates
    `pts.length` bytes and runs `fromPb_inner_loop_sepWP` (`+304 -> +672`), then finishes
    the iteration via `fromPb_finish_iter_sepWP` (`+672 -> +204 / +876`). -/
theorem fromPb_outer_alloc_and_push_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i remLen : Nat) (htot : i + (remLen + 1) = 16)
    (pts : List (BitVec 8)) (hmod4 : pts.length % 4 = 0)
    (v416 v424 v432 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = 24#64)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w416 w424 w432 : BitVec 64),
      sm.pc = (if i + 1 = 16 then
          (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64
        else
          (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64) →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x19 = 24#64 →
      sm.readReg64 .x21 = ptsPtr →
      sm.readReg64 .x24 = 16#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 (i + 1) →
      sm.readReg64 .x29 = fsp + 448#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗
          ((fsp + 424#64) ↦₆₄ w424) ∗
          ((fsp + 432#64) ↦₆₄ w432) ∗
          sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
            (pushChunks4Total pts { vec := [] }) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
          vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
        ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗
        ((fsp + 424#64) ↦₆₄ v424) ∗
        ((fsp + 432#64) ↦₆₄ v432) ∗
        emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  have hshim := hA.shim_ok_at fromPbDecName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  have halloc := hA.alloc_ok_at fromPbDecName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" "__rustc::__rust_alloc"))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  refine SepWPp.weaken_pre (sepConj_mono_left (vecU8_expose A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_u8
  apply SepWPp.exists_elim; intro ptr_u8
  apply SepWPp.pure_elim; rintro ⟨hlen_bound, hptr_u8⟩
  have hand3 : ((BitVec.ofNat 64 pts.length) &&& 3#64 == 0#64) = true := by
    rw [and_3_of_mod4 (by omega)]; simp [hmod4]
  by_cases hpts0 : pts.length = 0
  · have hpts_nil : pts = [] := List.eq_nil_of_length_eq_zero hpts0
    have hbeq0 : (BitVec.ofNat 64 pts.length == 0#64) = true := by simp [hpts0]
    refine SepWPp.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 672#64)
      (P_mid :=
        ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ 0#64) ∗
          ((fsp + 424#64) ↦₆₄ 2#64) ∗
          ((fsp + 432#64) ↦₆₄ 0#64) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
          (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (Q_mid := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 i ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 204 20
      from_pb_fetches_range b (Rust.withPanics ext) 660 12
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      wp_steps 8
      have hfold_u8 := vecU8_intro A (ptsPtr + BitVec.ofNat 64 (24 * i)) cap_u8 ptr_u8 pts
      have hent0 :
        (((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          (ptr_u8 ↦ₛ pts) ∗
          vecU8Tail A cap_u8 ptr_u8 pts.length ∗
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
        (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
          (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by
        refine Entails.trans (Entails.of_eq (show
          ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
            (ptr_u8 ↦ₛ pts) ∗
            vecU8Tail A cap_u8 ptr_u8 pts.length ∗
            ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame =
          (((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
            (ptr_u8 ↦ₛ pts) ∗
            vecU8Tail A cap_u8 ptr_u8 pts.length) ∗
            (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
              ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
              emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hfold_u8) ?_
        exact Entails.of_eq (by ac_rfl)
      exact SepWP.weaken_pre hent0 (by wp_done)
    · intro s1 hpc1 hrun1 ⟨hsp1, hx24_1, hx25_1, hx29_1, htr1, hvregs1⟩
      have hfin := fromPb_finish_iter_sepWP (A := A) fsp ptsPtr hfsp_align i remLen htot
        0#64 2#64 { vec := [] } s1
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc1 hrun1 hsp1 hx24_1 hx25_1 hx29_1
      refine SepWPp.seq_clean hfin ?_
      intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx19_2, hx21_2, hx24_2, hx25_2, hx29_2, hvregs2⟩
      rw [htr1] at htr2
      rw [hvregs1] at hvregs2
      have hpush_nil : pushChunks4Total pts { vec := [] } = { vec := [] } := by
        subst hpts_nil; rfl
      have hslot := emptySlotAt_entails_sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      unfold emptySlotAt at hslot
      have hent :
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗
            ((fsp + 432#64) ↦₆₄ BitVec.ofNat 64 ([] : List Pt).length) ∗
            (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) ↦₆₄ 0#64) ∗
              (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ 2#64) ∗
              (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List Pt).length)) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
            (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ⊢
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        rw [hpush_nil]
        dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
        refine Entails.trans (Entails.of_eq (show
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
            (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) ↦₆₄ 0#64) ∗
              (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ 2#64) ∗
              (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 0#64)) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
            (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
          (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) ↦₆₄ 0#64) ∗
            (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ 2#64) ∗
            (((fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 0#64)) ∗
            (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
              ((fsp + 416#64) ↦₆₄ 0#64) ∗ ((fsp + 424#64) ↦₆₄ 2#64) ∗ ((fsp + 432#64) ↦₆₄ 0#64) ∗
              emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1))) remLen ∗
              vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hslot) ?_
        exact Entails.of_eq (by ac_rfl)
      exact SepWPp.weaken_pre hent
        (hnext s2 0#64 2#64 0#64 hpc2 hrun2 hsp2 hx19_2 hx21_2 hx24_2 hx25_2 hx29_2 htr2 hvregs2)
  · have hpts_pos : 0 < pts.length := by omega
    let n := pts.length / 4 - 1
    have hn_eq : pts.length = 4 * (n + 1) := by omega
    have hbeq0 : (BitVec.ofNat 64 pts.length == 0#64) = false :=
      ofNat_beq_zero_false hpts_pos (by omega)
    have hlsr2 : (BitVec.ofNat 64 pts.length) >>> 2 = BitVec.ofNat 64 (n + 1) := by
      rw [bv64_lsr2_ofNat (by omega)]
      congr 1; omega
    have hand_neg4 := and_neg4_of_mod4_zero hmod4
    have hand_neg4' : (BitVec.ofNat 64 (4 * (n + 1))) &&& 18446744073709551612#64 =
        BitVec.ofNat 64 (4 * (n + 1)) := by
      rw [← hn_eq]; exact hand_neg4
    have htoNat_len : (BitVec.ofNat 64 pts.length).toNat = pts.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
    have hlay : LayoutOk pts.length 2 := ⟨hpts_pos, hpow2, by omega⟩
    dsimp only [Reg.x19, Reg.x21, Reg.x24, Reg.x25, Reg.x29] at hx19 hx21 hx24 hx25 hx29
    from_pb_fetches_range b (Rust.withPanics ext) 204 84
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc ⊢
    have hentry_raw : HiddenEq ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb") (fromPbEntry b ext) :=
      ⟨fromPbEntry_raw_eq b ext⟩
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    have hentry : HiddenEq entry ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName) :=
      ⟨hentry_raw.eq.trans (fromPbEntry_eq b ext)⟩
    clear hentry_raw
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 240#64)
    wp_steps 6
    wp_apply
    wp_steps 3
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine SepWPp.seq_clean (mid := entry + 1288#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          (ptr_u8 ↦ₛ pts) ∗
          vecU8Tail A cap_u8 ptr_u8 pts.length ∗
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        rw [hentry.eq] at hpcm
        exact decoder_from_pb_panic_1288 s0 sm _ R hpcm hrunm htrm
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_tmp := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.seq_clean (mid := entry + 304#64)
        (P_mid :=
          tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp { vec := [] } ∗
          (ptr_u8 ↦ₛ pts) ∗
          stackAt fsp 0 ∗
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
            ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
            vecU8Tail A cap_u8 ptr_u8 pts.length ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
        (Q_mid := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x19 = 1#64 ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 pts.length ∧
          sm.readReg64 .x22 = ptr_tmp ∧
          sm.readReg64 .x24 = 16#64 ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 i ∧
          sm.readReg64 .x26 = 0#64 ∧
          sm.readReg64 .x28 = ptr_u8 ∧
          sm.readReg64 .x29 = fsp + 448#64 ∧
          sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · wp_steps 12
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
        refine ⟨?_, ?_⟩
        · have hsf_sp : sf.sp = fsp := h_1.trans hsp
          have htmp := tempVecPtAt_empty_intro A fsp n ptr_tmp (by omega)
          have hsp0 : stackAt fsp 0 = emp := stackAt_zero_of_aligned hfsp_align
          dsimp only [ptr_tmp] at htmp ⊢
          rw [hsf_sp, ← hn_eq, htoNat_len, hlsr2, hn_eq, ← htmp, hsp0]
          simp only [emp_sepConj]
          exact Entails.of_eq (by ac_rfl)
        · simp [wp_norm, arm64_norm, ptr_tmp, hand_neg4, *]
      · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx21_1, hx22_1, hx24_1, hx25_1, hx26_1, hx28_1, hx29_1, htr1, hvregs1⟩
        rw [hentry.eq] at hpc1
        rw [hn_eq] at hx21_1
        have hsp_al1 : s1.spAligned = true := by
          unfold State.spAligned; rwa [hsp1]
        have htoNat_cap : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine SepWPp.seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 672#64)
          (P_mid :=
            ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
              tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] }) ∗
              emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
              (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
          (Q_mid := fun s2 =>
            s2.sp = fsp ∧
            s2.readReg64 .x24 = 16#64 ∧
            s2.readReg64 .x25 = BitVec.ofNat 64 i ∧
            s2.readReg64 .x29 = fsp + 448#64 ∧
            s2.trace = s0.trace ∧
            calleeSavedVRegs s2 = calleeSavedVRegs s0)
          ?_ ?_
        · have hsp1_0 : stackAt fsp 0 = stackAt s1.sp 0 := by rw [hsp1]
          rw [hsp1_0]
          have hsort_nil : SortedSetPtStrictSorted { vec := [] } := by
            simp [SortedSetPtStrictSorted, PtListStrictSorted]
          refine fromPb_inner_loop_sepWP hA fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp
            (by rw [htoNat_cap]; omega) n pts ptr_u8 { vec := [] } s1 _ _
            hn_eq (by rw [htoNat_cap]; simp) hsort_nil
            hpc1 hrun1 hsp_al1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 hx29_1 ?_
          intro sf hpc_f hrun_f hsp_f htr_f _ _ hx24_f hx25_f _ hx29_f hvregs_f
          have hsp_f' : sf.sp = fsp := hsp_f.trans hsp1
          have htr_f' : sf.trace = s0.trace := htr_f.trans htr1
          have hvregs_f' : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregs_f.trans hvregs1
          have hx24_f' : sf.readReg64 .x24 = 16#64 := hx24_f.trans hx24_1
          have hx25_f' : sf.readReg64 .x25 = BitVec.ofNat 64 i := hx25_f.trans hx25_1
          have hsp0_emp : stackAt s1.sp 0 = emp := by
            rw [hsp1]; exact stackAt_zero_of_aligned hfsp_align
          have hfold_u8 := vecU8_intro A (ptsPtr + BitVec.ofNat 64 (24 * i)) cap_u8 ptr_u8 pts
          apply SepWP.done hpc_f hrun_f
          refine ⟨?_, hsp_f', hx24_f', hx25_f', hx29_f, htr_f', hvregs_f'⟩
          rw [hsp0_emp]
          refine Entails.trans (Entails.of_eq (show
            tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] }) ∗
              (ptr_u8 ↦ₛ pts) ∗ emp ∗
              (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
                ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
                (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
                (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
                vecU8Tail A cap_u8 ptr_u8 pts.length ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
              (ptr_u8 ↦ₛ pts) ∗
              vecU8Tail A cap_u8 ptr_u8 pts.length) ∗
              (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] }) ∗
                emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by simp [sepConj_emp]; ac_rfl)) ?_
          refine Entails.trans (sepConj_mono_left hfold_u8) ?_
          exact Entails.of_eq (by ac_rfl)
        · intro s2 hpc2 hrun2 ⟨hsp2, hx24_2, hx25_2, hx29_2, htr2, hvregs2⟩
          have hlen_push : (pushChunks4Total pts { vec := [] }).vec.length ≤ (BitVec.ofNat 64 (n + 1)).toNat := by
            have hle := pushChunks4Total_length_le pts { vec := [] }
            rw [htoNat_cap]; dsimp only [List.length_nil] at hle; omega
          have hfin := fromPb_finish_iter_tempVecPtAt_sepWP (A := A) fsp ptsPtr hfsp_align i remLen htot
            (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] })
            hlen_push (by rw [htoNat_cap]; omega) (by rw [htoNat_cap]; omega) hoom
            s2 (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            hpc2 hrun2 hsp2 hx24_2 hx25_2 hx29_2
          refine SepWPp.seq_clean hfin ?_
          intro s3 hpc3 hrun3 ⟨hsp3, htr3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3⟩
          rw [htr2] at htr3
          rw [hvregs2] at hvregs3
          rw [hentry.eq] at hnext
          exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext s3 (BitVec.ofNat 64 (n + 1)) ptr_tmp
              (BitVec.ofNat 64 (pushChunks4Total pts { vec := [] }).vec.length)
              hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3 htr3 hvregs3)

/-- Invalid outer-loop iteration (`+204 -> +740`, when `pts.length % 4 ≠ 0`):
    checks `pts.length % 4 == 0`, fails (`b.ne 0x62e00`), and branches to `entry + 740#64`
    without modifying any memory. -/
theorem fromPb_outer_invalid_mod4_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (i : Nat)
    (pts : List (BitVec 8)) (hmod4 : pts.length % 4 ≠ 0)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = 24#64)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (herr : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 740#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x21 = ptsPtr →
      sm.readReg64 .x24 = 16#64 →
      sm.readReg64 .x29 = fsp + 448#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (sepConj_mono_left (vecU8_expose A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_u8
  apply SepWPp.exists_elim; intro ptr_u8
  apply SepWPp.pure_elim; rintro ⟨hlen_bound, hptr_u8⟩
  have hand3 : ((BitVec.ofNat 64 pts.length) &&& 3#64 == 0#64) = false := by
    rw [and_3_of_mod4 (by omega)]; simp [hmod4]
  refine SepWPp.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 740#64)
    (P_mid := vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
    (Q_mid := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x24 = 16#64 ∧
      sm.readReg64 .x29 = fsp + 448#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · from_pb_fetches_range b (Rust.withPanics ext) 204 16
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps 4
    have hfold_u8 := vecU8_intro A (ptsPtr + BitVec.ofNat 64 (24 * i)) cap_u8 ptr_u8 pts
    refine SepWP.weaken_pre ?_ (by wp_done)
    refine Entails.trans (Entails.of_eq (show
      ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
        (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
        (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (ptr_u8 ↦ₛ pts) ∗
        vecU8Tail A cap_u8 ptr_u8 pts.length ∗ Frame =
      (((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
        (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
        (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (ptr_u8 ↦ₛ pts) ∗
        vecU8Tail A cap_u8 ptr_u8 pts.length) ∗ Frame by ac_rfl)) ?_
    exact sepConj_mono_left hfold_u8
  · intro sm hpcm hrunm ⟨hspm, hx21m, hx24m, hx29m, htrm, hvregsm⟩
    exact herr sm hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm

end CryptoVerification.SpqrV1.Poly.DecoderPb

