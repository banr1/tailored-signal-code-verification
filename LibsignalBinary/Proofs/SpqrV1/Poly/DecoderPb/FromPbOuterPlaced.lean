/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Relocatable Inner Chunk Loop and Outer Slot Steps

Relocatable `[LibsignalPlacement]` proofs of the 4-byte chunk decoding loop (`+304..+672`),
outer-iteration completion (`+672 → +204 / +876`), OOM panic (`+1288`), and outer-loop steps on
Block `376`.
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
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop (vecPtOf vecPtListOf
  sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf)
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm]
  fp_add_448_sub_32 fp_add_448_sub_32_int
  fp_add_448_sub_24 fp_add_448_sub_24_int
  fp_add_448_sub_16 fp_add_448_sub_16_int
  truncate16_truncate32 and_ffff_truncate32 and_ffff_zeroExtend64_truncate32
  ofNat_add_one madd_24_eq
  fsp_add_416_add_8 fsp_add_416_add_16

/-! ## Placed 4-Byte Big-Endian Point Decoding and Inner Loop (`+304 -> +672`) -/

theorem fromPb_inner_step_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (fsp cap ptr chunkPtr : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) (s : SortedSetPt)
    (hlt_cap : s.vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hlen : s.vec.length ≤ 65536)
    (st : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : st.pc = (blkPl_376).base + 304#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (hx19 : st.readReg64 .x19 = 1#64)
    (hx22 : st.readReg64 .x22 = ptr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length)
    (hx28 : st.readReg64 .x28 = chunkPtr)
    (hx29 : st.readReg64 .x29 = fsp + 448#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_376).base + 296#64 →
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
      SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) target_pc sf
        (tempVecPtAt A fsp cap ptr
          (bsearchPush s { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }) ∗
          (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗
          stackAt st.sp 0 ∗ P)
        post) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗
        (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗
        stackAt st.sp 0 ∗ P)
      post := by
  let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
  have hpush := @fromPb_bsearchPush_at_320_placed_sepWP _ A ext target_pc hmemmove_sat fsp cap ptr s pt
    hlt_cap hcap hlen
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

theorem fromPb_inner_loop_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (fsp cap ptr : BitVec 64)
    (hcap : cap.toNat * 4 < 2 ^ 63) :
    ∀ (n : Nat) (rem : List (BitVec 8)) (chunkPtr : BitVec 64) (s : SortedSetPt)
      (st : State) (P : SepProp) (post : State → SepProp → Prop),
      rem.length = 4 * (n + 1) →
      s.vec.length + (n + 1) ≤ cap.toNat →
      SortedSetPtStrictSorted s →
      st.pc = (blkPl_376).base + 304#64 →
      st.status = .Running →
      st.spAligned = true →
      st.readReg64 .x19 = 1#64 →
      st.readReg64 .x21 = BitVec.ofNat 64 (4 * (n + 1)) →
      st.readReg64 .x22 = ptr →
      st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length →
      st.readReg64 .x28 = chunkPtr →
      st.readReg64 .x29 = fsp + 448#64 →
      (∀ sf : State,
        sf.pc = (blkPl_376).base + 672#64 →
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
        SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) target_pc sf
          (tempVecPtAt A fsp cap ptr (pushChunks4Total rem s) ∗
            (chunkPtr ↦ₛ rem) ∗
            stackAt st.sp 0 ∗ P)
          post) →
      SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) target_pc st
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
      refine fromPb_inner_step_placed_sepWP hmemmove_sat fsp cap ptr chunkPtr b0 b1 b2 b3 [] s
        (by omega) hcap hlen st P post hpc hrun hsp_al hx19 hx22 hx26 hx28 hx29 ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1
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
      refine fromPb_inner_step_placed_sepWP hmemmove_sat fsp cap ptr chunkPtr b0 b1 b2 b3 rest s
        (by omega) hcap hlen st P post hpc hrun hsp_al hx19 hx22 hx26 hx28 hx29 ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1
      have hsub4 : BitVec.ofNat 64 (4 * (n + 1 + 1)) - 4#64 = BitVec.ofNat 64 (4 * (n + 1)) :=
        bv64_mul4_succ_sub_four (n + 1)
      have hne0 : (BitVec.ofNat 64 (4 * (n + 1)) == 0#64) = false :=
        ofNat_beq_zero_false (by omega) (by omega)
      have hx21_s1 : s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (4 * (n + 1 + 1)) := hx21_1.trans hx21
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
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

/-! ## Placed Outer Loop Iteration (`+204 -> +672 -> +204 / +876`) -/

theorem fromPb_finish_iter_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i remLen : Nat) (htot : i + (remLen + 1) = 16)
    (cap_v ptr_v : BitVec 64) (v : SortedSetPt)
    (st : State) (P : SepProp)
    (hpc : st.pc = (blkPl_376).base + 672#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = fsp)
    (hx24 : st.readReg64 .x24 = 16#64)
    (hx25 : st.readReg64 .x25 = BitVec.ofNat 64 i)
    (hx29 : st.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (if i + 1 = 16 then
        (blkPl_376).base + 876#64
      else
        (blkPl_376).base + 204#64)
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

theorem fromPb_finish_iter_tempVecPtAt_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i remLen : Nat) (htot : i + (remLen + 1) = 16)
    (cap_v ptr_v : BitVec 64) (v : SortedSetPt)
    (hle : v.vec.length ≤ cap_v.toNat) (hcap : cap_v.toNat * 4 < 2 ^ 63)
    (hpos : 0 < cap_v.toNat) (hptr : ptr_v ≠ 0)
    (st : State) (P : SepProp)
    (hpc : st.pc = (blkPl_376).base + 672#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = fsp)
    (hx24 : st.readReg64 .x24 = 16#64)
    (hx25 : st.readReg64 .x25 = BitVec.ofNat 64 i)
    (hx29 : st.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (if i + 1 = 16 then
        (blkPl_376).base + 876#64
      else
        (blkPl_376).base + 204#64)
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
  have hfin := fromPb_finish_iter_placed_sepWP (A := A) (ext := ext) fsp ptsPtr hfsp_align i remLen htot cap_v ptr_v v st
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

/-! ## Placed OOM Panic Helper (`+0x508 = +1288`) and Outer Loop (`+204`) -/

theorem decoder_from_pb_panic_1288_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_376).base + 1288#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  have hpanic : ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [fromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem fromPb_outer_alloc_and_push_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i remLen : Nat) (htot : i + (remLen + 1) = 16)
    (pts : List (BitVec 8)) (hmod4 : pts.length % 4 = 0)
    (v416 v424 v432 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 204#64)
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
          (blkPl_376).base + 876#64
        else
          (blkPl_376).base + 204#64) →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x19 = 24#64 →
      sm.readReg64 .x21 = ptsPtr →
      sm.readReg64 .x24 = 16#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 (i + 1) →
      sm.readReg64 .x29 = fsp + 448#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
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
    SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
        ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗
        ((fsp + 424#64) ↦₆₄ v424) ∗
        ((fsp + 432#64) ↦₆₄ v432) ∗
        emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  have hshim : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
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
    refine SepWPp.seq_clean (mid := (blkPl_376).base + 672#64)
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
    · wp_steps 8
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
      have hfin := fromPb_finish_iter_placed_sepWP (A := A) (ext := ext) fsp ptsPtr hfsp_align i remLen htot
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
    apply SepWPp.of_sepWP (mid := (blkPl_376).base + 240#64)
    wp_steps 6
    wp_apply
    wp_steps 3
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      conv => arg 4; simp only [hoom64, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine SepWPp.seq_clean (mid := (blkPl_376).base + 1288#64)
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
        exact decoder_from_pb_panic_1288_placed h_panic s0 sm _ R hpcm hrunm htrm
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      conv => arg 4; simp only [hoom64, ↓reduceIte, htoNat_len, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_tmp := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.seq_clean (mid := (blkPl_376).base + 304#64)
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
        rw [hn_eq] at hx21_1
        have hsp_al1 : s1.spAligned = true := by
          unfold State.spAligned; rwa [hsp1]
        have htoNat_cap : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine SepWPp.seq_clean
          (mid := (blkPl_376).base + 672#64)
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
          refine fromPb_inner_loop_placed_sepWP hmemmove_sat fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp
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
          have hfin := fromPb_finish_iter_tempVecPtAt_placed_sepWP (A := A) (ext := ext) fsp ptsPtr hfsp_align i remLen htot
            (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] })
            hlen_push (by rw [htoNat_cap]; omega) (by rw [htoNat_cap]; omega) hoom
            s2 (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            hpc2 hrun2 hsp2 hx24_2 hx25_2 hx29_2
          refine SepWPp.seq_clean hfin ?_
          intro s3 hpc3 hrun3 ⟨hsp3, htr3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3⟩
          rw [htr2] at htr3
          rw [hvregs2] at hvregs3
          exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext s3 (BitVec.ofNat 64 (n + 1)) ptr_tmp
              (BitVec.ofNat 64 (pushChunks4Total pts { vec := [] }).vec.length)
              hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3 htr3 hvregs3)

theorem fromPb_outer_invalid_mod4_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (i : Nat)
    (pts : List (BitVec 8)) (hmod4 : pts.length % 4 ≠ 0)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 204#64)
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
      sm.pc = (blkPl_376).base + 740#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x21 = ptsPtr →
      sm.readReg64 .x24 = 16#64 →
      sm.readReg64 .x29 = fsp + 448#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (sepConj_mono_left (vecU8_expose A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_u8
  apply SepWPp.exists_elim; intro ptr_u8
  apply SepWPp.pure_elim; rintro ⟨hlen_bound, hptr_u8⟩
  have hand3 : ((BitVec.ofNat 64 pts.length) &&& 3#64 == 0#64) = false := by
    rw [and_3_of_mod4 (by omega)]; simp [hmod4]
  refine SepWPp.seq_clean (mid := (blkPl_376).base + 740#64)
    (P_mid := vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
    (Q_mid := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x24 = 16#64 ∧
      sm.readReg64 .x29 = fsp + 448#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps 4
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
