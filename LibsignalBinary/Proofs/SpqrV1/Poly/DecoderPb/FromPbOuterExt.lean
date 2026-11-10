/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuter
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerExt
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Outer Loop Induction for `<PolyDecoder>::from_pb`

Lifts `fromPb_inner_step_sepWP`, `fromPb_inner_loop_sepWP`, `fromPb_outer_alloc_and_push_wpp`, and
`fromPb_outer_loop_wpp` to `AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop (vecPtOf vecPtListOf
  sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf)
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L37a

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
  uxth32_of_truncate16_64 and_ffff_of_truncate16_64 truncate16_32_of_truncate16_64
  ofNat_add_one madd_24_eq
  fsp_add_416_add_8 fsp_add_416_add_16

theorem fromPb_inner_step_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
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
          stackAt st.sp allocHookStack ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗
        (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗
        stackAt st.sp allocHookStack ∗ P)
      post := by
  let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
  have hpush := @fromPb_bsearchPush_at_320_sepWP_4k b A ext target_pc hA fsp cap ptr s pt
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
      (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗ stackAt st.sp allocHookStack ∗ P)
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

theorem fromPb_inner_loop_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
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
            stackAt st.sp allocHookStack ∗ P)
          post) →
      SepWP (tripleRatchetProgAtExt b ext) target_pc st
        (tempVecPtAt A fsp cap ptr s ∗
          (chunkPtr ↦ₛ rem) ∗
          stackAt st.sp allocHookStack ∗ P)
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
      refine fromPb_inner_step_sepWP_4k hA fsp cap ptr chunkPtr b0 b1 b2 b3 [] s
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
      refine fromPb_inner_step_sepWP_4k hA fsp cap ptr chunkPtr b0 b1 b2 b3 rest s
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
          (chunkPtr ↦ₛ (b0 :: b1 :: b2 :: b3 :: rest)) ∗ stackAt st.sp allocHookStack ∗ P)
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

theorem fromPb_outer_alloc_and_push_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
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
    have _hand_neg4 := and_neg4_of_mod4_zero hmod4
    have _hand_neg4' := and_neg4_of_mod4_zero (n := 4 * (n + 1)) (by omega)
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
          stackAt fsp allocHookStack ∗
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
            ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
            vecU8Tail A cap_u8 ptr_u8 pts.length ∗
            A.pool ∗ Frame))
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
          dsimp only [ptr_tmp] at htmp ⊢
          rw [hsf_sp, ← hn_eq, htoNat_len, hlsr2, hn_eq, ← htmp]
          exact Entails.of_eq (by ac_rfl)
        · simp [wp_norm, arm64_norm, ptr_tmp, *]
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
        · have hsp1_4k : stackAt fsp allocHookStack = stackAt s1.sp allocHookStack := by rw [hsp1]
          rw [hsp1_4k]
          have hsort_nil : SortedSetPtStrictSorted { vec := [] } := by
            simp [SortedSetPtStrictSorted, PtListStrictSorted]
          refine fromPb_inner_loop_sepWP_4k hA fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp
            (by rw [htoNat_cap]; omega) n pts ptr_u8 { vec := [] } s1 _ _
            hn_eq (by rw [htoNat_cap]; simp) hsort_nil
            hpc1 hrun1 hsp_al1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 hx29_1 ?_
          intro sf hpc_f hrun_f hsp_f htr_f _ _ hx24_f hx25_f _ hx29_f hvregs_f
          have hsp_f' : sf.sp = fsp := hsp_f.trans hsp1
          have htr_f' : sf.trace = s0.trace := htr_f.trans htr1
          have hvregs_f' : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregs_f.trans hvregs1
          have hx24_f' : sf.readReg64 .x24 = 16#64 := hx24_f.trans hx24_1
          have hx25_f' : sf.readReg64 .x25 = BitVec.ofNat 64 i := hx25_f.trans hx25_1
          have hfold_u8 := vecU8_intro A (ptsPtr + BitVec.ofNat 64 (24 * i)) cap_u8 ptr_u8 pts
          apply SepWP.done hpc_f hrun_f
          refine ⟨?_, hsp_f', hx24_f', hx25_f', hx29_f, htr_f', hvregs_f'⟩
          rw [← hsp1_4k]
          refine Entails.trans (Entails.of_eq (show
            tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] }) ∗
              (ptr_u8 ↦ₛ pts) ∗ stackAt fsp allocHookStack ∗
              (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
                ((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
                (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
                (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
                vecU8Tail A cap_u8 ptr_u8 pts.length ∗
                A.pool ∗ Frame) =
            (((ptsPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap_u8) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr_u8) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
              (ptr_u8 ↦ₛ pts) ∗
              vecU8Tail A cap_u8 ptr_u8 pts.length) ∗
              (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                tempVecPtAt A fsp (BitVec.ofNat 64 (n + 1)) ptr_tmp (pushChunks4Total pts { vec := [] }) ∗
                emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (remLen + 1) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
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

theorem fromPb_outer_loop_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (i : Nat) (htot : i + rem.length = 16)
      (v416 v424 v432 : BitVec 64)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x19 = 24#64 →
      s.readReg64 .x21 = ptsPtr →
      s.readReg64 .x24 = 16#64 →
      s.readReg64 .x25 = BitVec.ofNat 64 i →
      s.readReg64 .x29 = fsp + 448#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (sm : State) (w416 w424 w432 : BitVec 64),
        (∀ bs ∈ rem, bs.length % 4 = 0) →
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64 →
        sm.status = .Running → sm.sp = fsp → sm.readReg64 .x21 = ptsPtr →
        sm.readReg64 .x24 = 16#64 → sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (rem.map fun bs => pushChunks4Total bs { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) →
      (∀ (sm : State) (sets_err : List SortedSetPt) (w416 w424 w432 : BitVec 64),
        (∃ bs ∈ rem, bs.length % 4 ≠ 0) → sets_err.length = rem.length →
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 740#64 →
        sm.status = .Running → sm.sp = fsp → sm.readReg64 .x21 = ptsPtr →
        sm.readReg64 .x24 = 16#64 → sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) sets_err ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
        (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ v416) ∗
          ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))
  | [], hrem_ne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hrem_ne rfl
  | [pts], _, i, htot, v416, v424, v432,
      s, Frame, hpc, hrun, hsp, hx19, hx21, hx24, hx25, hx29, htr, hvregs, hok, herr => by
    have hi1 : i + 1 = 16 := by simp at htot; omega
    by_cases hmod4 : pts.length % 4 = 0
    · conv => arg 4; simp only [List.length_singleton, arrayAt_cons, arrayAt_nil, sepConj_emp]
      refine align_pre_wpp
        (fromPb_outer_alloc_and_push_wpp_4k hA s0 fsp ptsPtr hfsp_align i 0 (by omega) pts hmod4
          v416 v424 v432 s Frame hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1, ↓reduceIte] at hpcm
      have hall : ∀ bs ∈ [pts], bs.length % 4 = 0 := by
        intro bs hbs; simp only [List.mem_singleton] at hbs; subst hbs; exact hmod4
      refine SepWPp.weaken_pre ?_
        (hok sm w416 w424 w432 hall hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      dsimp only [sortedSetPtListOf, List.map]
      simp only [emptySlotsAt_zero, arrayAt_cons, arrayAt_nil, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · have hempty := emptySlotsAt_entails_sortedSetPtListOf A 1
        (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; simp only [List.length_singleton, arrayAt_cons, arrayAt_nil, sepConj_emp]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) (by ac_rfl) (by ac_rfl))
        (fromPb_outer_invalid_mod4_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (List.replicate 1 { vec := [] }) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate 1 { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_singleton.mpr rfl, hmod4⟩ rfl hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      simp only [arrayAt_cons, arrayAt_nil, sepConj_emp]; ac_rfl
  | pts :: pts2 :: rem', _, i, htot, v416, v424, v432,
      s, Frame, hpc, hrun, hsp, hx19, hx21, hx24, hx25, hx29, htr, hvregs, hok, herr => by
    have hi1_ne : i + 1 ≠ 16 := by simp at htot; omega
    have hoff_out : (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 24#64 =
        fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1)) := off_24_succ (fsp + 32#64) i
    have hoff_in : (ptsPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
        ptsPtr + BitVec.ofNat 64 (24 * (i + 1)) := off_24_succ ptsPtr i
    by_cases hmod4 : pts.length % 4 = 0
    · conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine align_pre_wpp
        (fromPb_outer_alloc_and_push_wpp_4k hA s0 fsp ptsPtr hfsp_align i (pts2 :: rem').length
          (by simp at htot ⊢; omega) pts hmod4 v416 v424 v432 s
          (arrayAt (fun bs addr => vecU8 A addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1_ne, ↓reduceIte] at hpcm
      refine align_pre_wpp
        (fromPb_outer_loop_wpp_4k hA s0 fsp ptsPtr hfsp_align
          (pts2 :: rem') (List.cons_ne_nil pts2 rem') (i + 1) (by simp at htot ⊢; omega)
          w416 w424 w432 sm
          (sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
            (pushChunks4Total pts { vec := [] }) ∗
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
          hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm ?_ ?_)
        (by ac_rfl)
      · intro s_end u416 u424 u432 hall_rem hpc_end hrun_end hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end
        have hall : ∀ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 = 0 := by
          intro bs hbs; rcases List.mem_cons.mp hbs with rfl | hbs'
          · exact hmod4
          · exact hall_rem bs hbs'
        refine SepWPp.weaken_pre ?_
          (hok s_end u416 u424 u432 hall hpc_end hrun_end hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end)
        rw [show sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              ((pts :: pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) =
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64)
                ((pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) from rfl,
          hoff_out,
          show arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl,
          hoff_in]
        exact Entails.of_eq (by ac_rfl)
      · intro s_err sets_rem u416 u424 u432 hex_rem hlen_rem hpc_err hrun_err hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err
        rcases hex_rem with ⟨bs_bad, hbs_bad, hbad⟩
        have hex : ∃ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 ≠ 0 :=
          ⟨bs_bad, List.mem_cons_of_mem pts hbs_bad, hbad⟩
        refine SepWPp.weaken_pre ?_
          (herr s_err (pushChunks4Total pts { vec := [] } :: sets_rem) u416 u424 u432
            hex (by simp [hlen_rem]) hpc_err hrun_err hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err)
        rw [show sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (pushChunks4Total pts { vec := [] } :: sets_rem) =
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64) sets_rem from rfl,
          hoff_out,
          show arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl,
          hoff_in]
        exact Entails.of_eq (by ac_rfl)
    · have hempty := emptySlotsAt_entails_sortedSetPtListOf A (pts :: pts2 :: rem').length
        (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) (by ac_rfl) (by ac_rfl))
        (fromPb_outer_invalid_mod4_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (List.replicate (pts :: pts2 :: rem').length { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24
              (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate (pts :: pts2 :: rem').length { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_cons_self, hmod4⟩ (by simp) hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      simp only [arrayAt_cons, hoff_in]; ac_rfl

end CryptoVerification.SpqrV1.Poly.DecoderPb
