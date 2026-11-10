/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInner
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Inner `bsearchPush` Helpers for `<PolyDecoder>::from_pb`

Lifts `fromPb_bsearch_memmove_insert_sepWP`, `fromPb_bsearch_insert_at_532_sepWP`,
`fromPb_bsearchReplace_sepWP`, and `fromPb_bsearchPush_at_320_sepWP` to `AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
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

theorem fromPb_bsearch_memmove_insert_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (fsp cap ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 544#64)
    (hstat : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (vec.length - insertIdx))
    (hx20 : s.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx23 : s.readReg64 .x23 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vec.length)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = pt.x.value)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (vec.length + 1) →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp allocHookStack ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      (tempVecPtAt A fsp cap ptr { vec := vec } ∗ stackAt s.sp allocHookStack ∗ P)
      post := by
  have hmemmove := hA.session_memmove_ok_at fromPbDecName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" "memmove")) allocHookStack
    (by decide) (by decide)
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  from_pb_fetches_range b (Rust.withPanics ext) 544 40
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hmemmove hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  refine SepWP.weaken_pre (sepConj_mono_left (tempVecPtAt_prepare_memmove A fsp cap ptr vec insertIdx hins hlt hcap)) ?_
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro slotBs
  simp only [sepConj_assoc]
  apply SepWP.focus_pure (by sep_focus)
  intro hslot
  have hlsl_rem : (BitVec.ofNat 64 (vec.length - insertIdx)) <<< 2 =
      BitVec.ofNat 64 (4 * (vec.length - insertIdx)) :=
    bv64_lsl2_ofNat (by omega)
  have htoNat_rem : (BitVec.ofNat 64 (4 * (vec.length - insertIdx))).toNat =
      4 * (vec.length - insertIdx) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbuf_len : (ptListBytes (vec.drop insertIdx) ++ slotBs).length =
      4 * (vec.length - insertIdx) + 4 := by
    rw [List.length_append, ptListBytes_length, List.length_drop, hslot]
  wp_steps 4
  wp_call hmemmove (ptr + BitVec.ofNat 64 (4 * insertIdx),
    ptListBytes (vec.drop insertIdx) ++ slotBs, 4, 0, 4 * (vec.length - insertIdx))
  have hmove_pt := pointsToBytes_listMove_insert_pt (ptr + BitVec.ofNat 64 (4 * insertIdx))
    (vec.drop insertIdx) hslot
  rw [List.length_drop] at hmove_pt
  refine SepWP.weaken_pre (sepConj_mono_left hmove_pt) ?_
  wp_pull_exists
  wp_steps 6
  have hreasm := reassemble_tempVecPtAt_insert A fsp cap ptr vec insertIdx pt (by omega)
  refine SepWP.weaken_pre
    (P' := tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
      stackAt s.sp allocHookStack ∗ P)
    (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
        exact Entails.of_eq (by ac_rfl)) ?_
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 (vec.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  apply hcont <;> simp [wp_norm, arm64_norm, hbv_len', *]

theorem fromPb_bsearch_insert_at_532_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (fsp cap ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 532#64)
    (hstat : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 insertIdx)
    (hx20 : s.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vec.length)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = pt.x.value)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (vec.length + 1) →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp allocHookStack ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      (tempVecPtAt A fsp cap ptr { vec := vec } ∗ stackAt s.sp allocHookStack ∗ P)
      post := by
  have hmem := @fromPb_bsearch_memmove_insert_sepWP_4k b A ext target_pc hA fsp cap ptr vec insertIdx pt
  have hend := @fromPb_bsearch_end_insert_sepWP b A ext target_pc fsp cap ptr vec insertIdx pt
  from_pb_fetches_range b (Rust.withPanics ext) 532 12
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hmem hend hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  have hlsl_ins : (BitVec.ofNat 64 insertIdx) <<< 2 = BitVec.ofNat 64 (4 * insertIdx) :=
    bv64_lsl2_ofNat (by omega)
  have hsub_ins : BitVec.ofNat 64 vec.length - BitVec.ofNat 64 insertIdx =
      BitVec.ofNat 64 (vec.length - insertIdx) :=
    bv64_sub_ofNat hins (by omega)
  wp_steps 3
  rw [bv64_ule_ofNat (by omega) (by omega)]
  rcases Nat.eq_or_lt_of_le hins with hins_eq | hins_lt
  · have hle_t : vec.length ≤ insertIdx := by omega
    simp only [hle_t, decide_true, ↓reduceIte]
    refine hend hins_eq hlt hcap _ (stackAt s.sp allocHookStack ∗ P) post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simp [wp_norm, arm64_norm, hx22])
      (by simp [wp_norm, arm64_norm, hx22, hx19, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hstat_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx19_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · exact hx22_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · exact hx26_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · exact hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f
  · have hle_f : ¬ vec.length ≤ insertIdx := by omega
    simp only [hle_f, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine hmem hins_lt hlt hcap _ P post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simpa [wp_norm, arm64_norm] using hsp_align)
      (by simp [wp_norm, arm64_norm, hx26, hx19, hsub_ins])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simp [wp_norm, arm64_norm, hx22])
      (by simp [wp_norm, arm64_norm, hx22, hx19, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hstat_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx19_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · exact hx22_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · exact hx26_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · exact hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

theorem fromPb_bsearchReplace_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (fsp cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (h1 : 1 ≤ s.vec.length) (hlt_cap : s.vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (st : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 432#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (hx19 : st.readReg64 .x19 = 1#64)
    (hx20 : st.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : st.readReg64 .x22 = ptr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length)
    (hx27 : BitVec.truncate 16 (st.readReg64 .x27) = pt.x.value)
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
      sf.readReg64 .x26 = BitVec.ofNat 64 (bsearchReplace s pt).vec.length →
      sf.readReg64 .x28 = st.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr (bsearchReplace s pt) ∗ stackAt st.sp allocHookStack ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗ stackAt st.sp allocHookStack ∗ P)
      post := by
  unfold tempVecPtAt
  refine SepWP.weaken_pre
    (P' := ptSliceAt ptr s.vec ∗
      (((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
        ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
        stackAt st.sp allocHookStack ∗ P))
    (Entails.of_eq (by ac_rfl)) ?_
  refine fromPb_bsearch_to_492_sepWP h1 (by omega) st _ _ hpc hrun hx22 hx26 hx27
    (fun s1 hpc1 hrun1 hsp1 htr1 hx22_1 hx8_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 => ?_)
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
  let base := bsearchLoop s.vec pt.x.value 0 s.vec.length
  change s1.readReg64 .x8 = BitVec.ofNat 64 base at hx8_1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec pt.x.value 0 s.vec.length h1 (by omega)
  have hb_lt : base < s.vec.length := by omega
  have hb_get : s.vec[base]?.getD default = s.vec[base]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  let baseX := (s.vec[base]'hb_lt).x.value
  have hlsl_base : (BitVec.ofNat 64 base) <<< 2 = BitVec.ofNat 64 (4 * base) :=
    bv64_lsl2_ofNat (by omega)
  have huxth_1 : BitVec.zeroExtend 32 (BitVec.truncate 16 (s1.readReg64 .x27)) = pt.x.value.zeroExtend 32 := by
    rw [hx27_1, hx27]
  unfold bsearchReplace at hnext
  dsimp only at hnext
  rw [hb_get] at hnext
  by_cases heq : ((s.vec[base]'hb_lt).x.value == pt.x.value) = true
  · simp only [heq, ↓reduceIte] at hnext
    have hbaseX_eq : (s.vec[base]'hb_lt).x.value = pt.x.value := beq_iff_eq.mp heq
    from_pb_fetches_range b (Rust.withPanics ext) 492 24
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    rw [AddChunk.ptSliceAt_focus s.vec base ptr hb_lt]
    unfold ptAt
    wp_steps 6
    have hreasm := reassemble_tempVecPtAt_set A fsp cap ptr s.vec base pt hb_lt
    refine SepWP.weaken_pre
      (P' := tempVecPtAt A fsp cap ptr { vec := s.vec.set base pt } ∗ stackAt st.sp allocHookStack ∗ P)
      (by rw [hbaseX_eq]
          refine Entails.trans ?_ (sepConj_mono_left hreasm)
          exact Entails.of_eq (by ac_rfl)) ?_
    have hlen_set : (s.vec.set base pt).length = s.vec.length := List.length_set
    apply hnext
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hrun1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · simpa [wp_norm, arm64_norm, hx19] using hx19_1
    · simpa [wp_norm, arm64_norm] using hx21_1
    · simpa [wp_norm, arm64_norm, hx22] using hx22_1
    · simpa [wp_norm, arm64_norm] using hx24_1
    · simpa [wp_norm, arm64_norm] using hx25_1
    · rw [hlen_set]; simpa [wp_norm, arm64_norm, hx26] using hx26_1
    · simpa [wp_norm, arm64_norm] using hx28_1
    · simpa [wp_norm, arm64_norm, hx29] using hx29_1
    · simpa [wp_norm, arm64_norm] using hvregs_1
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext
    let insertIdx := if baseX.toNat < pt.x.value.toNat then base + 1 else base
    have hins_le : insertIdx ≤ s.vec.length := by dsimp [insertIdx]; split_ifs <;> omega
    have hcap_ne : ¬ s.vec.length = cap.toNat := by omega
    have hfold_slice :
        ((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ (s.vec[base]'hb_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
            ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
            A.live ptr (cap.toNat * 4) 2 ∗
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
            stackAt st.sp allocHookStack ∗ P)) =
        (tempVecPtAt A fsp cap ptr { vec := s.vec } ∗ stackAt st.sp allocHookStack ∗ P) := by
      unfold tempVecPtAt
      change ((ptSliceAt ptr (List.take base s.vec) ∗
        ptAt (s.vec[base]'hb_lt) (ptr + BitVec.ofNat 64 (4 * base)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗ _) = _
      rw [← AddChunk.ptSliceAt_focus s.vec base ptr hb_lt]
      ac_rfl
    have hins532 := @fromPb_bsearch_insert_at_532_sepWP_4k b A ext target_pc hA fsp cap ptr
      s.vec insertIdx pt hins_le hlt_cap hcap
    from_pb_fetches_range b (Rust.withPanics ext) 492 40
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hins532 hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    rw [AddChunk.ptSliceAt_focus s.vec base ptr hb_lt]
    unfold ptAt
    wp_steps 4
    rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
      Bool.eq_false_iff.mpr heq]
    simp only [Bool.not_false, ↓reduceIte]
    wp_steps 4
    rw [hfold_slice, bv64_beq_cap_ofNat (by omega)]
    simp only [hcap_ne, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [← hsp1]
    refine hins532 _ P _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm] using hsp1_al)
      (by simp only [wp_norm, arm64_norm, hx27_1, hx27]
          exact cinc_insertIdx_eq baseX pt.x.value base)
      (by simp [wp_norm, arm64_norm, hx20_1, hx20])
      (by simp [wp_norm, arm64_norm, hx22_1, hx22])
      (by simp [wp_norm, arm64_norm, hx26_1, hx26])
      (by simpa [wp_norm, arm64_norm, hx27_1] using hx27)
      (by simp [wp_norm, arm64_norm, hx29_1, hx29])
      (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    have hsp_f' : sf.sp = st.sp := by
      simpa [wp_norm, arm64_norm, hsp1] using hsp_f
    rw [← hsp_f, hsp_f']
    have hlen_ins : (s.vec.take insertIdx ++ (pt :: s.vec.drop insertIdx)).length = s.vec.length + 1 := by
      rw [List.length_append, List.length_take_of_le hins_le, List.length_cons, List.length_drop]
      omega
    apply hnext sf hpc_f hrun_f hsp_f' (htr_f.trans htr1) hx19_f
    · rw [hx21_f]; simpa [wp_norm, arm64_norm] using hx21_1
    · exact hx22_f
    · rw [hx24_f]; simpa [wp_norm, arm64_norm] using hx24_1
    · rw [hx25_f]; simpa [wp_norm, arm64_norm] using hx25_1
    · change sf.readReg64 .x26 = BitVec.ofNat 64 (s.vec.take insertIdx ++ (pt :: s.vec.drop insertIdx)).length
      rw [hlen_ins]; exact hx26_f
    · rw [hx28_f]; simpa [wp_norm, arm64_norm] using hx28_1
    · exact hx29_f
    · rw [hvregs_f]; simpa [wp_norm, arm64_norm] using hvregs_1

theorem fromPb_bsearchPush_at_320_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (fsp cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (hlt_cap : s.vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hlen : s.vec.length ≤ 65536)
    (st : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 320#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (hx19 : st.readReg64 .x19 = 1#64)
    (hx20 : st.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : st.readReg64 .x22 = ptr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length)
    (hx27 : BitVec.truncate 16 (st.readReg64 .x27) = pt.x.value)
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
      sf.readReg64 .x26 = BitVec.ofNat 64 (bsearchPush s pt).vec.length →
      sf.readReg64 .x28 = st.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr (bsearchPush s pt) ∗ stackAt st.sp allocHookStack ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗ stackAt st.sp allocHookStack ∗ P)
      post := by
  by_cases h1 : 1 ≤ s.vec.length
  · let lastIdx := s.vec.length - 1
    have hlast_lt : lastIdx < s.vec.length := by omega
    let lastPt := s.vec[lastIdx]'hlast_lt
    have hlast_eq : s.vec.getLast? = some lastPt := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_lt]
    have hne0 : (BitVec.ofNat 64 s.vec.length == 0#64) = false := bv64_ne_zero_of_pos h1 hlen
    have hlsl_len : (BitVec.ofNat 64 s.vec.length) <<< 2 = BitVec.ofNat 64 (4 * s.vec.length) :=
      bv64_lsl2_ofNat (by omega)
    have hsub4 := ptr_add_len_sub4 ptr h1 hlen
    change _ = ptr + BitVec.ofNat 64 (4 * lastIdx) at hsub4
    have hsub2 := ptr_add_len_sub2 ptr h1 hlen
    change _ = ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64 at hsub2
    unfold bsearchPush at hnext
    rw [hlast_eq] at hnext
    dsimp only at hnext
    cases hcmp : Pt.cmp pt lastPt with
    | eq =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hset_eq : s.vec.dropLast ++ [pt] = s.vec.set lastIdx pt :=
        dropLast_append_singleton_eq_set s.vec pt h1
      rw [hset_eq] at hnext
      have hcmp' : pt.x.value.toNat = (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_eq_iff_eq.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      from_pb_fetches_range b (Rust.withPanics ext) 288 8
      from_pb_fetches_range b (Rust.withPanics ext) 320 36
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      unfold tempVecPtAt
      rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      rw [hsub4, hsub2]
      have hreasm := reassemble_tempVecPtAt_set A fsp cap ptr s.vec lastIdx pt hlast_lt
      refine SepWP.weaken_pre
        (P' := tempVecPtAt A fsp cap ptr { vec := s.vec.set lastIdx pt } ∗ stackAt st.sp allocHookStack ∗ P)
        (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
            exact Entails.of_eq (by ac_rfl)) ?_
      have hlen_set : (s.vec.set lastIdx pt).length = s.vec.length := List.length_set
      apply hnext <;> simp [wp_norm, arm64_norm, hlen_set, *]
    | lt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : pt.x.value.toNat < (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_lt_iff_lt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hrep := @fromPb_bsearchReplace_sepWP_4k b A ext target_pc hA fsp cap ptr s pt h1 hlt_cap hcap
      from_pb_fetches_range b (Rust.withPanics ext) 320 44
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hrep hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      unfold tempVecPtAt
      rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      rw [hsub4, hsub2]
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      rw [hfold_slice]
      refine SepWP.weaken_pre (Entails.of_eq (by unfold tempVecPtAt; ac_rfl))
        (hrep _ P _
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al)
          (by simp [wp_norm, arm64_norm, hx19])
          (by simp [wp_norm, arm64_norm, hx20])
          (by simp [wp_norm, arm64_norm, hx22])
          (by simp [wp_norm, arm64_norm, hx26])
          (by simpa [wp_norm, arm64_norm] using hx27)
          (by simp [wp_norm, arm64_norm, hx29])
          (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_))
      apply hnext sf hpc_f hrun_f
      · simpa [wp_norm, arm64_norm] using hsp_f
      · simpa [wp_norm, arm64_norm] using htr_f
      · exact hx19_f
      · simpa [wp_norm, arm64_norm] using hx21_f
      · exact hx22_f
      · simpa [wp_norm, arm64_norm] using hx24_f
      · simpa [wp_norm, arm64_norm] using hx25_f
      · exact hx26_f
      · simpa [wp_norm, arm64_norm] using hx28_f
      · exact hx29_f
      · simpa [wp_norm, arm64_norm] using hvregs_f
    | gt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : (s.vec[lastIdx]'hlast_lt).x.value.toNat < pt.x.value.toNat :=
        compare_gt_iff_gt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = false := by
        rw [bv64_beq_cap_ofNat (by omega), decide_eq_false_iff_not]; omega
      have hule_succ :
          (BitVec.ofNat 64 s.vec.length).ule (BitVec.ofNat 64 (s.vec.length + 1)) = true :=
        bv64_ule_succ (by omega)
      have hadd1 :
          BitVec.ofNat 64 s.vec.length + 1#64 = BitVec.ofNat 64 (s.vec.length + 1) := by
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
      from_pb_fetches_range b (Rust.withPanics ext) 320 76
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      unfold tempVecPtAt
      rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      rw [memRegion_spare_split_one ptr hlt_cap hcap]
      wp_pull_exists
      wp_steps 19
      rw [hsub4, hsub2]
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      have hreasm := reassemble_tempVecPtAt_snoc A fsp cap ptr s.vec pt
      rw [← hfold_slice] at hreasm
      refine SepWP.weaken_pre
        (P' := tempVecPtAt A fsp cap ptr { vec := s.vec ++ [pt] } ∗ stackAt st.sp allocHookStack ∗ P)
        (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
            exact Entails.of_eq (by ac_rfl)) ?_
      have hlen_snoc : (s.vec ++ [pt]).length = s.vec.length + 1 := by simp
      apply hnext <;> simp [wp_norm, arm64_norm, hlen_snoc, hadd1, *]
  · have hnil : s.vec = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    have hs_eq : s = { vec := [] } := by cases s; subst hnil; rfl
    subst hs_eq
    have hpush_nil : bsearchPush { vec := [] } pt = { vec := [pt] } := rfl
    rw [hpush_nil] at hnext
    have hpush400 := @fromPb_bsearch_push_empty_at_400_sepWP b A ext target_pc fsp cap ptr pt
      (by simpa using hlt_cap) hcap
    from_pb_fetches_range b (Rust.withPanics ext) 320 4
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpush400 hpc hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    dsimp only [List.length_nil] at hx26
    wp_steps 1
    refine hpush400 _ (stackAt st.sp allocHookStack ∗ P) _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hx19])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    apply hnext sf hpc_f hrun_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx19_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · exact hx22_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · exact hx26_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · exact hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

end CryptoVerification.SpqrV1.Poly.DecoderPb
