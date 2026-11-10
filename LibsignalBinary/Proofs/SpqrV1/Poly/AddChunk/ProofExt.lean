/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopExt -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Main Proof for `<PolyDecoder as Decoder>::add_chunk`

Lifts `bsearchPush_wpp`, `addChunk_body_wpp`, `addChunk_loop_wpp`, `add_chunk_bsearch_ok_ext`,
and `add_chunk_ok_ext` to `AllocContracts4K` (`allocHookStack = 4096`).
-/

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (GF16 Pt SortedSetPt Chunk PolyDecoder)
open CryptoVerification.SpqrV1.Poly
  (boolByte ptAt ptSliceAt sortedSetPtOf sortedSetPtListOf
   polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
   polyDecoderPadOff polyDecoderPadSize chunkAt chunkIndexOff)
open CryptoVerification.SpqrV1.Alloc
  (AllocContracts4K growOneStack)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (addChunkName addChunk_fnOff addChunkStack addChunkOnPanic
   ptSliceAt_focus reassemble_sortedSetPtOf_snoc reassemble_sortedSetPtOf_set
   sortedSetPtOf_expose sortedSetPtOf_eq_len_sep sortedSetPtListOf_focus sortedSetPtListOf_set
   memRegion_spare_split_one chunk_data_focus16 dropLast_append_singleton_eq_set
   ptr_add_len_sub4 ptr_add_len_sub2 bv64_ne_zero_of_pos bv32_ule_zeroExtend16
   bv64_beq_cap_ofNat bv64_ule_succ bv64_madd24_ofNat bv64_lsr4_ofNat bv64_and15_ofNat
   bv64_lsl1_ofNat bv64_lsl2_ofNat bv64_add1_beq16 necessaryPoints_lt cinc_necessaryPoints_eq
   addChunk_skip_cond_eq addChunk_poly_eq addChunk_x_eq addChunk_polyIdx_eq
   bsearchPush addChunkBsearchStep addChunkBsearchLoop addChunkBsearch
   addChunkBsearchSpec addChunkSpec AddChunkOkExt ptListStrictSorted_length_le
   addChunkBsearchStep_pts_length addChunkBsearchStep_ptsNeeded addChunkBsearchStep_getElem_after
   addChunkBsearch_pts_length addChunkBsearch_ptsNeeded addChunkBsearch_isComplete
   addChunkBsearch_eq_addChunkTotal
   bsearch_push_empty_at_216_sepWP bsearch_push_grown_at_412_sepWP)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (ofNat_add_one_norm)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopExt
  (call_grow_one_pt_empty_wpp_4k call_grow_one_pt_full_wpp_4k bsearchReplace_wpp_4k)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree spqrAddChunkProof4KBin [
  (ls_off% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk") →
    (ls_off% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" + 512)
]

local macro "add_chunk_fetches_4k " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrAddChunkProof4KBin $b $H
      addChunk_fnOff
      (ls_off% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk")
      $k0 $len)

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

/-! ## 4K `bsearchPush` (`entry + 128#64` to `entry + 64#64`) -/

theorem bsearchPush_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {target_pc : BitVec 64} {s0 st : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (v : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (hlen : s.vec.length ≤ 65536)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 128#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64)
    (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running →
      sf.sp = st.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (sortedSetPtOf A v (bsearchPush s pt) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc st
      (sortedSetPtOf A v s ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (sepConj_mono_left (sortedSetPtOf_expose A v s)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_elim; rintro ⟨hle_cap, hcap, hptr⟩
  rcases Nat.eq_zero_or_pos s.vec.length with hlen0 | h1
  · -- Empty vector (`s.vec = []`)
    have hvec_nil : s.vec = [] := List.eq_nil_of_length_eq_zero hlen0
    have hpush_nil : bsearchPush s pt = { vec := [pt] } := by
      unfold bsearchPush; rw [hvec_nil]; rfl
    rw [hpush_nil] at hnext
    rw [hlen0] at hx28
    have hslice_nil : ptSliceAt ptr [] = emp := rfl
    simp only [hvec_nil, List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.add_zero, hslice_nil, emp_sepConj]
    by_cases hcap0 : cap = 0#64
    · subst hcap0
      simp only [↓reduceIte, emp_sepConj]
      have hcall := @call_grow_one_pt_empty_wpp_4k b A ext hA
        ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 396#64) target_pc s0
      have hpush216 := @bsearch_push_empty_at_216_sepWP b A ext v 4#64
      apply SepWPp.of_sepWP
        (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName +
          bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one"
            "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"))
      add_chunk_fetches_4k b (Rust.withPanics ext) 128 4
      add_chunk_fetches_4k b (Rust.withPanics ext) 208 8
      add_chunk_fetches_4k b (Rust.withPanics ext) 388 16
      dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hcall hpush216 hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
      examples_hide_fetches
      wp_steps 5
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hcall (F := F) v ptr 0#64 hptr
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al)
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using htr)
          (fun s2 p' hp' hpc2 hrun2 hsp2 htr2 hcs2 => ?_))
      have hsp2' : s2.sp = st.sp := by
        simpa [wp_norm, arm64_norm] using hsp2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, _, hx29_2, hvregs_2⟩
      rw [← hsp2]
      apply SepWPp.of_sepWP (mid := entry + 64#64)
      wp_steps 2
      have h4_16 : (4#64 : BitVec 64).toNat * 4 = 16 := rfl
      refine SepWP.weaken_pre (by rw [h4_16]; exact Entails.of_eq (by sep_ac_rfl))
        (hpush216 p' 0#64 pt (by decide) (by decide) hp' _
          (A.pool ∗ stackAt s2.sp growOneStack ∗ F) _
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun2])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx21_2, hx21])
          (by simp [wp_norm, arm64_norm, hx24_2, hx24])
          (by simp [wp_norm, arm64_norm, hx27_2, hx27])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f
      have hsp_f' : sf.sp = st.sp := by
        simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
      rw [hsp2']
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hpc_f hrun_f hsp_f'
          (by simpa [wp_norm, arm64_norm, htr2] using htr_f)
          hx14_f
          (by simpa [wp_norm, arm64_norm, hx19_2] using hx19_f)
          (by simpa [wp_norm, arm64_norm, hx20_2] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx23_2] using hx23_f)
          (by simpa [wp_norm, arm64_norm, hx24_2] using hx24_f)
          (by simpa [wp_norm, arm64_norm, hx25_2] using hx25_f)
          (by simpa [wp_norm, arm64_norm, hx29_2] using hx29_f)
          (by simpa [wp_norm, arm64_norm, hvregs_2] using hvregs_f))
    · simp only [hcap0, ↓reduceIte]
      have hlt0 : 0 < cap.toNat := by
        by_contra hle0
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        change cap.toNat = 0; omega
      have hbeq0 : (cap == 0#64) = false := beq_false_of_ne hcap0
      have hpush216 := @bsearch_push_empty_at_216_sepWP b A ext v cap ptr 0#64 pt hlt0 hcap hptr
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64)
      add_chunk_fetches_4k b (Rust.withPanics ext) 128 4
      add_chunk_fetches_4k b (Rust.withPanics ext) 208 8
      dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpush216 hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
      examples_hide_fetches
      wp_steps 3
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hpush216 _ (A.pool ∗ stackAt st.sp growOneStack ∗ F) _
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm, hx21])
          (by simp [wp_norm, arm64_norm, hx24])
          (by simp [wp_norm, arm64_norm, hx27])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hpc_f hrun_f
          (by simpa [wp_norm, arm64_norm] using hsp_f)
          (by simpa [wp_norm, arm64_norm, htr] using htr_f)
          hx14_f
          (by simpa [wp_norm, arm64_norm] using hx19_f)
          (by simpa [wp_norm, arm64_norm] using hx20_f)
          (by simpa [wp_norm, arm64_norm] using hx23_f)
          (by simpa [wp_norm, arm64_norm] using hx24_f)
          (by simpa [wp_norm, arm64_norm] using hx25_f)
          (by simpa [wp_norm, arm64_norm] using hx29_f)
          (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · -- Non-empty vector (`1 ≤ s.vec.length`)
    have hcap0 : cap ≠ 0#64 := by
      intro hc; subst hc
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
    simp only [hcap0, ↓reduceIte]
    let lastIdx := s.vec.length - 1
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
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64)
      add_chunk_fetches_4k b (Rust.withPanics ext) 56 8
      add_chunk_fetches_4k b (Rust.withPanics ext) 128 36
      dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
      examples_hide_fetches
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      rw [hsub4, hsub2]
      have hreasm := reassemble_sortedSetPtOf_set A v cap ptr s.vec lastIdx pt hlast_lt hle_cap hcap hptr
      refine SepWPp.weaken_pre
        (P' := sortedSetPtOf A v { vec := s.vec.set lastIdx pt } ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
            exact Entails.of_eq (by sep_ac_rfl))
        (hnext _
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using htr)
          (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]))
    | lt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : pt.x.value.toNat < (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_lt_iff_lt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hrep := @bsearchReplace_wpp_4k b A ext hA target_pc s0
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 236#64)
      add_chunk_fetches_4k b (Rust.withPanics ext) 128 44
      dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hrep hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
      examples_hide_fetches
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      rw [hsub4, hsub2]
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      rw [hfold_slice]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hrep (F := F) v cap ptr s pt h1 hlen hle_cap hcap hptr
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al)
          (by simpa [wp_norm, arm64_norm] using htr)
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx14])
          (by simp [wp_norm, arm64_norm, hx21])
          (by simp [wp_norm, arm64_norm, hx24])
          (by simp [wp_norm, arm64_norm, hx27])
          (by simp [wp_norm, arm64_norm, hx28])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      have hsp_f' : sf.sp = st.sp := by
        simpa [wp_norm, arm64_norm] using hsp_f
      simp only [wp_norm, arm64_norm]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hpc_f hrun_f hsp_f' htr_f hx14_f
          (by simpa [wp_norm, arm64_norm] using hx19_f)
          (by simpa [wp_norm, arm64_norm] using hx20_f)
          (by simpa [wp_norm, arm64_norm] using hx23_f)
          (by simpa [wp_norm, arm64_norm] using hx24_f)
          (by simpa [wp_norm, arm64_norm] using hx25_f)
          (by simpa [wp_norm, arm64_norm] using hx29_f)
          (by simpa [wp_norm, arm64_norm] using hvregs_f))
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
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      by_cases hlt_cap : s.vec.length < cap.toNat
      · -- Non-full buffer (`s.vec.length < cap.toNat`)
        have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = false := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_false_iff_not]; omega
        have hule_succ :
            (BitVec.ofNat 64 s.vec.length).ule (BitVec.ofNat 64 (s.vec.length + 1)) = true :=
          bv64_ule_succ (by omega)
        have hadd1 :
            BitVec.ofNat 64 s.vec.length + 1#64 = BitVec.ofNat 64 (s.vec.length + 1) := by
          rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64)
        add_chunk_fetches_4k b (Rust.withPanics ext) 128 80
        dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)).fnAddr
          "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
        examples_hide_fetches
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        rw [memRegion_spare_split_one ptr hlt_cap hcap]
        wp_pull_exists
        rename_i v1 v0
        wp_steps 19
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        rw [hsub4, hsub2]
        have hreasm := reassemble_sortedSetPtOf_snoc A v cap ptr s.vec pt hlt_cap hcap hptr
        rw [← hfold_slice] at hreasm
        refine SepWPp.weaken_pre
          (P' := sortedSetPtOf A v { vec := s.vec ++ [pt] } ∗
            A.pool ∗ stackAt st.sp growOneStack ∗ F)
          (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
              exact Entails.of_eq (by sep_ac_rfl))
          (hnext _
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr)
            (by simp [wp_norm, arm64_norm, hx14])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]))
      · -- Full buffer (`s.vec.length = cap.toNat`): call `RawVec<Pt>::grow_one`
        have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = true := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_true_eq]; omega
        have hcall := @call_grow_one_pt_full_wpp_4k b A ext hA
          ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 412#64) target_pc s0
        have hgrown := @bsearch_push_grown_at_412_sepWP b A ext v s.vec pt
        apply SepWPp.of_sepWP
          (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName +
            bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one"
              "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"))
        add_chunk_fetches_4k b (Rust.withPanics ext) 128 56
        add_chunk_fetches_4k b (Rust.withPanics ext) 404 8
        dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hcall hgrown hpc hnext ⊢
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)).fnAddr
          "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
        examples_hide_fetches
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        wp_steps 16
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        rw [hsub4, hsub2, hfold_slice]
        have hcap_eq : cap.toNat = s.vec.length := by omega
        have hmem_zero :
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
          rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
        rw [hmem_zero]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hcall (F := F) v cap ptr s.vec h1 hlen hcap_eq hptr
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simpa [wp_norm, arm64_norm] using hsp_al)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr)
            (fun s2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_))
        have hsp2' : s2.sp = st.sp := by
          simpa [wp_norm, arm64_norm] using hsp2
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, hx28_2, hx29_2, hvregs_2⟩
        rw [← hsp2]
        apply SepWPp.of_sepWP (mid := entry + 64#64)
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hgrown s2 (A.pool ∗ stackAt s2.sp growOneStack ∗ F) _
            hpc2 hrun2
            (by rw [hx21_2]; simp [wp_norm, arm64_norm, hx21])
            (by rw [hx24_2]; simp [wp_norm, arm64_norm, hx24])
            (by rw [hx27_2]; simp [wp_norm, arm64_norm, hx27])
            (by rw [hx28_2]; simp [wp_norm, arm64_norm, hx28])
            (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        have hsp_f' : sf.sp = st.sp := by
          simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
        rw [hsp2']
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf hpc_f hrun_f hsp_f'
            (by simpa [wp_norm, arm64_norm, htr2] using htr_f)
            hx14_f
            (by rw [hx19_f, hx19_2]; simp [wp_norm, arm64_norm])
            (by rw [hx20_f, hx20_2]; simp [wp_norm, arm64_norm])
            (by rw [hx23_f, hx23_2]; simp [wp_norm, arm64_norm])
            (by rw [hx24_f, hx24_2]; simp [wp_norm, arm64_norm])
            (by rw [hx25_f, hx25_2]; simp [wp_norm, arm64_norm])
            (by rw [hx29_f, hx29_2]; simp [wp_norm, arm64_norm])
            (by rw [hvregs_f, hvregs_2]; simp [wp_norm, arm64_norm]))

/-! ## 4K Outer 16-Iteration Loop (`addChunk_body_wpp_4k`, `addChunk_loop_wpp_4k`) -/

private theorem rev16_64_pair (a b : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (rev16_64 (BitVec.zeroExtend 64 (b ++ a)))) =
      BitVec.zeroExtend 64 ((a.zeroExtend 16 <<< 8) + b.zeroExtend 16) := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (rev16_64 (BitVec.zeroExtend 64 (b ++ a)))) =
      BitVec.zeroExtend 64 ((a.zeroExtend 16 <<< 8) ||| b.zeroExtend 16) := by
    unfold rev16_64; bv_slice
  rw [h1]; congr 1; bv_kernel

theorem addChunk_body_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {target_pc : BitVec 64} {s0 st : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (decA chunkA : BitVec 64) (self : PolyDecoder) (chunk : Chunk) (i : Nat)
    (hi : i < 16) (hpts_len : self.pts.length = 16) (hneed : self.ptsNeeded < 2 ^ 64)
    (hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 76#64)
    (hrun : st.status = .Running) (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64) (hx19 : st.readReg64 .x19 = chunkA) (hx20 : st.readReg64 .x20 = decA)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 i) (hx24 : st.readReg64 .x24 = chunk.index.zeroExtend 64)
    (hx25 : st.readReg64 .x25 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = chunkA → sf.readReg64 .x20 = decA →
      sf.readReg64 .x23 = BitVec.ofNat 64 i → sf.readReg64 .x24 = chunk.index.zeroExtend 64 →
      sf.readReg64 .x25 = 24#64 → sf.readReg64 .x29 = st.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (sortedSetPtListOf A decA (addChunkBsearchStep chunk i self).pts ∗
          ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc st
      (sortedSetPtListOf A decA self.pts ∗
        ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
        (chunkA ↦ₛ chunk.data.toList) ∗
        A.pool ∗ stackAt st.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hi_pts : i < self.pts.length := by omega
  let nec := self.necessaryPoints i
  have hnec : nec < 2 ^ 64 := necessaryPoints_lt self i hneed
  have hmadd : decA + BitVec.ofNat 64 i * 24#64 = decA + BitVec.ofNat 64 (24 * i) :=
    bv64_madd24_ofNat decA hi
  have _hlsr4 : (BitVec.ofNat 64 self.ptsNeeded) >>> 4 = BitVec.ofNat 64 (self.ptsNeeded / 16) :=
    bv64_lsr4_ofNat hneed
  have _hand15 : (BitVec.ofNat 64 self.ptsNeeded) &&& 15#64 = BitVec.ofNat 64 (self.ptsNeeded % 16) :=
    bv64_and15_ofNat hneed
  have _hcinc_nec :
      (if (BitVec.ofNat 64 (self.ptsNeeded % 16)).ule (BitVec.ofNat 64 i) = true then
        BitVec.ofNat 64 (self.ptsNeeded / 16)
      else BitVec.ofNat 64 (self.ptsNeeded / 16) + 1#64) =
        BitVec.ofNat 64 (self.necessaryPoints i) := by
    rw [ofNat_add_one_norm]; exact cinc_necessaryPoints_eq self hi hneed
  have hskip_cond := addChunk_skip_cond_eq chunk.index hnec
    (by omega : (self.pts[i]'hi_pts).vec.length < 2 ^ 64)
  have hget_i : self.pts[(chunk.index.toNat * 16 + i) % 16]?.getD SortedSetPt.new = self.pts[i]'hi_pts := by
    rw [addChunk_poly_eq chunk hi, List.getElem?_eq_getElem hi_pts, Option.getD_some]
  by_cases hcond : (decide (chunk.index.toNat < nec) || decide ((self.pts[i]'hi_pts).vec.length < nec)) = true
  · -- Push branch (`entry + 76#64` to `entry + 128#64`, then `bsearchPush_wpp_4k`)
    have hstep_eq :
        (addChunkBsearchStep chunk i self).pts =
          self.pts.set i
            (bsearchPush (self.pts[i]'hi_pts)
              { x := GF16.new chunk.index
                y := GF16.new
                  (((chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16 <<< 8) +
                    (chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩).zeroExtend 16) }) := by
      unfold addChunkBsearchStep SortedSetPt.len
      dsimp only
      rw [hget_i, addChunk_poly_eq chunk hi, addChunk_x_eq chunk hi, addChunk_polyIdx_eq chunk hi, hcond]
      rfl
    rw [hstep_eq] at hnext
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let pt : Pt := { x := GF16.new chunk.index, y := y }
    have hlsl1 : (BitVec.ofNat 64 i) <<< 1 = BitVec.ofNat 64 (i * 2) := bv64_lsl1_ofNat hi
    have hpush := @bsearchPush_wpp_4k b A ext hA target_pc s0
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 128#64)
    add_chunk_fetches_4k b (Rust.withPanics ext) 76 52
    dsimp only [tripleRatchetProgAtExt, addChunkName, polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at hpush hpc hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
    examples_hide_fetches
    have _hbr_false :
        (if (if (BitVec.ofNat 64 (self.necessaryPoints i)).ule (BitVec.zeroExtend 64 chunk.index) = true then
            (BitVec.ofNat 64 (self.necessaryPoints i)).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length)
          else ConditionHolds CondCode.CS { }) = true then
          entry + 64#64
        else entry + 116#64) = entry + 116#64 := by
      change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
          (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
          entry + 64#64 else entry + 116#64) = entry + 116#64
      rw [hskip_cond, hcond]; rfl
    rw [sortedSetPtListOf_focus A self.pts i decA hi_pts]
    rw [sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts), ← hmadd]
    rw [chunk_data_focus16 chunkA chunk i hi]
    rw [← hlsl1]
    wp_steps 13
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    rw [hmadd, ← sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts)]
    rw [hlsl1]
    have hfold_chunk :
        ((chunkA ↦ₛ chunk.data.toList.take (i * 2)) ∗
          ((chunkA + BitVec.ofNat 64 (i * 2)) ↦₁₆ (y2 ++ y1)) ∗
          ((chunkA + BitVec.ofNat 64 (i * 2 + 2)) ↦ₛ chunk.data.toList.drop (i * 2 + 2))) =
        (chunkA ↦ₛ chunk.data.toList) :=
      (chunk_data_focus16 chunkA chunk i hi).symm
    refine SepWPp.weaken_pre
      (by rw [← hfold_chunk]; dsimp only [y1, y2]; simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl))
      (hpush (F := sortedSetPtListOf A decA (self.pts.take i) ∗
          sortedSetPtListOf A (decA + BitVec.ofNat 64 (24 * (i + 1))) (self.pts.drop (i + 1)) ∗
          ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗ F)
        (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts) pt hcap_i
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simpa [wp_norm, arm64_norm] using hsp_al)
        (by simpa [wp_norm, arm64_norm] using htr)
        (by simp [wp_norm, arm64_norm, hx14])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24, pt, GF16.new])
        (by simp only [wp_norm, arm64_norm, pt, y, GF16.new]; exact rev16_64_pair y1 y2)
        (by simp [wp_norm, arm64_norm])
        (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
    have hsp_f' : sf.sp = st.sp := by
      simpa [wp_norm, arm64_norm] using hsp_f
    simp only [wp_norm, arm64_norm]
    refine SepWPp.weaken_pre
      (by rw [sortedSetPtListOf_set A self.pts i (bsearchPush (self.pts[i]'hi_pts) pt) decA hi_pts]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f' htr_f hx14_f
        (by simpa [wp_norm, arm64_norm, hx19] using hx19_f)
        (by simpa [wp_norm, arm64_norm, hx20] using hx20_f)
        (by simpa [wp_norm, arm64_norm, hx23] using hx23_f)
        (by simpa [wp_norm, arm64_norm, hx24] using hx24_f)
        (by simpa [wp_norm, arm64_norm, hx25] using hx25_f)
        (by simpa [wp_norm, arm64_norm] using hx29_f)
        (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · -- Skip branch (`entry + 76#64` jumps directly to `entry + 64#64`)
    have hcond_f : (decide (chunk.index.toNat < nec) || decide ((self.pts[i]'hi_pts).vec.length < nec)) = false :=
       Bool.eq_false_iff.mpr hcond
    have hstep_eq : (addChunkBsearchStep chunk i self).pts = self.pts := by
      unfold addChunkBsearchStep SortedSetPt.len
      dsimp only
      rw [hget_i, addChunk_polyIdx_eq chunk hi, hcond_f]
      rfl
    rw [hstep_eq] at hnext
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64)
    add_chunk_fetches_4k b (Rust.withPanics ext) 76 40
    dsimp only [tripleRatchetProgAtExt, addChunkName, polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
    examples_hide_fetches
    rw [sortedSetPtListOf_focus A self.pts i decA hi_pts]
    rw [sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts), ← hmadd]
    wp_steps 10
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm]
          change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
              (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
              entry + 64#64 else entry + 116#64) = entry + 64#64
          rw [hskip_cond, hcond_f]; rfl)
      (by simp [wp_norm, arm64_norm, hrun])
    rw [hmadd, ← sortedSetPtOf_eq_len_sep A (decA + BitVec.ofNat 64 (24 * i)) (self.pts[i]'hi_pts)]
    refine SepWPp.weaken_pre
      (by rw [sortedSetPtListOf_focus A self.pts i decA hi_pts]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _
        (by simp only [wp_norm, arm64_norm]
            change (if (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 chunk.index) = true then
                (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 (self.pts[i]'hi_pts).vec.length) else false) = true then
                entry + 64#64 else entry + 116#64) = entry + 64#64
            rw [hskip_cond, hcond_f]; rfl)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using htr)
        (by simp [wp_norm, arm64_norm, hx14])
        (by simp [wp_norm, arm64_norm, hx19])
        (by simp [wp_norm, arm64_norm, hx20])
        (by simp [wp_norm, arm64_norm, hx23])
        (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm, hx25])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]))

theorem addChunk_loop_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {target_pc : BitVec 64} {s0 : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (decA chunkA sp : BitVec 64) (chunk : Chunk)
    (rem : Nat) :
    ∀ (i : Nat) (self : PolyDecoder) (st : State),
      i + (rem + 1) = 16 →
      self.pts.length = 16 →
      self.ptsNeeded < 2 ^ 64 →
      (∀ j (hj : j < self.pts.length), i ≤ j → (self.pts[j]'hj).vec.length ≤ 65536) →
      st.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 76#64 →
      st.status = .Running →
      st.sp = sp →
      st.spAligned = true →
      st.trace = s0.trace →
      st.readReg64 .x14 = 1#64 →
      st.readReg64 .x19 = chunkA →
      st.readReg64 .x20 = decA →
      st.readReg64 .x23 = BitVec.ofNat 64 i →
      st.readReg64 .x24 = chunk.index.zeroExtend 64 →
      st.readReg64 .x25 = 24#64 →
      (∀ sf : State,
        sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 476#64 →
        sf.status = .Running →
        sf.sp = sp →
        sf.trace = s0.trace →
        sf.readReg64 .x29 = st.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs st →
        SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
          (sortedSetPtListOf A decA (addChunkBsearchLoop chunk i (rem + 1) self).pts ∗
            ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
            (chunkA ↦ₛ chunk.data.toList) ∗
            A.pool ∗ stackAt sp growOneStack ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc st
        (sortedSetPtListOf A decA self.pts ∗
          ((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 self.ptsNeeded) ∗
          (chunkA ↦ₛ chunk.data.toList) ∗
          A.pool ∗ stackAt sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  induction rem with
  | zero =>
    intro i self st hirem hpts_len hneed hcap hpc hrun hsp hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25 hnext
    have hi : i < 16 := by omega
    have hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536 := hcap i (by omega) (Nat.le_refl i)
    have _hbeq16 : (BitVec.ofNat 64 i + 1#64 == 16#64) = true := by
      rw [ofNat_add_one_norm, bv64_add1_beq16 hi, decide_eq_true_eq]; omega
    rw [← hsp]
    refine addChunk_body_wpp_4k hA decA chunkA self chunk i hi hpts_len hneed hcap_i
      hpc hrun hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25
      (fun s1 hpc1 hrun1 hsp1 htr1 _hx14_1 _hx19_1 _hx20_1 _hx23_1 _hx24_1 _hx25_1 hx29_1 hvregs_1 => ?_)
    rw [hsp]
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 476#64)
    add_chunk_fetches_4k b (Rust.withPanics ext) 64 12
    dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
    examples_hide_fetches
    wp_steps 3
    apply SepWP.done
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
    exact hnext _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm, hsp] using hsp1)
      (by simpa [wp_norm, arm64_norm] using htr1)
      (by simpa [wp_norm, arm64_norm] using hx29_1)
      (by simpa [wp_norm, arm64_norm] using hvregs_1)
  | succ rem ih =>
    intro i self st hirem hpts_len hneed hcap hpc hrun hsp hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25 hnext
    have hi : i < 16 := by omega
    have hcap_i : (self.pts[i]'(by omega)).vec.length ≤ 65536 := hcap i (by omega) (Nat.le_refl i)
    have _hbeq16 : (BitVec.ofNat 64 i + 1#64 == 16#64) = false := by
      rw [ofNat_add_one_norm, bv64_add1_beq16 hi, decide_eq_false_iff_not]; omega
    rw [← hsp]
    refine addChunk_body_wpp_4k hA decA chunkA self chunk i hi hpts_len hneed hcap_i
      hpc hrun hsp_al htr hx14 hx19 hx20 hx23 hx24 hx25
      (fun s1 hpc1 hrun1 hsp1 htr1 hx14_1 hx19_1 hx20_1 _hx23_1 hx24_1 hx25_1 hx29_1 hvregs_1 => ?_)
    rw [hsp]
    have hsp_al1 : s1.spAligned = true := by
      unfold State.spAligned at hsp_al ⊢
      rwa [hsp1]
    have hpts_len' : (addChunkBsearchStep chunk i self).pts.length = 16 := by
      rw [addChunkBsearchStep_pts_length]; exact hpts_len
    have hneed' : (addChunkBsearchStep chunk i self).ptsNeeded < 2 ^ 64 := by
      rw [addChunkBsearchStep_ptsNeeded]; exact hneed
    have hcap' : ∀ j (hj : j < (addChunkBsearchStep chunk i self).pts.length),
        i + 1 ≤ j → ((addChunkBsearchStep chunk i self).pts[j]'hj).vec.length ≤ 65536 := by
      intro j hj hij
      have hj0 : j < self.pts.length := by rw [← addChunkBsearchStep_pts_length chunk i self]; exact hj
      rw [addChunkBsearchStep_getElem_after chunk self hi (by omega) hj0]
      exact hcap j hj0 (by omega)
    have hstep := ih (i + 1) (addChunkBsearchStep chunk i self)
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 76#64)
    add_chunk_fetches_4k b (Rust.withPanics ext) 64 12
    dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hstep hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
    examples_hide_fetches
    wp_steps 3
    apply SepWP.done
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
    have hadd1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    rw [← addChunkBsearchStep_ptsNeeded chunk i self]
    refine hstep _ (by omega) hpts_len' hneed' hcap'
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm, hsp] using hsp1)
      (by simpa [wp_norm, arm64_norm] using hsp_al1)
      (by simpa [wp_norm, arm64_norm] using htr1)
      (by simp [wp_norm, arm64_norm, hx14_1])
      (by simp [wp_norm, arm64_norm, hx19_1])
      (by simp [wp_norm, arm64_norm, hx20_1])
      (by simp [wp_norm, arm64_norm, hadd1])
      (by simp [wp_norm, arm64_norm, hx24_1])
      (by simp [wp_norm, arm64_norm, hx25_1])
      (fun sf hpc_f hrun_f hsp_f htr_f hx29_f hvregs_f => ?_)
    rw [addChunkBsearchStep_ptsNeeded chunk i self]
    exact hnext sf hpc_f hrun_f hsp_f htr_f
      (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
      (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f)

/-! ## 4K Top-Level Theorems (`add_chunk_bsearch_ok_ext_4k`, `add_chunk_ok_ext_4k`) -/

private theorem stackAt_addChunk_split (sp : BitVec 64) :
    stackAt sp addChunkStack =
      stackAt (sp - 96#64) growOneStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
          ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
          ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
          ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
          ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4208 12 (by decide)
  change stackAt sp addChunkStack = stackAt (sp - 96#64) growOneStack ∗ cells (sp - 96#64) 12 at h1
  rw [h1]; congr 1; cells_unfold

set_option maxHeartbeats 800000 in
theorem add_chunk_bsearch_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName) (addChunkBsearchSpec A) := by
  simp only [addChunkBsearchSpec, polyDecoderAt, chunkAt, chunkIndexOff, stackAt_addChunk_split,
    addChunkBsearch_pts_length, addChunkBsearch_ptsNeeded, addChunkBsearch_isComplete,
    sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr addChunkName := by
    rw [Program.fnAddr_rebase, addChunk_fnOff]; exact hpc
  clear hpc
  have hsp0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hloop := @addChunk_loop_wpp_4k b A ext hA (s0.readReg64 .lr) s0
  add_chunk_fetches_4k b (Rust.withPanics ext) 0 56
  add_chunk_fetches_4k b (Rust.withPanics ext) 476 28
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hloop hpc' ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 76#64); wp_steps 14
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hloop (F := ((x.decA + polyDecoderIsCompleteOff) ↦₈ boolByte x.dec.isComplete) ∗
        memRegion (x.decA + polyDecoderPadOff) polyDecoderPadSize ∗ ((x.chunkA + 32#64) ↦₁₆ x.chunk.index) ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      x.decA x.chunkA (s0.sp - 96#64) x.chunk 15 0 x.dec _ rfl h_3 h
      (fun j hj _ => h_1 (x.dec.pts[j]'hj) (List.getElem_mem hj))
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp0]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (fun sf hpc_f hrun_f hsp_f htr_f _hx29_f _hvregs_f => ?_))
  change SepWPp _ _ sf (sortedSetPtListOf A x.decA (addChunkBsearch x.dec x.chunk).pts ∗ _) _ _
  apply SepWPp.of_sepWP_ret; wp_steps 7; wp_done

theorem add_chunk_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    AddChunkOkExt b A ext := by
  unfold AddChunkOkExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [addChunkSpec, polyDecoderAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hsort⟩, ⟨hlen, hneed⟩, hmem⟩
  have hcap : ∀ s ∈ x.dec.pts, s.vec.length ≤ 65536 :=
    fun s hs => ptListStrictSorted_length_le (hsort s hs)
  have hpre_b : s0.mem ⊨ (addChunkBsearchSpec A).pre x s0 ∗ R := by
    simp only [addChunkBsearchSpec, polyDecoderAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hcap⟩, ⟨hlen, hneed⟩, hmem⟩
  refine ((add_chunk_bsearch_ok_ext_4k hA).to_outcome x R s0 hpc hrun hpre_b hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hb_eq, hsort'⟩ := addChunkBsearch_eq_addChunkTotal x.dec x.chunk hlen hsort
    simp only [addChunkBsearchSpec, addChunkSpec, hb_eq, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1, hsort'⟩, hq.2⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.Poly.AddChunk
export LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofExt
  (bsearchPush_wpp_4k addChunk_body_wpp_4k addChunk_loop_wpp_4k
   add_chunk_bsearch_ok_ext_4k add_chunk_ok_ext_4k)
end CryptoVerification.SpqrV1.Poly.AddChunk
-- AUTO-BRIDGE END
