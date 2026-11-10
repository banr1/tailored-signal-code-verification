/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk`: Loop Proofs

**Checked by Lean.**

Proves the inner binary-search loop (`0x6c524..0x6c548`) and single-iteration `memmove` / `grow_one`
helpers (`0x6c46c..0x6c460`) for `<PolyDecoder as Decoder>::add_chunk` (`0x6c420`).
-/

namespace CryptoVerification.SpqrV1.Poly.AddChunk

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_stub% "memmove")

namespace AddChunkNorm
@[scoped arm64_norm, scoped wp_norm] theorem ofNat_add_one_norm (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := EncoderIntoPb.ofNat_add_one j
@[local arm64_norm ↓, local wp_norm ↓] theorem sp_setPC_pre (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) : ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) : (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) : ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) : calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) : calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl
end AddChunkNorm
open AddChunkNorm

/-! ## Fetch Macro and Arithmetic / BitVector Helpers -/

macro "add_chunk_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode addChunkBin $b $H addChunk_fnOff 0x67028 $k0 $len)

theorem bv64_lsr1_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl

theorem bv64_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by rw [← BitVec.ofNat_add]

theorem bv64_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; exact hba

theorem bv64_lsl2_ofNat {n : Nat} (hn : 4 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega

theorem truncate32_zeroExtend64_16 (x : BitVec 16) :
    BitVec.truncate 32 (x.zeroExtend 64) = x.zeroExtend 32 := by bv_bits

theorem bv32_ult_zeroExtend16 (a b : BitVec 16) :
    (a.zeroExtend 32).ult (b.zeroExtend 32) = decide (a.toNat < b.toNat) := by
  rw [BitVec.ult_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

set_option linter.unusedSimpArgs false

theorem bv64_ult_one_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (1#64).ult (BitVec.ofNat 64 n) = decide (1 < n) := by
  rw [BitVec.ult_eq_decide, show (1#64 : BitVec 64).toNat = 1 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-! ## Inner Binary Search Loop (`0x6c524..0x6c548`) -/

theorem bsearchLoop_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (vec : List Pt) (ptr : BitVec 64) (xVal : BitVec 16) (hlen_bound : 4 * vec.length < 2 ^ 64) :
    ∀ (size base : Nat) (s : State) (P : SepProp) (post : State → SepProp → Prop),
      1 < size → base + size ≤ vec.length → s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 260#64 →
      s.status = .Running → s.readReg64 .x8 = ptr → s.readReg64 .x9 = BitVec.ofNat 64 base →
      s.readReg64 .x10 = BitVec.ofNat 64 size → s.readReg64 .x24 = xVal.zeroExtend 64 →
      (∀ (sf : State), sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64 →
        sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace → sf.readReg64 .x8 = ptr →
        sf.readReg64 .x9 = BitVec.ofNat 64 (bsearchLoop vec xVal base size) →
        sf.readReg64 .x14 = s.readReg64 .x14 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 → sf.readReg64 .x30 = s.readReg64 .x30 → calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64) sf (ptSliceAt ptr vec ∗ P) post) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64) s (ptSliceAt ptr vec ∗ P) post := by
  add_chunk_fetches_range b (Rust.withPanics ext) 260 36
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches; intro size; induction size using Nat.strongRecOn with
  | ind size ih =>
    intro base s P post hgt hle hpc hstat hx8 hx9 hx10 hx24 hcont
    have hhalf_pos : 0 < size / 2 := Nat.div_pos (by omega) (by decide)
    have hmid_lt : base + size / 2 < vec.length := by omega
    have hsize_lt64 : size < 2 ^ 64 := by omega
    have hlsr : (BitVec.ofNat 64 size) >>> 1 = BitVec.ofNat 64 (size / 2) := bv64_lsr1_ofNat hsize_lt64
    have hadd_mid : BitVec.ofNat 64 (size / 2) + BitVec.ofNat 64 base = BitVec.ofNat 64 (base + size / 2) := by
      rw [← BitVec.ofNat_add, Nat.add_comm]
    have hsub_size : BitVec.ofNat 64 size - BitVec.ofNat 64 (size / 2) = BitVec.ofNat 64 (size - size / 2) :=
      bv64_sub_ofNat (by omega) hsize_lt64
    have hlsl_mid : (BitVec.ofNat 64 (base + size / 2)) <<< 2 = BitVec.ofNat 64 (4 * (base + size / 2)) :=
      bv64_lsl2_ofNat (by omega)
    have hmid_get : vec[base + size / 2]?.getD default = vec[base + size / 2]'hmid_lt := by
      rw [List.getElem?_eq_getElem hmid_lt, Option.getD_some]
    let base' := if xVal.toNat < (vec[base + size / 2]'hmid_lt).x.value.toNat then base else base + size / 2
    have hcsel : (if (BitVec.zeroExtend 32 xVal).ult (BitVec.zeroExtend 32 (vec[base + size / 2]'hmid_lt).x.value) = true then
        BitVec.ofNat 64 base else BitVec.ofNat 64 (base + size / 2)) = BitVec.ofNat 64 base' := by
      rw [bv32_ult_zeroExtend16]; by_cases hlt : xVal.toNat < (vec[base + size / 2]'hmid_lt).x.value.toNat <;> simp [base', hlt]
    have hfold_slice :
        ((ptSliceAt ptr (List.take (base + size / 2) vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * (base + size / 2))) ↦₁₆ (vec[base + size / 2]'hmid_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * (base + size / 2)) + 2#64) ↦₁₆ (vec[base + size / 2]'hmid_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + size / 2 + 1))) (List.drop (base + size / 2 + 1) vec)) ∗ P) =
        (ptSliceAt ptr vec ∗ P) := by
      change ((ptSliceAt ptr (List.take (base + size / 2) vec) ∗ ptAt (vec[base + size / 2]'hmid_lt) (ptr + BitVec.ofNat 64 (4 * (base + size / 2))) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + size / 2 + 1))) (List.drop (base + size / 2 + 1) vec)) ∗ P) = _
      rw [← ptSliceAt_focus vec (base + size / 2) ptr hmid_lt]
    rw [ptSliceAt_focus vec (base + size / 2) ptr hmid_lt]; unfold ptAt; wp_steps
    rw [hfold_slice, bv64_ult_one_ofNat (by omega)]
    have hbs_step : bsearchLoop vec xVal base size = bsearchLoop vec xVal base' (size - size / 2) := by
      conv_lhs => rw [bsearchLoop]
      simp only [hgt, ↓reduceDIte, hmid_get]; rfl
    by_cases hgt' : 1 < size - size / 2
    · simp only [hgt', decide_true, ↓reduceIte]
      refine ih (size - size / 2) (by omega) base' _ P post hgt' (by dsimp [base']; split_ifs <;> omega)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx24])
        (fun sf hpc_f hstat_f hsp_f htr_f hx8_f hx9_f hx14_f hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx27_f hx28_f hx29_f hx30_f hvregs_f => ?_)
      exact hcont sf hpc_f hstat_f (by simpa [wp_norm, arm64_norm] using hsp_f) (by simpa [wp_norm, arm64_norm] using htr_f)
        hx8_f (by rw [hbs_step]; exact hx9_f)
        (by simpa [wp_norm, arm64_norm] using hx14_f) (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f)
        (by simpa [wp_norm, arm64_norm] using hx21_f) (by simpa [wp_norm, arm64_norm] using hx23_f) (by simpa [wp_norm, arm64_norm] using hx24_f)
        (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx27_f) (by simpa [wp_norm, arm64_norm] using hx28_f)
        (by simpa [wp_norm, arm64_norm] using hx29_f) (by simpa [wp_norm, arm64_norm] using hx30_f) (by simpa [wp_norm, arm64_norm] using hvregs_f)
    · simp only [hgt', decide_false, Bool.false_eq_true, ↓reduceIte]
      have hbs_done : bsearchLoop vec xVal base size = base' := by rw [hbs_step, bsearchLoop]; simp [hgt']
      exact hcont _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx8])
        (by rw [hbs_done]; simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

/-! ## Separation-Logic Helpers for `sortedSetPtOf` and `memmove` Insertion -/

theorem fnAddr_growOnePt_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr growOnePtName =
      (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk") := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, addChunk_fnOff,
    (ls_lemma% fnOff "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one")]
  bv_omega

theorem insert_suffix_prepare_memmove (ptr : BitVec 64) (vec : List Pt) (insertIdx cap : Nat)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap) (hcap : cap * 4 < 2 ^ 63) :
    let x22 := ptr + BitVec.ofNat 64 (4 * insertIdx)
    let suffix := vec.drop insertIdx
    (ptSliceAt ptr vec ∗ memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap - vec.length) * 4)) ⊢
      ∃∗ slotBs : List (BitVec 8),
        ⌜slotBs.length = 4⌝ ∗ ptSliceAt ptr (vec.take insertIdx) ∗
        (x22 ↦ₛ (ptListBytes suffix ++ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap - (vec.length + 1)) * 4) := by
  intro x22 suffix
  have hmul : (cap - vec.length) * 4 = 4 + (cap - (vec.length + 1)) * 4 := by omega
  have hadd4 : ptr + BitVec.ofNat 64 (vec.length * 4) + 4#64 =
      ptr + BitVec.ofNat 64 ((vec.length + 1) * 4) := by
    rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 2; omega
  have hx22_add : x22 + BitVec.ofNat 64 (ptListBytes suffix).length =
      ptr + BitVec.ofNat 64 (vec.length * 4) := by
    dsimp only [x22, suffix]; rw [ptListBytes_length, List.length_drop, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [ptSliceAt_split_take_drop vec insertIdx ptr (by omega), hmul,
    memRegion_split (ptr + BitVec.ofNat 64 (vec.length * 4)) 4 ((cap - (vec.length + 1)) * 4) (by omega),
    hadd4, ProofLib.memRegion_eq_exists_bytes (ptr + BitVec.ofNat 64 (vec.length * 4)) 4 (by decide),
    ptSliceAt_eq_pointsToBytes suffix x22, ← hx22_add]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro slotBs; refine Entails.sepExists_right slotBs ?_
  rw [pointsToBytes_append]; exact Entails.of_eq (by sep_ac_rfl)

theorem ptSliceAt_reassemble_insert (ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) :
    let x22 := ptr + BitVec.ofNat 64 (4 * insertIdx)
    (ptSliceAt ptr (vec.take insertIdx) ∗ ((x22 ↦₁₆ pt.x.value) ∗ ((x22 + 2#64) ↦₁₆ pt.y.value)) ∗
      ptSliceAt (x22 + 4#64) (vec.drop insertIdx)) =
      ptSliceAt ptr (vec.take insertIdx ++ (pt :: vec.drop insertIdx)) := by
  intro x22; rw [ptSliceAt_append, List.length_take_of_le hins]; rfl

theorem reassemble_sortedSetPtOf_insert (A : RustAlloc) (v cap ptr : BitVec 64)
    (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
      ptSliceAt ptr (vec.take insertIdx) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 vec.length + 1#64)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } := by
  let vec' := vec.take insertIdx ++ (pt :: vec.drop insertIdx)
  have hlen' : vec'.length = vec.length + 1 := by
    dsimp [vec']; rw [List.length_append, List.length_take_of_le hins, List.length_cons, List.length_drop]; omega
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 vec'.length := by
    rw [hlen', show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hcap_ne : cap ≠ 0#64 := by intro hc; subst hc; have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
  have hslice := ptSliceAt_reassemble_insert ptr vec insertIdx pt hins; dsimp only at hslice
  rw [hbv_len', ← hlen']
  refine Entails.trans ?_ (sortedSetPtOf_intro_nonempty A v cap ptr vec' (by omega) hcap hptr hcap_ne)
  rw [← hslice]; exact Entails.of_eq (by sep_ac_rfl)

theorem reassemble_sortedSetPtOf_snoc (A : RustAlloc) (v cap ptr : BitVec 64)
    (vec : List Pt) (pt : Pt)
    (hlt : vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (ptSliceAt ptr vec ∗ ((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢ sortedSetPtOf A v { vec := vec ++ [pt] } := by
  let vec' := vec ++ [pt]
  have hlen' : vec'.length = vec.length + 1 := by simp [vec']
  have hcap_ne : cap ≠ 0#64 := by intro hc; subst hc; have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
  rw [← hlen']
  refine Entails.trans ?_ (sortedSetPtOf_intro_nonempty A v cap ptr vec' (by omega) hcap hptr hcap_ne)
  dsimp [vec']; rw [ptSliceAt_append_singleton]; unfold ptAt; exact Entails.of_eq (by ac_rfl)

theorem reassemble_sortedSetPtOf_set (A : RustAlloc) (v cap ptr : BitVec 64)
    (vec : List Pt) (idx : Nat) (pt : Pt)
    (hidx : idx < vec.length) (hle : vec.length ≤ cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (ptSliceAt ptr (vec.take idx) ∗ ((ptr + BitVec.ofNat 64 (4 * idx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * idx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * (idx + 1))) (vec.drop (idx + 1)) ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢ sortedSetPtOf A v { vec := vec.set idx pt } := by
  let vec' := vec.set idx pt
  have hlen' : vec'.length = vec.length := List.length_set
  have hcap_ne : cap ≠ 0#64 := by intro hc; subst hc; have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
  rw [← hlen']
  refine Entails.trans ?_ (sortedSetPtOf_intro_nonempty A v cap ptr vec' (by omega) hcap hptr hcap_ne)
  dsimp [vec']; rw [ptSliceAt_set vec idx pt ptr hidx]; unfold ptAt; exact Entails.of_eq (by ac_rfl)

private theorem bsearch_memmove_insert_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove")))
      (sessionMemmoveSpec growOneStack))
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 348#64)
    (hstat : s.status = .Running) (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (vec.length - insertIdx))
    (hx21 : s.readReg64 .x21 = v) (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64) (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp growOneStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
        stackAt s.sp growOneStack ∗ P) post := by
  add_chunk_fetches_range b (Rust.withPanics ext) 348 40
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hmemmove hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches
  have hprep := insert_suffix_prepare_memmove ptr vec insertIdx cap.toNat hins hlt hcap
  refine SepWP.weaken_pre (P' := ∃∗ slotBs : List (BitVec 8),
      ⌜slotBs.length = 4⌝ ∗ ptSliceAt ptr (vec.take insertIdx) ∗
      ((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦ₛ (ptListBytes (vec.drop insertIdx) ++ slotBs)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
      A.live ptr (cap.toNat * 4) 2 ∗ stackAt s.sp growOneStack ∗ P)
    (by
      refine Entails.trans (Entails.of_eq (Q := (ptSliceAt ptr vec ∗
          memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)) ∗
          ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
            A.live ptr (cap.toNat * 4) 2 ∗ stackAt s.sp growOneStack ∗ P)) (by ac_rfl))
        (Entails.trans (sepConj_mono_left hprep) ?_)
      rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro slotBs
      exact Entails.sepExists_right slotBs (Entails.of_eq (by ac_rfl))) ?_
  apply SepWP.exists_left; intro slotBs; apply SepWP.focus_pure (by sep_focus); intro hslot
  have hlsl_rem : (BitVec.ofNat 64 (vec.length - insertIdx)) <<< 2 =
      BitVec.ofNat 64 (4 * (vec.length - insertIdx)) := bv64_lsl2_ofNat (by omega)
  have htoNat_rem : (BitVec.ofNat 64 (4 * (vec.length - insertIdx))).toNat =
      4 * (vec.length - insertIdx) := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
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
  wp_pull_exists; wp_steps 6
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 (vec.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hreasm := reassemble_sortedSetPtOf_insert A v cap ptr vec insertIdx pt (by omega) hlt hcap hptr
  rw [hbv_len'] at hreasm
  refine SepWP.weaken_pre
    (P' := sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
      stackAt s.sp growOneStack ∗ P)
    (Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hreasm)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, *]

theorem bsearch_memmove_insert_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop) :
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 348#64 →
    s.status = .Running → s.spAligned = true →
    s.readReg64 .x8 = BitVec.ofNat 64 (vec.length - insertIdx) →
    s.readReg64 .x21 = v → s.readReg64 .x22 = ptr + BitVec.ofNat 64 (4 * insertIdx) →
    s.readReg64 .x24 = pt.x.value.zeroExtend 64 → s.readReg64 .x27 = pt.y.value.zeroExtend 64 →
    s.readReg64 .x28 = BitVec.ofNat 64 vec.length →
    (∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp growOneStack ∗ P) post) →
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
        stackAt s.sp growOneStack ∗ P) post :=
  bsearch_memmove_insert_sepWP_core
    (hA.session_memmove_ok_at addChunkName
      (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove"))
      growOneStack (by rw [addChunk_fnOff]; simp only [arm64_norm]))
    v cap ptr lenOld vec insertIdx pt hins hlt hcap hptr s P post

theorem bsearch_end_insert_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx = vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 368#64)
    (hstat : s.status = .Running) (hx14 : s.readReg64 .x14 = 1#64) (hx21 : s.readReg64 .x21 = v)
    (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗ P) post := by
  subst hins; add_chunk_fetches_range b (Rust.withPanics ext) 368 20
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches
  rw [memRegion_spare_split_one ptr hlt hcap]; wp_pull_exists; wp_steps 5
  have htake_drop : vec.take vec.length ++ (pt :: vec.drop vec.length) = vec ++ [pt] := by
    rw [List.take_length, List.drop_length]
  have hreasm := reassemble_sortedSetPtOf_snoc A v cap ptr vec pt hlt hcap hptr
  rw [← htake_drop] at hreasm
  refine SepWP.weaken_pre (P' := sortedSetPtOf A v { vec := vec.take vec.length ++ (pt :: vec.drop vec.length) } ∗ P)
    (Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hreasm)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, *]

theorem bv64_beq_one_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 1#64) = decide (n = 1) := by
  by_cases h : n = 1
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; intro heq
    have hto := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hto; exact h hto

theorem bv64_bne_one_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != 1#64) = decide (n ≠ 1) := by
  by_cases h : n = 1
  · subst h; rfl
  · simp only [h, not_false_eq_true, decide_true, bne_iff_ne, ne_eq]; intro heq
    have hto := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hto; exact h hto

theorem bv32_beq_zeroExtend16 (a b : BitVec 16) :
    (BitVec.zeroExtend 32 a == BitVec.zeroExtend 32 b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne, ne_eq]; intro heq; apply h
    apply BitVec.eq_of_toNat_eq; have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at hto
    exact hto

theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv64_ule_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

def sortedSetPtGrownAt (A : RustAlloc) (v : BitVec 64) (vec : List Pt) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜vec.length < cap.toNat ∧ ptr ≠ 0#64 ∧ cap.toNat * 4 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
    A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
    memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)

/-- Symbolic execution of `0x6c50c..0x6c548` (`entry + 236#64` to `entry + 296#64`). -/
theorem bsearch_to_296_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ptr : BitVec 64} {vec : List Pt} {xVal : BitVec 16}
    (h1 : 1 ≤ vec.length) (hlen : vec.length < 2 ^ 62) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 236#64) (hstat : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr) (hx24 : s.readReg64 .x24 = xVal.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ (sf : State), sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace → sf.readReg64 .x8 = ptr →
      sf.readReg64 .x9 = BitVec.ofNat 64 (bsearchLoop vec xVal 0 vec.length) →
      sf.readReg64 .x14 = s.readReg64 .x14 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 → sf.readReg64 .x30 = s.readReg64 .x30 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64) sf (ptSliceAt ptr vec ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64) s (ptSliceAt ptr vec ∗ P) post := by
  have hloop := @bsearchLoop_sepWP b ext vec ptr xVal (by omega)
  add_chunk_fetches_range b (Rust.withPanics ext) 236 24
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hloop hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches; wp_steps 2; rw [bv64_bne_one_ofNat (by omega)]
  by_cases heq1 : vec.length = 1
  · simp only [heq1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]; wp_steps 2
    have hbs1 : bsearchLoop vec xVal 0 vec.length = 0 := by rw [heq1, bsearchLoop]; simp
    exact hcont _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hbs1]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
  · simp only [heq1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]; wp_steps 2
    refine hloop vec.length 0 _ P post (by omega) (by omega)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx28]) (by simp [wp_norm, arm64_norm, hx24])
      (fun sf hpc_f hstat_f hsp_f htr_f hx8_f hx9_f hx14_f hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx27_f hx28_f hx29_f hx30_f hvregs_f => ?_)
    exact hcont sf hpc_f hstat_f (by simpa [wp_norm, arm64_norm] using hsp_f) (by simpa [wp_norm, arm64_norm] using htr_f) hx8_f hx9_f
      (by simpa [wp_norm, arm64_norm] using hx14_f) (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f)
      (by simpa [wp_norm, arm64_norm] using hx21_f) (by simpa [wp_norm, arm64_norm] using hx23_f) (by simpa [wp_norm, arm64_norm] using hx24_f)
      (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx27_f) (by simpa [wp_norm, arm64_norm] using hx28_f)
      (by simpa [wp_norm, arm64_norm] using hx29_f) (by simpa [wp_norm, arm64_norm] using hx30_f) (by simpa [wp_norm, arm64_norm] using hvregs_f)

private theorem bsearch_insert_at_336_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove")))
      (sessionMemmoveSpec growOneStack))
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 336#64)
    (hstat : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = ptr) (hx14 : s.readReg64 .x14 = 1#64) (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64) (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 insertIdx)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64) (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ stackAt s.sp growOneStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗ stackAt s.sp growOneStack ∗ P) post := by
  have hmem := @bsearch_memmove_insert_sepWP_core b A ext hmemmove v cap ptr lenOld vec insertIdx pt
  have hend := @bsearch_end_insert_sepWP b A ext v cap ptr lenOld vec insertIdx pt
  add_chunk_fetches_range b (Rust.withPanics ext) 336 12
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hmem hend hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches
  have hlsl_ins : (BitVec.ofNat 64 insertIdx) <<< 2 = BitVec.ofNat 64 (4 * insertIdx) := bv64_lsl2_ofNat (by omega)
  have hsub_ins : BitVec.ofNat 64 vec.length - BitVec.ofNat 64 insertIdx =
      BitVec.ofNat 64 (vec.length - insertIdx) := bv64_sub_ofNat hins (by omega)
  wp_steps 3; rw [bv64_ule_ofNat (by omega) (by omega)]
  rcases Nat.eq_or_lt_of_le hins with hins_eq | hins_lt
  · have hle_t : vec.length ≤ insertIdx := by omega
    simp only [hle_t, decide_true, ↓reduceIte]
    refine hend hins_eq hlt hcap hptr _ (stackAt s.sp growOneStack ∗ P) post
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) (by simp [wp_norm, arm64_norm, hx14])
      (by simp [wp_norm, arm64_norm, hx21]) (by simp [wp_norm, arm64_norm, hx8, hx26, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx24]) (by simp [wp_norm, arm64_norm, hx27]) (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    exact hcont sf hpc_f hstat_f (by simpa [wp_norm, arm64_norm] using hsp_f) (by simpa [wp_norm, arm64_norm] using htr_f) hx14_f
      (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f) (by simpa [wp_norm, arm64_norm] using hx23_f)
      (by simpa [wp_norm, arm64_norm] using hx24_f) (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
      (by simpa [wp_norm, arm64_norm] using hvregs_f)
  · have hle_f : ¬ vec.length ≤ insertIdx := by omega
    simp only [hle_f, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine hmem hins_lt hlt hcap hptr _ P post
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) (by simpa [wp_norm, arm64_norm] using hsp_align)
      (by simp [wp_norm, arm64_norm, hx28, hx26, hsub_ins]) (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm, hx8, hx26, hlsl_ins]) (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm, hx27]) (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    exact hcont sf hpc_f hstat_f (by simpa [wp_norm, arm64_norm] using hsp_f) (by simpa [wp_norm, arm64_norm] using htr_f) hx14_f
      (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f) (by simpa [wp_norm, arm64_norm] using hx23_f)
      (by simpa [wp_norm, arm64_norm] using hx24_f) (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
      (by simpa [wp_norm, arm64_norm] using hvregs_f)

theorem bsearch_insert_at_336_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop) :
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 336#64 → s.status = .Running → s.spAligned = true →
    s.readReg64 .x8 = ptr → s.readReg64 .x14 = 1#64 → s.readReg64 .x21 = v →
    s.readReg64 .x24 = pt.x.value.zeroExtend 64 → s.readReg64 .x26 = BitVec.ofNat 64 insertIdx →
    s.readReg64 .x27 = pt.y.value.zeroExtend 64 → s.readReg64 .x28 = BitVec.ofNat 64 vec.length →
    (∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ stackAt s.sp growOneStack ∗ P) post) →
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗ stackAt s.sp growOneStack ∗ P) post :=
  bsearch_insert_at_336_sepWP_core
    (hA.session_memmove_ok_at addChunkName
      (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove"))
      growOneStack (by rw [addChunk_fnOff]; simp only [arm64_norm]))
    v cap ptr lenOld vec insertIdx pt hins hlt hcap hptr s P post

private theorem bsearch_insert_at_452_sepWP_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove")))
      (sessionMemmoveSpec growOneStack))
    (v : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt) (hins : insertIdx ≤ vec.length)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 452#64)
    (hstat : s.status = .Running) (hsp_align : s.spAligned = true) (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64) (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 insertIdx)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64) (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ stackAt s.sp growOneStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      (sortedSetPtGrownAt A v vec ∗ stackAt s.sp growOneStack ∗ P) post := by
  unfold sortedSetPtGrownAt; wp_pull_exists; rename_i cap ptr
  apply SepWP.focus_pure (by sep_focus); rintro ⟨hlt, hptr, hcap⟩
  have hmem := @bsearch_memmove_insert_sepWP_core b A ext hmemmove v cap ptr (BitVec.ofNat 64 vec.length) vec insertIdx pt
  have hend := @bsearch_end_insert_sepWP b A ext v cap ptr (BitVec.ofNat 64 vec.length) vec insertIdx pt
  add_chunk_fetches_range b (Rust.withPanics ext) 452 24
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hmem hend hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches
  have hlsl_ins : (BitVec.ofNat 64 insertIdx) <<< 2 = BitVec.ofNat 64 (4 * insertIdx) := bv64_lsl2_ofNat (by omega)
  have hsub_ins : BitVec.ofNat 64 vec.length - BitVec.ofNat 64 insertIdx =
      BitVec.ofNat 64 (vec.length - insertIdx) := bv64_sub_ofNat hins (by omega)
  wp_steps 5; rw [bv64_ult_ofNat (by omega) (by omega)]
  rcases Nat.eq_or_lt_of_le hins with hins_eq | hins_lt
  · have hlt_f : ¬ insertIdx < vec.length := by omega
    simp only [hlt_f, decide_false, Bool.false_eq_true, ↓reduceIte]; wp_steps 1
    refine hend hins_eq hlt hcap hptr _ (stackAt s.sp growOneStack ∗ P) post
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx21]) (by simp [wp_norm, arm64_norm, hx26, hlsl_ins, hins_eq])
      (by simp [wp_norm, arm64_norm, hx24]) (by simp [wp_norm, arm64_norm, hx27]) (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    exact hcont sf hpc_f hstat_f (by simpa [wp_norm, arm64_norm] using hsp_f) (by simpa [wp_norm, arm64_norm] using htr_f) hx14_f
      (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f) (by simpa [wp_norm, arm64_norm] using hx23_f)
      (by simpa [wp_norm, arm64_norm] using hx24_f) (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
      (by simpa [wp_norm, arm64_norm] using hvregs_f)
  · simp only [hins_lt, decide_true, ↓reduceIte]
    refine hmem hins_lt hlt hcap hptr _ P post
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) (by simpa [wp_norm, arm64_norm] using hsp_align)
      (by simp [wp_norm, arm64_norm, hx28, hx26, hsub_ins]) (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm, hx26, hlsl_ins]) (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm, hx27]) (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    exact hcont sf hpc_f hstat_f (by simpa [wp_norm, arm64_norm] using hsp_f) (by simpa [wp_norm, arm64_norm] using htr_f) hx14_f
      (by simpa [wp_norm, arm64_norm] using hx19_f) (by simpa [wp_norm, arm64_norm] using hx20_f) (by simpa [wp_norm, arm64_norm] using hx23_f)
      (by simpa [wp_norm, arm64_norm] using hx24_f) (by simpa [wp_norm, arm64_norm] using hx25_f) (by simpa [wp_norm, arm64_norm] using hx29_f)
      (by simpa [wp_norm, arm64_norm] using hvregs_f)

theorem bsearch_insert_at_452_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (v : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt) (hins : insertIdx ≤ vec.length)
    (s : State) (P : SepProp) (post : State → SepProp → Prop) :
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 452#64 →
    s.status = .Running → s.spAligned = true → s.readReg64 .x21 = v →
    s.readReg64 .x24 = pt.x.value.zeroExtend 64 → s.readReg64 .x26 = BitVec.ofNat 64 insertIdx →
    s.readReg64 .x27 = pt.y.value.zeroExtend 64 → s.readReg64 .x28 = BitVec.ofNat 64 vec.length →
    (∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ stackAt s.sp growOneStack ∗ P) post) →
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      (sortedSetPtGrownAt A v vec ∗ stackAt s.sp growOneStack ∗ P) post :=
  bsearch_insert_at_452_sepWP_core
    (hA.session_memmove_ok_at addChunkName
      (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove"))
      growOneStack (by rw [addChunk_fnOff]; simp only [arm64_norm]))
    v vec insertIdx pt hins s P post

theorem growOnePtFull_post_entails_grown (A : RustAlloc) (v cap : BitVec 64) (vec : List Pt)
    (h1 : 1 ≤ vec.length) (hcap_eq : cap.toNat = vec.length) (hlen_le : vec.length ≤ 65536) :
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
      memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ⊢
    sortedSetPtGrownAt A v vec := by
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p'
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hp', _⟩
  unfold sortedSetPtGrownAt
  let cap' := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
    dsimp [cap']
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : vec.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 4 < 2 ^ 63 := by omega
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  apply Entails.pure_right ⟨hlt, hp', hcap'_lt⟩
  rw [← ptSliceAt_eq_pointsToBytes, ptListBytes_length, Nat.mul_comm 4 vec.length, ← hcap'_toNat,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, hcap_eq]
  exact Entails.of_eq (by ac_rfl)

private theorem finish_grow_8_zero_cells_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8ZeroCellsSpecG A allocHookStack) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_8_zero_cells_opt_of_spec (subroutine_ok_withOptInv_none_of (finish_grow_8_ok_ext_4k hA)))

private theorem finish_grow_8_ne_cells_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8NeCellsSpecG A allocHookStack) :=
  subroutine_ok_of_withOptInv_none
    (finish_grow_8_ne_cells_opt_of_spec (subroutine_ok_withOptInv_none_of (finish_grow_8_ok_ext_4k hA)))

private theorem stackAt_growOne4k (sp : BitVec 64) :
    stackAt sp growOneStack = stackAt (sp - 64#64) finishGrowStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗ ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (by decide)

private theorem grow_new_cap_eq4k {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have h2 : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hsh : cap <<< 1 = BitVec.ofNat 64 (2 * cap.toNat) :=
    BitVec.eq_of_toNat_eq (by rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  by_cases hlt : 4 < 2 * cap.toNat
  · have hult : (4#64).ult (cap <<< 1) = true := by rw [BitVec.ult_eq_decide, decide_eq_true_iff, h2]; exact hlt
    rw [hult]; simp only [↓reduceIte, hsh, (by omega : max (2 * cap.toNat) 4 = 2 * cap.toNat)]
  · have hult : (4#64).ult (cap <<< 1) = false := by rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, h2]; exact hlt
    rw [hult]; simp only [Bool.false_eq_true, ↓reduceIte, (by omega : max (2 * cap.toNat) 4 = 4)]

theorem grow_one_pt_bs_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName) (growOnePtBsSpec A) := by
  simp only [growOnePtBsSpec, growOneStrideBsSpec, stackAt_growOne4k, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOnePtName = 0x5a748 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x5a748
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext) (name := growOnePtName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x5a748))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_4k hA
  have hfg1 := finish_grow_8_ne_cells_ok_4k hA
  rw [Program.fnAddr_rel (name := growOnePtName)
    hfn CryptoVerification.libsignalSessionCode_fnOff_0x5a8e8 (k := 416) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b (Rust.withPanics ext) hfn 0x5a748 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢; clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr growOnePtName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches; wpp_init x s0; obtain ⟨v, cap, ptr, bs⟩ := x; dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq4k hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_lay : LayoutOk (new.toNat * (4#64 : BitVec 64).toNat) (2#64 : BitVec 64).toNat :=
    ⟨by change 0 < new.toNat * 4; omega, ⟨1, rfl⟩, by change new.toNat * 4 + 2 ≤ 2 ^ 63; omega⟩
  have hpow2 : ∃ k, (2#64 : BitVec 64).toNat = 2 ^ k := ⟨1, rfl⟩
  have hpow2' : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0; have h0_mul : (0#64 : BitVec 64).toNat * 4 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega); subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 4 = new.toNat * 4 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64); wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a748))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0; apply SepWPp.of_sepWP_ret; wp_steps; wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    rw [show max (2 * cap.toNat) 4 * 4 - bs.length = new.toNat * 4 - bs.length by rw [hnew_toNat],
      show max (2 * cap.toNat) 4 * 4 = new.toNat * 4 by rw [hnew_toNat]]
    apply SepWPp.of_sepWP (mid := entry + 60#64); wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a748))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0; apply SepWPp.of_sepWP_ret; wp_steps; wp_done

theorem grow_one_pt_full_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName) (growOnePtFullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_pt_bs_ok_4k hA)

theorem grow_one_pt_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName) (growOnePtSpec A) :=
  grow_one_stride_empty_of_bs (grow_one_pt_bs_ok_4k hA)

private theorem call_grow_one_pt_full_wpp_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName) (growOnePtFullSpec A))
    {ret_pc target_pc : BitVec 64} {s0 s : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (v cap ptr : BitVec 64) (vec : List Pt)
    (h1 : 1 ≤ vec.length) (hlen : vec.length ≤ 65536)
    (hcap_eq : cap.toNat = vec.length) (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace →
      CalleeSavedPreserved s sf →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (sortedSetPtGrownAt A v vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  rw [← fnAddr_growOnePt_eq b ext] at hpc
  have hcap_ne0 : cap ≠ 0#64 := by intro hc0; subst hc0; change 0 = vec.length at hcap_eq; omega
  have hbs_len : (ptListBytes vec).length = cap.toNat * 4 := by
    rw [ptListBytes_length, hcap_eq, Nat.mul_comm]
  have hmax_bound : max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by omega
  refine SepWPp.call (x := (v, cap, ptr, ptListBytes vec))
    (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F) hcall hpc hrun hsp hlr ?_ ?_ ?_ ?_
  · intro R' hm
    simp only [growOnePtFullSpec, growOneStrideFullSpec, hcap_ne0, ↓reduceIte,
      hbs_len, ← ptSliceAt_eq_pointsToBytes, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, trivial, hptr, hmax_bound⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [growOnePtFullSpec, growOneStrideFullSpec, addChunkOnPanic] at hm ⊢
    exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f
    simp only [growOnePtFullSpec, growOneStrideFullSpec, sepConj_assoc]
    apply SepWPp.pure_elim; intro htr_f
    have hgrown := growOnePtFull_post_entails_grown A v cap vec h1 hcap_eq hlen
    refine SepWPp.weaken_pre ?_ (hnext sf hpc_f hrun_f hsp_f (htr_f.trans htr) hcs_f)
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hgrown)

/-- Call `RawVec<Pt>::grow_one` when `cap.toNat = vec.length` (`1 ≤ vec.length ≤ 65536`),
    producing `sortedSetPtGrownAt A v vec`. -/
theorem call_grow_one_pt_full_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (v cap ptr : BitVec 64) (vec : List Pt) :
    1 ≤ vec.length → vec.length ≤ 65536 → cap.toNat = vec.length → ptr ≠ 0#64 →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk") →
    s.status = .Running → s.spAligned = true → s.readReg64 .x0 = v → s.readReg64 Reg.lr = ret_pc → s.trace = s0.trace →
    (∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf (sortedSetPtGrownAt A v vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) →
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) :=
  call_grow_one_pt_full_wpp_core (grow_one_pt_full_ok_ext hA) v cap ptr vec

theorem call_grow_one_pt_full_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (v cap ptr : BitVec 64) (vec : List Pt) :
    1 ≤ vec.length → vec.length ≤ 65536 → cap.toNat = vec.length → ptr ≠ 0#64 →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk") →
    s.status = .Running → s.spAligned = true → s.readReg64 .x0 = v → s.readReg64 Reg.lr = ret_pc → s.trace = s0.trace →
    (∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf (sortedSetPtGrownAt A v vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) →
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) :=
  call_grow_one_pt_full_wpp_core (grow_one_pt_full_ok_4k hA) v cap ptr vec

private theorem call_grow_one_pt_empty_wpp_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName) (growOnePtSpec A))
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (v ptr lenOld : BitVec 64) (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      p' ≠ 0#64 → sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        ((v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.live p' 16 2 ∗ memRegion p' 16 ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  rw [← fnAddr_growOnePt_eq b ext] at hpc
  have hmax_bound : max (2 * (0#64 : BitVec 64).toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by decide
  refine SepWPp.call (x := (v, 0#64, ptr)) (F := ((v + 16#64) ↦₆₄ lenOld) ∗ F) hcall hpc hrun hsp hlr ?_ ?_ ?_ ?_
  · intro R' hm
    simp only [growOnePtSpec, growOneStrideEmptySpec, ↓reduceIte, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hptr, hmax_bound⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [growOnePtSpec, growOneStrideEmptySpec, addChunkOnPanic] at hm ⊢
    exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f
    have hmax0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [growOnePtSpec, growOneStrideEmptySpec, hmax0, sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.pure_elim; intro htr_f; apply SepWPp.exists_elim; intro p'; apply SepWPp.pure_elim; rintro ⟨hp', _⟩
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (hnext sf p' hp' hpc_f hrun_f hsp_f (htr_f.trans htr) hcs_f)

/-- Call `RawVec<Pt>::grow_one` when `cap = 0#64` (`vec = []`), producing a capacity-`4` buffer. -/
theorem call_grow_one_pt_empty_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (v ptr lenOld : BitVec 64) :
    ptr ≠ 0#64 →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk") →
    s.status = .Running → s.spAligned = true → s.readReg64 .x0 = v → s.readReg64 Reg.lr = ret_pc → s.trace = s0.trace →
    (∀ (sf : State) (p' : BitVec 64), p' ≠ 0#64 → sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        ((v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.live p' 16 2 ∗ memRegion p' 16 ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) →
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) :=
  call_grow_one_pt_empty_wpp_core (grow_one_pt_ok_ext hA) v ptr lenOld

theorem call_grow_one_pt_empty_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {ret_pc target_pc : BitVec 64} {s0 s : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (v ptr lenOld : BitVec 64) :
    ptr ≠ 0#64 →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk") →
    s.status = .Running → s.spAligned = true → s.readReg64 .x0 = v → s.readReg64 Reg.lr = ret_pc → s.trace = s0.trace →
    (∀ (sf : State) (p' : BitVec 64), p' ≠ 0#64 → sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        ((v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.live p' 16 2 ∗ memRegion p' 16 ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) →
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) :=
  call_grow_one_pt_empty_wpp_core (grow_one_pt_ok_4k hA) v ptr lenOld

/-- Symbolic execution of `0x6c4f8..0x6c508` (`entry + 216#64` to `entry + 64#64`). -/
theorem bsearch_push_empty_at_216_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (v cap ptr lenOld : BitVec 64) (pt : Pt)
    (hlt : 0 < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 216#64)
    (hstat : s.status = .Running) (hx14 : s.readReg64 .x14 = 1#64) (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64) (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hcont : ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) sf
        (sortedSetPtOf A v { vec := [pt] } ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64) s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ memRegion ptr (cap.toNat * 4) ∗ P) post := by
  add_chunk_fetches_range b (Rust.withPanics ext) 216 20
  dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
  examples_hide_fetches
  have hsplit := memRegion_spare_split_one ptr (len := 0) hlt hcap
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.sub_zero, BitVec.add_zero, Nat.zero_add] at hsplit
  rw [hsplit]; wp_pull_exists; rename_i v1 v0; wp_steps 5
  have hreasm := reassemble_sortedSetPtOf_snoc A v cap ptr [] pt hlt hcap hptr
  unfold ptSliceAt arrayAt at hreasm
  simp only [List.length_nil, Nat.mul_zero, BitVec.add_zero, Nat.zero_add, List.nil_append, emp_sepConj] at hreasm
  refine SepWP.weaken_pre (P' := sortedSetPtOf A v { vec := [pt] } ∗ P)
    (Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hreasm)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, hstat, hx14]

theorem bsearchReplace_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    {target_pc : BitVec 64} {s0 st : State} {Q : State → SepProp → Prop} {R F : SepProp}
    (v cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (h1 : 1 ≤ s.vec.length) (hlen : s.vec.length ≤ 65536)
    (hle_cap : s.vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 236#64)
    (hrun : st.status = .Running) (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx8 : st.readReg64 .x8 = ptr) (hx14 : st.readReg64 .x14 = 1#64) (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64) (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 → sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 → sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (sortedSetPtOf A v (bsearchReplace s pt) ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc st
      (ptSliceAt ptr s.vec ∗ (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
        A.pool ∗ stackAt st.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hmem4k := hA.session_memmove_ok_at addChunkName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" "memmove"))
    growOneStack (by decide) (by decide) (by rw [addChunk_fnOff]; simp only [arm64_norm])
  apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 296#64)
  refine bsearch_to_296_sepWP h1 (by omega) st _ _ hpc hrun hx8 hx24 hx28
    (fun s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx9_1 hx14_1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 _ hvregs_1 => ?_)
  apply SepWP.done hpc1 hrun1
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hsp1_al : s1.spAligned = true := by unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
  let base := bsearchLoop s.vec pt.x.value 0 s.vec.length
  change s1.readReg64 .x9 = BitVec.ofNat 64 base at hx9_1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec pt.x.value 0 s.vec.length h1 (by omega)
  have hb_lt : base < s.vec.length := by omega
  have hb_get : s.vec[base]?.getD default = s.vec[base]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  let baseX := (s.vec[base]'hb_lt).x.value
  have hlsl_base : (BitVec.ofNat 64 base) <<< 2 = BitVec.ofNat 64 (4 * base) := bv64_lsl2_ofNat (by omega)
  unfold bsearchReplace at hnext; dsimp only at hnext; rw [hb_get] at hnext
  by_cases heq : ((s.vec[base]'hb_lt).x.value == pt.x.value) = true
  · simp only [heq, ↓reduceIte] at hnext
    change ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 → sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 → sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (sortedSetPtOf A v { vec := s.vec.set base pt } ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) at hnext
    have hbaseX_eq : (s.vec[base]'hb_lt).x.value = pt.x.value := beq_iff_eq.mp heq
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64)
    add_chunk_fetches_range b (Rust.withPanics ext) 296 24
    dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
    examples_hide_fetches; rw [ptSliceAt_focus s.vec base ptr hb_lt]; unfold ptAt; wp_steps 6
    have hreasm := reassemble_sortedSetPtOf_set A v cap ptr s.vec base pt hb_lt hle_cap hcap hptr
    rw [hbaseX_eq]
    apply SepWP.weaken_pre (P' := sortedSetPtOf A v { vec := s.vec.set base pt } ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
    · exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hreasm)
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm] using hsp1) (by simpa [wp_norm, arm64_norm] using htr1')
      (by simpa [wp_norm, arm64_norm, hx14] using hx14_1)
      (by simpa [wp_norm, arm64_norm] using hx19_1) (by simpa [wp_norm, arm64_norm] using hx20_1)
      (by simpa [wp_norm, arm64_norm] using hx23_1) (by simpa [wp_norm, arm64_norm] using hx24_1)
      (by simpa [wp_norm, arm64_norm] using hx25_1) (by simpa [wp_norm, arm64_norm] using hx29_1)
      (by simpa [wp_norm, arm64_norm] using hvregs_1)
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext
    let insertIdx := if baseX.toNat < pt.x.value.toNat then base + 1 else base
    change ∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64 →
      sf.status = .Running → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 → sf.readReg64 .x20 = st.readReg64 .x20 →
      sf.readReg64 .x23 = st.readReg64 .x23 → sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (sortedSetPtOf A v { vec := s.vec.take insertIdx ++ (pt :: s.vec.drop insertIdx) } ∗ A.pool ∗ stackAt st.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) at hnext
    have hins_le : insertIdx ≤ s.vec.length := by dsimp [insertIdx]; split_ifs <;> omega
    have hfold_slice :
        ((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ (s.vec[base]'hb_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗ memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F) =
        (ptSliceAt ptr s.vec ∗ (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗ A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          A.pool ∗ stackAt st.sp growOneStack ∗ F) := by
      change ((ptSliceAt ptr (List.take base s.vec) ∗ ptAt (s.vec[base]'hb_lt) (ptr + BitVec.ofNat 64 (4 * base)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗ _) = _
      rw [← ptSliceAt_focus s.vec base ptr hb_lt]
    by_cases hlt_cap : s.vec.length < cap.toNat
    · have hcap_ne : ¬ s.vec.length = cap.toNat := by omega
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName + 64#64)
      have hins336 := @bsearch_insert_at_336_sepWP_core b A ext hmem4k v cap ptr
        (BitVec.ofNat 64 s.vec.length) s.vec insertIdx pt hins_le hlt_cap hcap hptr
      add_chunk_fetches_range b (Rust.withPanics ext) 296 40
      dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hins336 hpc1 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
      examples_hide_fetches; rw [ptSliceAt_focus s.vec base ptr hb_lt]; unfold ptAt; wp_steps 4
      rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from Bool.eq_false_iff.mpr heq]
      simp only [Bool.not_false, ↓reduceIte]; wp_steps 4
      rw [hfold_slice, bv64_beq_cap_ofNat (by omega)]
      simp only [hcap_ne, decide_false, Bool.false_eq_true, ↓reduceIte]; rw [← hsp1]
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hins336 _ (A.pool ∗ F) _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
          (by simpa [wp_norm, arm64_norm] using hsp1_al) (by simp [wp_norm, arm64_norm, hx8_1])
          (by simp [wp_norm, arm64_norm, hx14_1, hx14]) (by simp [wp_norm, arm64_norm, hx21_1, hx21])
          (by simp [wp_norm, arm64_norm, hx24_1, hx24])
          (by simp only [wp_norm, arm64_norm]; exact cinc_insertIdx_eq baseX pt.x.value base)
          (by simp [wp_norm, arm64_norm, hx27_1, hx27]) (by simp [wp_norm, arm64_norm, hx28_1, hx28])
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f
      have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm, hsp1] using hsp_f
      rw [← hsp_f, hsp_f']
      exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hpc_f hrun_f hsp_f' (by simpa [wp_norm, arm64_norm, htr1'] using htr_f) hx14_f
          (by simpa [wp_norm, arm64_norm, hx19_1] using hx19_f) (by simpa [wp_norm, arm64_norm, hx20_1] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx23_1] using hx23_f) (by simpa [wp_norm, arm64_norm, hx24_1] using hx24_f)
          (by simpa [wp_norm, arm64_norm, hx25_1] using hx25_f) (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
          (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f))
    · have hcall := @call_grow_one_pt_full_wpp_4k b A ext hA
        ((tripleRatchetProgAtExt b ext).fnAddr addChunkName + 452#64) target_pc s0
      have hins452 := @bsearch_insert_at_452_sepWP_core b A ext hmem4k v s.vec insertIdx pt hins_le
      apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr addChunkName +
        bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one"
          "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"))
      add_chunk_fetches_range b (Rust.withPanics ext) 296 40
      add_chunk_fetches_range b (Rust.withPanics ext) 444 8
      dsimp only [tripleRatchetProgAtExt, addChunkName, BitVec.ofNat_eq_ofNat] at hcall hins452 hpc1 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk" = entry
      examples_hide_fetches; rw [ptSliceAt_focus s.vec base ptr hb_lt]; unfold ptAt; wp_steps 4
      rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from Bool.eq_false_iff.mpr heq]
      simp only [Bool.not_false, ↓reduceIte]; wp_steps 4
      rw [hfold_slice, bv64_beq_cap_ofNat (by omega), show decide (s.vec.length = cap.toNat) = true from decide_eq_true (by omega)]
      simp only [↓reduceIte]; wp_steps 2
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      have hcap_eq : cap.toNat = s.vec.length := by omega
      rw [show memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp by
        rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero], ← hsp1]; simp only [emp_sepConj]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hcall (F := F) v cap ptr s.vec h1 hlen hcap_eq hptr
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
          (by simpa [wp_norm, arm64_norm] using hsp1_al) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr1')
          (fun s2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_))
      have hsp2' : s2.sp = st.sp := by rw [hsp2]; simpa [wp_norm, arm64_norm] using hsp1
      have hsp2_al : s2.spAligned = true := by unfold State.spAligned at hsp_al ⊢; rwa [hsp2']
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
      have hx26_s2 : s2.readReg64 .x26 = BitVec.ofNat 64 insertIdx := by
        rw [hx26_2]; simp only [wp_norm, arm64_norm]; exact cinc_insertIdx_eq baseX pt.x.value base
      rw [← hsp2]; apply SepWPp.of_sepWP (mid := entry + 64#64)
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hins452 s2 (A.pool ∗ F) _ hpc2 hrun2 hsp2_al
          (by rw [hx21_2]; simpa [wp_norm, arm64_norm, hx21] using hx21_1)
          (by rw [hx24_2]; simpa [wp_norm, arm64_norm, hx24] using hx24_1) hx26_s2
          (by rw [hx27_2]; simpa [wp_norm, arm64_norm, hx27] using hx27_1)
          (by rw [hx28_2]; simpa [wp_norm, arm64_norm, hx28] using hx28_1)
          (fun sf hpc_f hrun_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
      apply SepWP.done hpc_f hrun_f; rw [hsp2']
      exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hpc_f hrun_f (hsp_f.trans hsp2') (htr_f.trans htr2) hx14_f
          (by rw [hx19_f, hx19_2]; simpa [wp_norm, arm64_norm] using hx19_1)
          (by rw [hx20_f, hx20_2]; simpa [wp_norm, arm64_norm] using hx20_1)
          (by rw [hx23_f, hx23_2]; simpa [wp_norm, arm64_norm] using hx23_1)
          (by rw [hx24_f, hx24_2]; simpa [wp_norm, arm64_norm] using hx24_1)
          (by rw [hx25_f, hx25_2]; simpa [wp_norm, arm64_norm] using hx25_1)
          (by rw [hx29_f, hx29_2]; simpa [wp_norm, arm64_norm] using hx29_1)
          (by rw [hvregs_f, hvregs_2]; simpa [wp_norm, arm64_norm] using hvregs_1))

end CryptoVerification.SpqrV1.Poly.AddChunk
