/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# Relocated `.rodata` Pointer Slots

**Checked by Lean.**

Reads 8-byte `R_AARCH64_ABS64` relocated pointer slots in `.rodata` (such as Rust `dyn` trait
vtable entries and `&'static` references) that `LinkedImage.load` patches to `img.base + target`:
* `reloc64At rs dataLen k target`: decidable check that `rs` writes `base + target` at `[k, k + 8)`
  with no later overlapping relocation.
* `loads_reloc64_holdsBytes`, `loads_reloc64_read64`: under `Obj.Loads li img` and
  `img.FrozenLoaded s`, the slot at `img.base + off` holds `bytesLE 8 (img.base + target)` with
  permission `.ro`.
* `Satisfies.of_reloc64`, `SepWP.reloc64_intro`, `SepWPp.reloc64_intro`: introduce the relocated
  slot as a read-only points-to `↦₆₄ᵣ` in spatial and `SepWP` / `SepWPp` contexts.
-/

@[expose] public section

namespace CryptoProofLib.RoDataReloc

open Arm64 Arm64.Obj ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux

/-- `rs` (applied in order by `LinkedImage.load`) leaves `base + target` in the 8 bytes at data
offset `k`: some relocation of width 8 at offset `k` with this target, and no later relocation
overlapping `[k, k + 8)`. Every relocation up to the match lies within `dataLen` (the later ones
are checked by `noRelocInRange`). -/
def reloc64At (rs : List DataReloc) (dataLen k target : Nat) : Bool :=
  match rs with
  | [] => false
  | r :: rs =>
    decide (r.off + r.width ≤ dataLen) &&
      ((decide (r.off = k ∧ r.width = 8 ∧ r.target = target) && noRelocInRange rs dataLen k 8) ||
        reloc64At rs dataLen k target)

/-- The fold lemma. If `reloc64At rs dataLen k target` and the relocations apply successfully to
`d` (of length `dataLen`), the result has length `dataLen` and holds `bytesLE 8 (base + target)` at
`[k, k + 8)`. -/
theorem foldlM_reloc64At {base : BitVec 64} {target : Nat} :
    ∀ (rs : List DataReloc) (d d' : List (BitVec 8)) (dataLen k : Nat),
      d.length = dataLen →
      reloc64At rs dataLen k target = true →
      rs.foldlM (DataReloc.apply base) d = .ok d' →
      d'.length = dataLen ∧ (d'.drop k).take 8 = bytesLE 8 (base + BitVec.ofNat 64 target)
  | [], _, _, _, _, _, hrel, _ => by simp [reloc64At] at hrel
  | r :: rs, d, d', dataLen, k, hlen, hrel, hfold => by
    simp only [reloc64At, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hrel
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · contradiction
    rename_i d1 happ
    obtain ⟨hrN, hcase⟩ := hrel
    have hlen1 : d1.length = dataLen := by
      rw [dataReloc_apply_length happ (by omega), hlen]
    rcases hcase with ⟨⟨hroff, hrw, hrtgt⟩, hno⟩ | htail
    · -- the matching relocation: it writes the slot, and no later relocation touches it
      have hd1 : d.take r.off ++ bytesLE r.width (base + BitVec.ofNat 64 r.target) ++
          d.drop (r.off + r.width) = d1 := by
        simp only [DataReloc.apply, bind, Except.bind, pure, Except.pure] at happ
        split at happ
        · contradiction
        · injection happ
      rw [hroff, hrw, hrtgt] at hd1
      have hslot : (d1.drop k).take 8 = bytesLE 8 (base + BitVec.ofNat 64 target) := by
        have htk : (d.take k).length = k := by simp only [List.length_take]; omega
        have hb8 : (bytesLE 8 (base + BitVec.ofNat 64 target)).length = 8 := bytesLE_length _ _
        rw [← hd1, List.append_assoc, List.drop_left' htk, List.take_left' hb8]
      obtain ⟨hlen2, hslice2⟩ := foldlM_dataReloc_preserves_slice rs d1 d' dataLen k 8 hlen1 hno hfold
      exact ⟨hlen2, hslice2.trans hslot⟩
    · exact foldlM_reloc64At rs d1 d' dataLen k hlen1 htail hfold

/-- A relocated `.rodata` pointer slot holds its target. For an 8-byte slot at image offset
`off` inside `li.roData` whose data offset `off - li.dataOff` carries an ABS64 relocation to
`target` (`reloc64At`), every image `img` of `li` with `img.FrozenLoaded s` holds the little-endian
bytes of `img.base + target` at `img.base + off`, read-only. -/
theorem loads_reloc64_holdsBytes {li : LinkedImage} {img : Image} {s : State}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {off target : Nat}
    (hoff : li.dataOff ≤ off)
    (hrel : reloc64At li.relocs (li.data.length + li.bss) (off - li.dataOff) target = true)
    (hro : inLiRoData li off 8 = true) :
    Obj.HoldsBytes s.mem (img.base + BitVec.ofNat 64 off)
      (bytesLE 8 (img.base + BitVec.ofNat 64 target)) (fun _ => .ro) := by
  obtain ⟨data, hfold, _, _, _, himg_eq⟩ := load_eq_ok himg
  have haddr : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff :=
    congrArg Image.dataAddr himg_eq
  have hdata : img.data = data := congrArg Image.data himg_eq
  have hro_map : img.roData = li.roData.map (fun (o, m) => (img.base + BitVec.ofNat 64 o, m)) :=
    congrArg Image.roData himg_eq
  have hlen0 : (li.data ++ List.replicate li.bss 0).length = li.data.length + li.bss := by simp
  obtain ⟨_, hd_slot⟩ :=
    foldlM_reloc64At li.relocs _ data (li.data.length + li.bss) (off - li.dataOff) hlen0 hrel hfold
  simp only [inLiRoData, List.any_eq_true, decide_eq_true_eq] at hro
  obtain ⟨⟨rOff, rLen⟩, hr_mem, hr_le1, hr_le2, hr_lt⟩ := hro
  intro j hj
  rw [bytesLE_length] at hj
  -- the slot lies inside the data (it is inside a `.rodata` section, which `wellFormed` bounds;
  -- here it follows from the slice equation)
  have hslot_len : ((data.drop (off - li.dataOff)).take 8).length = 8 := by
    rw [hd_slot, bytesLE_length]
  have hi : (off - li.dataOff) + j < img.data.length := by
    rw [hdata]
    rw [List.length_take, List.length_drop] at hslot_len
    omega
  have ha_eq : img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j) =
      img.base + BitVec.ofNat 64 off + BitVec.ofNat 64 j := by
    rw [haddr, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (img.base + ·) (congrArg (BitVec.ofNat 64) (by omega))
  have ha_eq' : img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j) =
      img.base + BitVec.ofNat 64 (off + j) := by
    rw [ha_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hisRo : img.isRoData (img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j)) = true := by
    simp only [Image.isRoData, hro_map, List.any_map, List.any_eq_true]
    refine ⟨(rOff, rLen), hr_mem, ?_⟩
    simp only [Function.comp_apply, decide_eq_true_eq, ha_eq']
    rw [bv_add_sub_add_of_le img.base (by omega) (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hread, hperm⟩ := hF.roData ((off - li.dataOff) + j) hi hisRo
  have hget : (bytesLE 8 (img.base + BitVec.ofNat 64 target))[j]'(by rw [bytesLE_length]; omega) =
      img.data[(off - li.dataOff) + j] := by
    have h1 : ((img.data.drop (off - li.dataOff)).take 8)[j]'(by
        rw [List.length_take, List.length_drop]; omega) =
        (bytesLE 8 (img.base + BitVec.ofNat 64 target))[j]'(by rw [bytesLE_length]; omega) := by
      simp only [hdata, hd_slot]
    rw [← h1, List.getElem_take, List.getElem_drop]
  rw [← ha_eq, hget]
  exact ⟨hread, hperm⟩

/-- `bytesLE 8` is `unpack64` (both little-endian). -/
theorem bytesLE_eight (v : BitVec 64) : bytesLE 8 v = unpack64 v := by
  simp [bytesLE, unpack64, List.range_succ]

/-- `loads_reloc64_holdsBytes` as `read64` / `RO` facts. -/
theorem loads_reloc64_read64 {li : LinkedImage} {img : Image} {s : State}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {off target : Nat}
    (hoff : li.dataOff ≤ off)
    (hrel : reloc64At li.relocs (li.data.length + li.bss) (off - li.dataOff) target = true)
    (hro : inLiRoData li off 8 = true) :
    s.mem.RO (img.base + BitVec.ofNat 64 off) 8 ∧
      s.mem.read64 (img.base + BitVec.ofNat 64 off) = img.base + BitVec.ofNat 64 target := by
  obtain ⟨hRO, hread⟩ := holdsBytes_ro (loads_reloc64_holdsBytes himg hF hoff hrel hro)
  rw [bytesLE_length] at hRO hread
  exact ⟨hRO, Memory.read64_of_readBytes_eq_unpack64 _ _ _ (by rw [hread, bytesLE_eight])⟩

/-- Introduce the relocated slot as a read-only points-to `↦₆₄ᵣ` into `s.mem ⊨ P`. -/
theorem Satisfies.of_reloc64 {li : LinkedImage} {img : Image} {s : State} {P : SepProp}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {off target : Nat}
    (hoff : li.dataOff ≤ off)
    (hrel : reloc64At li.relocs (li.data.length + li.bss) (off - li.dataOff) target = true)
    (hro : inLiRoData li off 8 = true) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ (img.base + BitVec.ofNat 64 target)) ∗ P := by
  obtain ⟨hRO, hread⟩ := loads_reloc64_read64 himg hF hoff hrel hro
  exact Satisfies.rodata64_intro hRO hread hP

/-- Introduce a relocated `.rodata` pointer slot into a `SepWP` spatial context. -/
theorem SepWP.reloc64_intro {li : LinkedImage} {img : Image}
    {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {off target : Nat}
    (hoff : li.dataOff ≤ off)
    (hrel : reloc64At li.relocs (li.data.length + li.bss) (off - li.dataOff) target = true)
    (hro : inLiRoData li off 8 = true)
    (h : SepWP prog target_pc s
      (((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ (img.base + BitVec.ofNat 64 target)) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  apply h R
  rw [sepConj_assoc]
  exact Satisfies.of_reloc64 himg hF hoff hrel hro hm

/-- Introduce a relocated `.rodata` pointer slot into a `SepWPp` (panic-aware) spatial context. -/
theorem SepWPp.reloc64_intro {li : LinkedImage} {img : Image}
    {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {off target : Nat}
    (hoff : li.dataOff ≤ off)
    (hrel : reloc64At li.relocs (li.data.length + li.bss) (off - li.dataOff) target = true)
    (hro : inLiRoData li off 8 = true)
    (h : SepWPp prog ret s
      (((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ (img.base + BitVec.ofNat 64 target)) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unfold SepWPp at h ⊢
  intro R hm hcode
  apply h R _ hcode
  rw [sepConj_assoc]
  exact Satisfies.of_reloc64 himg hF hoff hrel hro hm

end CryptoProofLib.RoDataReloc
