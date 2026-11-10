/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Multi
public meta import Lean.Elab.Term

/-!
# Split Kernel Verification for Multi-Block Placement

Decomposes `Obj.Interned.checkMultiDisjoint` into independent kernel-checkable obligations so peak
kernel WHNF cache memory scales with a single segment or chunk walk:
- `List.rec`-based list primitives (`rDrop`, `rTake`, `rDropN?`, `rLen`, `rGetD`) and precomputed
  segment-length walks (`seg_lens%`, `lRegionView`, `lNextView`, `lMultiTextWalk`, `lDataWalk`);
- single-pass sorted data relocation patching (`relocsLinOk`, `patchLin`, `patchedDataLin`) and
  address-ordered linear data-disjointness scanning (`dataScanB`, `dataDisjointFastB`);
- chunked text, data, and per-index obligations (`lTextChunks`, `lDataChunks`, `AllIdxChunks`)
  recombined by `checkMultiDisjoint_spec_split` and `checkMultiDisjoint_spec_chunks`.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib.Placed.Split
open Arm64 Arm64.Process Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection ProofLib.ObjectLoad

noncomputable def rDrop {α : Type} (n : Nat) (l : List α) : List α :=
  @List.rec α (fun _ => Nat → List α) (fun _ => [])
    (fun b t ih k => Nat.casesOn (motive := fun _ => List α) k (b :: t) ih) l n

theorem rDrop_eq {α : Type} (n : Nat) (l : List α) : rDrop n l = l.drop n := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons b t ih => cases n with
    | zero => rfl
    | succ k => exact ih k

noncomputable def rLenAux {α : Type} (l : List α) : Nat → Nat :=
  @List.rec α (fun _ => Nat → Nat) (fun acc => acc)
    (fun _ _ ih acc => Nat.casesOn (motive := fun _ => Nat) acc (ih 1) fun k => ih (k + 2)) l

theorem rLenAux_eq {α : Type} (l : List α) (acc : Nat) : rLenAux l acc = l.length + acc := by
  induction l generalizing acc with
  | nil => simp [rLenAux]
  | cons b t ih =>
    show (Nat.casesOn (motive := fun _ => Nat) acc (rLenAux t 1) fun k => rLenAux t (k + 2)) = _
    cases acc with
    | zero => exact (ih 1).trans (by simp)
    | succ k => exact (ih (k + 2)).trans (by simp; omega)

noncomputable def rLen {α : Type} (l : List α) : Nat := rLenAux l 0

theorem rLen_eq {α : Type} (l : List α) : rLen l = l.length := by
  simp [rLen, rLenAux_eq]

/-- `List.take`, `List.rec`-based. -/
noncomputable def rTake {α : Type} (n : Nat) (l : List α) : List α :=
  @List.rec α (fun _ => Nat → List α) (fun _ => [])
    (fun b _ ih k => Nat.casesOn (motive := fun _ => List α) k [] fun k => b :: ih k) l n

theorem rTake_eq {α : Type} (n : Nat) (l : List α) : rTake n l = l.take n := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons b t ih => cases n with
    | zero => rfl
    | succ k => exact congrArg (b :: ·) (ih k)

/-- `List.getD`, `List.rec`-based. -/
noncomputable def rGetD {α : Type} (l : List α) (n : Nat) (d : α) : α :=
  @List.rec α (fun _ => Nat → α) (fun _ => d)
    (fun b _ ih k => Nat.casesOn (motive := fun _ => α) k b ih) l n

theorem rGetD_eq {α : Type} (l : List α) (n : Nat) (d : α) : rGetD l n d = l.getD n d := by
  induction l generalizing n with
  | nil => rfl
  | cons b t ih => cases n with
    | zero => rfl
    | succ k => exact (ih k).trans (by simp)

/-- `dropN?`, `List.rec`-based. -/
noncomputable def rDropN? {α : Type} (n : Nat) (l : List α) : Option (List α) :=
  @List.rec α (fun _ => Nat → Option (List α))
    (fun k => Nat.casesOn (motive := fun _ => Option (List α)) k (some []) fun _ => none)
    (fun b t ih k => Nat.casesOn (motive := fun _ => Option (List α)) k (some (b :: t)) ih) l n

theorem rDropN?_eq {α : Type} (n : Nat) (l : List α) : rDropN? n l = dropN? n l := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons b t ih => cases n with
    | zero => rfl
    | succ k => exact ih k


noncomputable def lRegionView (addr : BitVec 64) : List (Snapshot.Region × Nat) → Option (Perm × List (BitVec 8) × Nat)
  | [] => none
  | (r, len) :: rs =>
    let d := (addr - r.start).toNat
    if Nat.blt d len then
      if Nat.ble len 18446744073709551616 then some (r.perm, rDrop d r.bytes, len - d) else none
    else
      match lRegionView addr rs with
      | some (p, bs, m) =>
        if Nat.ble len d && Nat.ble (d + m) 18446744073709551616 then some (p, bs, m) else none
      | none => none

theorem lRegionView_eq (addr : BitVec 64) :
    ∀ regions, lRegionView addr (regions.map fun r => (r, r.bytes.length)) = regionView addr regions
  | [] => rfl
  | r :: rs => by
    simp only [List.map_cons, lRegionView, regionView, rDrop_eq, lRegionView_eq addr rs]
    cases regionView addr rs <;> rfl

noncomputable def lNextView (rl : List (Snapshot.Region × Nat)) (a : BitVec 64) :
    Option (BitVec 64 × Perm × List (BitVec 8)) → Option (Perm × List (BitVec 8))
  | some (c, p, bs) =>
    if Nat.ble c.toNat a.toNat then
      match rDropN? (a - c).toNat bs with
      | some bs' => some (p, bs')
      | none => (lRegionView a rl).map fun v => (v.1, v.2.1)
    else (lRegionView a rl).map fun v => (v.1, v.2.1)
  | none => (lRegionView a rl).map fun v => (v.1, v.2.1)

theorem lNextView_eq (regions : List Snapshot.Region) (a : BitVec 64) :
    ∀ cur, lNextView (regions.map fun r => (r, r.bytes.length)) a cur = nextView regions a cur
  | some (c, p, bs) => by
    simp only [lNextView, nextView, lRegionView_eq, rDropN?_eq]
    cases dropN? (a - c).toNat bs <;> rfl
  | none => by simp only [lNextView, nextView, lRegionView_eq]

/-! ## Linear Data Relocation Patching -/

/-- Value written by `patchDataRelocId` for `r` in an object at `addr`. -/
def dataRelocVal (L : Lib) (ly : Layout) (addr : BitVec 64) (r : Reloc) : BitVec 64 :=
  match r.kind with
  | .prel32 => targetId L ly r - (addr + BitVec.ofNat 64 r.off)
  | _ => targetId L ly r

/-- `dataRelocVal` reading `ly.addrs` via `rGetD`. -/
noncomputable def dataRelocValR (L : Lib) (ly : Layout) (addr : BitVec 64) (r : Reloc) : BitVec 64 :=
  let t := addSignedAddr (match lookupId r.sym L.symbols with
    | some off => ly.base + BitVec.ofNat 64 off
    | none => rGetD ly.addrs r.sym 0#64) r.addend
  match r.kind with
  | .prel32 => t - (addr + BitVec.ofNat 64 r.off)
  | _ => t

theorem dataRelocValR_eq (L : Lib) (ly : Layout) (addr : BitVec 64) (r : Reloc) :
    dataRelocValR L ly addr r = dataRelocVal L ly addr r := by
  unfold dataRelocValR dataRelocVal targetId resolveId
  simp only [rGetD_eq]
  cases r.kind <;> rfl

/-- The relocations that write bytes are sorted by offset, start at or after `pos`, do not
    overlap and end within `len` bytes. -/
def relocsLinOk (len : Nat) : Nat → List Reloc → Bool
  | _, [] => true
  | pos, r :: rs =>
    cond (Nat.beq (dataRelocWidth r.kind) 0) (relocsLinOk len pos rs)
      (Nat.ble pos r.off && Nat.ble (r.off + dataRelocWidth r.kind) len &&
        relocsLinOk len (r.off + dataRelocWidth r.kind) rs)

/-- One left-to-right pass patching `rs` into `bs`, the bytes from offset `pos` on. -/
noncomputable def patchLin (L : Lib) (ly : Layout) (addr : BitVec 64) :
    Nat → List Reloc → List (BitVec 8) → List (BitVec 8)
  | _, [], bs => bs
  | pos, r :: rs, bs =>
    cond (Nat.beq (dataRelocWidth r.kind) 0) (patchLin L ly addr pos rs bs)
      (rTake (r.off - pos) bs ++ bytesLE (dataRelocWidth r.kind) (dataRelocValR L ly addr r) ++
        patchLin L ly addr (r.off + dataRelocWidth r.kind) rs
          (rDrop (r.off + dataRelocWidth r.kind - pos) bs))

theorem patchDataRelocId_width (L : Lib) (ly : Layout) (addr : BitVec 64) (bytes : List (BitVec 8))
    (r : Reloc) :
    patchDataRelocId L ly addr bytes r =
      if dataRelocWidth r.kind = 0 then bytes
      else bytes.take r.off ++ bytesLE (dataRelocWidth r.kind) (dataRelocVal L ly addr r) ++
        bytes.drop (r.off + dataRelocWidth r.kind) := by
  unfold patchDataRelocId dataRelocWidth dataRelocVal
  cases r.kind <;> simp

theorem length_bytesLE' (n : Nat) (v : BitVec 64) : (bytesLE n v).length = n := by
  simp [bytesLE]

/-- Patching relocations at or after `pos` leaves the first `pos` bytes alone: the fold over the
    whole object is the prefix followed by `patchLin` over the rest. -/
theorem foldl_patchLin (L : Lib) (ly : Layout) (addr : BitVec 64) :
    ∀ (rs : List Reloc) (pos : Nat) (bytes : List (BitVec 8)),
      relocsLinOk bytes.length pos rs = true →
      rs.foldl (patchDataRelocId L ly addr) bytes =
        bytes.take pos ++ patchLin L ly addr pos rs (bytes.drop pos)
  | [], pos, bytes, _ => by simp [patchLin]
  | r :: rs, pos, bytes, h => by
    simp only [relocsLinOk] at h
    simp only [List.foldl_cons, patchLin, patchDataRelocId_width]
    by_cases hw : dataRelocWidth r.kind = 0
    · have hb : Nat.beq (dataRelocWidth r.kind) 0 = true := by rw [hw]; rfl
      simp only [hw, ↓reduceIte] at h ⊢
      exact foldl_patchLin L ly addr rs pos bytes h
    · have hb : Nat.beq (dataRelocWidth r.kind) 0 = false := by
        cases hc : Nat.beq (dataRelocWidth r.kind) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hc) hw
      simp only [hb, Bool.cond_false, Bool.and_eq_true, Nat.ble_eq] at h
      obtain ⟨⟨hpos, hlen⟩, hrest⟩ := h
      simp only [hw, ↓reduceIte, hb, Bool.cond_false, rTake_eq, rDrop_eq, dataRelocValR_eq]
      have hvl := length_bytesLE' (dataRelocWidth r.kind) (dataRelocVal L ly addr r)
      generalize bytesLE (dataRelocWidth r.kind) (dataRelocVal L ly addr r) = v at hvl ⊢
      generalize dataRelocWidth r.kind = w at hvl hlen hrest ⊢
      have hl : (bytes.take r.off ++ v ++ bytes.drop (r.off + w)).length = bytes.length := by
        simp only [List.length_append, List.length_take, List.length_drop, hvl]; omega
      rw [foldl_patchLin L ly addr rs (r.off + w) _ (hl ▸ hrest)]
      have hpl : (bytes.take r.off ++ v).length = r.off + w := by
        simp only [List.length_append, List.length_take, hvl]; omega
      have htk : (bytes.take r.off ++ v ++ bytes.drop (r.off + w)).take (r.off + w) =
          bytes.take r.off ++ v := List.take_left' hpl
      have hdr : (bytes.take r.off ++ v ++ bytes.drop (r.off + w)).drop (r.off + w) =
          bytes.drop (r.off + w) := List.drop_left' hpl
      have hpre : bytes.take r.off = bytes.take pos ++ (bytes.drop pos).take (r.off - pos) := by
        rw [← List.take_add, Nat.add_sub_cancel' hpos]
      have hdd : (bytes.drop pos).drop (r.off + w - pos) = bytes.drop (r.off + w) := by
        rw [List.drop_drop]; congr 1; omega
      rw [htk, hdr, hdd, hpre]
      simp only [List.append_assoc]

/-- `patchedDataId` by one pass when the relocations are sorted and disjoint. -/
noncomputable def patchedDataLin (L : Lib) (ly : Layout) (d : Data) : List (BitVec 8) :=
  cond (relocsLinOk (rLen d.bytes) 0 d.relocs)
    (patchLin L ly (rGetD ly.addrs d.sym 0#64) 0 d.relocs d.bytes ++ List.replicate d.zeroTail 0#8)
    (patchedDataId L ly d)

theorem patchedDataLin_eq (L : Lib) (ly : Layout) (d : Data) :
    patchedDataLin L ly d = patchedDataId L ly d := by
  unfold patchedDataLin
  cases h : relocsLinOk (rLen d.bytes) 0 d.relocs
  · rfl
  · rw [rLen_eq] at h
    simp only [Bool.cond_true, patchedDataId, rGetD_eq, foldl_patchLin L ly _ d.relocs 0 d.bytes h, List.take_zero,
      List.drop_zero, List.nil_append]

noncomputable def lDataWalk (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat)) :
    Option (BitVec 64 × Perm × List (BitVec 8)) → List Data → Bool
  | _, [] => true
  | cur, d :: ds =>
    let a := rGetD ly.addrs d.sym 0#64
    match lNextView rl a cur with
    | some (p, bs) =>
      dataPermOk d.readOnly p && (patchedDataLin L ly d).isPrefixOf bs &&
        lDataWalk L ly rl (some (a, p, bs)) ds
    | none => false

theorem lDataWalk_eq (L : Lib) (ly : Layout) (regions : List Snapshot.Region) :
    ∀ cur ds, lDataWalk L ly (regions.map fun r => (r, r.bytes.length)) cur ds = dataWalk L ly regions cur ds
  | _, [] => rfl
  | cur, d :: ds => by
    simp only [lDataWalk, dataWalk, lNextView_eq, patchedDataLin_eq, rGetD_eq]
    cases nextView regions (ly.addrs.getD d.sym 0#64) cur with
    | none => rfl
    | some v => obtain ⟨p, bs⟩ := v; simp only [lDataWalk_eq]

noncomputable def lMultiTextWalk (ML : MultiLib) (mly : MultiLayout) (rl : List (Snapshot.Region × Nat)) :
    Nat → Option (BitVec 64 × Perm × List (BitVec 8)) → List Block → Bool
  | _, _, [] => true
  | i, cur, b :: rest =>
    let ly := mly.blockLayout i
    match lNextView rl ly.base cur with
    | some (p, bs) =>
      (p == Perm.rx) && walk (ML.blockLib b) ly 0 false b.relocs b.code bs &&
        lMultiTextWalk ML mly rl (i + 1) (some (ly.base, p, bs)) rest
    | none => false

theorem lMultiTextWalk_eq (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region) :
    ∀ i cur blks, lMultiTextWalk ML mly (regions.map fun r => (r, r.bytes.length)) i cur blks =
      multiTextWalk ML mly regions i cur blks
  | _, _, [] => rfl
  | i, cur, b :: rest => by
    simp only [lMultiTextWalk, multiTextWalk, lNextView_eq]
    cases nextView regions (mly.blockLayout i).base cur with
    | none => rfl
    | some v => obtain ⟨p, bs⟩ := v; simp only [lMultiTextWalk_eq]

noncomputable def lCheckMultiDisjoint (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (rl : List (Snapshot.Region × Nat)) (enc : EncSymTable (BitVec 64)) : Bool :=
  (namesNodup nameChars && ML.idsOk && blockSymsMatchB ML mly &&
    multiPlaceableB ML mly &&
    lMultiTextWalk ML mly rl 0 none ML.blocks &&
    lDataWalk (ML.blockLib { code := [] }) mly.dataLayout rl none ML.data &&
    multiExportsOk ML mly nameChars enc) && multiDataDisjointB ML mly

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.zip_cons_cons, zip_map_self f l]

theorem lCheckMultiDisjoint_spec {ML : MultiLib} {mly : MultiLayout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)} {lens : List Nat}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hlens : img.segments.map (fun r => rLen r.bytes) = lens)
    (h : lCheckMultiDisjoint ML mly nameChars (img.segments.zip lens) (prepareCharAssocVal symChars) = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  refine checkMultiDisjoint_spec hnames hsyms ?_
  subst hlens
  simp only [rLen_eq, zip_map_self] at h
  simpa only [lCheckMultiDisjoint, checkMultiDisjoint, checkMulti, lMultiTextWalk_eq, lDataWalk_eq] using h


/-- The checks of `checkMultiDisjoint` that do not read the ELF segments. -/
def restOk (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (enc : EncSymTable (BitVec 64)) : Bool :=
  namesNodup nameChars && ML.idsOk && blockSymsMatchB ML mly && multiPlaceableB ML mly &&
    multiExportsOk ML mly nameChars enc && multiDataDisjointB ML mly

/-- `checkMultiDisjoint_spec` from separately proved segment lengths, text walk, data walk and
    segment-free checks. -/
theorem checkMultiDisjoint_spec_split {ML : MultiLib} {mly : MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    {lens : List Nat}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hlens : img.segments.map (fun r => rLen r.bytes) = lens)
    (htext : lMultiTextWalk ML mly (img.segments.zip lens) 0 none ML.blocks = true)
    (hdata : lDataWalk (ML.blockLib { code := [] }) mly.dataLayout (img.segments.zip lens) none
      ML.data = true)
    (hrest : restOk ML mly nameChars (prepareCharAssocVal symChars) = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  refine lCheckMultiDisjoint_spec hnames hsyms hlens ?_
  simp only [restOk, Bool.and_eq_true] at hrest
  simp only [lCheckMultiDisjoint, htext, hdata, hrest, Bool.and_self]

/-! ## Per-Conjunct Segment-Free Checks -/

/-- Every block satisfies `textPlaceableB` at its layout (first conjunct of `multiPlaceableB`). -/
def textPlaceableAllB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  allIdx (fun i b => textPlaceableB (ML.blockLib b) (mly.blockLayout i)) 0 ML.blocks

/-- The blocks occupy disjoint address ranges (second conjunct of `multiPlaceableB`). -/
def blocksDisjointB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  sortedRangesB (·.code.length) 0 mly.bases ML.blocks ||
    allIdx (fun i b1 =>
      allIdx (fun j b2 =>
        !Nat.blt i j ||
          checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
            (mly.bases.getD j 0#64).toNat b2.code.length)
        0 ML.blocks) 0 ML.blocks

/-- No symbol is defined by two blocks (third conjunct of `multiPlaceableB`). -/
def blockSymsNodupB (ML : MultiLib) : Bool :=
  natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1))

/-- The data objects satisfy `dataPlaceableB` (fourth conjunct of `multiPlaceableB`). -/
def dataPlaceableAllB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  dataPlaceableB (ML.blockLib { code := [] }) mly.dataLayout

/-- No data object's symbol is defined by a block (fifth conjunct of `multiPlaceableB`). -/
def dataNotBlockB (ML : MultiLib) : Bool :=
  ML.data.all fun d => (lookupBlockSymId d.sym ML.blocks).isNone

theorem multiPlaceableB_of {ML : MultiLib} {mly : MultiLayout}
    (htext : textPlaceableAllB ML mly = true) (hdisj : blocksDisjointB ML mly = true)
    (hsyms : blockSymsNodupB ML = true) (hdata : dataPlaceableAllB ML mly = true)
    (hnone : dataNotBlockB ML = true) : multiPlaceableB ML mly = true := by
  simp only [textPlaceableAllB, blocksDisjointB, blockSymsNodupB, dataPlaceableAllB,
    dataNotBlockB] at htext hdisj hsyms hdata hnone
  simp only [multiPlaceableB, htext, hdisj, hsyms, hdata, hnone, Bool.and_self]

/-! ## Linear Data-Disjointness Scan -/

/-- `max hi e` via `Nat.ble` and `cond`. -/
def bumpHi (hi e : Nat) : Nat := cond (Nat.ble e hi) hi e

theorem le_bumpHi_left (hi e : Nat) : hi ≤ bumpHi hi e := by
  unfold bumpHi; cases h : Nat.ble e hi
  · have : ¬ e ≤ hi := fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; cases h
    show hi ≤ e; omega
  · exact Nat.le_refl _

theorem le_bumpHi_right (hi e : Nat) : e ≤ bumpHi hi e := by
  unfold bumpHi; cases h : Nat.ble e hi
  · exact Nat.le_refl _
  · exact Nat.le_of_ble_eq_true h

/-- One pass over `(readOnly, addr, len)` entries: every entry fits below `2 ^ 64`, starts at or
    after `hiW`, and, if writable, at or after `hiAll`. -/
def dataScanB (hiAll hiW : Nat) : List (Bool × BitVec 64 × Nat) → Bool
  | [] => true
  | (ro, a, n) :: rest =>
    Nat.ble (a.toNat + n) 18446744073709551616 && Nat.ble hiW a.toNat &&
      (ro || Nat.ble hiAll a.toNat) &&
      dataScanB (bumpHi hiAll (a.toNat + n)) (cond ro hiW (bumpHi hiW (a.toNat + n))) rest

/-- Every entry after a successful scan starts at or after `hiW`, and a writable one at or after
    `hiAll`. -/
theorem dataScanB_lo : ∀ {hiAll hiW : Nat} {ds : List (Bool × BitVec 64 × Nat)},
    dataScanB hiAll hiW ds = true →
    ∀ x ∈ ds, hiW ≤ x.2.1.toNat ∧ (x.1 = false → hiAll ≤ x.2.1.toNat)
  | _, _, [], _, _, hx => nomatch hx
  | hiAll, hiW, (ro, a, n) :: rest, h, x, hx => by
    simp only [dataScanB, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨_, hw⟩, hro⟩, hrest⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨Nat.le_of_ble_eq_true hw, fun hf => ?_⟩
      cases hf
      rcases hro with hro | hro
      · cases hro
      · exact Nat.le_of_ble_eq_true hro
    · have ih := dataScanB_lo hrest x hx
      refine ⟨Nat.le_trans ?_ ih.1, fun hf => Nat.le_trans (le_bumpHi_left _ _) (ih.2 hf)⟩
      cases ro
      · exact le_bumpHi_left _ _
      · exact Nat.le_refl _

/-- A successful scan implies the pairwise check, whatever the order of the entries. -/
theorem dataEntriesDisjointB_of_scan : ∀ {hiAll hiW : Nat} {ds : List (Bool × BitVec 64 × Nat)},
    dataScanB hiAll hiW ds = true → dataEntriesDisjointB ds = true
  | _, _, [], _ => rfl
  | hiAll, hiW, (ro, a, n) :: rest, h => by
    have h' := h
    simp only [dataScanB, Bool.and_eq_true] at h'
    obtain ⟨⟨⟨hb, _⟩, _⟩, hrest⟩ := h'
    have hlo := dataScanB_lo hrest
    simp only [dataEntriesDisjointB, hb, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun y hy => ?_, dataEntriesDisjointB_of_scan hrest⟩
    obtain ⟨ro2, a2, n2⟩ := y
    have ⟨hyw, hyall⟩ := hlo _ hy
    have hdisj : ∀ lo, lo ≤ a2.toNat → a.toNat + n ≤ lo →
        ((ro && ro2) || checkRangesDisjoint a.toNat n a2.toNat n2) = true := fun lo h1 h2 => by
      unfold checkRangesDisjoint
      rw [Nat.ble_eq_true_of_le (Nat.le_trans h2 h1), Bool.true_or, Bool.or_true]
    cases ro with
    | false => exact hdisj _ hyw (le_bumpHi_right _ _)
    | true =>
      cases ro2 with
      | false => exact hdisj _ (hyall rfl) (le_bumpHi_right _ _)
      | true => rfl

/-- `multiDataDisjointB`'s entries with `rLen` lengths. -/
noncomputable def dataEntriesL (ML : MultiLib) (mly : MultiLayout) : List (Bool × BitVec 64 × Nat) :=
  ML.data.map fun d => (d.readOnly, mly.addrs.getD d.sym 0#64, rLen d.bytes + d.zeroTail)

/-- `multiDataDisjointB` by one address-ordered pass, falling back to the pairwise check. -/
noncomputable def dataDisjointFastB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  dataScanB 0 0 (dataEntriesL ML mly) || multiDataDisjointB ML mly

theorem multiDataDisjointB_of_fast {ML : MultiLib} {mly : MultiLayout}
    (h : dataDisjointFastB ML mly = true) : multiDataDisjointB ML mly = true := by
  simp only [dataDisjointFastB, Bool.or_eq_true] at h
  rcases h with h | h
  · have := dataEntriesDisjointB_of_scan h
    simpa only [multiDataDisjointB, dataEntriesL, rLen_eq] using this
  · exact h

/-- `dataDisjointFastB` decides exactly `multiDataDisjointB`. -/
theorem dataDisjointFastB_eq (ML : MultiLib) (mly : MultiLayout) :
    dataDisjointFastB ML mly = multiDataDisjointB ML mly := by
  cases h : multiDataDisjointB ML mly
  · cases hf : dataDisjointFastB ML mly
    · rfl
    · simp [multiDataDisjointB_of_fast hf] at h
  · simp only [dataDisjointFastB, h, Bool.or_true]

/-! ## Chunked Text and Data Walks -/

theorem mem_drop_of_le {α : Type} {l : List α} {a : α} {t k : Nat} (h : t ≤ k)
    (ha : a ∈ l.drop k) : a ∈ l.drop t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have : l.drop (t + m) = (l.drop t).drop m := by rw [List.drop_drop, Nat.add_comm]
  rw [this] at ha
  exact List.mem_of_mem_drop ha

/-- Text walk over blocks `[s, t)` of `ML` from a fresh view. -/
noncomputable def lTextChunk (ML : MultiLib) (mly : MultiLayout) (rl : List (Snapshot.Region × Nat))
    (s t : Nat) : Bool :=
  lMultiTextWalk ML mly rl s none (rTake (t - s) (rDrop s ML.blocks))

/-- Text walk over blocks `[s, end)` of `ML` from a fresh view. -/
noncomputable def lTextTail (ML : MultiLib) (mly : MultiLayout) (rl : List (Snapshot.Region × Nat))
    (s : Nat) : Bool :=
  lMultiTextWalk ML mly rl s none (rDrop s ML.blocks)

/-- All text walk chunks `[s, t_1), [t_1, t_2), ..., [t_k, end)` succeed. -/
noncomputable def lTextChunks (ML : MultiLib) (mly : MultiLayout)
    (rl : List (Snapshot.Region × Nat)) : Nat → List Nat → Prop
  | s, [] => lTextTail ML mly rl s = true
  | s, t :: ts => lTextChunk ML mly rl s t = true ∧ lTextChunks ML mly rl t ts

theorem lTextChunks_nil {ML : MultiLib} {mly : MultiLayout} {rl : List (Snapshot.Region × Nat)}
    {s : Nat} (h : lTextTail ML mly rl s = true) : lTextChunks ML mly rl s [] := h

theorem lTextChunks_cons {ML : MultiLib} {mly : MultiLayout} {rl : List (Snapshot.Region × Nat)}
    {s t : Nat} {ts : List Nat} (h : lTextChunk ML mly rl s t = true)
    (hr : lTextChunks ML mly rl t ts) : lTextChunks ML mly rl s (t :: ts) := ⟨h, hr⟩

/-- A fresh-view text walk from block `s` over a prefix `blks` of `ML.blocks.drop s` proves
    `BlockTextOk` for blocks `[s, s + blks.length)`. -/
theorem blockTextOk_of_walkFrom {ML : MultiLib} {mly : MultiLayout} (hnd : ML.names.Nodup)
    (hids : ML.idsOk = true) (hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true)
    {regions : List Snapshot.Region} {s : Nat} {blks : List Block}
    (hpre : blks <+: ML.blocks.drop s) (h : multiTextWalk ML mly regions s none blks = true)
    (i : Nat) (hi : i < ML.blocks.length) (hs : s ≤ i) (ht : i < s + blks.length) :
    BlockTextOk ML mly regions i ML.blocks[i] := by
  obtain ⟨j, rfl⟩ : ∃ j, i = s + j := ⟨i - s, by omega⟩
  have hj : j < blks.length := by omega
  have heq : blks[j] = ML.blocks[s + j] := by rw [hpre.getElem hj, List.getElem_drop]
  have hmem : ∀ b ∈ blks, b ∈ ML.blocks := fun b hb => List.mem_of_mem_drop (hpre.subset hb)
  have := blockTextOk_of_walk (cur := none) hnd hids hmem (fun b hb => hwf b (hmem b hb))
    (fun _ _ _ hc => nomatch hc) h j hj
  rw [heq] at this
  exact this

theorem blockTextOk_of_chunks {ML : MultiLib} {mly : MultiLayout} (hnd : ML.names.Nodup)
    (hids : ML.idsOk = true) (hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true)
    {regions : List Snapshot.Region} :
    ∀ (s : Nat) (ts : List Nat), lTextChunks ML mly (regions.map fun r => (r, r.bytes.length)) s ts →
      ∀ (i : Nat) (hi : i < ML.blocks.length), s ≤ i → BlockTextOk ML mly regions i ML.blocks[i]
  | s, [], h, i, hi, hs => by
    simp only [lTextChunks, lTextTail, lMultiTextWalk_eq, rDrop_eq] at h
    exact blockTextOk_of_walkFrom hnd hids hwf (List.prefix_refl _) h i hi hs
      (by simp only [List.length_drop]; omega)
  | s, t :: ts, h, i, hi, hs => by
    simp only [lTextChunks, lTextChunk, lMultiTextWalk_eq, rDrop_eq, rTake_eq] at h
    by_cases hit : i < t
    · exact blockTextOk_of_walkFrom hnd hids hwf (List.take_prefix _ _) h.1 i hi hs
        (by simp only [List.length_take, List.length_drop]; omega)
    · exact blockTextOk_of_chunks hnd hids hwf t ts h.2 i hi (by omega)

/-- Chunked text walks from block `0` prove `MultiTextOk`. -/
theorem multiTextOk_of_chunks {ML : MultiLib} {mly : MultiLayout} (hnd : ML.names.Nodup)
    (hids : ML.idsOk = true) (hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true)
    {regions : List Snapshot.Region} {ts : List Nat}
    (h : lTextChunks ML mly (regions.map fun r => (r, r.bytes.length)) 0 ts) :
    MultiTextOk ML mly regions :=
  fun i hi => blockTextOk_of_chunks hnd hids hwf 0 ts h i hi (Nat.zero_le _)

/-- Data walk over objects `[s, t)` of `ML` from a fresh view. -/
noncomputable def lDataChunk (ML : MultiLib) (mly : MultiLayout) (rl : List (Snapshot.Region × Nat))
    (s t : Nat) : Bool :=
  lDataWalk (ML.blockLib { code := [] }) mly.dataLayout rl none (rTake (t - s) (rDrop s ML.data))

/-- Data walk over objects `[s, end)` of `ML` from a fresh view. -/
noncomputable def lDataTail (ML : MultiLib) (mly : MultiLayout) (rl : List (Snapshot.Region × Nat))
    (s : Nat) : Bool :=
  lDataWalk (ML.blockLib { code := [] }) mly.dataLayout rl none (rDrop s ML.data)

/-- All data walk chunks `[s, t_1), [t_1, t_2), ..., [t_k, end)` succeed. -/
noncomputable def lDataChunks (ML : MultiLib) (mly : MultiLayout)
    (rl : List (Snapshot.Region × Nat)) : Nat → List Nat → Prop
  | s, [] => lDataTail ML mly rl s = true
  | s, t :: ts => lDataChunk ML mly rl s t = true ∧ lDataChunks ML mly rl t ts

theorem lDataChunks_nil {ML : MultiLib} {mly : MultiLayout} {rl : List (Snapshot.Region × Nat)}
    {s : Nat} (h : lDataTail ML mly rl s = true) : lDataChunks ML mly rl s [] := h

theorem lDataChunks_cons {ML : MultiLib} {mly : MultiLayout} {rl : List (Snapshot.Region × Nat)}
    {s t : Nat} {ts : List Nat} (h : lDataChunk ML mly rl s t = true)
    (hr : lDataChunks ML mly rl t ts) : lDataChunks ML mly rl s (t :: ts) := ⟨h, hr⟩

theorem dataObjOk_of_chunks {ML : MultiLib} {mly : MultiLayout} {regions : List Snapshot.Region} :
    ∀ (s : Nat) (ts : List Nat), lDataChunks ML mly (regions.map fun r => (r, r.bytes.length)) s ts →
      ∀ d ∈ ML.data.drop s, DataObjOk ML mly regions d
  | s, [], h, d, hd => by
    simp only [lDataChunks, lDataTail, lDataWalk_eq, rDrop_eq] at h
    exact dataWalk_sound none _ (fun _ _ _ hc => nomatch hc) h d hd
  | s, t :: ts, h, d, hd => by
    simp only [lDataChunks, lDataChunk, lDataWalk_eq, rDrop_eq, rTake_eq] at h
    rw [← List.take_append_drop (t - s) (ML.data.drop s), List.mem_append] at hd
    rcases hd with hd | hd
    · exact dataWalk_sound none _ (fun _ _ _ hc => nomatch hc) h.1 d hd
    · refine dataObjOk_of_chunks t ts h.2 d (mem_drop_of_le (k := s + (t - s)) (by omega) ?_)
      rwa [List.drop_drop] at hd

/-- Chunked data walks from object `0` prove `MultiDataOk`. -/
theorem multiDataOk_of_chunks {ML : MultiLib} {mly : MultiLayout} {regions : List Snapshot.Region}
    {ts : List Nat} (h : lDataChunks ML mly (regions.map fun r => (r, r.bytes.length)) 0 ts) :
    MultiDataOk ML mly regions :=
  fun d hd => dataObjOk_of_chunks 0 ts h d (by rw [List.drop_zero]; exact hd)

/-! ## Chunked Per-Index Checks and Library Equality -/

/-- `allIdx f` over items `[s, t)` of `l`. -/
noncomputable def allIdxChunk {α : Type} (f : Nat → α → Bool) (l : List α) (s t : Nat) : Bool :=
  allIdx f s (rTake (t - s) (rDrop s l))

/-- `allIdx f` over items `[s, end)` of `l`. -/
noncomputable def allIdxTail {α : Type} (f : Nat → α → Bool) (l : List α) (s : Nat) : Bool :=
  allIdx f s (rDrop s l)

/-- All chunks `[s, t_1), [t_1, t_2), ..., [t_k, end)` of `allIdx f` over `l` succeed. -/
noncomputable def AllIdxChunks {α : Type} (f : Nat → α → Bool) (l : List α) : Nat → List Nat → Prop
  | s, [] => allIdxTail f l s = true
  | s, t :: ts => allIdxChunk f l s t = true ∧ AllIdxChunks f l t ts

theorem allIdxChunks_nil {α : Type} {f : Nat → α → Bool} {l : List α} {s : Nat}
    (h : allIdxTail f l s = true) : AllIdxChunks f l s [] := h

theorem allIdxChunks_cons {α : Type} {f : Nat → α → Bool} {l : List α} {s t : Nat} {ts : List Nat}
    (h : allIdxChunk f l s t = true) (hr : AllIdxChunks f l t ts) : AllIdxChunks f l s (t :: ts) :=
  ⟨h, hr⟩

theorem allIdx_of_forall {α : Type} {f : Nat → α → Bool} :
    ∀ {k : Nat} {xs : List α}, (∀ (i : Nat) (hi : i < xs.length), f (k + i) xs[i] = true) →
      allIdx f k xs = true
  | _, [], _ => rfl
  | k, x :: xs, h => by
    simp only [allIdx, Bool.and_eq_true]
    refine ⟨h 0 (by simp), allIdx_of_forall fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    rwa [show k + (i + 1) = (k + 1) + i by omega] at this

theorem allIdxChunks_spec {α : Type} {f : Nat → α → Bool} {l : List α} :
    ∀ (s : Nat) (ts : List Nat), AllIdxChunks f l s ts →
      ∀ (i : Nat) (hi : i < l.length), s ≤ i → f i l[i] = true
  | s, [], h, i, hi, hs => by
    simp only [AllIdxChunks, allIdxTail, rDrop_eq] at h
    have := allIdx_spec h (i - s) (by simp only [List.length_drop]; omega)
    simp only [List.getElem_drop] at this
    simpa only [Nat.add_sub_cancel' hs] using this
  | s, t :: ts, h, i, hi, hs => by
    simp only [AllIdxChunks, allIdxChunk, rDrop_eq, rTake_eq] at h
    by_cases hit : i < t
    · have := allIdx_spec h.1 (i - s) (by simp only [List.length_take, List.length_drop]; omega)
      simp only [List.getElem_take, List.getElem_drop] at this
      simpa only [Nat.add_sub_cancel' hs] using this
    · exact allIdxChunks_spec t ts h.2 i hi (by omega)

/-- Chunked `allIdx f` checks from item `0` prove `allIdx f 0 l`. -/
theorem allIdx_of_chunks {α : Type} {f : Nat → α → Bool} {l : List α} {ts : List Nat}
    (h : AllIdxChunks f l 0 ts) : allIdx f 0 l = true :=
  allIdx_of_forall fun i hi => by
    simpa using allIdxChunks_spec 0 ts h i hi (Nat.zero_le _)

/-- The per-block test of `blockSymsMatchB`, with the kernel-cheap `rGetD` lookups. -/
noncomputable def blockSymsMatchAt (mly : MultiLayout) (i : Nat) (b : Block) : Bool :=
  b.symbols.all fun s => rGetD mly.addrs s.1 0#64 == rGetD mly.bases i 0#64 + BitVec.ofNat 64 s.2

theorem blockSymsMatchB_of_chunks {ML : MultiLib} {mly : MultiLayout} {ts : List Nat}
    (h : AllIdxChunks (blockSymsMatchAt mly) ML.blocks 0 ts) : blockSymsMatchB ML mly = true := by
  have hf : blockSymsMatchAt mly = fun i (b : Block) => b.symbols.all fun s =>
      mly.addrs.getD s.1 0#64 == mly.bases.getD i 0#64 + BitVec.ofNat 64 s.2 := by
    funext i b; simp only [blockSymsMatchAt, rGetD_eq]
  rw [hf] at h
  exact allIdx_of_chunks h

/-- The per-block test of `textPlaceableAllB`. -/
def textPlaceableAt (ML : MultiLib) (mly : MultiLayout) (i : Nat) (b : Block) : Bool :=
  textPlaceableB (ML.blockLib b) (mly.blockLayout i)

theorem textPlaceableAllB_of_chunks {ML : MultiLib} {mly : MultiLayout} {ts : List Nat}
    (h : AllIdxChunks (textPlaceableAt ML mly) ML.blocks 0 ts) : textPlaceableAllB ML mly = true :=
  allIdx_of_chunks h

/-- The per-object test of `dataNotBlockB` (the index is unused). -/
def dataNotBlockAt (ML : MultiLib) (_ : Nat) (d : Data) : Bool :=
  (lookupBlockSymId d.sym ML.blocks).isNone

theorem all_eq_allIdx {α : Type} (p : α → Bool) :
    ∀ (k : Nat) (xs : List α), xs.all p = allIdx (fun _ x => p x) k xs
  | _, [] => rfl
  | k, x :: xs => by simp only [List.all_cons, allIdx, all_eq_allIdx p (k + 1) xs]

theorem dataNotBlockB_of_chunks {ML : MultiLib} {ts : List Nat}
    (h : AllIdxChunks (dataNotBlockAt ML) ML.data 0 ts) : dataNotBlockB ML = true := by
  rw [dataNotBlockB, all_eq_allIdx _ 0]
  exact allIdx_of_chunks h

/-- `Reloc.toEntry` with the kernel-cheap `rGetD` lookup. -/
noncomputable def relocEntryR (names : List String) (r : Reloc) : RelocEntry :=
  { off := r.off, kind := r.kind, sym := rGetD names r.sym "", addend := r.addend,
    localSym := r.localSym }

/-- `Block.toCodeBlock` with the kernel-cheap `rGetD` lookups. -/
noncomputable def codeBlockR (names : List String) (b : Block) : CodeBlock :=
  { code := b.code
    align := b.align
    symbols := b.symbols.map fun s => (rGetD names s.1 "", s.2)
    relocs := b.relocs.map (relocEntryR names)
    externs := b.externs.map fun e => rGetD names e ""
    weakRefs := b.weakRefs.map fun e => rGetD names e "" }

/-- `Data.toInfo` with the kernel-cheap `rGetD` lookups. -/
noncomputable def dataInfoR (names : List String) (d : Data) : SymDataInfo :=
  { sym := rGetD names d.sym "", align := d.align, readOnly := d.readOnly, bytes := d.bytes,
    zeroTail := d.zeroTail, relocs := d.relocs.map (relocEntryR names) }

/-- `MultiLib.toMultiPlacedLib` using `rGetD` for `O(1)`-overhead name lookups in the kernel. -/
noncomputable def toMultiPlacedLibR (ML : MultiLib) : MultiPlacedLib :=
  { name := ML.name
    blocks := ML.blocks.map (codeBlockR ML.names)
    data := ML.data.map (dataInfoR ML.names)
    exports := ML.exports.map fun e => rGetD ML.names e ""
    exportSyms := ML.exportSyms.map fun p => (rGetD ML.names p.1 "", rGetD ML.names p.2 "") }

theorem relocEntryR_eq (names : List String) : relocEntryR names = Reloc.toEntry names := by
  funext r; simp only [relocEntryR, Reloc.toEntry, rGetD_eq]

theorem toMultiPlacedLibR_eq (ML : MultiLib) : toMultiPlacedLibR ML = ML.toMultiPlacedLib := by
  have hb : codeBlockR ML.names = Block.toCodeBlock ML.names := by
    funext b; simp only [codeBlockR, Block.toCodeBlock, rGetD_eq, relocEntryR_eq]
  have hd : dataInfoR ML.names = Data.toInfo ML.names := by
    funext d; simp only [dataInfoR, Data.toInfo, rGetD_eq, relocEntryR_eq]
  simp only [toMultiPlacedLibR, MultiLib.toMultiPlacedLib, hb, hd, rGetD_eq]

/-- `lib = ML.toMultiPlacedLib` from the kernel-cheap `lib = toMultiPlacedLibR ML`. -/
theorem toMultiPlacedLib_of_r {lib : MultiPlacedLib} {ML : MultiLib}
    (h : lib = toMultiPlacedLibR ML) : lib = ML.toMultiPlacedLib :=
  h.trans (toMultiPlacedLibR_eq ML)

/-- `checkMultiDisjoint_spec`'s conclusion from the segment lengths, the text and data walks in
    chunks (`lTextChunks` / `lDataChunks`), and one fact per segment-free check
    (`multiPlaceableB` per conjunct, `multiPlaceableB_of`; `multiDataDisjointB` by
    `dataDisjointFastB`, `multiDataDisjointB_of_fast`). -/
theorem checkMultiDisjoint_spec_chunks {ML : MultiLib} {mly : MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    {lens textBounds dataBounds : List Nat}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hlens : img.segments.map (fun r => rLen r.bytes) = lens)
    (htext : lTextChunks ML mly (img.segments.zip lens) 0 textBounds)
    (hdata : lDataChunks ML mly (img.segments.zip lens) 0 dataBounds)
    (hnodup : namesNodup nameChars = true) (hids : ML.idsOk = true)
    (hmatch : blockSymsMatchB ML mly = true)
    (hptext : textPlaceableAllB ML mly = true) (hpdisj : blocksDisjointB ML mly = true)
    (hpsyms : blockSymsNodupB ML = true) (hpdata : dataPlaceableAllB ML mly = true)
    (hpnone : dataNotBlockB ML = true)
    (hexports : multiExportsOk ML mly nameChars (prepareCharAssocVal symChars) = true)
    (hddisj : dataDisjointFastB ML mly = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  have hmp := multiPlaceableB_of hptext hpdisj hpsyms hpdata hpnone
  have hnd := nodup_of_namesNodup hnames hnodup
  subst hlens
  simp only [rLen_eq, zip_map_self] at htext hdata
  have ⟨hpl, hin⟩ := checkMulti_spec_of_ok hnames hsyms hnodup hids hmatch hmp
    (multiTextOk_of_chunks hnd hids (relocsWf_of_multiPlaceableB hmp) htext)
    (multiDataOk_of_chunks hdata) hexports
  exact ⟨hpl, hin,
    dataDisjoint_of_multiDataDisjointB hnd hids hmatch hpl (multiDataDisjointB_of_fast hddisj)⟩

end ProofLib.Placed.Split

end

/-! ## `seg_lens% img` -/

public meta section

namespace ProofLib.Placed.Split

open Lean Elab Term Meta Arm64 Arm64.Process

/-- Unfold the head constant of `e` until it is not a constant with a value. -/
partial def unfoldConsts (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  match e with
  | .const n _ =>
    match (← getEnv).find? n with
    | some ci => match ci.value? (allowOpaque := true) with
      | some v => unfoldConsts v
      | none => pure e
    | none => pure e
  | .mdata _ b => unfoldConsts b
  | _ => pure e

/-- Number of `List.cons` cells of the list literal `e` (a constant is unfolded). -/
partial def listLitLen (e : Expr) (acc : Nat := 0) : MetaM Nat := do
  let e ← unfoldConsts e
  match e.getAppFnArgs with
  | (``List.cons, #[_, _, t]) => listLitLen t (acc + 1)
  | (``List.nil, #[_]) => pure acc
  | (``List.flatten, #[_, ls]) => do
    let mut n := acc
    for l in ← listLitElems ls do n ← listLitLen l n
    pure n
  | _ => throwError "seg_lens%: not a list literal: {e}"
where
  listLitElems (e : Expr) : MetaM (List Expr) := do
    let e ← unfoldConsts e
    match e.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => return h :: (← listLitElems t)
    | (``List.nil, #[_]) => return []
    | _ => throwError "seg_lens%: not a list literal: {e}"

/-- Elaborates `seg_lens% img` to the `List Nat` literal of byte lengths of `img.segments` for an
    `ElfImage.mk` constant `img`. -/
elab "seg_lens% " c:ident : term => do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let img ← unfoldConsts (mkConst cn)
  let segs ← match img.getAppFnArgs with
    | (``ElfImage.mk, #[_, _, _, _, segs, _, _]) => pure segs
    | _ => throwError "seg_lens%: {cn} does not unfold to an `ElfImage.mk` literal"
  let mut lens : Array Expr := #[]
  for r in ← listLitLen.listLitElems segs do
    let r ← unfoldConsts r
    match r.getAppFnArgs with
    | (``Snapshot.Region.mk, #[_, _, bytes, _]) => lens := lens.push (mkNatLit (← listLitLen bytes))
    | _ => throwError "seg_lens%: segment is not a `Snapshot.Region.mk` literal"
  return lens.toList.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Nat) x acc)
    (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat))

end ProofLib.Placed.Split

end
