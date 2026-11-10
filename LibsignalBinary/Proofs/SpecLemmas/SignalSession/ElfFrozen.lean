/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElf
public import LibsignalBinary.Proofs.RoDataReloc

@[expose] public section

set_option autoImplicit false

/-!
# `Obj.Image.FrozenLoaded` from ELF `PT_LOAD` Segment Slices

**Checked by Lean.** Establishes `Obj.Image.FrozenLoaded` (code `r-x`, `.rodata` `r--`, GOT `r--`)
after `ElfImage.loadState` from `SegSlice` containment hypotheses, both via explicit relocation-fold
outputs (`frozenLoaded_of_loads`) and fold-free `Piece` decompositions (`frozenLoaded_of_loads_pieces`)
that check `.rodata` runs linearly against `li.relocs`.
-/

namespace CryptoVerification.SignalSession.ElfFrozen

open Arm64 Arm64.Process ProofLib CryptoVerification.SignalSession.MuslElf
  CryptoVerification.SignalSession.InitStack

/-- A sub-range `[off', off' + n)` of a `SegSlice` is a `SegSlice` with the same permission. -/
theorem SegSlice.sub {elf : ElfImage} {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (h : SegSlice elf a bs p) (off' n : Nat) (hn : off' + n ≤ bs.length) :
    SegSlice elf (a + BitVec.ofNat 64 off') ((bs.drop off').take n) p := by
  obtain ⟨k, hk, off, hp, rfl, hbs⟩ := h
  refine ⟨k, hk, off + off', hp, ?_, ?_⟩
  · rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · have hlen : ((bs.drop off').take n).length = n := by
      rw [List.length_take, List.length_drop]; omega
    rw [hlen]
    conv => rhs; rw [← hbs]
    rw [List.drop_take, List.drop_drop, List.take_take]
    congr 1
    omega

/-- `CodeLoaded` from a single `r-x` `SegSlice` mapping `img.code` at `img.base`. -/
theorem codeLoaded_of_segSlice {elf : ElfImage} {img : Obj.Image}
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hal : img.base.toNat % 4 = 0) (hcode : SegSlice elf img.base img.code Perm.rx)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    (Program.ofImage img).CodeLoaded s0.mem := by
  have hh := hcode.holdsBytes hwf hbrk hload
  have hsb := stackBase_eq
  refine Program.CodeLoaded.intro hal ?_ (fun i hi => hh i hi)
  show img.base.toNat + img.code.length ≤ 2 ^ 64
  cases hc : img.code with
  | nil => have := img.base.isLt; simp only [List.length_nil]; omega
  | cons b bs =>
    have := hcode.bound (by rw [hc]; simp) hwf hbrk
    rw [hc] at this
    omega

theorem sub_offsets (b : BitVec 64) (i o : Nat) :
    (b + BitVec.ofNat 64 i) - (b + BitVec.ofNat 64 o) = BitVec.ofNat 64 i - BitVec.ofNat 64 o := by
  bv_omega

theorem toNat_sub_offsets (b : BitVec 64) (i o L : Nat) (hL : L < 2 ^ 64) (hi : i < L)
    (ho : o < L) :
    ((b + BitVec.ofNat 64 i) - (b + BitVec.ofNat 64 o)).toNat = (2 ^ 64 - o + i) % 2 ^ 64 := by
  rw [sub_offsets, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : o < 2 ^ 64)]

theorem offset_in_range (i o n L : Nat) (hL : L < 2 ^ 64) (hi : i < L) (hon : o + n ≤ L)
    (h : (2 ^ 64 - o + i) % 2 ^ 64 < n) : o ≤ i ∧ i - o < n := by
  omega

/-- `RoDataLoaded` from `r--` `SegSlice`s over `(off, len)` runs of `img.data` covering every
`.rodata` range. -/
theorem roDataLoaded_of_runs {elf : ElfImage} {img : Obj.Image} (runs : List (Nat × Nat))
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hdlen : img.data.length < 2 ^ 64)
    (hruns : ∀ r ∈ runs, r.1 + r.2 ≤ img.data.length ∧
      SegSlice elf (img.dataAddr + BitVec.ofNat 64 r.1) ((img.data.drop r.1).take r.2) Perm.ro)
    (hcover : ∀ q ∈ img.roData, ∃ o, q.1 = img.dataAddr + BitVec.ofNat 64 o ∧
      ∃ r ∈ runs, r.1 ≤ o ∧ o + q.2 ≤ r.1 + r.2)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    img.RoDataLoaded s0.mem := by
  intro i hi
  dsimp only
  intro hro
  simp only [Obj.Image.isRoData, List.any_eq_true, decide_eq_true_eq] at hro
  obtain ⟨q, hq, hlt⟩ := hro
  obtain ⟨o, hqo, r, hr, hro, hor⟩ := hcover q hq
  obtain ⟨hrlen, hslice⟩ := hruns r hr
  have hoL : o + q.2 ≤ img.data.length := by omega
  rw [hqo, toNat_sub_offsets img.dataAddr i o img.data.length hdlen hi (by
    cases hq2 : q.2 with
    | zero => rw [hq2] at hlt; omega
    | succ _ => omega)] at hlt
  obtain ⟨hoi, hio⟩ := offset_in_range i o q.2 img.data.length hdlen hi hoL hlt
  have hj : i - r.1 < ((img.data.drop r.1).take r.2).length := by
    rw [List.length_take, List.length_drop]; omega
  have hh := hslice.holdsBytes hwf hbrk hload (i - r.1) hj
  have ha : img.dataAddr + BitVec.ofNat 64 r.1 + BitVec.ofNat 64 (i - r.1) =
      img.dataAddr + BitVec.ofNat 64 i := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
    omega
  rw [ha] at hh
  refine ⟨?_, hh.2⟩
  rw [hh.1, List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- Combines `r-x` code, `r--` `.rodata` runs, and `r--` GOT `SegSlice`s into `FrozenLoaded`. -/
theorem frozenLoaded_of_segslices {elf : ElfImage} {img : Obj.Image} (runs : List (Nat × Nat))
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hal : img.base.toNat % 4 = 0)
    (hcode : SegSlice elf img.base img.code Perm.rx)
    (hdlen : img.data.length < 2 ^ 64)
    (hruns : ∀ r ∈ runs, r.1 + r.2 ≤ img.data.length ∧
      SegSlice elf (img.dataAddr + BitVec.ofNat 64 r.1) ((img.data.drop r.1).take r.2) Perm.ro)
    (hcover : ∀ q ∈ img.roData, ∃ o, q.1 = img.dataAddr + BitVec.ofNat 64 o ∧
      ∃ r ∈ runs, r.1 ≤ o ∧ o + q.2 ≤ r.1 + r.2)
    (hgot : SegSlice elf img.gotAddr img.gotBytes Perm.ro)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    img.FrozenLoaded s0 :=
  Obj.Image.frozenLoaded_iff.2
    ⟨codeLoaded_of_segSlice hwf hbrk hal hcode hload,
     roDataLoaded_of_runs runs hwf hbrk hdlen hruns hcover hload,
     hgot.holdsBytes hwf hbrk hload⟩

/-- `FrozenLoaded` for `Obj.Loads li img` with `img.data` given by the relocation fold of
`Obj.LinkedImage.load` and `.rodata` coverage checked on `li.roData`. -/
theorem frozenLoaded_of_loads {elf : ElfImage} {li : Obj.LinkedImage} {img : Obj.Image}
    (hli : Obj.Loads li img) (data : List (BitVec 8)) (runs : List (Nat × Nat))
    (hfold : li.relocs.foldlM (Obj.DataReloc.apply img.base) (li.data ++ List.replicate li.bss 0) =
      .ok data)
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hcode : SegSlice elf img.base li.code Perm.rx)
    (hdlen : data.length < 2 ^ 64)
    (hruns : ∀ r ∈ runs, r.1 + r.2 ≤ data.length ∧
      SegSlice elf (img.base + BitVec.ofNat 64 li.dataOff + BitVec.ofNat 64 r.1)
        ((data.drop r.1).take r.2) Perm.ro)
    (hcover : ∀ q ∈ li.roData, li.dataOff ≤ q.1 ∧
      ∃ r ∈ runs, r.1 ≤ q.1 - li.dataOff ∧ q.1 - li.dataOff + q.2 ≤ r.1 + r.2)
    (hgot : SegSlice elf (img.base + BitVec.ofNat 64 li.gotOff)
      ((li.got.map (Obj.GotEntry.value img.base)).flatMap (Obj.bytesLE 8)) Perm.ro)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    img.FrozenLoaded s0 := by
  obtain ⟨data', hfold', hpage, -, -, himg⟩ := ProofLib.ObjectLoad.load_eq_ok hli
  rw [hfold] at hfold'
  injection hfold' with e
  subst e
  generalize img.base = b at hpage hcode hruns hgot himg
  subst himg
  have hal : b.toNat % 4 = 0 := by
    have : b.toNat % Obj.pageSize = 0 := hpage
    unfold Obj.pageSize at this
    omega
  refine frozenLoaded_of_segslices runs hwf hbrk hal hcode hdlen hruns ?_ hgot hload
  intro q hq
  obtain ⟨⟨o, n⟩, hon, rfl⟩ := List.mem_map.1 hq
  obtain ⟨hdo, r, hr, h1, h2⟩ := hcover (o, n) hon
  refine ⟨o - li.dataOff, ?_, r, hr, h1, h2⟩
  show b + BitVec.ofNat 64 o = b + BitVec.ofNat 64 li.dataOff + BitVec.ofNat 64 (o - li.dataOff)
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega

/-! ## Fold-Free `Piece` Decomposition

Describes each `r--` run as a sequence of unrelocated byte spans (`Piece.raw`) and 8-byte `ABS64`
relocation slots (`Piece.abs64`), checked directly against `li.relocs` via `piecesOk` without
evaluating the full `LinkedImage` relocation fold in the kernel. -/

/-- Segment of a `.rodata` run: `raw n` for `n` unrelocated bytes, or `abs64 target` for an 8-byte
slot relocated to `base + target`. -/
inductive Piece where
  | raw (n : Nat)
  | abs64 (target : Nat)
  deriving Repr, DecidableEq

def piecesLen : List Piece → Nat
  | [] => 0
  | .raw n :: ps => n + piecesLen ps
  | .abs64 _ :: ps => 8 + piecesLen ps

/-- Checks that `rs` (over data of length `dataLen`) matches the `Piece` layout starting at offset `k`. -/
def piecesOk (rs : List Obj.DataReloc) (dataLen : Nat) : Nat → List Piece → Bool
  | _, [] => true
  | k, .raw n :: ps => ProofLib.ObjectLoad.noRelocInRange rs dataLen k n && piecesOk rs dataLen (k + n) ps
  | k, .abs64 t :: ps => CryptoProofLib.RoDataReloc.reloc64At rs dataLen k t &&
      piecesOk rs dataLen (k + 8) ps

/-- Evaluates the relocated byte list denoted by a `Piece` list at `base` in one linear pass. -/
def piecesBytes (base : BitVec 64) : List (BitVec 8) → List Piece → List (BitVec 8)
  | _, [] => []
  | d, .raw n :: ps => d.take n ++ piecesBytes base (d.drop n) ps
  | d, .abs64 t :: ps => Obj.bytesLE 8 (base + BitVec.ofNat 64 t) ++ piecesBytes base (d.drop 8) ps

/-- If `rs` applies to `d` and satisfies `piecesOk` from offset `k`, the relocated slice equals
`piecesBytes base`. -/
theorem fold_pieces {base : BitVec 64} (rs : List Obj.DataReloc) (d d' : List (BitVec 8))
    (dataLen : Nat) (hlen : d.length = dataLen)
    (hfold : rs.foldlM (Obj.DataReloc.apply base) d = .ok d') :
    ∀ (ps : List Piece) (k : Nat), piecesOk rs dataLen k ps = true →
      (d'.drop k).take (piecesLen ps) = piecesBytes base (d.drop k) ps
  | [], _, _ => by simp [piecesLen, piecesBytes]
  | .raw n :: ps, k, hok => by
    simp only [piecesOk, Bool.and_eq_true] at hok
    have ih := fold_pieces rs d d' dataLen hlen hfold ps (k + n) hok.2
    obtain ⟨-, hs⟩ := ProofLib.ObjectLoad.foldlM_dataReloc_preserves_slice rs d d' dataLen k n
      hlen hok.1 hfold
    simp only [piecesLen, piecesBytes]
    rw [List.take_add, hs]
    simp only [List.drop_drop]
    rw [ih]
  | .abs64 t :: ps, k, hok => by
    simp only [piecesOk, Bool.and_eq_true] at hok
    have ih := fold_pieces rs d d' dataLen hlen hfold ps (k + 8) hok.2
    obtain ⟨-, hs⟩ := CryptoProofLib.RoDataReloc.foldlM_reloc64At rs d d' dataLen k hlen hok.1
      hfold
    simp only [piecesLen, piecesBytes]
    rw [List.take_add, hs]
    simp only [List.drop_drop]
    rw [ih]

/-- Fold-free `FrozenLoaded` for `Obj.Loads li img` from `(off, pieces)` `.rodata` descriptions
checked by `piecesOk`. -/
theorem frozenLoaded_of_loads_pieces {elf : ElfImage} {li : Obj.LinkedImage} {img : Obj.Image}
    (hli : Obj.Loads li img) (runs : List (Nat × List Piece))
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hcode : SegSlice elf img.base li.code Perm.rx)
    (hdlen : li.data.length + li.bss < 2 ^ 64)
    (hruns : ∀ r ∈ runs, r.1 + piecesLen r.2 ≤ li.data.length + li.bss ∧
      piecesOk li.relocs (li.data.length + li.bss) r.1 r.2 = true ∧
      SegSlice elf (img.base + BitVec.ofNat 64 li.dataOff + BitVec.ofNat 64 r.1)
        (piecesBytes img.base ((li.data ++ List.replicate li.bss 0).drop r.1) r.2) Perm.ro)
    (hcover : ∀ q ∈ li.roData, li.dataOff ≤ q.1 ∧
      ∃ r ∈ runs, r.1 ≤ q.1 - li.dataOff ∧ q.1 - li.dataOff + q.2 ≤ r.1 + piecesLen r.2)
    (hgot : SegSlice elf (img.base + BitVec.ofNat 64 li.gotOff)
      ((li.got.map (Obj.GotEntry.value img.base)).flatMap (Obj.bytesLE 8)) Perm.ro)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    img.FrozenLoaded s0 := by
  obtain ⟨data, hfold, -, hwfli, -, -⟩ := ProofLib.ObjectLoad.load_eq_ok hli
  have hlen0 : (li.data ++ List.replicate li.bss 0).length = li.data.length + li.bss := by simp
  have hrel : li.relocs.all (fun r => decide (r.off + r.width ≤ li.data.length + li.bss)) = true := by
    have h : li.relocs.all (fun r => (r.width == 8 || r.width == 4) &&
        decide (r.off + r.width ≤ li.data.length)) = true := by
      simp only [Obj.LinkedImage.wellFormed, Bool.and_eq_true] at hwfli
      exact hwfli.1.1.2
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    intro r hr
    have := (h r hr).2
    omega
  have hdl : data.length = li.data.length + li.bss :=
    (ProofLib.ObjectLoad.RoDataFactsAux.foldlM_dataReloc_length _ _ _ hfold hrel (Nat.le_of_eq hlen0.symm)).trans hlen0
  refine frozenLoaded_of_loads hli data (runs.map fun r => (r.1, piecesLen r.2)) hfold hwf hbrk
    hcode (by omega) ?_ ?_ hgot hload
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    obtain ⟨hb, hok, hs⟩ := hruns r' hr'
    refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    rw [fold_pieces li.relocs _ data _ hlen0 hfold r'.2 r'.1 hok]
    exact hs
  · intro q hq
    obtain ⟨hdo, r, hr, h1, h2⟩ := hcover q hq
    exact ⟨hdo, (r.1, piecesLen r.2), List.mem_map.2 ⟨r, hr, rfl⟩, h1, h2⟩

end CryptoVerification.SignalSession.ElfFrozen
