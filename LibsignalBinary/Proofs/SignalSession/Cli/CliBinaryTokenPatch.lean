/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElf
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed

@[expose] public section

set_option autoImplicit false

/-!
# Initial Token Cells and Ghost `patchElfTokens` Transport (`DEV-CLI10`)

Layout-generic ELF segment-patching lemmas bridging `CliRunsTo`'s `cliTokenPatch s0` to
`Cli.MuslHarness`'s unpatched `elf'.loadState` interface via `patchElfTokens elf`:
- `CliElfTokenCells` and `tokenCellsInitial_of_dataSeg` witness that an unpatched loaded state holds
  `0xff#8` at `cliBase + tokenStorageOff` and `3#32` at `cliBase + tokenOnceOff`.
- `loadState_patchElfTokens` proves `(patchElfTokens elf).loadState inputs = (elf.loadState inputs).map cliTokenPatch`.
- `keepsFrozen_cliTokenPatch` and `segSlice_patchElfTokens_of_ne*` lift `FrozenLoaded` and disjoint
  `SegSlice`s from `elf` to `patchElfTokens elf`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.InitStack

/-- `PT_LOAD` `.data` slice bundle witnessing SPQR's initial unprobed CPU-feature cells
(`STORAGE.0 = 0xff` and `TOKEN` `Once` state `= 3`, `DEV-CLI10`). -/
structure CliElfTokenCells (elf : ElfImage) : Prop where
  storage : SegSlice elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff)
    [0xff#8] Perm.rw
  once : SegSlice elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff)
    [3#8, 0#8, 0#8, 0#8] Perm.rw

/-- Before `cliTokenPatch`, any state `s0` loaded from `elf` holds `0xff#8` at
`cliBase + tokenStorageOff` and `3#32` (`[3, 0, 0, 0]`) at `cliBase + tokenOnceOff`. -/
theorem tokenCellsInitial_of_dataSeg {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    s0.mem.read8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) = 0xff#8 ∧
    s0.mem.read32 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) = 3#32 := by
  have hs := (htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)
  have ho0 := (htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)
  have ho1 := (htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)
  have ho2 := (htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)
  have ho3 := (htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)
  have h0 : [0xff#8][0] = 0xff#8 := rfl
  refine ⟨by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, h0] using hs.1, ?_⟩
  unfold Memory.read32; dsimp only
  have e0 : s0.mem.read8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 0#64) = 3#8 := ho0.1
  have e1 : s0.mem.read8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 1#64) = 0#8 := ho1.1
  have e2 : s0.mem.read8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 2#64) = 0#8 := ho2.1
  have e3 : s0.mem.read8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 3#64) = 0#8 := ho3.1
  rw [e0, e1, e2, e3]; rfl

/-- Specialization of `tokenCellsInitial_of_dataSeg` to `cliProcessInputs i`. -/
theorem tokenCellsInitial_cliProcessInputs {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf) :
    ∀ i s0, elf.loadState (cliProcessInputs i) = .ok s0 →
      s0.mem.read8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) = 0xff#8 ∧
      s0.mem.read32 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) = 3#32 :=
  fun _ _ hload => tokenCellsInitial_of_dataSeg hE htok hload

/-- Overwrite byte `addr` with `val` in region `r` when `addr` falls within `r`. -/
def patchRegionByte (addr : BitVec 64) (val : BitVec 8) (r : Snapshot.Region) : Snapshot.Region :=
  let i := (addr - r.start).toNat
  if i < r.bytes.length then { r with bytes := r.bytes.set i val } else r

/-- Overwrite byte `addr` with `val` across all `PT_LOAD` segments of `elf`. -/
def patchElfByte (addr : BitVec 64) (val : BitVec 8) (elf : ElfImage) : ElfImage :=
  { elf with segments := elf.segments.map (patchRegionByte addr val) }

/-- Ghost `ElfImage` with spqr's 5 CPU-probe `.data` bytes pre-set to `0` (`DEV-CLI10`), so its
`loadState` equals `(elf.loadState ·).map cliTokenPatch`. -/
def patchElfTokens (elf : ElfImage) : ElfImage :=
  let sAddr := cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff
  let oAddr := cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff
  patchElfByte (oAddr + 3#64) 0#8 (patchElfByte (oAddr + 2#64) 0#8
    (patchElfByte (oAddr + 1#64) 0#8 (patchElfByte oAddr 0#8 (patchElfByte sAddr 0#8 elf))))

@[simp] private theorem patchRegionByte_start (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).start = r.start := by unfold patchRegionByte; dsimp only; split <;> rfl
@[simp] private theorem patchRegionByte_perm (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).perm = r.perm := by unfold patchRegionByte; dsimp only; split <;> rfl
@[simp] private theorem patchRegionByte_bytes_length (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).bytes.length = r.bytes.length := by unfold patchRegionByte; dsimp only; split <;> simp
@[simp] private theorem patchRegionByte_nonAnonLen (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).nonAnonLen = r.nonAnonLen := by unfold patchRegionByte; dsimp only; split <;> rfl

private theorem regionAlignedValid_patchRegionByte (addr : BitVec 64) (val : BitVec 8)
    (r : Snapshot.Region) : regionAlignedValid (patchRegionByte addr val r) = regionAlignedValid r := by
  simp [regionAlignedValid]

private theorem regionsDisjointAndAligned_map_patchRegionByte (addr : BitVec 64) (val : BitVec 8) :
    ∀ segs : List Snapshot.Region,
      regionsDisjointAndAligned (segs.map (patchRegionByte addr val)) = regionsDisjointAndAligned segs
  | [] => rfl
  | [r] => regionAlignedValid_patchRegionByte addr val r
  | r1 :: r2 :: rest => by
    have ih := regionsDisjointAndAligned_map_patchRegionByte addr val (r2 :: rest)
    simp only [List.map_cons] at ih
    simp only [List.map_cons, regionsDisjointAndAligned, regionAlignedValid_patchRegionByte,
      patchRegionByte_start, patchRegionByte_bytes_length, ih]

private theorem entryInExecRegion_map_patchRegionByte (entry addr : BitVec 64) (val : BitVec 8)
    (segs : List Snapshot.Region) :
    entryInExecRegion entry (segs.map (patchRegionByte addr val)) = entryInExecRegion entry segs := by
  simp [entryInExecRegion, List.any_map, Function.comp_def]

@[simp] theorem wellFormed_patchElfByte (addr : BitVec 64) (val : BitVec 8) (elf : ElfImage) :
    (patchElfByte addr val elf).WellFormed = elf.WellFormed := by
  unfold ElfImage.WellFormed patchElfByte
  simp [regionsDisjointAndAligned_map_patchRegionByte, entryInExecRegion_map_patchRegionByte,
    List.all_map, Function.comp_def]

theorem elfStaticOk_patchElfByte {addr : BitVec 64} {val : BitVec 8} {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) : Cli.ElfStaticOk (patchElfByte addr val elf) :=
  ⟨by simpa using hE.1, hE.2⟩

theorem elfStaticOk_patchElfTokens {elf : ElfImage} (hE : Cli.ElfStaticOk elf) :
    Cli.ElfStaticOk (patchElfTokens elf) :=
  elfStaticOk_patchElfByte (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte
    (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte hE))))

/-- `addr` falls within at least one `PT_LOAD` segment of `elf`. -/
def AddrInElf (elf : ElfImage) (addr : BitVec 64) : Prop :=
  ∃ r ∈ elf.segments, (addr - r.start).toNat < r.bytes.length

@[simp] theorem addrInElf_patchElfByte (a : BitVec 64) (v : BitVec 8) (elf : ElfImage)
    (addr : BitVec 64) : AddrInElf (patchElfByte a v elf) addr ↔ AddrInElf elf addr := by
  simp [AddrInElf, patchElfByte]

theorem segSlice_addrInElf {elf : ElfImage} {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (hs : SegSlice elf a bs p) (hE : Cli.ElfStaticOk elf) {j : Nat} (hj : j < bs.length) :
    AddrInElf elf (a + BitVec.ofNat 64 j) := by
  obtain ⟨k, hk, off, -, rfl, hbs⟩ := hs
  have hlen : bs.length = min bs.length (elf.segments[k].bytes.length - off) := by
    conv => lhs; rw [← hbs]
    rw [List.length_take, List.length_drop]
  have hoffj : off + j < elf.segments[k].bytes.length := by omega
  have hseg := segs_below elf hE.1 hE.2 _ (List.getElem_mem hk)
  have hsb := stackBase_eq
  refine ⟨elf.segments[k], List.getElem_mem hk, ?_⟩
  have h1 : (elf.segments[k].start + BitVec.ofNat 64 off).toNat =
      elf.segments[k].start.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h2 : (elf.segments[k].start + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat =
      elf.segments[k].start.toNat + off + j := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le]
  · rw [h2]; omega
  · rw [BitVec.le_def, h2]; omega

theorem sub_toNat_eq_iff {a b s : BitVec 64} :
    (a - s).toNat = (b - s).toNat ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := a.isLt; have := b.isLt; have := s.isLt
    simp only [BitVec.toNat_sub] at h
    omega
  · rintro rfl; rfl

private theorem loadCellAt_cons (r : Snapshot.Region) (rs : List Snapshot.Region) (a : BitVec 64) :
    Snapshot.loadCellAt (r :: rs) a =
      if h : (a - r.start).toNat < r.bytes.length then
        some (some (Perm.mk r.perm.r r.perm.w r.perm.x false
          (if (a - r.start).toNat < r.nonAnonLen then false else r.perm.anon)),
          r.bytes[(a - r.start).toNat]'h)
      else Snapshot.loadCellAt rs a := by
  unfold Snapshot.loadCellAt
  rw [List.findSome?_cons]
  dsimp only
  by_cases h : (a - r.start).toNat < r.bytes.length <;> simp only [h, ↓reduceDIte]

private theorem loadCellAt_append (xs ys : List Snapshot.Region) (a : BitVec 64) :
    Snapshot.loadCellAt (xs ++ ys) a = (Snapshot.loadCellAt xs a).or (Snapshot.loadCellAt ys a) := by
  unfold Snapshot.loadCellAt
  exact List.findSome?_append

private theorem patchRegionByte_eq_of_lt {addr : BitVec 64} {val : BitVec 8} {r : Snapshot.Region}
    (hi : (addr - r.start).toNat < r.bytes.length) :
    patchRegionByte addr val r = { r with bytes := r.bytes.set (addr - r.start).toNat val } := by
  unfold patchRegionByte; dsimp only; simp only [hi, ↓reduceIte]

private theorem patchRegionByte_eq_of_not_lt {addr : BitVec 64} {val : BitVec 8}
    {r : Snapshot.Region} (hi : ¬ (addr - r.start).toNat < r.bytes.length) :
    patchRegionByte addr val r = r := by
  unfold patchRegionByte; dsimp only; simp only [hi, ↓reduceIte]

private theorem loadCellAt_map_patchRegionByte_ne (segs : List Snapshot.Region)
    (addr : BitVec 64) (val : BitVec 8) {a : BitVec 64} (hne : a ≠ addr) :
    Snapshot.loadCellAt (segs.map (patchRegionByte addr val)) a = Snapshot.loadCellAt segs a := by
  have hidx : ∀ r : Snapshot.Region, (addr - r.start).toNat ≠ (a - r.start).toNat :=
    fun r heq => hne (sub_toNat_eq_iff.mp heq.symm)
  induction segs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons]
    by_cases hi : (addr - r.start).toNat < r.bytes.length
    · rw [patchRegionByte_eq_of_lt hi, loadCellAt_cons, loadCellAt_cons]
      by_cases ha_lt : (a - r.start).toNat < r.bytes.length
      · have ha_lt' : (a - r.start).toNat < (r.bytes.set (addr - r.start).toNat val).length := by
          rwa [List.length_set]
        simp only [ha_lt', ha_lt, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq, true_and]
        exact List.getElem_set_ne (hidx r) ha_lt'
      · have ha_lt' : ¬ (a - r.start).toNat < (r.bytes.set (addr - r.start).toNat val).length := by
          rwa [List.length_set]
        simp only [ha_lt', ha_lt, ↓reduceDIte]
        exact ih
    · rw [patchRegionByte_eq_of_not_lt hi, loadCellAt_cons, loadCellAt_cons]
      split
      · rfl
      · exact ih

private theorem loadCellAt_map_patchRegionByte_self {segs : List Snapshot.Region}
    {addr : BitVec 64} (val : BitVec 8)
    (hmem : ∃ r ∈ segs, (addr - r.start).toNat < r.bytes.length) :
    ∃ (p : Perm) (old : BitVec 8),
      p.lazyFree = false ∧
      Snapshot.loadCellAt segs addr = some (some p, old) ∧
      Snapshot.loadCellAt (segs.map (patchRegionByte addr val)) addr = some (some p, val) := by
  induction segs with
  | nil =>
    rcases hmem with ⟨_, hm, _⟩
    simp at hm
  | cons r rs ih =>
    rw [List.map_cons]
    by_cases hlt : (addr - r.start).toNat < r.bytes.length
    · rw [patchRegionByte_eq_of_lt hlt, loadCellAt_cons, loadCellAt_cons]
      have hlt' : (addr - r.start).toNat < (r.bytes.set (addr - r.start).toNat val).length := by
        rwa [List.length_set]
      refine ⟨Perm.mk r.perm.r r.perm.w r.perm.x false
          (if (addr - r.start).toNat < r.nonAnonLen then false else r.perm.anon),
        r.bytes[(addr - r.start).toNat]'hlt, rfl, by simp only [hlt, ↓reduceDIte], ?_⟩
      simp only [hlt', ↓reduceDIte, List.getElem_set_self]
    · rw [patchRegionByte_eq_of_not_lt hlt, loadCellAt_cons, loadCellAt_cons]
      simp only [hlt, ↓reduceDIte]
      rcases hmem with ⟨r', hr', hlt_r'⟩
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact absurd hlt_r' hlt
      · exact ih ⟨r', hr', hlt_r'⟩

private theorem perm_with_lazyFree_false {p : Perm} (h : p.lazyFree = false) :
    { p with lazyFree := false } = p := by
  cases p; simp at h; subst h; rfl

private theorem mapZero_loadCellAt_patchRegionByte {segs : List Snapshot.Region}
    {addr : BitVec 64} (val : BitVec 8) (stackRegion : Snapshot.Region)
    (sb : BitVec 64) (sz : Nat)
    (hmem : ∃ r ∈ segs, (addr - r.start).toNat < r.bytes.length) :
    ((⟨Snapshot.loadCellAt (segs.map (patchRegionByte addr val) ++ [stackRegion])⟩ : Memory).mapZero sb sz) =
      (((⟨Snapshot.loadCellAt (segs ++ [stackRegion])⟩ : Memory).mapZero sb sz).write8 addr val) := by
  obtain ⟨p, old, hp_lf, hc1, hc2⟩ := loadCellAt_map_patchRegionByte_self val hmem
  have happ1 : Snapshot.loadCellAt (segs ++ [stackRegion]) addr = some (some p, old) := by
    rw [loadCellAt_append, hc1]; rfl
  have happ2 : Snapshot.loadCellAt (segs.map (patchRegionByte addr val) ++ [stackRegion]) addr =
      some (some p, val) := by
    rw [loadCellAt_append, hc2]; rfl
  apply Memory.ext
  funext a
  by_cases ha : a = addr
  · subst ha
    simp [Memory.mapZero, Memory.write8, Memory.perm, Memory.rawPerm, Option.mapped,
      happ1, happ2, perm_with_lazyFree_false hp_lf]
  · have hne : Snapshot.loadCellAt (segs.map (patchRegionByte addr val) ++ [stackRegion]) a =
        Snapshot.loadCellAt (segs ++ [stackRegion]) a := by
      rw [loadCellAt_append, loadCellAt_append, loadCellAt_map_patchRegionByte_ne segs addr val ha]
    simp [Memory.mapZero, Memory.write8, Memory.perm, ha, hne]

/-- Single-byte `loadState` commutation: patching an already-mapped ELF byte `addr` in
`elf.segments` equals applying `s.setMem (s.mem.write8 addr val)` after `elf.loadState`. -/
theorem loadState_patchElfByte {elf : ElfImage} {addr : BitVec 64} (val : BitVec 8)
    (hmem : AddrInElf elf addr) (inputs : ProcessInputs) :
    (patchElfByte addr val elf).loadState inputs =
      (elf.loadState inputs).map (fun s => s.setMem (s.mem.write8 addr val)) := by
  unfold ElfImage.loadState
  dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure]
  rw [wellFormed_patchElfByte]
  cases elf.WellFormed
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases inputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases inputs.files.any (fun (p, bs) => hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hstk : buildInitialStack (patchElfByte addr val elf) inputs =
            buildInitialStack elf inputs := rfl
        rw [hstk]
        cases buildInitialStack elf inputs with
        | error _ => rfl
        | ok pair =>
          obtain ⟨sp, stackRegion⟩ := pair
          simp only [Except.map, State.setMem, Except.ok.injEq]
          congr 1
          exact mapZero_loadCellAt_patchRegionByte val stackRegion _ _ hmem
      · rfl
    · rfl

private theorem bv_add_1_1 (x : BitVec 64) : x + 1#64 + 1#64 = x + 2#64 := by
  rw [BitVec.add_assoc]; rfl

private theorem bv_add_2_1 (x : BitVec 64) : x + 2#64 + 1#64 = x + 3#64 := by
  rw [BitVec.add_assoc]; rfl

/-- When SPQR's 5 token `.data` cells lie in `elf` (`htok`), loading `patchElfTokens elf`
produces `(elf.loadState inputs).map cliTokenPatch`. -/
theorem loadState_patchElfTokens {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf) (inputs : ProcessInputs) :
    (patchElfTokens elf).loadState inputs = (elf.loadState inputs).map cliTokenPatch := by
  have hs : AddrInElf elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.storage hE (j := 0) (by decide)
  have ho0 : AddrInElf elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.once hE (j := 0) (by decide)
  have ho1 : AddrInElf elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 1#64) :=
    segSlice_addrInElf htok.once hE (j := 1) (by decide)
  have ho2 : AddrInElf elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 2#64) :=
    segSlice_addrInElf htok.once hE (j := 2) (by decide)
  have ho3 : AddrInElf elf (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 3#64) :=
    segSlice_addrInElf htok.once hE (j := 3) (by decide)
  unfold patchElfTokens
  dsimp only
  rw [loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho3),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho2),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho1),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho0),
      loadState_patchElfByte _ hs]
  cases elf.loadState inputs with
  | error _ => rfl
  | ok s0 =>
    simp only [Except.map, cliTokenPatch, State.setMem,
      Memory.writeBytes, bv_add_1_1, bv_add_2_1]

private theorem keepsFrozen_write8_of_perm_rw {m : Memory} {addr : BitVec 64} (val : BitVec 8)
    (hp : m.perm addr = some Perm.rw) : m.KeepsFrozen (m.write8 addr val) := by
  intro a ha
  have hne : a ≠ addr := by
    rintro rfl
    unfold Memory.Frozen at ha
    simp only [hp, Option.frozen, Perm.frozen] at ha
    exact Bool.noConfusion ha
  simp [Memory.write8, Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, hne]

/-- `cliTokenPatch` preserves all frozen (`.rx`/`.ro`) bytes of `s0.mem` because spqr's 5 token
cells are `Perm.rw` (`htok`). -/
theorem keepsFrozen_cliTokenPatch {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    s0.mem.KeepsFrozen (cliTokenPatch s0).mem := by
  have ps : s0.mem.perm (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : s0.mem.perm (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p1 : s0.mem.perm (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 1#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1
  have p2 : s0.mem.perm (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 2#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1
  have p3 : s0.mem.perm (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 3#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1
  have hmem : (cliTokenPatch s0).mem =
      (((((s0.mem.write8 (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) 0#8).write8
        (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) 0#8).write8
        (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 1#64) 0#8).write8
        (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 2#64) 0#8).write8
        (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 3#64) 0#8) := by
    simp only [cliTokenPatch, State.setMem, Memory.writeBytes, bv_add_1_1, bv_add_2_1]
  rw [hmem]
  exact ((((keepsFrozen_write8_of_perm_rw 0#8 ps).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p0))).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p1))).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p2))).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p3))

/-- Any `SegSlice` disjoint from `addr` is preserved by `patchElfByte addr val`. -/
theorem segSlice_patchElfByte_of_ne {elf : ElfImage} {a addr : BitVec 64} {val : BitVec 8}
    {bs : List (BitVec 8)} {p : Perm} (hs : SegSlice elf a bs p) (hE : Cli.ElfStaticOk elf)
    (hne : ∀ j (_ : j < bs.length), a + BitVec.ofNat 64 j ≠ addr) :
    SegSlice (patchElfByte addr val elf) a bs p := by
  obtain ⟨k, hk, off, hp, rfl, hbs⟩ := hs
  refine ⟨k, by simp [patchElfByte, hk], off, by simpa [patchElfByte] using hp,
    by simp [patchElfByte], ?_⟩
  simp only [patchElfByte, List.getElem_map]
  unfold patchRegionByte; dsimp only
  split
  · have hseg := segs_below elf hE.1 hE.2 _ (List.getElem_mem hk)
    have hsb := stackBase_eq
    have hlen : bs.length = min bs.length (elf.segments[k].bytes.length - off) := by
      conv => lhs; rw [← hbs]
      rw [List.length_take, List.length_drop]
    refine Eq.trans ?_ hbs
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_set]
    · intro j _ hj2
      simp only [List.getElem_take, List.getElem_drop]
      have hj : j < bs.length := by
        rw [List.length_take, List.length_drop] at hj2; omega
      have hidx_ne : (addr - elf.segments[k].start).toNat ≠ off + j := by
        intro heq; apply hne j hj
        have h1 : (elf.segments[k].start + BitVec.ofNat 64 off).toNat =
            elf.segments[k].start.toNat + off := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have h2 : (elf.segments[k].start + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat =
            elf.segments[k].start.toNat + off + j := by
          rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have hsub : (elf.segments[k].start + BitVec.ofNat 64 off + BitVec.ofNat 64 j -
            elf.segments[k].start).toNat = off + j := by
          rw [BitVec.toNat_sub_of_le]; · rw [h2]; omega
          · rw [BitVec.le_def, h2]; omega
        exact sub_toNat_eq_iff.mp (hsub.trans heq.symm)
      exact List.getElem_set_ne hidx_ne _
  · exact hbs

theorem segSlice_patchElfTokens_of_ne {elf : ElfImage} {a : BitVec 64}
    {bs : List (BitVec 8)} {p : Perm} (hs : SegSlice elf a bs p) (hE : Cli.ElfStaticOk elf)
    (hs_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff)
    (ho0_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff)
    (ho1_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 1#64)
    (ho2_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 2#64)
    (ho3_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 3#64) :
    SegSlice (patchElfTokens elf) a bs p := by
  have e1 := elfStaticOk_patchElfByte (addr := cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) (val := 0#8) hE
  have e2 := elfStaticOk_patchElfByte (addr := cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) (val := 0#8) e1
  have e3 := elfStaticOk_patchElfByte (addr := cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 1#64) (val := 0#8) e2
  have e4 := elfStaticOk_patchElfByte (addr := cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + 2#64) (val := 0#8) e3
  exact segSlice_patchElfByte_of_ne
    (segSlice_patchElfByte_of_ne
      (segSlice_patchElfByte_of_ne
        (segSlice_patchElfByte_of_ne
          (segSlice_patchElfByte_of_ne hs hE hs_ne)
          e1 ho0_ne)
        e2 ho1_ne)
      e3 ho2_ne)
    e4 ho3_ne

/-- Any non-`.rw` `SegSlice` (e.g. `.rx` code or `.ro` program headers) is preserved by `patchElfTokens`. -/
theorem segSlice_patchElfTokens_of_ne_rw {elf : ElfImage} {a : BitVec 64}
    {bs : List (BitVec 8)} {p : Perm} (hs : SegSlice elf a bs p) (hp_ne : p.rwx ≠ Perm.rw)
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf) :
    SegSlice (patchElfTokens elf) a bs p := by
  have hload := (loadState_cli_layout elf [] [] [] [] hE.1 hE.2
    (by simp) (by simp) (by simp) (by simp)).1
  have hperm_ne : ∀ addr,
      (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm addr = some .rw →
      ∀ j (_ : j < bs.length), a + BitVec.ofNat 64 j ≠ addr := by
    intro addr hrw j hj heq
    have hpj := ((hs.holdsBytes hE.1 hE.2 hload) j hj).2.1
    rw [heq, hrw] at hpj
    exact hp_ne (Option.some.inj hpj).symm
  have ps : (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm
      (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm
      (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  exact segSlice_patchElfTokens_of_ne hs hE (hperm_ne _ ps) (hperm_ne _ p0)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1)

end CryptoVerification.SignalSession
