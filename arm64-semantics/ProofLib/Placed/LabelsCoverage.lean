/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.RustRuntime
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsInterned
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

/-!
# Placed-Library Label Coverage

Anchors placed-library label families (hooks and pruned stubs, extern-table partitions, Rust
panic symbol sets, and covered RW/RO statics) directly to extracted `.o` objects
(`Arm64.Obj.ExtractedObj`) and `Arm64.Obj.LabelsFromObjects`. Pre-decoded `List Char` checkers
(`isPanicSymbolFast`, `checkExternDataUndefB`, `checkReferencedExternsB`, `checkCoveredDataSpecB`,
`checkGateALabelsB`) discharge coverage certificates via `decide +kernel`.
-/

@[expose] public section

namespace Arm64.Obj

/-! ## Kernel-Fast Rust Panic Predicates -/

/-- Exact out-of-line Rust panic symbol names matched by `Arm64.Rust.isPanicSymbol`. -/
def rustPanicExactNames : List String :=
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ]

/-- Character-list form of `Arm64.Rust.isPanicSymbol` operating on `s.toList` without UTF-8 re-decoding. -/
def isPanicSymbolChars (cs : List Char) : Bool :=
  List.isPrefixOf ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':'] cs ||
  (rustPanicExactNames.map String.toList).any (fun p => cs == p)

/-- Kernel-fast character-list decision procedure equivalent to `Arm64.Rust.isPanicSymbol`. -/
def isPanicSymbolFast (name : String) : Bool :=
  isPanicSymbolChars name.toList

private theorem list_contains_eq_any_toList (xs : List String) (s : String) :
    xs.contains s = (xs.map String.toList).any (fun p => s.toList == p) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.contains_cons, List.map_cons, List.any_cons, ih]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, String.ext_iff]

/-- `Arm64.Rust.isPanicSymbol` agrees with `isPanicSymbolFast`. -/
theorem rust_isPanicSymbol_eq_fast (s : String) :
    Arm64.Rust.isPanicSymbol s = isPanicSymbolFast s := by
  unfold Arm64.Rust.isPanicSymbol isPanicSymbolFast isPanicSymbolChars rustPanicExactNames
  have hpref : s.startsWith "core::panicking::" =
      List.isPrefixOf ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']
        s.toList := by
    have hpat : ("core::panicking::" : String).toList =
        ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':'] := by
      decide
    apply Bool.eq_iff_iff.2
    rw [String.startsWith_string_iff, hpat, List.isPrefixOf_iff_prefix]
  rw [hpref, list_contains_eq_any_toList]

/-- `Arm64.Rust.isPanicSymbol` extended with an explicit list of extra project-specific demangled
    panic entry points (empty when standard `Rust.isPanicSymbol` suffices). -/
def isRustPanicPlus (extraPanicDemangled : List String) (name : String) : Bool :=
  Arm64.Rust.isPanicSymbol name || extraPanicDemangled.contains name

/-- Character-list form of `isRustPanicPlus` operating on pre-decoded character lists. -/
def isRustPanicPlusChars (extraChars : List (List Char)) (cs : List Char) : Bool :=
  isPanicSymbolChars cs || extraChars.any (fun p => cs == p)

/-- Kernel-fast form of `isRustPanicPlus`. -/
def isRustPanicPlusFast (extraPanicDemangled : List String) (name : String) : Bool :=
  isRustPanicPlusChars (extraPanicDemangled.map String.toList) name.toList

theorem isRustPanicPlus_eq_chars (extraPanicDemangled : List String) (s : String) :
    isRustPanicPlus extraPanicDemangled s =
      isRustPanicPlusChars (extraPanicDemangled.map String.toList) s.toList := by
  unfold isRustPanicPlus isRustPanicPlusChars
  rw [rust_isPanicSymbol_eq_fast, isPanicSymbolFast, list_contains_eq_any_toList]

theorem isRustPanicPlus_eq_fast (extraPanicDemangled : List String) (s : String) :
    isRustPanicPlus extraPanicDemangled s = isRustPanicPlusFast extraPanicDemangled s :=
  isRustPanicPlus_eq_chars extraPanicDemangled s

/-! ## Core `.o` Symbol Predicates and Single-Pass Summary Helpers -/

/-- Raw `.call26` / `.jump26` branch relocation in an executable section of `objs` targeting an
    undefined symbol with mangled name `raw`.
    Note: this certifies `.o`-level branch-relocation reference across `objs`; cone reachability
    from exported entry points is established via `LabelsFromObjects` + the placed library contract. -/
def HasRawUndefBranchReloc (objs : List ExtractedObj) (raw : String) : Prop :=
  ∃ o ∈ objs, ∃ sec ∈ o.sections, sec.isExec = true ∧
    ∃ rr ∈ sec.relocs, (rr.kind = some .call26 ∨ rr.kind = some .jump26) ∧
      ∃ sy, o.symbols[rr.symIdx]? = some sy ∧ sy.sec = .undef ∧ sy.rawName = raw

/-- `raw` appears at least once as a non-local undefined symbol in `objs`, and every
    non-local occurrence of `raw` in `objs` is undefined (`.undef`). Fails closed if `raw` is
    absent (e.g. a typo) or defined in any `.o` file. -/
def NonVacuousUndefSym (objs : List ExtractedObj) (raw : String) : Prop :=
  (∃ o ∈ objs, ∃ sy ∈ o.symbols, sy.rawName = raw ∧ sy.bind ≠ .local ∧ sy.sec = .undef) ∧
  (∀ o ∈ objs, ∀ sy ∈ o.symbols, sy.rawName = raw → sy.bind ≠ .local → sy.sec = .undef)

/-- Strengthens `NonVacuousUndefSym` by pinning `sy.name = expectedDemangled` on both the witness
    and every non-local `.o` symbol table entry for `raw`. -/
def NonVacuousUndefSymDemangled (objs : List ExtractedObj) (raw expectedDemangled : String) : Prop :=
  (∃ o ∈ objs, ∃ sy ∈ o.symbols,
    sy.rawName = raw ∧ sy.bind ≠ .local ∧ sy.sec = .undef ∧ sy.name = expectedDemangled) ∧
  (∀ o ∈ objs, ∀ sy ∈ o.symbols,
    sy.rawName = raw → sy.bind ≠ .local → sy.sec = .undef ∧ sy.name = expectedDemangled)

/-- Pre-decoded `(rawName.toList, name.toList, sec == .undef)` for every non-local symbol across
    `objs`. Decodes UTF-8 once per non-local `.o` symbol so multi-symbol checks run in `List Char`
    time under `decide +kernel`. -/
def collectNonLocalSymChars (objs : List ExtractedObj) : List (List Char × List Char × Bool) :=
  objs.flatMap fun o =>
    o.symbols.filterMap fun sy =>
      if sy.bind != .local then
        some (sy.rawName.toList, sy.name.toList, sy.sec == .undef)
      else
        none

private theorem mem_collectNonLocalSymChars {objs : List ExtractedObj}
    {rc nc : List Char} {isUndef : Bool} :
    (rc, nc, isUndef) ∈ collectNonLocalSymChars objs ↔
      ∃ o ∈ objs, ∃ sy ∈ o.symbols,
        sy.bind ≠ .local ∧ sy.rawName.toList = rc ∧ sy.name.toList = nc ∧
        (sy.sec == .undef) = isUndef := by
  unfold collectNonLocalSymChars
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, sy, hsy, hite⟩
    by_cases hb : sy.bind != .local
    · simp only [hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hite
      have hne : sy.bind ≠ .local := by simpa [bne_iff_ne] using hb
      exact ⟨o, ho, sy, hsy, hne, hite.1, hite.2.1, hite.2.2⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hite
  · rintro ⟨o, ho, sy, hsy, hne, hrc, hnc, hu⟩
    have hb : (sy.bind != .local) = true := by simpa [bne_iff_ne] using hne
    exact ⟨o, ho, sy, hsy, by simp [hb, hrc, hnc, hu]⟩

/-- Pre-decoded `rawName.toList` for every raw `.call26` / `.jump26` relocation in an executable
    section of `objs` targeting a `.undef` symbol. -/
def collectUndefBranchRawChars (objs : List ExtractedObj) : List (List Char) :=
  objs.flatMap fun o =>
    o.sections.flatMap fun sec =>
      if sec.isExec then
        sec.relocs.filterMap fun rr =>
          if rr.kind == some .call26 || rr.kind == some .jump26 then
            match o.symbols[rr.symIdx]? with
            | some sy => if sy.sec == .undef then some sy.rawName.toList else none
            | none => none
          else
            none
      else
        []

private theorem mem_collectUndefBranchRawChars {objs : List ExtractedObj} {raw : String} :
    raw.toList ∈ collectUndefBranchRawChars objs ↔ HasRawUndefBranchReloc objs raw := by
  unfold collectUndefBranchRawChars HasRawUndefBranchReloc
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨o, ho, sec, hsec, hmem⟩
    by_cases hexec : sec.isExec
    · simp only [hexec, ↓reduceIte, List.mem_filterMap] at hmem
      obtain ⟨rr, hrr, hrr_ok⟩ := hmem
      by_cases hkind : rr.kind == some .call26 || rr.kind == some .jump26
      · simp only [hkind, ↓reduceIte] at hrr_ok
        cases hsy : o.symbols[rr.symIdx]? with
        | none => simp [hsy] at hrr_ok
        | some sy =>
          simp only [hsy] at hrr_ok
          by_cases hu : sy.sec == .undef
          · simp only [hu, ↓reduceIte, Option.some.injEq] at hrr_ok
            have hk_or : rr.kind = some .call26 ∨ rr.kind = some .jump26 := by
              simpa [Bool.or_eq_true, beq_iff_eq] using hkind
            have hu_eq : sy.sec = .undef := by simpa [beq_iff_eq] using hu
            exact ⟨o, ho, sec, hsec, hexec, rr, hrr, hk_or, sy, hsy, hu_eq,
              String.ext_iff.2 hrr_ok⟩
          · simp [hu] at hrr_ok
      · simp [hkind] at hrr_ok
    · simp [hexec] at hmem
  · rintro ⟨o, ho, sec, hsec, hexec, rr, hrr, hk_or, sy, hsy, hu_eq, hraw⟩
    refine ⟨o, ho, sec, hsec, ?_⟩
    simp only [hexec, ↓reduceIte, List.mem_filterMap]
    have hkind : (rr.kind == some .call26 || rr.kind == some .jump26) = true := by
      simpa [Bool.or_eq_true, beq_iff_eq] using hk_or
    have hu : (sy.sec == .undef) = true := by simpa [beq_iff_eq] using hu_eq
    exact ⟨rr, hrr, by simp [hkind, hsy, hu, hraw]⟩

/-- Boolean checker certifying that every `raw ∈ externs` has a raw `.call26`/`.jump26` branch
    relocation to `.undef` in `objs` (`HasRawUndefBranchReloc`). -/
def checkReferencedExternsB (objs : List ExtractedObj) (externs : List String) : Bool :=
  let brs := collectUndefBranchRawChars objs
  externs.all fun raw =>
    let rc := raw.toList
    brs.any fun b => b == rc

/-- Alias for `checkReferencedExternsB`. -/
abbrev checkReachedExternsB := checkReferencedExternsB

theorem referencedExterns_of_check {objs : List ExtractedObj} {externs : List String}
    (h : checkReferencedExternsB objs externs = true) :
    ∀ raw ∈ externs, HasRawUndefBranchReloc objs raw := by
  unfold checkReferencedExternsB at h
  rw [List.all_eq_true] at h
  intro raw hraw
  have h1 := h raw hraw
  rw [List.any_eq_true] at h1
  obtain ⟨b, hb_mem, hb_eq⟩ := h1
  rw [beq_iff_eq] at hb_eq
  subst hb_eq
  exact mem_collectUndefBranchRawChars.1 hb_mem

/-- Character-list helper for `NonVacuousUndefSym`. -/
def checkNonVacuousUndefChars (nls : List (List Char × List Char × Bool))
    (rc : List Char) : Bool :=
  nls.any (fun (r, _, u) => r == rc && u) &&
  nls.all (fun (r, _, u) => if r == rc then u else true)

private theorem nonVacuousUndef_of_chars {objs : List ExtractedObj} {raw : String}
    (h : checkNonVacuousUndefChars (collectNonLocalSymChars objs) raw.toList = true) :
    NonVacuousUndefSym objs raw := by
  unfold checkNonVacuousUndefChars at h
  rw [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨r0, n0, u0⟩, hmem0, heq0⟩, hall⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at heq0
  obtain ⟨rfl, rfl⟩ := heq0
  obtain ⟨o0, ho0, sy0, hsy0, hbind0, hraw0, _, hu0⟩ := mem_collectNonLocalSymChars.1 hmem0
  rw [beq_iff_eq] at hu0
  refine ⟨⟨o0, ho0, sy0, hsy0, String.ext_iff.2 hraw0, hbind0, hu0⟩, ?_⟩
  intro o ho sy hsy hraw hbind
  have hmem : (sy.rawName.toList, sy.name.toList, sy.sec == .undef) ∈
      collectNonLocalSymChars objs :=
    mem_collectNonLocalSymChars.2 ⟨o, ho, sy, hsy, hbind, rfl, rfl, rfl⟩
  have h1 := hall _ hmem
  simp only [hraw, beq_self_eq_true, ↓reduceIte, beq_iff_eq] at h1
  exact h1

/-- Character-list helper for `NonVacuousUndefSymDemangled`. -/
def checkNonVacuousUndefDemangledChars (nls : List (List Char × List Char × Bool))
    (rc dc : List Char) : Bool :=
  nls.any (fun (r, n, u) => r == rc && u && n == dc) &&
  nls.all (fun (r, n, u) => if r == rc then u && n == dc else true)

private theorem nonVacuousUndefDemangled_of_chars {objs : List ExtractedObj}
    {raw dem : String}
    (h : checkNonVacuousUndefDemangledChars (collectNonLocalSymChars objs)
      raw.toList dem.toList = true) :
    NonVacuousUndefSymDemangled objs raw dem := by
  unfold checkNonVacuousUndefDemangledChars at h
  rw [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨r0, n0, u0⟩, hmem0, heq0⟩, hall⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at heq0
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq0
  obtain ⟨o0, ho0, sy0, hsy0, hbind0, hraw0, hdem0, hu0⟩ := mem_collectNonLocalSymChars.1 hmem0
  rw [beq_iff_eq] at hu0
  refine ⟨⟨o0, ho0, sy0, hsy0, String.ext_iff.2 hraw0, hbind0, hu0, String.ext_iff.2 hdem0⟩, ?_⟩
  intro o ho sy hsy hraw hbind
  have hmem : (sy.rawName.toList, sy.name.toList, sy.sec == .undef) ∈
      collectNonLocalSymChars objs :=
    mem_collectNonLocalSymChars.2 ⟨o, ho, sy, hsy, hbind, rfl, rfl, rfl⟩
  have h1 := hall _ hmem
  simp only [hraw, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1, String.ext_iff.2 h1.2⟩

/-- Non-vacuous external-data `.undef` checker: every `raw ∈ externData` must match at least one
    non-local `.undef` `RawSym` in `objs` and have every non-local occurrence in `objs` be `.undef`.
    Fails closed (`false`) if `raw` is absent from `objs` (e.g. a typo) or defined in `objs`. -/
def checkExternDataUndefB (objs : List ExtractedObj) (externData : List String) : Bool :=
  let nls := collectNonLocalSymChars objs
  externData.all fun raw => checkNonVacuousUndefChars nls raw.toList

theorem externDataUndef_of_check {objs : List ExtractedObj} {externData : List String}
    (h : checkExternDataUndefB objs externData = true) :
    ∀ raw ∈ externData, NonVacuousUndefSym objs raw := by
  unfold checkExternDataUndefB at h
  rw [List.all_eq_true] at h
  intro raw hraw
  exact nonVacuousUndef_of_chars (h raw hraw)

/-- External-data `.undef` checker that also pins the demangled symbol name `(rawName, demangled)`. -/
def checkExternDataDemangledB (objs : List ExtractedObj)
    (externDataSpecs : List (String × String)) : Bool :=
  let nls := collectNonLocalSymChars objs
  externDataSpecs.all fun (raw, dem) =>
    checkNonVacuousUndefDemangledChars nls raw.toList dem.toList

theorem externDataDemangled_of_check {objs : List ExtractedObj}
    {externDataSpecs : List (String × String)}
    (h : checkExternDataDemangledB objs externDataSpecs = true) :
    ∀ p ∈ externDataSpecs, NonVacuousUndefSymDemangled objs p.1 p.2 := by
  unfold checkExternDataDemangledB at h
  rw [List.all_eq_true] at h
  rintro ⟨raw, dem⟩ hp
  exact nonVacuousUndefDemangled_of_chars (h (raw, dem) hp)

/-! ## Covered Data and RW Static Label Anchoring -/

/-- Specification anchoring a data object `lib.data[di]` (such as a `STB_LOCAL` RW CPU-probe static
    omitted from a linked `.symtab`) to its covering `STT_OBJECT` `RawSym` in `objs`. -/
structure CoveredDataSpec where
  /-- Index `di` in `lib.data`. -/
  di : Nat
  /-- Expected `MultiPlacedLib` data symbol name `lib.data[di].sym`. -/
  sym : String
  /-- Slice origin `(oi, si, start, len)` in `objs`. -/
  origin : SliceOrigin
  /-- Expected raw `.symtab` name `sy.rawName` of the covering `STT_OBJECT` symbol. -/
  rawName : String
  /-- Expected demangled name `sy.name` of the covering `STT_OBJECT` symbol. -/
  demangledName : String
  /-- Optional expected `readOnly` flag (`some false` for writable statics). -/
  expectedReadOnly : Option Bool := none
  /-- Optional expected initial byte list `lib.data[di].bytes`. -/
  expectedBytes : Option (List (BitVec 8)) := none
  /-- Optional expected zero-tail byte count `lib.data[di].zeroTail`. -/
  expectedZeroTail : Option Nat := none
  /-- Require `dO ⟨di, _⟩` to be the unique data slice in `(origin.oi, origin.si)`. -/
  soleInSection : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Proposition certifying that `spec` anchors `lib.data[spec.di]` directly to a covering
    `STT_OBJECT` `RawSym` in `objs[spec.origin.oi]` via `dO`. -/
structure DataLabelAnchored (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (dO : Fin lib.data.length → SliceOrigin) (spec : CoveredDataSpec) : Prop where
  in_bounds : spec.di < lib.data.length
  sym_eq : lib.data[spec.di].sym = spec.sym
  origin_eq : dO ⟨spec.di, in_bounds⟩ = spec.origin
  readOnly_ok : ∀ ro, spec.expectedReadOnly = some ro → lib.data[spec.di].readOnly = ro
  bytes_ok : ∀ bs, spec.expectedBytes = some bs → lib.data[spec.di].bytes = bs
  zeroTail_ok : ∀ zt, spec.expectedZeroTail = some zt → lib.data[spec.di].zeroTail = zt
  obj_witness :
    ∃ o sec sy,
      objs[spec.origin.oi]? = some o ∧
      o.sections[spec.origin.si]? = some sec ∧
      sy ∈ o.symbols ∧
      CoversDataSlice spec.origin sy ∧
      sy.rawName = spec.rawName ∧
      sy.name = spec.demangledName ∧
      SymNameDerived spec.sym sy.name o.name ∧
      sec.readOnly = lib.data[spec.di].readOnly
  sole_in_section :
    spec.soleInSection = true →
      ∀ dj : Fin lib.data.length,
        (dO dj).oi = spec.origin.oi → (dO dj).si = spec.origin.si →
        dj = ⟨spec.di, in_bounds⟩

/-- Boolean checker for `DataLabelAnchored`. -/
def checkCoveredDataSpecB (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (dO : Fin lib.data.length → SliceOrigin) (spec : CoveredDataSpec) : Bool :=
  if hdi : spec.di < lib.data.length then
    let d := lib.data[spec.di]
    let o := spec.origin
    (d.sym == spec.sym) &&
    (dO ⟨spec.di, hdi⟩ == o) &&
    (match spec.expectedReadOnly with | none => true | some ro => d.readOnly == ro) &&
    (match spec.expectedBytes with | none => true | some bs => d.bytes == bs) &&
    (match spec.expectedZeroTail with | none => true | some zt => d.zeroTail == zt) &&
    (match objs[o.oi]? with
     | none => false
     | some obj =>
       match obj.sections[o.si]? with
       | none => false
       | some sec =>
         (sec.readOnly == d.readOnly) &&
         obj.symbols.any fun sy =>
           checkCoversDataSliceB o sy &&
           (sy.rawName == spec.rawName) && (sy.name == spec.demangledName) &&
           checkSymNameDerivedB spec.sym sy.name obj.name) &&
    (if spec.soleInSection then
       (List.finRange lib.data.length).all fun dj =>
         if (dO dj).oi == o.oi && (dO dj).si == o.si then dj.val == spec.di else true
     else true)
  else
    false

theorem dataLabelAnchored_of_check {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {dO : Fin lib.data.length → SliceOrigin} {spec : CoveredDataSpec}
    (h : checkCoveredDataSpecB objs lib dO spec = true) :
    DataLabelAnchored objs lib dO spec := by
  unfold checkCoveredDataSpecB at h
  split at h
  case isFalse hnot => exact nomatch h
  case isTrue hdi =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hsym, horig⟩, hro⟩, hbs⟩, hzt⟩, hobj⟩, hsole⟩ := h
    rw [beq_iff_eq] at hsym horig
    refine
      { in_bounds := hdi
        sym_eq := hsym
        origin_eq := horig
        readOnly_ok := ?_
        bytes_ok := ?_
        zeroTail_ok := ?_
        obj_witness := ?_
        sole_in_section := ?_ }
    · intro ro hro_eq; rw [hro_eq] at hro; exact beq_iff_eq.1 hro
    · intro bs hbs_eq; rw [hbs_eq] at hbs; exact beq_iff_eq.1 hbs
    · intro zt hzt_eq; rw [hzt_eq] at hzt; exact beq_iff_eq.1 hzt
    · cases ho : objs[spec.origin.oi]? with
      | none => rw [ho] at hobj; exact nomatch hobj
      | some obj =>
        rw [ho] at hobj; dsimp only at hobj
        cases hs : obj.sections[spec.origin.si]? with
        | none => rw [hs] at hobj; exact nomatch hobj
        | some sec =>
          rw [hs] at hobj; dsimp only at hobj
          rw [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hobj
          obtain ⟨hsec_ro, sy, hsy_mem, hsy_ok⟩ := hobj
          simp only [Bool.and_eq_true] at hsy_ok
          obtain ⟨⟨⟨hcov, hraw⟩, hdem⟩, hder⟩ := hsy_ok
          rw [beq_iff_eq] at hraw hdem
          exact ⟨obj, sec, sy, rfl, hs, hsy_mem,
            (coversDataSlice_iff_check spec.origin sy).1 hcov,
            hraw, hdem,
            symNameDerived_of_check hder,
            hsec_ro⟩
    · intro hsole_t dj hdoi hdsi
      simp only [hsole_t, ↓reduceIte, List.all_eq_true] at hsole
      have h1 := hsole dj (List.mem_finRange dj)
      simp only [hdoi, hdsi, beq_self_eq_true, eq_self, and_self, ↓reduceIte, beq_iff_eq] at h1
      exact Fin.ext h1

/-- Under `LabelsFromObjects`, `lib.resolve mpl spec.sym = mpl.ρ spec.sym` for any anchored data
    slice `spec`. -/
theorem DataLabelAnchored.resolve_eq_rho
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    {spec : CoveredDataSpec} (hd : DataLabelAnchored objs lib dO spec)
    (mpl : MultiPlacement) :
    lib.resolve mpl spec.sym = mpl.ρ spec.sym := by
  have hd_mem : lib.data[spec.di]'hd.in_bounds ∈ lib.data := List.getElem_mem hd.in_bounds
  have hres := hlbl.resolve_data_eq_rho mpl hd_mem
  rwa [hd.sym_eq] at hres

/-- Under `LabelsFromObjects` and `spec.soleInSection = true`, every raw relocation inside kept
    block `bO bi` targeting either an `STB_LOCAL` symbol in `(spec.origin.oi, spec.origin.si)` or
    a non-local symbol whose `Resolves` winner is in `(spec.origin.oi, spec.origin.si)` maps to a
    `RelocEntry` `r ∈ lib.blocks[bi].relocs` with `r.sym = spec.sym`. -/
theorem DataLabelAnchored.sole_reloc_sym_eq
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    {spec : CoveredDataSpec} (hd : DataLabelAnchored objs lib dO spec)
    (hsole_flag : spec.soleInSection = true)
    (bi : Fin lib.blocks.length)
    {bObj : ExtractedObj} {bSec : RawSec} {rr : RawReloc} {sy : RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    {t : Int}
    (htarget :
      ((bO bi).oi = spec.origin.oi ∧ sy.bind = .local ∧ sy.sec = .sec spec.origin.si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Resolves objs sy.rawName spec.origin.oi k spec.origin.si tSym ∧
        t = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = spec.sym ∧ (spec.origin.start : Int) + r.addend = t := by
  let di : Fin lib.data.length := ⟨spec.di, hd.in_bounds⟩
  obtain ⟨dObj, dSec, _, hdobj, hdsec, _⟩ := hd.obj_witness
  have hdO_eq : dO di = spec.origin := hd.origin_eq
  have hdobj' : objs[(dO di).oi]? = some dObj := by rw [hdO_eq]; exact hdobj
  have hdsec' : dObj.sections[(dO di).si]? = some dSec := by rw [hdO_eq]; exact hdsec
  have hsole : ∀ dj : Fin lib.data.length,
      (dO dj).oi = (dO di).oi → (dO dj).si = (dO di).si → dj = di := by
    intro dj h1 h2
    rw [hdO_eq] at h1 h2
    exact hd.sole_in_section hsole_flag dj h1 h2
  have htarget' :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend) := by
    rwa [hdO_eq]
  obtain ⟨r, hr_mem, hoff, hkind, hsym_eq, hadd⟩ :=
    hlbl.sole_data_reloc_sym_eq bi di hbobj hbsec hdobj' hdsec' hsole hrr hlo hhi hsy htarget'
  rw [hdO_eq] at hadd
  have hd_sym : lib.data[di].sym = spec.sym := hd.sym_eq
  rw [hd_sym] at hsym_eq
  exact ⟨r, hr_mem, hoff, hkind, hsym_eq, hadd⟩

/-! ## Unified Gate-A Label Bundle -/

/-- Certificate anchoring all four placed-library label families to `objs : List ExtractedObj`:
    hooks, pruned stubs, and external data (`hookSpecs`, `prunedStubs`, `externData`); uniform
    `allExterns` across `lib.blocks` partitioned into hooks, panics, and `expectedUnhookedCount`
    unhooked externs; bidirectional panic-symbol soundness and completeness under
    `isRustPanicPlus extraPanicDemangled`; and covered RW/RO statics (`dataSpecs`). -/
structure GateALabelsAnchored
    (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (dO : Fin lib.data.length → SliceOrigin)
    (allExterns : List String)
    (hookSpecs : List (String × String))
    (prunedStubs : List String)
    (externData : List String)
    (panicSyms : List String)
    (extraPanicDemangled : List String)
    (isPanic : String → Bool)
    (expectedUnhookedCount : Nat)
    (dataSpecs : List CoveredDataSpec) : Prop where
  blocks_externs : ∀ b ∈ lib.blocks, b.externs = allExterns
  externs_nodup : allExterns.Nodup
  hooks_nodup : (hookSpecs.map Prod.fst).Nodup
  hooks_in_externs : ∀ p ∈ hookSpecs, p.1 ∈ allExterns
  hooks_referenced : ∀ p ∈ hookSpecs, HasRawUndefBranchReloc objs p.1
  hooks_demangled : ∀ p ∈ hookSpecs, NonVacuousUndefSymDemangled objs p.1 p.2
  hooks_not_pruned : ∀ p ∈ hookSpecs, p.1 ∉ prunedStubs
  hooks_not_panic_sym : ∀ p ∈ hookSpecs, p.1 ∉ panicSyms
  hooks_not_isPanic : ∀ p ∈ hookSpecs, isPanic p.1 = false
  pruned_disjoint : ∀ st ∈ prunedStubs, st ∉ hookSpecs.map Prod.fst ∧ st ∉ panicSyms
  extern_data_undef : ∀ ed ∈ externData, NonVacuousUndefSym objs ed
  panics_nodup : panicSyms.Nodup
  panics_in_externs : ∀ p ∈ panicSyms, p ∈ allExterns
  panics_referenced : ∀ p ∈ panicSyms, HasRawUndefBranchReloc objs p
  panics_demangled : ∀ p ∈ panicSyms,
    (∃ o ∈ objs, ∃ sy ∈ o.symbols,
      sy.rawName = p ∧ sy.bind ≠ .local ∧ sy.sec = .undef ∧
      isRustPanicPlus extraPanicDemangled sy.name = true) ∧
    (∀ o ∈ objs, ∀ sy ∈ o.symbols,
      sy.rawName = p → sy.bind ≠ .local →
      sy.sec = .undef ∧ isRustPanicPlus extraPanicDemangled sy.name = true)
  isPanic_iff_mem : ∀ x ∈ allExterns, isPanic x = true ↔ x ∈ panicSyms
  panics_complete : ∀ x ∈ allExterns, ∀ o ∈ objs, ∀ sy ∈ o.symbols,
    sy.rawName = x → sy.bind ≠ .local → sy.sec = .undef →
    isRustPanicPlus extraPanicDemangled sy.name = true → x ∈ panicSyms
  unhooked_count :
    (allExterns.filter fun x =>
      !((hookSpecs.map Prod.fst).contains x || panicSyms.contains x)).length =
      expectedUnhookedCount
  data_anchored : ∀ ds ∈ dataSpecs, DataLabelAnchored objs lib dO ds

/-- Character-list duplicate-freedom check. -/
def listCharNodup : List (List Char) → Bool
  | [] => true
  | x :: xs => !(xs.any (fun y => x == y)) && listCharNodup xs

private theorem nodup_of_listCharNodup :
    ∀ {ss : List String}, listCharNodup (ss.map String.toList) = true → ss.Nodup
  | [], _ => List.Pairwise.nil
  | s :: ss, h => by
    simp only [List.map_cons, listCharNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨?_, nodup_of_listCharNodup h.2⟩
    intro hmem
    have hany : ((ss.map String.toList).any (fun y => s.toList == y)) = true :=
      List.any_eq_true.2 ⟨s.toList, List.mem_map_of_mem hmem, beq_self_eq_true _⟩
    rw [h.1] at hany
    exact nomatch hany

private theorem charAny_eq_contains (xs : List String) (s : String) :
    (xs.map String.toList).any (fun y => s.toList == y) = xs.contains s :=
  (list_contains_eq_any_toList xs s).symm

/-- Kernel-fast boolean checker for `GateALabelsAnchored`. Pre-decodes non-local `.o` symbol names
    and `.undef` branch targets to `List Char` once so `decide +kernel` avoids quadratic UTF-8
    decoding across `objs`. -/
def checkGateALabelsB
    (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (dO : Fin lib.data.length → SliceOrigin)
    (allExterns : List String)
    (hookSpecs : List (String × String))
    (prunedStubs : List String)
    (externData : List String)
    (panicSyms : List String)
    (extraPanicDemangled : List String)
    (isPanic : String → Bool)
    (expectedUnhookedCount : Nat)
    (dataSpecs : List CoveredDataSpec) : Bool :=
  let nls := collectNonLocalSymChars objs
  let brs := collectUndefBranchRawChars objs
  let allExtC := allExterns.map String.toList
  let hookKeys := hookSpecs.map Prod.fst
  let hookKeysC := hookKeys.map String.toList
  let prunedC := prunedStubs.map String.toList
  let panicC := panicSyms.map String.toList
  let extraC := extraPanicDemangled.map String.toList
  let inList (cs : List (List Char)) (x : List Char) : Bool := cs.any (fun y => x == y)
  (lib.blocks.all fun b => b.externs == allExterns) &&
  listCharNodup allExtC &&
  listCharNodup hookKeysC &&
  (hookSpecs.all fun (k, dem) =>
    let kc := k.toList
    inList allExtC kc &&
    inList brs kc &&
    checkNonVacuousUndefDemangledChars nls kc dem.toList &&
    !(inList prunedC kc) &&
    !(inList panicC kc) &&
    !(isPanic k)) &&
  (prunedC.all fun stc => !(inList hookKeysC stc) && !(inList panicC stc)) &&
  (externData.all fun ed => checkNonVacuousUndefChars nls ed.toList) &&
  listCharNodup panicC &&
  (panicSyms.all fun p =>
    let pc := p.toList
    inList allExtC pc &&
    inList brs pc &&
    nls.any (fun (r, n, u) => r == pc && u && isRustPanicPlusChars extraC n) &&
    nls.all (fun (r, n, u) => if r == pc then u && isRustPanicPlusChars extraC n else true)) &&
  (allExterns.all fun x => isPanic x == inList panicC x.toList) &&
  (nls.all fun (r, n, u) =>
    if u && isRustPanicPlusChars extraC n && inList allExtC r then
      inList panicC r
    else
      true) &&
  ((allExtC.filter fun xc => !(inList hookKeysC xc || inList panicC xc)).length ==
    expectedUnhookedCount) &&
  (dataSpecs.all fun ds => checkCoveredDataSpecB objs lib dO ds)

private theorem filter_allExtC_length (allExterns hookKeys panicSyms : List String) :
    ((allExterns.map String.toList).filter fun xc =>
      !((hookKeys.map String.toList).any (fun y => xc == y) ||
        (panicSyms.map String.toList).any (fun y => xc == y))).length =
    (allExterns.filter fun x => !(hookKeys.contains x || panicSyms.contains x)).length := by
  induction allExterns with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.filter_cons, charAny_eq_contains]
    cases (hookKeys.contains x || panicSyms.contains x) <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.length_cons, ih]

/-- Soundness of `checkGateALabelsB`: reduces `GateALabelsAnchored` to a single `decide +kernel`
    equality. -/
theorem gateALabels_of_check
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {dO : Fin lib.data.length → SliceOrigin}
    {allExterns : List String}
    {hookSpecs : List (String × String)}
    {prunedStubs externData panicSyms extraPanicDemangled : List String}
    {isPanic : String → Bool}
    {expectedUnhookedCount : Nat}
    {dataSpecs : List CoveredDataSpec}
    (h : checkGateALabelsB objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs = true) :
    GateALabelsAnchored objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs := by
  unfold checkGateALabelsB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hblks, hext_nd⟩, hhk_nd⟩, hhk_all⟩, hpruned⟩, hed⟩, hpan_nd⟩, hpan_all⟩,
    hisPanic⟩, hpan_comp⟩, hunhooked⟩, hdata⟩ := h
  rw [List.all_eq_true] at hblks hhk_all hpruned hed hpan_all hisPanic hpan_comp hdata
  have inList_iff : ∀ (xs : List String) (s : String),
      ((xs.map String.toList).any (fun y => s.toList == y) = true) ↔ s ∈ xs := by
    intro xs s
    rw [charAny_eq_contains, List.contains_iff_mem]
  have inList_false_iff : ∀ (xs : List String) (s : String),
      ((!(xs.map String.toList).any (fun y => s.toList == y)) = true) ↔ s ∉ xs := by
    intro xs s
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, inList_iff]
  have brs_iff : ∀ (s : String),
      ((collectUndefBranchRawChars objs).any (fun y => s.toList == y) = true) ↔
        HasRawUndefBranchReloc objs s := by
    intro s
    rw [List.any_eq_true]
    constructor
    · rintro ⟨y, hy, heq⟩
      rw [beq_iff_eq] at heq; subst heq
      exact mem_collectUndefBranchRawChars.1 hy
    · intro hbr
      exact ⟨s.toList, mem_collectUndefBranchRawChars.2 hbr, beq_self_eq_true _⟩
  refine
    { blocks_externs := fun b hb => beq_iff_eq.1 (hblks b hb)
      externs_nodup := nodup_of_listCharNodup hext_nd
      hooks_nodup := nodup_of_listCharNodup hhk_nd
      hooks_in_externs := ?_
      hooks_referenced := ?_
      hooks_demangled := ?_
      hooks_not_pruned := ?_
      hooks_not_panic_sym := ?_
      hooks_not_isPanic := ?_
      pruned_disjoint := ?_
      extern_data_undef := fun ed hed_mem => nonVacuousUndef_of_chars (hed ed hed_mem)
      panics_nodup := nodup_of_listCharNodup hpan_nd
      panics_in_externs := ?_
      panics_referenced := ?_
      panics_demangled := ?_
      isPanic_iff_mem := ?_
      panics_complete := ?_
      unhooked_count := ?_
      data_anchored := fun ds hds => dataLabelAnchored_of_check (hdata ds hds) }
  · rintro ⟨k, dem⟩ hp
    have h1 := hhk_all (k, dem) hp
    simp only [Bool.and_eq_true] at h1
    exact (inList_iff allExterns k).1 h1.1.1.1.1.1
  · rintro ⟨k, dem⟩ hp
    have h1 := hhk_all (k, dem) hp
    simp only [Bool.and_eq_true] at h1
    exact (brs_iff k).1 h1.1.1.1.1.2
  · rintro ⟨k, dem⟩ hp
    have h1 := hhk_all (k, dem) hp
    simp only [Bool.and_eq_true] at h1
    exact nonVacuousUndefDemangled_of_chars h1.1.1.1.2
  · rintro ⟨k, dem⟩ hp
    have h1 := hhk_all (k, dem) hp
    simp only [Bool.and_eq_true] at h1
    exact (inList_false_iff prunedStubs k).1 h1.1.1.2
  · rintro ⟨k, dem⟩ hp
    have h1 := hhk_all (k, dem) hp
    simp only [Bool.and_eq_true] at h1
    exact (inList_false_iff panicSyms k).1 h1.1.2
  · rintro ⟨k, dem⟩ hp
    have h1 := hhk_all (k, dem) hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
    exact h1.2
  · intro st hst
    have h1 := hpruned st.toList (List.mem_map_of_mem hst)
    simp only [Bool.and_eq_true] at h1
    exact ⟨(inList_false_iff (hookSpecs.map Prod.fst) st).1 h1.1,
      (inList_false_iff panicSyms st).1 h1.2⟩
  · intro p hp
    have h1 := hpan_all p hp
    simp only [Bool.and_eq_true] at h1
    exact (inList_iff allExterns p).1 h1.1.1.1
  · intro p hp
    have h1 := hpan_all p hp
    simp only [Bool.and_eq_true] at h1
    exact (brs_iff p).1 h1.1.1.2
  · intro p hp
    have h1 := hpan_all p hp
    simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h1
    obtain ⟨⟨_, ⟨r0, n0, u0⟩, hmem0, hwit⟩, hall⟩ := h1
    simp only [beq_iff_eq] at hwit
    obtain ⟨⟨rfl, rfl⟩, hpan0⟩ := hwit
    obtain ⟨o0, ho0, sy0, hsy0, hbind0, hraw0, hname0, hu0⟩ := mem_collectNonLocalSymChars.1 hmem0
    rw [beq_iff_eq] at hu0
    have hpan0' : isRustPanicPlus extraPanicDemangled sy0.name = true := by
      rw [isRustPanicPlus_eq_chars, hname0]; exact hpan0
    refine ⟨⟨o0, ho0, sy0, hsy0, String.ext_iff.2 hraw0, hbind0, hu0, hpan0'⟩, ?_⟩
    intro o ho sy hsy hraw hbind
    have hmem : (sy.rawName.toList, sy.name.toList, sy.sec == .undef) ∈
        collectNonLocalSymChars objs :=
      mem_collectNonLocalSymChars.2 ⟨o, ho, sy, hsy, hbind, rfl, rfl, rfl⟩
    have hall1 := hall _ hmem
    simp only [hraw, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hall1
    refine ⟨hall1.1, ?_⟩
    rw [isRustPanicPlus_eq_chars]
    exact hall1.2
  · intro x hx
    have h1 := hisPanic x hx
    rw [beq_iff_eq] at h1
    rw [h1]
    exact inList_iff panicSyms x
  · intro x hx o ho sy hsy hraw hbind hsec hpan
    have hmem : (sy.rawName.toList, sy.name.toList, sy.sec == .undef) ∈
        collectNonLocalSymChars objs :=
      mem_collectNonLocalSymChars.2 ⟨o, ho, sy, hsy, hbind, rfl, rfl, rfl⟩
    have h1 := hpan_comp _ hmem
    have hu : (sy.sec == .undef) = true := by simpa [beq_iff_eq] using hsec
    have hpanC : isRustPanicPlusChars (extraPanicDemangled.map String.toList) sy.name.toList = true := by
      rwa [← isRustPanicPlus_eq_chars]
    have hinExt : ((allExterns.map String.toList).any (fun y => x.toList == y)) = true :=
      (inList_iff allExterns x).2 hx
    rw [hraw] at h1
    simp only [hu, hpanC, hinExt, and_self, ↓reduceIte] at h1
    exact (inList_iff panicSyms x).1 h1
  · rw [beq_iff_eq] at hunhooked
    rw [← filter_allExtC_length]
    exact hunhooked

/-! ## Elimination Theorems for `GateALabelsAnchored` -/

private theorem lookup_isSome_mem_fst {α : Type} {xs : List (String × α)} {k : String} {v : α}
    (h : lookup k xs = some v) : k ∈ xs.map Prod.fst := by
  unfold lookup at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨a, _⟩, hf, _⟩ := h
  have hp := List.find?_some hf
  dsimp only at hp
  have heq : a = k := beq_iff_eq.1 hp
  subst heq
  exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)

/-- Because `GateALabelsAnchored` proves `isPanic k = false` on every `(k, _) ∈ hookSpecs`,
    hook-first dispatch and panic-first dispatch (`Rust.withPanics`-style) agree for
    any hook table whose keys lie in `hookSpecs.map Prod.fst`. -/
theorem GateALabelsAnchored.hookFirst_eq_panicFirst
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {dO : Fin lib.data.length → SliceOrigin}
    {allExterns : List String} {hookSpecs : List (String × String)}
    {prunedStubs externData panicSyms extraPanicDemangled : List String}
    {isPanic : String → Bool} {expectedUnhookedCount : Nat}
    {dataSpecs : List CoveredDataSpec}
    (hgate : GateALabelsAnchored objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs)
    {α : Type} (hooks : List (String × α))
    (hhooks : ∀ p ∈ hooks, p.1 ∈ hookSpecs.map Prod.fst)
    (panicVal : α) (x : String) :
    (match lookup x hooks with
     | some v => some v
     | none => if isPanic x then some panicVal else none) =
    (if isPanic x then some panicVal else lookup x hooks) := by
  cases hlk : lookup x hooks with
  | none =>
    cases isPanic x <;> rfl
  | some v =>
    have hx_fst : x ∈ hooks.map Prod.fst := lookup_isSome_mem_fst hlk
    obtain ⟨⟨k, _⟩, hk_mem, rfl⟩ := List.mem_map.1 hx_fst
    have hk_spec : k ∈ hookSpecs.map Prod.fst := hhooks _ hk_mem
    obtain ⟨⟨k', dem⟩, hspec_mem, hkeq⟩ := List.mem_map.1 hk_spec
    dsimp only at hkeq; subst hkeq
    have hnot : isPanic k' = false := hgate.hooks_not_isPanic (k', dem) hspec_mem
    simp [hnot]

/-- Combining `GateALabelsAnchored` with `LabelsFromObjects` certifies that every `x ∈ allExterns`
    in a non-empty `lib.blocks` is disjoint from all block and data symbols of `lib` and comes from
    a `.call26`/`.jump26` relocation in `lib.blocks`. -/
theorem GateALabelsAnchored.allExterns_not_internal
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    {allExterns : List String} {hookSpecs : List (String × String)}
    {prunedStubs externData panicSyms extraPanicDemangled : List String}
    {isPanic : String → Bool} {expectedUnhookedCount : Nat}
    {dataSpecs : List CoveredDataSpec}
    (hgate : GateALabelsAnchored objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs)
    (hne : lib.blocks ≠ []) {x : String} (hx : x ∈ allExterns) :
    lookupBlockSym x lib.blocks = none ∧ x ∉ lib.data.map (·.sym) ∧
      ∃ b' ∈ lib.blocks, ∃ r ∈ b'.relocs, (r.kind = .call26 ∨ r.kind = .jump26) ∧ r.sym = x := by
  have hb0 : ∃ b0, b0 ∈ lib.blocks := List.exists_mem_of_ne_nil lib.blocks hne
  obtain ⟨b0, hb0⟩ := hb0
  have hext0 : b0.externs = allExterns := hgate.blocks_externs b0 hb0
  have hx0 : x ∈ b0.externs := hext0 ▸ hx
  obtain ⟨hblk_none, hdata_ne, hrel⟩ := (hlbl.externs_valid b0 hb0).2.1 x hx0
  refine ⟨hblk_none, ?_, hrel⟩
  intro hmem
  obtain ⟨d, hd, hdsym⟩ := List.mem_map.1 hmem
  exact hdata_ne d hd hdsym

private theorem findSome_eq_of_unique_match {α β : Type} {xs ys : List α} {f : α → Option β}
    {a : α} {v : β}
    (hxs : a ∈ xs) (hys : a ∈ ys) (hfa : f a = some v)
    (hother_xs : ∀ x ∈ xs, x ≠ a → f x = none)
    (hother_ys : ∀ y ∈ ys, y ≠ a → f y = none) :
    xs.findSome? f = ys.findSome? f := by
  have eval_list : ∀ {zs : List α}, a ∈ zs → (∀ z ∈ zs, z ≠ a → f z = none) →
      zs.findSome? f = some v := by
    intro zs hmem hoth
    induction zs with
    | nil => cases hmem
    | cons z rest ih =>
      simp only [List.findSome?_cons]
      by_cases hza : z = a
      · subst hza; simp [hfa]
      · rw [hoth z List.mem_cons_self hza]
        rcases List.mem_cons.1 hmem with rfl | hrest
        · exact absurd rfl hza
        · exact ih hrest (fun w hw => hoth w (List.mem_cons_of_mem _ hw))
  rw [eval_list hxs hother_xs, eval_list hys hother_ys]

private theorem findSome_eq_none_of_all_none {α β : Type} {xs : List α} {f : α → Option β}
    (h : ∀ x ∈ xs, f x = none) : xs.findSome? f = none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.findSome?_cons, h x List.mem_cons_self]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem nodup_map_inj_on {α β : Type} {xs : List α} {g : α → β}
    (hnd : (xs.map g).Nodup) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs) (heq : g x = g y) :
    x = y := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 hx with rfl | hx_r
    · rcases List.mem_cons.1 hy with rfl | hy_r
      · rfl
      · exfalso; exact hnd.1 ⟨y, hy_r, heq.symm⟩
    · rcases List.mem_cons.1 hy with rfl | hy_r
      · exfalso; exact hnd.1 ⟨x, hx_r, heq⟩
      · exact ih hnd.2 hx_r hy_r

/-- Under `LabelsFromObjects` and `GateALabelsAnchored`, when `X` assigns `none` to all unhooked
    externs (`x ∉ hookKeys` and `x ∉ panicSyms`) and `mpl.ρ` is duplicate-free on the active externs
    `hookKeys ++ panicSyms`, `(lib.blockProgram mpl i X (fun _ => none) svc).externAt? pc` reduces
    at every `pc` to scanning only `hookKeys ++ panicSyms`, even when `--gc-sections` maps unused
    `unhookedExterns` to shared dummy addresses such as `0#64`. -/
theorem GateALabelsAnchored.externAt?_blockProgram_active
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    {allExterns : List String} {hookSpecs : List (String × String)}
    {prunedStubs externData panicSyms extraPanicDemangled : List String}
    {isPanic : String → Bool} {expectedUnhookedCount : Nat}
    {dataSpecs : List CoveredDataSpec}
    (hgate : GateALabelsAnchored objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs)
    (mpl : MultiPlacement) {i : Nat} (hi : i < lib.blocks.length)
    (X : String → Option (State → State))
    (hX_inactive : ∀ x ∈ allExterns, x ∉ hookSpecs.map Prod.fst → x ∉ panicSyms → X x = none)
    (hactive_nodup : (((hookSpecs.map Prod.fst) ++ panicSyms).map mpl.ρ).Nodup)
    (svc : State → State := Syscall.standard) (pc : BitVec 64) :
    (lib.blockProgram mpl i X (fun _ => none) svc).externAt? pc =
      ((hookSpecs.map Prod.fst) ++ panicSyms).findSome? fun e =>
        if mpl.ρ e == pc then X e else none := by
  rw [hlbl.externAt?_blockProgram mpl hi X svc pc]
  have hb_ext : lib.blocks[i].externs = allExterns :=
    hgate.blocks_externs lib.blocks[i] (List.getElem_mem hi)
  rw [hb_ext]
  let active := (hookSpecs.map Prod.fst) ++ panicSyms
  let f (e : String) : Option (State → State) := if mpl.ρ e == pc then X e else none
  have hactive_sub : ∀ e ∈ active, e ∈ allExterns := by
    intro e he
    rcases List.mem_append.1 he with hhk | hpan
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hhk
      exact hgate.hooks_in_externs p hp
    · exact hgate.panics_in_externs e hpan
  by_cases hex : ∃ a ∈ active, ∃ v, f a = some v
  · obtain ⟨a, ha_act, v, hfa⟩ := hex
    have hpc_eq : mpl.ρ a = pc := by
      dsimp only [f] at hfa
      by_cases h1 : mpl.ρ a == pc
      · exact beq_iff_eq.1 h1
      · simp [h1] at hfa
    apply findSome_eq_of_unique_match (hactive_sub a ha_act) ha_act hfa
    · intro x hx hne
      dsimp only [f]
      by_cases hx_act : x ∈ active
      · have hrho_ne : mpl.ρ x ≠ pc := by
          intro hrho_eq
          exact hne (nodup_map_inj_on hactive_nodup hx_act ha_act (hrho_eq.trans hpc_eq.symm))
        have hbeq : (mpl.ρ x == pc) = false := beq_eq_false_iff_ne.2 hrho_ne
        simp [hbeq]
      · have hnhk : x ∉ hookSpecs.map Prod.fst := fun h => hx_act (List.mem_append_left _ h)
        have hnpan : x ∉ panicSyms := fun h => hx_act (List.mem_append_right _ h)
        rw [hX_inactive x hx hnhk hnpan]
        simp
    · intro y hy hne
      dsimp only [f]
      have hrho_ne : mpl.ρ y ≠ pc := by
        intro hrho_eq
        exact hne (nodup_map_inj_on hactive_nodup hy ha_act (hrho_eq.trans hpc_eq.symm))
      have hbeq : (mpl.ρ y == pc) = false := beq_eq_false_iff_ne.2 hrho_ne
      simp [hbeq]
  · have hall_act : ∀ y ∈ active, f y = none := by
      intro y hy
      cases hfy : f y with
      | none => rfl
      | some v => exact absurd ⟨y, hy, v, hfy⟩ hex
    have hall_ext : ∀ x ∈ allExterns, f x = none := by
      intro x hx
      by_cases hx_act : x ∈ active
      · exact hall_act x hx_act
      · dsimp only [f]
        have hnhk : x ∉ hookSpecs.map Prod.fst := fun h => hx_act (List.mem_append_left _ h)
        have hnpan : x ∉ panicSyms := fun h => hx_act (List.mem_append_right _ h)
        rw [hX_inactive x hx hnhk hnpan]
        simp
    rw [findSome_eq_none_of_all_none hall_ext, findSome_eq_none_of_all_none hall_act]

/-- Pointwise evaluation of `externAt?` at `mpl.ρ e` for any active extern
    `e ∈ hookSpecs.map Prod.fst ++ panicSyms`. -/
theorem GateALabelsAnchored.externAt?_at_active
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    {allExterns : List String} {hookSpecs : List (String × String)}
    {prunedStubs externData panicSyms extraPanicDemangled : List String}
    {isPanic : String → Bool} {expectedUnhookedCount : Nat}
    {dataSpecs : List CoveredDataSpec}
    (hgate : GateALabelsAnchored objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs)
    (mpl : MultiPlacement) {i : Nat} (hi : i < lib.blocks.length)
    (X : String → Option (State → State))
    (hX_inactive : ∀ x ∈ allExterns, x ∉ hookSpecs.map Prod.fst → x ∉ panicSyms → X x = none)
    (hactive_nodup : (((hookSpecs.map Prod.fst) ++ panicSyms).map mpl.ρ).Nodup)
    {e : String} (he : e ∈ (hookSpecs.map Prod.fst) ++ panicSyms)
    (svc : State → State := Syscall.standard) :
    (lib.blockProgram mpl i X (fun _ => none) svc).externAt? (mpl.ρ e) = X e := by
  rw [hgate.externAt?_blockProgram_active hlbl mpl hi X hX_inactive hactive_nodup svc (mpl.ρ e)]
  let active := (hookSpecs.map Prod.fst) ++ panicSyms
  let f (y : String) : Option (State → State) := if mpl.ρ y == mpl.ρ e then X y else none
  have hother : ∀ y ∈ active, y ≠ e → f y = none := by
    intro y hy hne
    dsimp only [f]
    have hrho_ne : mpl.ρ y ≠ mpl.ρ e := fun h =>
      hne (nodup_map_inj_on hactive_nodup hy he h)
    simp [beq_eq_false_iff_ne.2 hrho_ne]
  cases hXe : X e with
  | none =>
    apply findSome_eq_none_of_all_none
    intro y hy
    by_cases hye : y = e
    · rw [hye]; show (if mpl.ρ e == mpl.ρ e then X e else none) = none; simp [hXe]
    · exact hother y hy hye
  | some v =>
    have hfe : f e = some v := by show (if mpl.ρ e == mpl.ρ e then X e else none) = some v; simp [hXe]
    have heq := findSome_eq_of_unique_match (ys := [e]) he (List.mem_singleton.2 rfl) hfe hother
      (fun y hy hne => absurd (List.mem_singleton.1 hy) hne)
    simpa [f, hXe] using heq

/-- Pointwise evaluation of `externAt?` outside `active.map mpl.ρ`. -/
theorem GateALabelsAnchored.externAt?_outside_active
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    {allExterns : List String} {hookSpecs : List (String × String)}
    {prunedStubs externData panicSyms extraPanicDemangled : List String}
    {isPanic : String → Bool} {expectedUnhookedCount : Nat}
    {dataSpecs : List CoveredDataSpec}
    (hgate : GateALabelsAnchored objs lib dO allExterns hookSpecs prunedStubs externData panicSyms
      extraPanicDemangled isPanic expectedUnhookedCount dataSpecs)
    (mpl : MultiPlacement) {i : Nat} (hi : i < lib.blocks.length)
    (X : String → Option (State → State))
    (hX_inactive : ∀ x ∈ allExterns, x ∉ hookSpecs.map Prod.fst → x ∉ panicSyms → X x = none)
    (hactive_nodup : (((hookSpecs.map Prod.fst) ++ panicSyms).map mpl.ρ).Nodup)
    {pc : BitVec 64} (hout : ∀ e ∈ (hookSpecs.map Prod.fst) ++ panicSyms, mpl.ρ e ≠ pc)
    (svc : State → State := Syscall.standard) :
    (lib.blockProgram mpl i X (fun _ => none) svc).externAt? pc = none := by
  rw [hgate.externAt?_blockProgram_active hlbl mpl hi X hX_inactive hactive_nodup svc pc]
  apply findSome_eq_none_of_all_none
  intro e he
  simp [beq_eq_false_iff_ne.2 (hout e he)]

end Arm64.Obj

end
