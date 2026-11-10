/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.Object.Labels
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.Multi

/-!
# Interned Certificate Checker for `LabelsFromObjects`

Defines `IdxTree`-backed interned mirrors of `ExtractedObj` and `MultiPlacedLib`, split boolean
certificates, and the `gen_labels_from_objects` command elaborator for proving `LabelsFromObjects`
by kernel reduction (`rfl_kernel`). Symbol names are mapped to indices in a sorted `IdxTree String`,
slices are grouped per `(oi, si)` section for single-pass byte verification and linear disjointness,
and non-local symbol resolution conservatively requires a unique `STB_GLOBAL` or `STB_WEAK`
definition with pairwise-distinct COMDAT group signatures.
-/

set_option autoImplicit false

@[expose] public section

namespace Arm64.Obj.LabelsInterned

open ProofLib.ProgramReflection

/-! ## Tree-backed slice origins and interned symbol lookup -/

instance {α : Type} : Inhabited (IdxTree α) := ⟨.empty⟩

/-- Look up slice origin `i` in $O(\log N)$ steps from a balanced `IdxTree SliceOrigin`. -/
def originAt (t : IdxTree SliceOrigin) {n : Nat} (i : Fin n) : SliceOrigin :=
  (t.get? i.1).getD { oi := 0, si := 0, start := 0, len := 0 }

/-- Look up interned string `id` in `namesTree` (`""` out of bounds). -/
def symAt (namesTree : IdxTree String) (id : Nat) : String :=
  (namesTree.get? id).getD ""

/-- Look up interned `List Char` `id` in `charsTree` (`[]` out of bounds). -/
def charsAt (charsTree : IdxTree (List Char)) (id : Nat) : List Char :=
  (charsTree.get? id).getD []

theorem originAt_eq_getElem {t : IdxTree SliceOrigin} {n : Nat}
    (hsz : t.size? = some n) (i : Fin n) :
    originAt t i = t.toList[i.1]'(by rw [IdxTree.length_toList_of_size? hsz]; exact i.2) := by
  have hlen : t.toList.length = n := IdxTree.length_toList_of_size? hsz
  unfold originAt
  rw [IdxTree.get?_eq_getElem? hsz i.1, List.getElem?_eq_getElem (hlen ▸ i.2)]
  rfl

theorem symAt_eq_getElem {namesTree : IdxTree String} {N : Nat}
    (hsz : namesTree.size? = some N) {id : Nat} (hid : id < N) :
    symAt namesTree id =
      namesTree.toList[id]'(by rw [IdxTree.length_toList_of_size? hsz]; exact hid) := by
  have hlen : namesTree.toList.length = N := IdxTree.length_toList_of_size? hsz
  unfold symAt
  rw [IdxTree.get?_eq_getElem? hsz id, List.getElem?_eq_getElem (hlen ▸ hid)]
  rfl

theorem symAt_inj {namesTree : IdxTree String} {N : Nat}
    (hsz : namesTree.size? = some N) (hnd : namesTree.toList.Nodup)
    {i j : Nat} (hi : i < N) (hj : j < N)
    (heq : symAt namesTree i = symAt namesTree j) : i = j := by
  rw [symAt_eq_getElem hsz hi, symAt_eq_getElem hsz hj] at heq
  exact List.nodup_iff_eq_of_getElem_eq.1 hnd i j _ _ heq

theorem symAt_zero_eq_empty {namesTree : IdxTree String}
    (h0 : namesTree.get? 0 = some "") : symAt namesTree 0 = "" := by
  unfold symAt; rw [h0]; rfl

theorem symAt_ne_empty_iff {namesTree : IdxTree String} {N : Nat}
    (hsz : namesTree.size? = some N) (hnd : namesTree.toList.Nodup)
    (h0 : namesTree.get? 0 = some "") {id : Nat} (hid : id < N) :
    symAt namesTree id ≠ "" ↔ id ≠ 0 := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) hid
  constructor
  · intro hne heq
    subst heq
    exact hne (symAt_zero_eq_empty h0)
  · intro hne heq
    rw [← symAt_zero_eq_empty h0] at heq
    exact hne (symAt_inj hsz hnd hid hN heq)

theorem symAt_eq_ofList_charsAt {namesTree : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : namesTree.size? = some N) (hcsz : charsTree.size? = some N)
    (heq : namesTree.toList = charsTree.toList.map String.ofList) {id : Nat} (hid : id < N) :
    symAt namesTree id = String.ofList (charsAt charsTree id) := by
  have hclen : charsTree.toList.length = N := IdxTree.length_toList_of_size? hcsz
  rw [symAt_eq_getElem hsz hid]
  unfold charsAt
  rw [IdxTree.get?_eq_getElem? hcsz id, List.getElem?_eq_getElem (hclen ▸ hid)]
  dsimp only [Option.getD]
  simp only [heq, List.getElem_map]

/-! ## Interned mirrors of `ExtractedObj` and `MultiPlacedLib` -/

/-- Interned `RawSym`: `rawId` and `nameId` index `namesTree`; `derivedId` stores the index of
    `name ++ " [" ++ obj.name ++ "]"` whenever `sec ≠ .undef ∧ rawId ≠ 0` (`0` otherwise). -/
structure ISym where
  rawId : Nat
  nameId : Nat
  derivedId : Nat := 0
  bind : SymBind
  kind : SymKind
  sec : SymSec
  value : Nat := 0
  size : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def ISym.toRawSym (names : IdxTree String) (s : ISym) : RawSym :=
  { rawName := symAt names s.rawId
    name := symAt names s.nameId
    bind := s.bind
    kind := s.kind
    sec := s.sec
    value := s.value
    size := s.size }

/-- Interned `RawSec` sharing the exact `bytes` and `relocs` expressions of the underlying
    `RawSec`. -/
structure ISec where
  nameId : Nat
  isExec : Bool
  readOnly : Bool
  isNobits : Bool
  isTls : Bool
  align : Nat
  size : Nat
  bytes : List (BitVec 8)
  relocs : List RawReloc
  deriving Inhabited

def ISec.toRawSec (names : IdxTree String) (s : ISec) : RawSec :=
  { name := symAt names s.nameId
    isExec := s.isExec
    readOnly := s.readOnly
    isNobits := s.isNobits
    isTls := s.isTls
    align := s.align
    size := s.size
    bytes := s.bytes
    relocs := s.relocs }

/-- Interned `ExtractedObj` with balanced `IdxTree` section and symbol tables (COMDAT `groups`
    are carried verbatim). -/
structure IObj where
  nameId : Nat
  nameChars : List Char
  sections : IdxTree ISec
  symbols : IdxTree ISym
  groups : List RawGroup := []
  deriving Inhabited

def IObj.toExtractedObj (names : IdxTree String) (o : IObj) : ExtractedObj :=
  { name := symAt names o.nameId
    sections := o.sections.toList.map (ISec.toRawSec names)
    symbols := o.symbols.toList.map (ISym.toRawSym names)
    groups := o.groups }

/-- Interned `RelocEntry` carrying an optional `tlsSymWit` index for $O(\log S)$ TLS target
    verification (`tlsSymWit` is erased by `toEntry`). -/
structure IReloc where
  off : Nat
  kind : RelocKind
  sym : Nat
  addend : Int := 0
  localSym : Bool := false
  tlsSymWit : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def IReloc.toEntry (names : IdxTree String) (r : IReloc) : RelocEntry :=
  { off := r.off
    kind := r.kind
    sym := symAt names r.sym
    addend := r.addend
    localSym := r.localSym }

/-- Interned `CodeBlock`: `symWits` pairs each `(symId, off, wit?)` (`wit? = some k` indexes
    `obj.symbols` in $O(\log S)$; `none` uses `rawClaimed`). `externsOverride = none` reuses the
    library-wide `commonExterns` list so string projection happens once instead of $B$ times. -/
structure IBlock where
  code : List (BitVec 8)
  align : Nat := 4
  symbols : List (Nat × Nat × Option Nat) := []
  relocs : IdxTree IReloc := .empty
  externsOverride : Option (List Nat) := none
  weakRefsOverride : Option (List Nat) := none
  relocPerm : List Nat := []
  relocInvPerm : IdxTree Nat := .empty
  deriving Inhabited

def IBlock.externIds (commonExterns : List Nat) (b : IBlock) : List Nat :=
  b.externsOverride.getD commonExterns

def IBlock.weakRefIds (commonWeakRefs : List Nat) (b : IBlock) : List Nat :=
  b.weakRefsOverride.getD commonWeakRefs

def IBlock.toCodeBlock (names : IdxTree String) (commonExt commonWeak : List String)
    (b : IBlock) : CodeBlock :=
  { code := b.code
    align := b.align
    symbols := b.symbols.map fun (s, off, _) => (symAt names s, off)
    relocs := b.relocs.toList.map (IReloc.toEntry names)
    externs := match b.externsOverride with
      | none => commonExt
      | some ids => ids.map (symAt names)
    weakRefs := match b.weakRefsOverride with
      | none => commonWeak
      | some ids => ids.map (symAt names) }

theorem IBlock.toCodeBlock_externs (names : IdxTree String) (commonExtIds : List Nat)
    (commonWeak : List String) (b : IBlock) :
    (b.toCodeBlock names (commonExtIds.map (symAt names)) commonWeak).externs =
      (b.externIds commonExtIds).map (symAt names) := by
  unfold toCodeBlock externIds
  cases b.externsOverride <;> rfl

theorem IBlock.toCodeBlock_weakRefs (names : IdxTree String) (commonExt : List String)
    (commonWeakIds : List Nat) (b : IBlock) :
    (b.toCodeBlock names commonExt (commonWeakIds.map (symAt names))).weakRefs =
      (b.weakRefIds commonWeakIds).map (symAt names) := by
  unfold toCodeBlock weakRefIds
  cases b.weakRefsOverride <;> rfl

/-- Interned `SymDataInfo` carrying `covWit?` (`some k` indexes a covering `ISym` in `obj.symbols`;
    `none` certifies no covering symbol exists and `d.sym` is unclaimed) and relocation permutation
    certificates. -/
structure IData where
  sym : Nat
  align : Nat := 1
  readOnly : Bool := true
  bytes : List (BitVec 8) := []
  zeroTail : Nat := 0
  relocs : IdxTree IReloc := .empty
  covWit : Option Nat := none
  relocPerm : List Nat := []
  relocInvPerm : IdxTree Nat := .empty
  deriving Inhabited

def IData.toSymDataInfo (names : IdxTree String) (d : IData) : SymDataInfo :=
  { sym := symAt names d.sym
    align := d.align
    readOnly := d.readOnly
    bytes := d.bytes
    zeroTail := d.zeroTail
    relocs := d.relocs.toList.map (IReloc.toEntry names) }

/-- Interned `MultiPlacedLib` with balanced `IdxTree` block and data tables. -/
structure IMultiLib where
  name : Nat
  commonExterns : List Nat := []
  commonWeakRefs : List Nat := []
  blocks : IdxTree IBlock
  data : IdxTree IData
  exports : List Nat := []
  exportSyms : List (Nat × Nat) := []
  deriving Inhabited

def IMultiLib.toMultiPlacedLib (names : IdxTree String) (L : IMultiLib) : MultiPlacedLib :=
  let commonExt := L.commonExterns.map (symAt names)
  let commonWeak := L.commonWeakRefs.map (symAt names)
  { name := symAt names L.name
    blocks := L.blocks.toList.map (IBlock.toCodeBlock names commonExt commonWeak)
    data := L.data.toList.map (IData.toSymDataInfo names)
    exports := L.exports.map (symAt names)
    exportSyms := L.exportSyms.map fun (a, b) => (symAt names a, symAt names b) }

/-! ## Left-inverse symbol role table (`SymRole`) -/

/-- Role assigned to interned symbol `id` in `lib`:
    - `blockSym bi j off`: `lib.blocks[bi].symbols[j] = (names[id], off)`;
    - `dataSym di`: `lib.data[di].sym = names[id]`;
    - `other`: neither a block symbol nor a data symbol. -/
inductive SymRole where
  | other
  | blockSym (bi j off : Nat)
  | dataSym (di : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Verify all block symbols and data symbols are in-bounds and invert `symRole`. -/
def checkSymRolesB (N : Nat) (L : IMultiLib) (symRole : IdxTree SymRole) : Bool :=
  (symRole.size? == some N) && L.blocks.size?.isSome && L.data.size?.isSome &&
  IdxTree.allIdx (fun bi b =>
    (List.range b.symbols.length).all fun j =>
      match b.symbols[j]? with
      | none => false
      | some (s, off, _) =>
        decide (s < N) && (symRole.get? s == some (.blockSym bi j off))) 0 L.blocks &&
  IdxTree.allIdx (fun di d =>
    decide (d.sym < N) && (symRole.get? d.sym == some (.dataSym di))) 0 L.data &&
  IdxTree.allIdx (fun id role =>
    match role with
    | .other => true
    | .blockSym bi j off =>
      match L.blocks.get? bi with
      | none => false
      | some b =>
        match b.symbols[j]? with
        | some (s, off', _) => (s == id) && (off' == off)
        | none => false
    | .dataSym di =>
      match L.data.get? di with
      | some d => d.sym == id
      | none => false) 0 symRole

private theorem allIdx_toList_getElem {α : Type} {p : Nat → α → Bool} {t : IdxTree α}
    {sz : Nat} (hsz : t.size? = some sz)
    (h : IdxTree.allIdx p 0 t = true) {i : Nat} (hi : i < t.toList.length) :
    p i t.toList[i] = true := by
  rw [IdxTree.allIdx_eq_checkListIdx p hsz 0] at h
  have h1 := (checkListIdx_eq_true_iff p 0 t.toList).1 h i hi
  simpa using h1

private theorem block_sym_role_of_mem {N : Nat} {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true)
    {bi : Nat} (hbi : bi < L.blocks.toList.length)
    {j : Nat} (hj : j < L.blocks.toList[bi].symbols.length) :
    let (s, off, _) := L.blocks.toList[bi].symbols[j]
    s < N ∧ symRole.get? s = some (.blockSym bi j off) := by
  unfold checkSymRolesB at hrole
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hrole
  obtain ⟨szB, hszB⟩ := hrole.1.1.1.1.2
  have hb := allIdx_toList_getElem hszB hrole.1.1.2 hbi
  rw [List.all_eq_true] at hb
  have h1 := hb j (List.mem_range.2 hj)
  rw [List.getElem?_eq_getElem hj] at h1
  dsimp only at h1
  rcases htr : L.blocks.toList[bi].symbols[j] with ⟨s, off, wit⟩
  rw [htr] at h1
  dsimp only at h1 ⊢
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h1

private theorem data_sym_role_of_mem {N : Nat} {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true)
    {di : Nat} (hdi : di < L.data.toList.length) :
    L.data.toList[di].sym < N ∧ symRole.get? L.data.toList[di].sym = some (.dataSym di) := by
  unfold checkSymRolesB at hrole
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hrole
  obtain ⟨szD, hszD⟩ := hrole.1.1.1.2
  have hd := allIdx_toList_getElem hszD hrole.1.2 hdi
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hd

private theorem nodup_flatMap_of_disjoint {α : Type} :
    ∀ (xss : List (List α)),
      (∀ i (_ : i < xss.length), xss[i].Nodup) →
      (∀ i j (hi : i < xss.length) (hj : j < xss.length), i ≠ j →
        ∀ x ∈ xss[i], x ∉ xss[j]) →
      (xss.flatMap id).Nodup
  | [], _, _ => List.Pairwise.nil
  | xs :: rest, hnd, hdisj => by
    simp only [List.flatMap_cons, id_eq, List.nodup_append]
    refine ⟨hnd 0 (by simp), nodup_flatMap_of_disjoint rest
      (fun i hi => hnd (i + 1) (by simp; omega))
      (fun i j hi hj hij => hdisj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)),
      ?_⟩
    intro x hx y hy heq
    obtain ⟨ys, hys, hxy⟩ := List.mem_flatMap.1 hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hys
    subst heq
    exact hdisj 0 (j + 1) (by simp) (by simp; omega) (by omega) x hx hxy

theorem blockSymbols_nodup_of_roles {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true) :
    (((L.toMultiPlacedLib names).blocks.flatMap (·.symbols)).map (·.1)).Nodup := by
  let xss : List (List String) :=
    L.blocks.toList.map fun b => b.symbols.map fun (s, _, _) => symAt names s
  have heq : (((L.toMultiPlacedLib names).blocks.flatMap (·.symbols)).map (·.1)) =
      xss.flatMap id := by
    unfold IMultiLib.toMultiPlacedLib xss
    induction L.blocks.toList with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, ih, IBlock.toCodeBlock,
        List.map_map, id_eq, Function.comp_def]
  rw [heq]
  apply nodup_flatMap_of_disjoint
  · intro bi hbi
    simp only [xss, List.length_map, List.getElem_map] at hbi ⊢
    rw [List.nodup_iff_eq_of_getElem_eq]
    intro j1 j2 hj1 hj2 hstr
    simp only [List.length_map, List.getElem_map] at hj1 hj2 hstr
    have hr1 := block_sym_role_of_mem hrole hbi hj1
    have hr2 := block_sym_role_of_mem hrole hbi hj2
    rcases h1 : L.blocks.toList[bi].symbols[j1] with ⟨s1, off1, w1⟩
    rcases h2 : L.blocks.toList[bi].symbols[j2] with ⟨s2, off2, w2⟩
    rw [h1] at hr1 hstr; rw [h2] at hr2 hstr
    dsimp only at hr1 hr2 hstr
    have hs_eq : s1 = s2 := symAt_inj hsz hnd hr1.1 hr2.1 hstr
    subst hs_eq
    rw [hr1.2] at hr2
    injection hr2.2 with hsame
    injection hsame
  · intro bi1 bi2 hbi1 hbi2 hne x hx1 hx2
    simp only [xss, List.length_map, List.getElem_map, List.mem_map] at hbi1 hbi2 hx1 hx2
    obtain ⟨t1, ht1, rfl⟩ := hx1
    obtain ⟨t2, ht2, hstr⟩ := hx2
    obtain ⟨j1, hj1, he1⟩ := List.getElem_of_mem ht1
    obtain ⟨j2, hj2, he2⟩ := List.getElem_of_mem ht2
    have hr1 := block_sym_role_of_mem hrole hbi1 hj1
    have hr2 := block_sym_role_of_mem hrole hbi2 hj2
    rcases t1 with ⟨s1, off1, w1⟩
    rcases t2 with ⟨s2, off2, w2⟩
    rw [he1] at hr1; rw [he2] at hr2
    dsimp only at hr1 hr2 hstr
    have hs_eq : s1 = s2 := symAt_inj hsz hnd hr1.1 hr2.1 hstr.symm
    subst hs_eq
    rw [hr1.2] at hr2
    injection hr2.2 with hsame
    injection hsame with hbi_eq
    exact hne hbi_eq

theorem dataSyms_nodup_of_roles {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true) :
    ((L.toMultiPlacedLib names).data.map (·.sym)).Nodup := by
  have heq : (L.toMultiPlacedLib names).data.map (·.sym) =
      L.data.toList.map fun d => symAt names d.sym := by
    simp [IMultiLib.toMultiPlacedLib, IData.toSymDataInfo, List.map_map, Function.comp_def]
  rw [heq, List.nodup_iff_eq_of_getElem_eq]
  intro i1 i2 hi1 hi2 hstr
  simp only [List.length_map, List.getElem_map] at hi1 hi2 hstr
  have hr1 := data_sym_role_of_mem hrole hi1
  have hr2 := data_sym_role_of_mem hrole hi2
  have hs_eq : L.data.toList[i1].sym = L.data.toList[i2].sym :=
    symAt_inj hsz hnd hr1.1 hr2.1 hstr
  have hr1_eq := hr1.2
  rw [hs_eq, hr2.2] at hr1_eq
  injection hr1_eq with hsame
  injection hsame with hdi
  exact hdi.symm

private theorem lookup_block_of_role {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true)
    {bi : Nat} (hbi : bi < L.blocks.toList.length)
    {commonExt commonWeak : List String} {id : Nat} (hid : id < N) :
    lookup (symAt names id)
      (L.blocks.toList[bi].toCodeBlock names commonExt commonWeak).symbols =
      match symRole.get? id with
      | some (.blockSym bi' _ off) => if bi' = bi then some off else none
      | _ => none := by
  have hsyms : (L.blocks.toList[bi].toCodeBlock names commonExt commonWeak).symbols =
      L.blocks.toList[bi].symbols.map fun (s, off, _) => (symAt names s, off) := rfl
  rw [hsyms]
  have hall : ∀ (k : Nat) (xs : List (Nat × Nat × Option Nat)),
      (∀ m (_ : m < xs.length), ∃ hkm : k + m < L.blocks.toList[bi].symbols.length,
        L.blocks.toList[bi].symbols[k + m]'hkm = xs[m]) →
      lookup (symAt names id) (xs.map fun (s, off, _) => (symAt names s, off)) =
        match xs.find? (fun (s, _, _) => s == id) with
        | some (_, off, _) => some off
        | none => none := by
    intro k xs
    induction xs generalizing k with
    | nil => intro _; rfl
    | cons hd tl ih =>
      intro hsub
      rcases hd with ⟨s, off, w⟩
      obtain ⟨h0lt, h0eq⟩ := hsub 0 (by simp)
      have hr0 := block_sym_role_of_mem hrole hbi h0lt
      rw [h0eq] at hr0; dsimp only [List.getElem_cons_zero] at hr0
      have hbeq : (symAt names s == symAt names id) = (s == id) := by
        cases hsid : s == id with
        | true =>
          have hse : s = id := beq_iff_eq.1 hsid
          subst hse; simp
        | false =>
          apply beq_eq_false_iff_ne.2
          intro heq
          exact beq_eq_false_iff_ne.1 hsid (symAt_inj hsz hnd hr0.1 hid heq)
      simp only [List.map_cons, lookup, List.find?_cons, hbeq]
      cases s == id with
      | true => rfl
      | false =>
        dsimp only
        exact ih (k + 1) fun m hm => by
          obtain ⟨hm1lt, hm1eq⟩ := hsub (m + 1) (by simp; omega)
          refine ⟨by omega, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm 1 m] using hm1eq
  rw [hall 0 L.blocks.toList[bi].symbols (fun m hm => ⟨by simpa using hm, by simp⟩)]
  cases hf : L.blocks.toList[bi].symbols.find? (fun (s, _, _) => s == id) with
  | some hit =>
    rcases hit with ⟨s, off, w⟩
    have hmem := List.mem_of_find?_eq_some hf
    have hsid_b := List.find?_some hf
    dsimp only at hsid_b
    have hsid : s = id := beq_iff_eq.1 hsid_b
    subst hsid
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
    have hr := block_sym_role_of_mem hrole hbi hj
    rw [hjeq] at hr; dsimp only at hr
    rw [hr.2]
    simp
  | none =>
    have hnot : ∀ x ∈ L.blocks.toList[bi].symbols, !((fun (s, _, _) => s == id) x) = true := by
      intro x hx
      cases hb : (fun (s, _, _) => s == id) x with
      | false => rfl
      | true => exact False.elim ((List.find?_eq_none.1 hf x hx) hb)
    cases hrg : symRole.get? id with
    | none => rfl
    | some role =>
      cases role with
      | other => rfl
      | dataSym _ => rfl
      | blockSym bi' j' off' =>
        by_cases hbieq : bi' = bi
        · subst hbieq
          exfalso
          unfold checkSymRolesB at hrole
          simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hrole
          obtain ⟨⟨⟨⟨⟨hszR, ⟨szB, hszB⟩⟩, _⟩, _⟩, _⟩, hinvAll⟩ := hrole
          have hlenR : symRole.toList.length = N := IdxTree.length_toList_of_size? hszR
          have hinv := allIdx_toList_getElem hszR hinvAll (hlenR ▸ hid)
          have hget_eq : symRole.toList[id]'(hlenR ▸ hid) = .blockSym bi' j' off' := by
            rw [IdxTree.get?_eq_getElem? hszR id, List.getElem?_eq_getElem (hlenR ▸ hid)] at hrg
            exact Option.some.inj hrg
          rw [hget_eq] at hinv; dsimp only at hinv
          rw [IdxTree.get?_eq_getElem? hszB bi', List.getElem?_eq_getElem hbi] at hinv
          dsimp only at hinv
          cases hsymj : L.blocks.toList[bi'].symbols[j']? with
          | none => rw [hsymj] at hinv; exact nomatch hinv
          | some triple =>
            rcases triple with ⟨s0, off0, w0⟩
            rw [hsymj] at hinv; dsimp only at hinv
            simp only [Bool.and_eq_true, beq_iff_eq] at hinv
            have hmem0 := List.mem_of_getElem? hsymj
            have hn0 := hnot (s0, off0, w0) hmem0
            simp [hinv.1] at hn0
        · simp [hbieq]

theorem lookupBlockSym_eq_of_role {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true) {id : Nat} (hid : id < N) :
    lookupBlockSym (symAt names id) (L.toMultiPlacedLib names).blocks =
      match symRole.get? id with
      | some (.blockSym bi _ off) => some (bi, off)
      | _ => none := by
  let commonExt := L.commonExterns.map (symAt names)
  let commonWeak := L.commonWeakRefs.map (symAt names)
  have hblks : (L.toMultiPlacedLib names).blocks =
      L.blocks.toList.map (IBlock.toCodeBlock names commonExt commonWeak) := rfl
  rw [hblks]
  have hrole_bi_lt : ∀ bi j off, symRole.get? id = some (.blockSym bi j off) →
      bi < L.blocks.toList.length := by
    intro bi j off hrg
    unfold checkSymRolesB at hrole
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hrole
    obtain ⟨⟨⟨⟨⟨hszR, ⟨szB, hszB⟩⟩, _⟩, _⟩, _⟩, hinvAll⟩ := hrole
    have hlenR : symRole.toList.length = N := IdxTree.length_toList_of_size? hszR
    have hinv := allIdx_toList_getElem hszR hinvAll (hlenR ▸ hid)
    have hget_eq : symRole.toList[id]'(hlenR ▸ hid) = .blockSym bi j off := by
      rw [IdxTree.get?_eq_getElem? hszR id, List.getElem?_eq_getElem (hlenR ▸ hid)] at hrg
      exact Option.some.inj hrg
    rw [hget_eq] at hinv; dsimp only at hinv
    rw [IdxTree.get?_eq_getElem? hszB bi] at hinv
    cases hbg : L.blocks.toList[bi]? with
    | none => rw [hbg] at hinv; exact nomatch hinv
    | some _ => exact (List.getElem?_eq_some_iff.1 hbg).1
  have haux : ∀ (k : Nat) (bs : List IBlock),
      (∀ m (_ : m < bs.length), ∃ hkm : k + m < L.blocks.toList.length,
        L.blocks.toList[k + m]'hkm = bs[m]) →
      lookupBlockSymAux (symAt names id) k
        (bs.map (IBlock.toCodeBlock names commonExt commonWeak)) =
        match symRole.get? id with
        | some (.blockSym bi _ off) => if k ≤ bi ∧ bi < k + bs.length then some (bi, off) else none
        | _ => none := by
    intro k bs
    induction bs generalizing k with
    | nil =>
      intro _
      simp only [List.map_nil, lookupBlockSymAux, List.length_nil, Nat.add_zero]
      cases symRole.get? id with
      | none => rfl
      | some role =>
        cases role with
        | other => rfl
        | dataSym _ => rfl
        | blockSym bi _ off =>
          have hfalse : ¬ (k ≤ bi ∧ bi < k) := by omega
          simp [hfalse]
    | cons b rest ih =>
      intro hsub
      obtain ⟨h0lt, h0eq⟩ := hsub 0 (by simp)
      simp only [Nat.add_zero] at h0lt h0eq
      simp only [List.map_cons, lookupBlockSymAux]
      have hlk := lookup_block_of_role hsz hnd hrole h0lt (commonExt := commonExt)
        (commonWeak := commonWeak) hid
      rw [h0eq, List.getElem_cons_zero] at hlk
      rw [hlk]
      have hih := ih (k + 1) fun m hm => by
        obtain ⟨hm1lt, hm1eq⟩ := hsub (m + 1) (by simp; omega)
        refine ⟨by omega, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1 m] using hm1eq
      cases hrg : symRole.get? id with
      | none => simpa [hrg] using hih
      | some role =>
        cases role with
        | other => simpa [hrg] using hih
        | dataSym _ => simpa [hrg] using hih
        | blockSym bi j off =>
          dsimp only
          by_cases hkeq : bi = k
          · subst hkeq; simp
          · simp only [hkeq, ↓reduceIte, hih, hrg]
            congr 1
            apply propext
            simp only [List.length_cons]
            omega
  unfold lookupBlockSym
  rw [haux 0 L.blocks.toList (fun m hm => ⟨by simpa using hm, by simp⟩)]
  cases hrg : symRole.get? id with
  | none => rfl
  | some role =>
    cases role with
    | other => rfl
    | dataSym _ => rfl
    | blockSym bi j off =>
      have hlt := hrole_bi_lt bi j off hrg
      simp [hlt]

theorem data_lookup_none_of_roles {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true)
    {d : SymDataInfo} (hd : d ∈ (L.toMultiPlacedLib names).data) :
    lookupBlockSym d.sym (L.toMultiPlacedLib names).blocks = none := by
  simp only [IMultiLib.toMultiPlacedLib, List.mem_map] at hd
  obtain ⟨d0, hd0, rfl⟩ := hd
  obtain ⟨di, hdi, rfl⟩ := List.getElem_of_mem hd0
  have hr := data_sym_role_of_mem hrole hdi
  dsimp only [IData.toSymDataInfo]
  rw [lookupBlockSym_eq_of_role hsz hnd hrole hr.1, hr.2]

theorem not_mem_data_of_role {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {L : IMultiLib} {symRole : IdxTree SymRole}
    (hrole : checkSymRolesB N L symRole = true) {id : Nat} (hid : id < N)
    (hnotd : (match symRole.get? id with | some (.dataSym _) => false | _ => true) = true) :
    ∀ d ∈ (L.toMultiPlacedLib names).data, d.sym ≠ symAt names id := by
  intro d hd heq
  simp only [IMultiLib.toMultiPlacedLib, List.mem_map] at hd
  obtain ⟨d0, hd0, rfl⟩ := hd
  obtain ⟨di, hdi, rfl⟩ := List.getElem_of_mem hd0
  have hr := data_sym_role_of_mem hrole hdi
  dsimp only [IData.toSymDataInfo] at heq
  have hid_eq : L.data.toList[di].sym = id := symAt_inj hsz hnd hr.1 hid heq
  rw [hid_eq] at hr
  rw [hr.2] at hnotd
  exact nomatch hnotd

/-! ## Object symbol summary (`RawIdStatus`, `rawClaimed`) -/

/-- Precomputed global status of interned `rawName` ID `id` across `objs`. -/
inductive RawIdStatus where
  | other
  | globalDef (oi k si : Nat)
  | allNonLocalUndef
  | weakOnlyUndef (wOi wKi : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Verify all object symbols are in-bounds, `rawClaimed` covers every non-empty symbol's
    `rawName`, `name`, and `"name [obj]"`, and `rawSummary` accurately characterizes global
    definitions and undefined/weak-only symbols. -/
def checkObjSymsB (N : Nat) (charsTree : IdxTree (List Char)) (objsTree : IdxTree IObj)
    (rawSummary : IdxTree RawIdStatus) (rawClaimed : IdxTree Bool) : Bool :=
  objsTree.size?.isSome && (rawSummary.size? == some N) && (rawClaimed.size? == some N) &&
  IdxTree.allIdx (fun oj o =>
    decide (o.nameId < N) && o.sections.size?.isSome && o.symbols.size?.isSome &&
    charListBeq (charsAt charsTree o.nameId) o.nameChars &&
    o.sections.all (fun sec => decide (sec.nameId < N)) &&
    IdxTree.allIdx (fun k' sy =>
      decide (sy.rawId < N) && decide (sy.nameId < N) &&
      (if sy.rawId != 0 then
        decide (sy.derivedId < N) &&
        charListBeq (charsAt charsTree sy.derivedId)
          (charsAt charsTree sy.nameId ++ (' ' :: '[' :: (o.nameChars ++ [']']))) &&
        (rawClaimed.get? sy.rawId == some true) &&
        (rawClaimed.get? sy.nameId == some true) &&
        (rawClaimed.get? sy.derivedId == some true)
       else true) &&
      match rawSummary.get? sy.rawId with
      | some (.globalDef oi k _) =>
        if (sy.bind != .local) && (sy.sec != .undef) then (oj == oi) && (k' == k) else true
      | some .allNonLocalUndef =>
        if sy.bind != .local then sy.sec == .undef else true
      | some (.weakOnlyUndef _ _) =>
        (if sy.sec == .undef then sy.bind == .weak else true) &&
        (if sy.bind != .local then sy.sec == .undef else true) &&
        match sy.sec with
        | .sec _ => false
        | _ => true
      | _ => true) 0 o.symbols) 0 objsTree &&
  IdxTree.allIdx (fun id st =>
    match st with
    | .other | .allNonLocalUndef => true
    | .globalDef oi k si =>
      (id != 0) &&
      match objsTree.get? oi with
      | none => false
      | some o =>
        match o.symbols.get? k with
        | none => false
        | some sy =>
          (sy.rawId == id) && ((sy.bind == .global) || (sy.bind == .weak)) && (sy.sec == .sec si)
    | .weakOnlyUndef wOi wKi =>
      match objsTree.get? wOi with
      | none => false
      | some o =>
        match o.symbols.get? wKi with
        | none => false
        | some sy => (sy.rawId == id) && (sy.sec == .undef) && (sy.bind == .weak)) 0 rawSummary

theorem symNameDerived_of_isym {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hcsz : charsTree.size? = some N)
    (heq : names.toList = charsTree.toList.map String.ofList)
    {objsTree : IdxTree IObj} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    {oi : Nat} (hoi : oi < objsTree.toList.length)
    {k : Nat} (hk : k < objsTree.toList[oi].symbols.toList.length)
    (hraw : objsTree.toList[oi].symbols.toList[k].rawId ≠ 0)
    {symId : Nat}
    (hmatch : symId = objsTree.toList[oi].symbols.toList[k].nameId ∨
      symId = objsTree.toList[oi].symbols.toList[k].derivedId) :
    SymNameDerived (symAt names symId)
      (objsTree.toList[oi].symbols.toList[k].toRawSym names).name
      (objsTree.toList[oi].toExtractedObj names).name := by
  unfold checkObjSymsB at hobjs
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
  obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
  have ho := allIdx_toList_getElem hszO hobjs.1.2 hoi
  simp only [Bool.and_eq_true, decide_eq_true_eq, charListBeq_iff_eq, Option.isSome_iff_exists] at ho
  have honame_lt : objsTree.toList[oi].nameId < N := ho.1.1.1.1.1
  obtain ⟨szSy, hszSy⟩ := ho.1.1.1.2
  have honame_cs : charsAt charsTree objsTree.toList[oi].nameId = objsTree.toList[oi].nameChars :=
    ho.1.1.2
  have hsy := allIdx_toList_getElem hszSy ho.2 hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy
  have hname_lt : objsTree.toList[oi].symbols.toList[k].nameId < N := hsy.1.1.2
  have hcnd : (objsTree.toList[oi].symbols.toList[k].rawId != 0) = true := bne_iff_ne.2 hraw
  have hder := hsy.1.2
  rw [hcnd] at hder
  simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, charListBeq_iff_eq] at hder
  rcases hmatch with rfl | rfl
  · exact Or.inl rfl
  · right
    dsimp only [ISym.toRawSym, IObj.toExtractedObj]
    rw [symAt_eq_ofList_charsAt hsz hcsz heq hder.1.1.1.1,
      symAt_eq_ofList_charsAt hsz hcsz heq hname_lt,
      symAt_eq_ofList_charsAt hsz hcsz heq honame_lt,
      hder.1.1.1.2, honame_cs]
    have hbrL : " [" = String.ofList [' ', '['] := rfl
    have hbrR : "]" = String.ofList [']'] := rfl
    rw [hbrL, hbrR, ← String.ofList_append, ← String.ofList_append, ← String.ofList_append]
    simp [List.append_assoc]

theorem unclaimed_of_rawClaimed_false {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hcsz : charsTree.size? = some N)
    (heq : names.toList = charsTree.toList.map String.ofList)
    (hnd : names.toList.Nodup) (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    {id : Nat} (hid : id < N) (hfalse : rawClaimed.get? id = some false) :
    UnclaimedSymName (objsTree.toList.map (IObj.toExtractedObj names)) (symAt names id) := by
  intro o ho sy hsy hraw
  simp only [List.mem_map] at ho
  obtain ⟨io, hio_mem, rfl⟩ := ho
  obtain ⟨oi, hoi, rfl⟩ := List.getElem_of_mem hio_mem
  simp only [IObj.toExtractedObj, List.mem_map] at hsy
  obtain ⟨isy, hisy_mem, rfl⟩ := hsy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hisy_mem
  unfold checkObjSymsB at hobjs
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
  obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
  have ho_ok := allIdx_toList_getElem hszO hobjs.1.2 hoi
  simp only [Bool.and_eq_true, decide_eq_true_eq, charListBeq_iff_eq, Option.isSome_iff_exists] at ho_ok
  have honame_lt : objsTree.toList[oi].nameId < N := ho_ok.1.1.1.1.1
  obtain ⟨szSy, hszSy⟩ := ho_ok.1.1.1.2
  have honame_cs : charsAt charsTree objsTree.toList[oi].nameId = objsTree.toList[oi].nameChars :=
    ho_ok.1.1.2
  have hsy_ok := allIdx_toList_getElem hszSy ho_ok.2 hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy_ok
  have hraw_lt : objsTree.toList[oi].symbols.toList[k].rawId < N := hsy_ok.1.1.1
  have hname_lt : objsTree.toList[oi].symbols.toList[k].nameId < N := hsy_ok.1.1.2
  have hraw_i : objsTree.toList[oi].symbols.toList[k].rawId ≠ 0 :=
    (symAt_ne_empty_iff hsz hnd h0 hraw_lt).1 hraw
  have hcnd : (objsTree.toList[oi].symbols.toList[k].rawId != 0) = true := bne_iff_ne.2 hraw_i
  have hclm := hsy_ok.1.2
  rw [hcnd] at hclm
  simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, charListBeq_iff_eq, beq_iff_eq] at hclm
  refine ⟨?_, ?_⟩
  · intro heq_raw
    dsimp only [ISym.toRawSym] at heq_raw
    have hid_eq : id = objsTree.toList[oi].symbols.toList[k].rawId :=
      symAt_inj hsz hnd hid hraw_lt heq_raw
    rw [hid_eq, hclm.1.1.2] at hfalse
    exact nomatch hfalse
  · intro hder
    rcases hder with h1 | h2
    · dsimp only [ISym.toRawSym] at h1
      have hid_eq : id = objsTree.toList[oi].symbols.toList[k].nameId :=
        symAt_inj hsz hnd hid hname_lt h1
      rw [hid_eq, hclm.1.2] at hfalse
      exact nomatch hfalse
    · dsimp only [ISym.toRawSym, IObj.toExtractedObj] at h2
      have hder_str : symAt names objsTree.toList[oi].symbols.toList[k].derivedId =
          symAt names objsTree.toList[oi].symbols.toList[k].nameId ++ " [" ++
            symAt names objsTree.toList[oi].nameId ++ "]" := by
        rw [symAt_eq_ofList_charsAt hsz hcsz heq hclm.1.1.1.1,
          symAt_eq_ofList_charsAt hsz hcsz heq hname_lt,
          symAt_eq_ofList_charsAt hsz hcsz heq honame_lt,
          hclm.1.1.1.2, honame_cs]
        have hbrL : " [" = String.ofList [' ', '['] := rfl
        have hbrR : "]" = String.ofList [']'] := rfl
        rw [hbrL, hbrR, ← String.ofList_append, ← String.ofList_append, ← String.ofList_append]
        simp [List.append_assoc]
      rw [← hder_str] at h2
      have hid_eq : id = objsTree.toList[oi].symbols.toList[k].derivedId :=
        symAt_inj hsz hnd hid hclm.1.1.1.1 h2
      rw [hid_eq, hclm.2] at hfalse
      exact nomatch hfalse

/-- A `.globalDef` summary is the unique non-local definition of its name, so it `Resolves`
    (the competitor clause is vacuous) whenever no section is `Discarded`. -/
theorem resolves_of_summary {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    {id oi k si : Nat} (hid : id < N)
    (hst : rawSummary.get? id = some (.globalDef oi k si)) :
    ∃ o sy, objsTree.get? oi = some o ∧ o.symbols.get? k = some sy ∧
      Resolves (objsTree.toList.map (IObj.toExtractedObj names))
        (symAt names id) oi k si (sy.toRawSym names) := by
  unfold checkObjSymsB at hobjs
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hobjs
  obtain ⟨⟨⟨⟨⟨szO, hszO⟩, hszRS⟩, _⟩, hallO⟩, hallRS⟩ := hobjs
  have hlenRS : rawSummary.toList.length = N := IdxTree.length_toList_of_size? hszRS
  have hrs_i := allIdx_toList_getElem hszRS hallRS (hlenRS ▸ hid)
  have hst_eq : rawSummary.toList[id]'(hlenRS ▸ hid) = .globalDef oi k si := by
    rw [IdxTree.get?_eq_getElem? hszRS id, List.getElem?_eq_getElem (hlenRS ▸ hid)] at hst
    exact Option.some.inj hst
  rw [hst_eq] at hrs_i; dsimp only at hrs_i
  rw [Bool.and_eq_true, bne_iff_ne] at hrs_i
  obtain ⟨hid_ne0, hwit⟩ := hrs_i
  cases ho : objsTree.get? oi with
  | none => rw [ho] at hwit; exact nomatch hwit
  | some o =>
    rw [ho] at hwit; dsimp only at hwit
    cases hsy : o.symbols.get? k with
    | none => rw [hsy] at hwit; exact nomatch hwit
    | some sy =>
      rw [hsy] at hwit; dsimp only at hwit
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hwit
      have ho_elem : objsTree.toList[oi]? = some o := by
        rw [← IdxTree.get?_eq_getElem? hszO oi]; exact ho
      have hoi_lt : oi < objsTree.toList.length := (List.getElem?_eq_some_iff.1 ho_elem).1
      have ho_eq : objsTree.toList[oi] = o := by
        rw [List.getElem?_eq_getElem hoi_lt] at ho_elem; exact Option.some.inj ho_elem
      have ho_all := allIdx_toList_getElem hszO hallO hoi_lt
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_all
      obtain ⟨szSy, hszSy⟩ := ho_all.1.1.1.2
      rw [ho_eq] at hszSy
      have hsy_elem : o.symbols.toList[k]? = some sy := by
        rw [← IdxTree.get?_eq_getElem? hszSy k]; exact hsy
      refine ⟨o, sy, rfl, hsy, ?_, ?_, ?_, hwit.1.2, hwit.2, hnd_disc oi si, ?_⟩
      · exact (symAt_ne_empty_iff hsz hnd h0 hid).2 hid_ne0
      · refine ⟨o.toExtractedObj names, ?_, ?_⟩
        · simp [List.getElem?_map, ho_elem]
        · simp [IObj.toExtractedObj, List.getElem?_map, hsy_elem]
      · dsimp only [ISym.toRawSym]; rw [hwit.1.1]
      · intro oj k' o' sy' hoj hk' hraw' hbind' hsec' hne
        exfalso
        simp only [List.getElem?_map] at hoj
        cases hoj0 : objsTree.toList[oj]? with
        | none => rw [hoj0] at hoj; exact nomatch hoj
        | some io' =>
          rw [hoj0] at hoj; cases hoj
          have hoj_lt : oj < objsTree.toList.length := (List.getElem?_eq_some_iff.1 hoj0).1
          have hio_eq : objsTree.toList[oj] = io' := by
            rw [List.getElem?_eq_getElem hoj_lt] at hoj0; exact Option.some.inj hoj0
          simp only [IObj.toExtractedObj, List.getElem?_map] at hk'
          cases hk0 : io'.symbols.toList[k']? with
          | none => rw [hk0] at hk'; exact nomatch hk'
          | some isy' =>
            rw [hk0] at hk'; cases hk'
            have hk_lt : k' < io'.symbols.toList.length := (List.getElem?_eq_some_iff.1 hk0).1
            have hisy_eq : io'.symbols.toList[k'] = isy' := by
              rw [List.getElem?_eq_getElem hk_lt] at hk0; exact Option.some.inj hk0
            have hoj_all := allIdx_toList_getElem hszO hallO hoj_lt
            simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hoj_all
            rw [hio_eq] at hoj_all
            obtain ⟨szSy', hszSy'⟩ := hoj_all.1.1.1.2
            have hisy_all := allIdx_toList_getElem hszSy' hoj_all.2 hk_lt
            rw [hisy_eq] at hisy_all
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hisy_all
            have hraw_id_eq : isy'.rawId = id :=
              symAt_inj hsz hnd hisy_all.1.1.1 hid hraw'
            have hrs_chk := hisy_all.2
            rw [hraw_id_eq, hst] at hrs_chk; dsimp only at hrs_chk
            dsimp only [ISym.toRawSym] at hbind' hsec'
            split at hrs_chk
            · simp only [Bool.and_eq_true, beq_iff_eq] at hrs_chk
              rcases hne with hne | hne
              · exact hne hrs_chk.1
              · exact hne hrs_chk.2
            · rename_i hneg
              simp [hbind', hsec'] at hneg

theorem allNonLocalUndef_of_summary {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {objsTree : IdxTree IObj} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    {id : Nat} (hid : id < N)
    (hst : (match rawSummary.get? id with
      | some .allNonLocalUndef | some (.weakOnlyUndef _ _) => true
      | _ => false) = true) :
    ∀ o' ∈ objsTree.toList.map (IObj.toExtractedObj names),
      ∀ sy' ∈ o'.symbols, sy'.rawName = symAt names id → sy'.bind ≠ .local → sy'.sec = .undef := by
  intro o' ho' sy' hsy' hraw' hbind'
  simp only [List.mem_map] at ho'
  obtain ⟨io', hio_mem, rfl⟩ := ho'
  obtain ⟨oj, hoj, rfl⟩ := List.getElem_of_mem hio_mem
  simp only [IObj.toExtractedObj, List.mem_map] at hsy'
  obtain ⟨isy', hisy_mem, rfl⟩ := hsy'
  obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hisy_mem
  unfold checkObjSymsB at hobjs
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
  obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
  have ho_ok := allIdx_toList_getElem hszO hobjs.1.2 hoj
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_ok
  obtain ⟨szSy, hszSy⟩ := ho_ok.1.1.1.2
  have hsy_ok := allIdx_toList_getElem hszSy ho_ok.2 hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy_ok
  have hraw_eq : (objsTree.toList[oj].symbols.toList[k']).rawId = id :=
    symAt_inj hsz hnd hsy_ok.1.1.1 hid hraw'
  have hrs_chk := hsy_ok.2
  rw [hraw_eq] at hrs_chk
  dsimp only [ISym.toRawSym] at hbind' ⊢
  have hbn : (objsTree.toList[oj].symbols.toList[k'].bind != .local) = true :=
    bne_iff_ne.2 hbind'
  cases hrs : rawSummary.get? id with
  | none => rw [hrs] at hst; exact nomatch hst
  | some s =>
    rw [hrs] at hst hrs_chk
    cases s with
    | other => exact nomatch hst
    | globalDef _ _ _ => exact nomatch hst
    | allNonLocalUndef =>
      dsimp only at hrs_chk
      rw [hbn] at hrs_chk
      simpa only [↓reduceIte, beq_iff_eq] using hrs_chk
    | weakOnlyUndef _ _ =>
      dsimp only at hrs_chk
      simp only [Bool.and_eq_true] at hrs_chk
      have h2 := hrs_chk.1.2
      rw [hbn] at h2
      simpa only [↓reduceIte, beq_iff_eq] using h2

theorem weakOnlyUndef_of_summary {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {objsTree : IdxTree IObj} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    {id wOi wKi : Nat} (hid : id < N)
    (hst : rawSummary.get? id = some (.weakOnlyUndef wOi wKi)) :
    WeakOnlyUndef (objsTree.toList.map (IObj.toExtractedObj names)) (symAt names id) := by
  unfold checkObjSymsB at hobjs
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hobjs
  obtain ⟨⟨⟨⟨⟨szO, hszO⟩, hszRS⟩, _⟩, hallO⟩, hallRS⟩ := hobjs
  have hlenRS : rawSummary.toList.length = N := IdxTree.length_toList_of_size? hszRS
  have hrs_i := allIdx_toList_getElem hszRS hallRS (hlenRS ▸ hid)
  have hst_eq : rawSummary.toList[id]'(hlenRS ▸ hid) = .weakOnlyUndef wOi wKi := by
    rw [IdxTree.get?_eq_getElem? hszRS id, List.getElem?_eq_getElem (hlenRS ▸ hid)] at hst
    exact Option.some.inj hst
  rw [hst_eq] at hrs_i; dsimp only at hrs_i
  refine ⟨?_, ?_⟩
  · cases ho : objsTree.get? wOi with
    | none => rw [ho] at hrs_i; exact nomatch hrs_i
    | some o =>
      rw [ho] at hrs_i; dsimp only at hrs_i
      cases hsy : o.symbols.get? wKi with
      | none => rw [hsy] at hrs_i; exact nomatch hrs_i
      | some sy =>
        rw [hsy] at hrs_i; dsimp only at hrs_i
        simp only [Bool.and_eq_true, beq_iff_eq] at hrs_i
        refine ⟨o.toExtractedObj names,
          List.mem_map.2 ⟨o, IdxTree.mem_toList_of_get? ho, rfl⟩,
          sy.toRawSym names,
          List.mem_map.2 ⟨sy, IdxTree.mem_toList_of_get? hsy, rfl⟩,
          hrs_i.1.2, ?_, hrs_i.2⟩
        dsimp only [ISym.toRawSym]; rw [hrs_i.1.1]
  · intro o' ho' sy' hsy' hraw'
    simp only [List.mem_map] at ho'
    obtain ⟨io', hio_mem, rfl⟩ := ho'
    obtain ⟨oj, hoj, rfl⟩ := List.getElem_of_mem hio_mem
    simp only [IObj.toExtractedObj, List.mem_map] at hsy'
    obtain ⟨isy', hisy_mem, rfl⟩ := hsy'
    obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hisy_mem
    have ho_ok := allIdx_toList_getElem hszO hallO hoj
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_ok
    obtain ⟨szSy, hszSy⟩ := ho_ok.1.1.1.2
    have hsy_ok := allIdx_toList_getElem hszSy ho_ok.2 hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy_ok
    have hraw_eq : (objsTree.toList[oj].symbols.toList[k']).rawId = id :=
      symAt_inj hsz hnd hsy_ok.1.1.1 hid hraw'
    have hrs_chk := hsy_ok.2
    rw [hraw_eq, hst] at hrs_chk; dsimp only at hrs_chk
    simp only [Bool.and_eq_true] at hrs_chk
    refine ⟨?_, ?_, ?_⟩
    · intro hu
      dsimp only [ISym.toRawSym] at hu ⊢
      have h1 := hrs_chk.1.1
      split at h1
      · simpa only [beq_iff_eq] using h1
      · rename_i hneg
        simp [hu] at hneg
    · intro hb
      dsimp only [ISym.toRawSym] at hb ⊢
      have h2 := hrs_chk.1.2
      split at h2
      · simpa only [beq_iff_eq] using h2
      · rename_i hneg
        simp [hb] at hneg
    · intro si hsec
      have h3 := hrs_chk.2
      dsimp only [ISym.toRawSym] at hsec
      rw [hsec] at h3
      exact nomatch h3

/-! ## Section byte cursor, `SliceGroup` disjointness, and slice validity -/

/-- Advance `k` bytes in `bs`, returning `some (bs.drop k)` iff `k ≤ bs.length`. -/
def dropCount : Nat → List (BitVec 8) → Option (List (BitVec 8))
  | 0, bs => some bs
  | k + 1, _ :: bs => dropCount k bs
  | _ + 1, [] => none

theorem dropCount_eq_some : ∀ (k : Nat) (bs rest : List (BitVec 8)),
    dropCount k bs = some rest → k ≤ bs.length ∧ rest = bs.drop k
  | 0, bs, rest, h => by
    simp only [dropCount, Option.some.injEq] at h
    exact ⟨Nat.zero_le _, h.symm⟩
  | k + 1, _ :: bs, rest, h => by
    simp only [dropCount] at h
    obtain ⟨hle, heq⟩ := dropCount_eq_some k bs rest h
    exact ⟨by simp; omega, by simpa using heq⟩
  | _ + 1, [], _, h => nomatch h

/-- Match `sub` as a prefix of `bs` using primitive `Nat.beq`, returning `some (bs.drop sub.length)`
    when `sub.length ≤ bs.length` and `sub = bs.take sub.length`. -/
def matchPrefixRest : List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))
  | [], bs => some bs
  | b :: sub, c :: bs => if Nat.beq b.toNat c.toNat then matchPrefixRest sub bs else none
  | _ :: _, [] => none

theorem matchPrefixRest_eq_some : ∀ (sub bs rest : List (BitVec 8)),
    matchPrefixRest sub bs = some rest →
      sub.length ≤ bs.length ∧ sub = bs.take sub.length ∧ rest = bs.drop sub.length
  | [], bs, rest, h => by
    simp only [matchPrefixRest, Option.some.injEq] at h
    exact ⟨Nat.zero_le _, rfl, h.symm⟩
  | b :: sub, c :: bs, rest, h => by
    simp only [matchPrefixRest] at h
    cases hb : Nat.beq b.toNat c.toNat with
    | false => rw [hb] at h; exact nomatch h
    | true =>
      rw [hb] at h; simp only [↓reduceIte] at h
      have hbc : b = c := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb)
      obtain ⟨hle, htake, hdrop⟩ := matchPrefixRest_eq_some sub bs rest h
      refine ⟨by simp; omega, ?_, by simpa using hdrop⟩
      change b :: sub = c :: bs.take sub.length
      rw [hbc, ← htake]
  | _ :: _, [], _, h => nomatch h

/-- Single-pass byte-cursor check over sorted `(start, len, sliceBytes)` triples in a section of
    total byte length `totalSize`. -/
def checkByteSlicesWalk : List (Nat × Nat × List (BitVec 8)) → Nat → Nat → List (BitVec 8) → Bool
  | [], totalSize, pos, rem =>
    decide (pos ≤ totalSize) &&
    match dropCount (totalSize - pos) rem with
    | some [] => true
    | _ => false
  | (start, len, sub) :: rest, totalSize, pos, rem =>
    decide (pos ≤ start) && (sub.length == len) &&
    match dropCount (start - pos) rem with
    | none => false
    | some rem1 =>
      match matchPrefixRest sub rem1 with
      | none => false
      | some rem2 => checkByteSlicesWalk rest totalSize (start + len) rem2

private theorem checkByteSlicesWalk_aux :
    ∀ (slices : List (Nat × Nat × List (BitVec 8))) (totalSize pos : Nat)
      (full rem : List (BitVec 8)),
      pos ≤ full.length → rem = full.drop pos →
      checkByteSlicesWalk slices totalSize pos rem = true →
      full.length = totalSize ∧
      ∀ start len sub, (start, len, sub) ∈ slices →
        start + len ≤ totalSize ∧ sub = (full.drop start).take len
  | [], totalSize, pos, full, rem, hpos, hrem, h => by
    simp only [checkByteSlicesWalk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hpt, hdrop⟩ := h
    cases hdc : dropCount (totalSize - pos) rem with
    | none => rw [hdc] at hdrop; exact nomatch hdrop
    | some tail =>
      rw [hdc] at hdrop
      cases tail with
      | cons _ _ => exact nomatch hdrop
      | nil =>
        obtain ⟨hle1, hnil⟩ := dropCount_eq_some _ _ _ hdc
        have hle2 : rem.length ≤ totalSize - pos := List.drop_eq_nil_iff.1 hnil.symm
        have hremlen : rem.length = full.length - pos := by simp [hrem]
        refine ⟨by omega, ?_⟩
        intro _ _ _ hm; exact nomatch hm
  | (start, len, sub) :: rest, totalSize, pos, full, rem, hpos, hrem, h => by
    simp only [checkByteSlicesWalk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hps, hlen⟩, hstep⟩ := h
    cases hdc : dropCount (start - pos) rem with
    | none => rw [hdc] at hstep; exact nomatch hstep
    | some rem1 =>
      rw [hdc] at hstep; dsimp only at hstep
      obtain ⟨hdle, hrem1⟩ := dropCount_eq_some _ _ _ hdc
      have hremlen : rem.length = full.length - pos := by simp [hrem]
      have hstart_le : start ≤ full.length := by omega
      have hrem1_eq : rem1 = full.drop start := by
        rw [hrem1, hrem, List.drop_drop]
        exact congrArg (full.drop ·) (by omega)
      cases hmp : matchPrefixRest sub rem1 with
      | none => rw [hmp] at hstep; exact nomatch hstep
      | some rem2 =>
        rw [hmp] at hstep; dsimp only at hstep
        obtain ⟨hmle, hsub_eq, hrem2⟩ := matchPrefixRest_eq_some _ _ _ hmp
        have hrem1len : rem1.length = full.length - start := by simp [hrem1_eq]
        have hend_le : start + len ≤ full.length := by omega
        have hrem2_eq : rem2 = full.drop (start + len) := by
          rw [hrem2, hrem1_eq, List.drop_drop]
          exact congrArg (full.drop ·) (by omega)
        obtain ⟨hflen, hrest⟩ :=
          checkByteSlicesWalk_aux rest totalSize (start + len) full rem2 hend_le hrem2_eq hstep
        refine ⟨hflen, ?_⟩
        intro s l sb hm
        rcases List.mem_cons.1 hm with heq | hmem
        · cases heq
          refine ⟨by omega, ?_⟩
          rw [hsub_eq, hrem1_eq, hlen]
        · exact hrest s l sb hmem

theorem checkByteSlicesWalk_spec {slices : List (Nat × Nat × List (BitVec 8))}
    {totalSize : Nat} {full : List (BitVec 8)}
    (h : checkByteSlicesWalk slices totalSize 0 full = true) :
    full.length = totalSize ∧
    ∀ start len sub, (start, len, sub) ∈ slices →
      start + len ≤ totalSize ∧ sub = (full.drop start).take len :=
  checkByteSlicesWalk_aux slices totalSize 0 full full (Nat.zero_le _) (by simp) h

/-- Sorted group of slice indices belonging to `(oi, si)`, ordered by non-decreasing `start`. -/
structure SliceGroup where
  oi : Nat
  si : Nat
  indices : IdxTree Nat
  deriving Inhabited

/-- Strict lexicographic order on `(oi, si)` using primitive `Nat.beq` / `Nat.blt`. -/
def groupLt (g1 g2 : SliceGroup) : Bool :=
  if Nat.beq g1.oi g2.oi then Nat.blt g1.si g2.si else Nat.blt g1.oi g2.oi

private theorem groupLt_iff (g1 g2 : SliceGroup) :
    groupLt g1 g2 = true ↔ g1.oi < g2.oi ∨ (g1.oi = g2.oi ∧ g1.si < g2.si) := by
  unfold groupLt
  cases h : Nat.beq g1.oi g2.oi with
  | true =>
    have heq : g1.oi = g2.oi := Nat.eq_of_beq_eq_true h
    simp [heq, Nat.blt_eq]
  | false =>
    have hne : g1.oi ≠ g2.oi := Nat.ne_of_beq_eq_false h
    simp [hne, Nat.blt_eq]

private theorem groupLt_trans {a b c : SliceGroup}
    (h1 : groupLt a b = true) (h2 : groupLt b c = true) : groupLt a c = true := by
  rw [groupLt_iff] at h1 h2 ⊢
  omega

/-- Adjacent slice ordering `o1.start + o1.len ≤ o2.start`. -/
def sliceFollows (originTree : IdxTree SliceOrigin) (i1 i2 : Nat) : Bool :=
  match originTree.get? i1, originTree.get? i2 with
  | some o1, some o2 => Nat.ble (o1.start + o1.len) o2.start
  | _, _ => false

private theorem sliceFollows_trans {originTree : IdxTree SliceOrigin} {a b c : Nat}
    (h1 : sliceFollows originTree a b = true) (h2 : sliceFollows originTree b c = true) :
    sliceFollows originTree a c = true := by
  unfold sliceFollows at h1 h2 ⊢
  cases ha : originTree.get? a with
  | none => rw [ha] at h1; exact nomatch h1
  | some oa =>
    rw [ha] at h1
    cases hb : originTree.get? b with
    | none => rw [hb] at h1; exact nomatch h1
    | some ob =>
      rw [hb] at h1 h2
      cases hc : originTree.get? c with
      | none => rw [hc] at h2; exact nomatch h2
      | some oc =>
        rw [hc] at h2
        dsimp only at h1 h2 ⊢
        rw [Nat.ble_eq] at h1 h2 ⊢
        omega

/-- Linear $O(M \log M)$ check that `originTree` (size `M`) is partitioned by strictly sorted
    `(oi, si)` groups `groups` via `toGroup`, with non-overlapping ordered slices in each group. -/
def checkGroupsDisjointB (M : Nat) (originTree : IdxTree SliceOrigin)
    (groups : IdxTree SliceGroup) (toGroup : IdxTree (Nat × Nat)) : Bool :=
  (originTree.size? == some M) && groups.size?.isSome && (toGroup.size? == some M) &&
  strictChain groupLt groups.toList &&
  groups.all (fun g => g.indices.size?.isSome &&
    strictChain (sliceFollows originTree) g.indices.toList) &&
  IdxTree.allIdx (fun i (gIdx, pos) =>
    match originTree.get? i, groups.get? gIdx with
    | some o, some g =>
      (o.oi == g.oi) && (o.si == g.si) && (g.indices.get? pos == some i)
    | _, _ => false) 0 toGroup

theorem group_mem_of_toGroup {M : Nat} {originTree : IdxTree SliceOrigin}
    {groups : IdxTree SliceGroup} {toGroup : IdxTree (Nat × Nat)}
    (h : checkGroupsDisjointB M originTree groups toGroup = true) (i : Fin M) :
    ∃ gi pi o g,
      originTree.get? i.1 = some o ∧
      originAt originTree i = o ∧
      groups.get? gi = some g ∧
      o.oi = g.oi ∧ o.si = g.si ∧
      g.indices.get? pi = some i.1 ∧
      i.1 ∈ g.indices.toList := by
  unfold checkGroupsDisjointB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨⟨hszO, ⟨szG, hszG⟩⟩, hszTG⟩, _⟩, _⟩, hallTG⟩ := h
  have hlenTG : toGroup.toList.length = M := IdxTree.length_toList_of_size? hszTG
  have hiTG : i.1 < toGroup.toList.length := hlenTG ▸ i.2
  have htg := allIdx_toList_getElem hszTG hallTG hiTG
  rcases hpair : toGroup.toList[i.1] with ⟨gi, pi⟩
  rw [hpair] at htg; dsimp only at htg
  unfold originAt
  cases ho : originTree.get? i.1 with
  | none => rw [ho] at htg; exact nomatch htg
  | some o =>
    rw [ho] at htg
    cases hg : groups.get? gi with
    | none => rw [hg] at htg; exact nomatch htg
    | some g =>
      rw [hg] at htg; dsimp only at htg
      simp only [Bool.and_eq_true, beq_iff_eq] at htg
      exact ⟨gi, pi, o, g, rfl, rfl, hg, htg.1.1, htg.1.2, htg.2,
        IdxTree.mem_toList_of_get? htg.2⟩

theorem groups_disjoint_of_check {M : Nat} {originTree : IdxTree SliceOrigin}
    {groups : IdxTree SliceGroup} {toGroup : IdxTree (Nat × Nat)}
    (h : checkGroupsDisjointB M originTree groups toGroup = true) :
    ∀ i j : Fin M, i ≠ j →
      (originAt originTree i).oi = (originAt originTree j).oi →
      (originAt originTree i).si = (originAt originTree j).si →
      RangesDisjoint (originAt originTree i).start (originAt originTree i).len
        (originAt originTree j).start (originAt originTree j).len := by
  intro i j hij hoi hsi
  obtain ⟨gi, pi, oi_o, gi_g, ho_i, horig_i, hg_i, hgoi_i, hgsi_i, hpi, _⟩ :=
    group_mem_of_toGroup h i
  obtain ⟨gj, pj, oj_o, gj_g, ho_j, horig_j, hg_j, hgoi_j, hgsi_j, hpj, _⟩ :=
    group_mem_of_toGroup h j
  rw [horig_i] at hoi hsi ⊢
  rw [horig_j] at hoi hsi ⊢
  unfold checkGroupsDisjointB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨⟨_, ⟨szG, hszG⟩⟩, _⟩, hchainG⟩, hallG⟩, _⟩ := h
  have hgi_elem : groups.toList[gi]? = some gi_g := by
    rw [← IdxTree.get?_eq_getElem? hszG gi]; exact hg_i
  have hgj_elem : groups.toList[gj]? = some gj_g := by
    rw [← IdxTree.get?_eq_getElem? hszG gj]; exact hg_j
  have hgi_lt : gi < groups.toList.length := (List.getElem?_eq_some_iff.1 hgi_elem).1
  have hgj_lt : gj < groups.toList.length := (List.getElem?_eq_some_iff.1 hgj_elem).1
  have hgi_eq : groups.toList[gi] = gi_g := by
    rw [List.getElem?_eq_getElem hgi_lt] at hgi_elem; exact Option.some.inj hgi_elem
  have hgj_eq : groups.toList[gj] = gj_g := by
    rw [List.getElem?_eq_getElem hgj_lt] at hgj_elem; exact Option.some.inj hgj_elem
  have hpwG := List.pairwise_iff_getElem.1 (strictChain_pairwise groupLt groupLt_trans groups.toList hchainG)
  have hge : gi = gj := by
    rcases Nat.lt_trichotomy gi gj with hlt | hge | hgt
    · have hltG := (groupLt_iff _ _).1 (hpwG gi gj hgi_lt hgj_lt hlt)
      rw [hgi_eq, hgj_eq] at hltG
      omega
    · exact hge
    · have hltG := (groupLt_iff _ _).1 (hpwG gj gi hgj_lt hgi_lt hgt)
      rw [hgi_eq, hgj_eq] at hltG
      omega
  subst hge
  cases hgi_eq.symm.trans hgj_eq
  have hg_ok := hallG
  rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hg_ok
  have hgi_ok := hg_ok gi_g (IdxTree.mem_toList_of_get? hg_i)
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hgi_ok
  obtain ⟨⟨szI, hszI⟩, hchainI⟩ := hgi_ok
  have hpi_elem : gi_g.indices.toList[pi]? = some i.1 := by
    rw [← IdxTree.get?_eq_getElem? hszI pi]; exact hpi
  have hpj_elem : gi_g.indices.toList[pj]? = some j.1 := by
    rw [← IdxTree.get?_eq_getElem? hszI pj]; exact hpj
  have hpi_lt : pi < gi_g.indices.toList.length := (List.getElem?_eq_some_iff.1 hpi_elem).1
  have hpj_lt : pj < gi_g.indices.toList.length := (List.getElem?_eq_some_iff.1 hpj_elem).1
  have hpi_eq : gi_g.indices.toList[pi] = i.1 := by
    rw [List.getElem?_eq_getElem hpi_lt] at hpi_elem; exact Option.some.inj hpi_elem
  have hpj_eq : gi_g.indices.toList[pj] = j.1 := by
    rw [List.getElem?_eq_getElem hpj_lt] at hpj_elem; exact Option.some.inj hpj_elem
  have hp_ne : pi ≠ pj := by
    intro heq; subst heq
    apply hij; exact Fin.ext (hpi_eq.symm.trans hpj_eq)
  have hpwI := List.pairwise_iff_getElem.1
    (strictChain_pairwise (sliceFollows originTree) sliceFollows_trans gi_g.indices.toList hchainI)
  rcases Nat.lt_or_gt_of_ne hp_ne with hlt | hgt
  · have hsf := hpwI pi pj hpi_lt hpj_lt hlt
    rw [hpi_eq, hpj_eq] at hsf
    unfold sliceFollows at hsf
    rw [ho_i, ho_j] at hsf; dsimp only at hsf
    rw [Nat.ble_eq] at hsf
    exact Or.inl hsf
  · have hsf := hpwI pj pi hpj_lt hpi_lt hgt
    rw [hpj_eq, hpi_eq] at hsf
    unfold sliceFollows at hsf
    rw [ho_j, ho_i] at hsf; dsimp only at hsf
    rw [Nat.ble_eq] at hsf
    exact Or.inr hsf

/-- Per-group single-pass byte check for executable text slices. -/
def checkTextGroupsBytesB (objsTree : IdxTree IObj) (blocksTree : IdxTree IBlock)
    (bOTree : IdxTree SliceOrigin) (textGroups : IdxTree SliceGroup) : Bool :=
  textGroups.all fun g =>
    match objsTree.get? g.oi with
    | none => false
    | some io =>
      match io.sections.get? g.si with
      | none => false
      | some sec =>
        let slices := g.indices.toList.map fun bi =>
          match bOTree.get? bi, blocksTree.get? bi with
          | some o, some b => (o.start, o.len, b.code)
          | _, _ => (0, 0, [])
        checkByteSlicesWalk slices sec.size 0 sec.bytes

/-- Per-block metadata, alignment, and `STT_FUNC` / `UnclaimedSymName` check. -/
def checkTextSlicesMetaB (N : Nat) (objsTree : IdxTree IObj) (blocksTree : IdxTree IBlock)
    (bOTree : IdxTree SliceOrigin) (rawClaimed : IdxTree Bool) : Bool :=
  IdxTree.allIdx (fun bi b =>
    match bOTree.get? bi with
    | none => false
    | some o =>
      match objsTree.get? o.oi with
      | none => false
      | some io =>
        match io.sections.get? o.si with
        | none => false
        | some sec =>
          sec.isExec && sec.readOnly && (!sec.isNobits) && (!sec.isTls) &&
          decide (0 < o.len) && (o.start % 4 == 0) && (o.len % 4 == 0) &&
          decide (0 < sec.align) && (b.align % Nat.gcd sec.align o.start == 0) &&
          b.symbols.all fun (s, off, wit?) =>
            decide (s < N) && decide (off < o.len) && (off % 4 == 0) &&
            match wit? with
            | some k =>
              match io.symbols.get? k with
              | none => false
              | some sy =>
                (sy.kind == .func) && (sy.sec == .sec o.si) && (sy.rawId != 0) &&
                (sy.value == o.start + off) && ((s == sy.nameId) || (s == sy.derivedId))
            | none => rawClaimed.get? s == some false) 0 blocksTree

theorem validTextSlices_of_check {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N B : Nat} (hsz : names.size? = some N) (hcsz : charsTree.size? = some N)
    (heq : names.toList = charsTree.toList.map String.ofList)
    (hnd : names.toList.Nodup) (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {L : IMultiLib}
    {bOTree : IdxTree SliceOrigin} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    {textGroups : IdxTree SliceGroup} {textToGroup : IdxTree (Nat × Nat)}
    (hB : L.blocks.size? = some B)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    (hbdisj : checkGroupsDisjointB B bOTree textGroups textToGroup = true)
    (htbytes : checkTextGroupsBytesB objsTree L.blocks bOTree textGroups = true)
    (htmeta : checkTextSlicesMetaB N objsTree L.blocks bOTree rawClaimed = true) :
    ∀ i : Fin (L.toMultiPlacedLib names).blocks.length,
      ValidTextSlice (objsTree.toList.map (IObj.toExtractedObj names))
        (L.toMultiPlacedLib names).blocks[i] (originAt bOTree i) := by
  intro i
  have hlenB : L.blocks.toList.length = B := IdxTree.length_toList_of_size? hB
  have hiB : i.1 < B := by
    have hiL : i.1 < L.blocks.toList.length := by simpa [IMultiLib.toMultiPlacedLib] using i.2
    omega
  have hiL : i.1 < L.blocks.toList.length := hlenB ▸ hiB
  obtain ⟨gi, _, o, g, ho_get, horig, hg_get, hgoi, hgsi, _, hi_mem⟩ :=
    group_mem_of_toGroup hbdisj ⟨i.1, hiB⟩
  have horig_i : originAt bOTree i = o := horig
  have hbi_eq : (L.toMultiPlacedLib names).blocks[i] =
      L.blocks.toList[i.1].toCodeBlock names
        (L.commonExterns.map (symAt names)) (L.commonWeakRefs.map (symAt names)) := by
    change (L.toMultiPlacedLib names).blocks[i.1] = _
    simp [IMultiLib.toMultiPlacedLib]
  rw [horig_i, hbi_eq]
  have hb_get : L.blocks.get? i.1 = some L.blocks.toList[i.1] := by
    rw [IdxTree.get?_eq_getElem? hB i.1, List.getElem?_eq_getElem hiL]
  have hm := allIdx_toList_getElem hB htmeta hiL
  rw [ho_get] at hm; dsimp only at hm
  cases hio : objsTree.get? o.oi with
  | none => rw [hio] at hm; exact nomatch hm
  | some io =>
    rw [hio] at hm; dsimp only at hm
    cases hsec : io.sections.get? o.si with
    | none => rw [hsec] at hm; exact nomatch hm
    | some sec =>
      rw [hsec] at hm; dsimp only at hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hm
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hexec, hro⟩, hnob⟩, htls⟩, hlen_pos⟩, hst4⟩, hln4⟩, hsal⟩, hbal⟩, hsyms⟩ := hm
      have hgb := htbytes
      unfold checkTextGroupsBytesB at hgb
      rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hgb
      have hgb_i := hgb g (IdxTree.mem_toList_of_get? hg_get)
      rw [← hgoi, ← hgsi, hio] at hgb_i; dsimp only at hgb_i
      rw [hsec] at hgb_i; dsimp only at hgb_i
      obtain ⟨hsec_len, hwalk⟩ := checkByteSlicesWalk_spec hgb_i
      have hmem_slice : (o.start, o.len, L.blocks.toList[i.1].code) ∈
          (g.indices.toList.map fun bi =>
            match bOTree.get? bi, L.blocks.get? bi with
            | some o', some b' => (o'.start, o'.len, b'.code)
            | _, _ => (0, 0, [])) := by
        refine List.mem_map.2 ⟨i.1, hi_mem, ?_⟩
        rw [ho_get, hb_get]
      obtain ⟨hend_le, hcode_eq⟩ := hwalk o.start o.len L.blocks.toList[i.1].code hmem_slice
      unfold checkObjSymsB at hobjs
      have hobjs_orig := hobjs
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
      obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
      have hio_elem : objsTree.toList[o.oi]? = some io := by
        rw [← IdxTree.get?_eq_getElem? hszO o.oi]; exact hio
      have hoi_lt : o.oi < objsTree.toList.length := (List.getElem?_eq_some_iff.1 hio_elem).1
      have hio_eq : objsTree.toList[o.oi] = io := by
        rw [List.getElem?_eq_getElem hoi_lt] at hio_elem; exact Option.some.inj hio_elem
      have ho_ok := allIdx_toList_getElem hszO hobjs.1.2 hoi_lt
      rw [hio_eq] at ho_ok
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_ok
      obtain ⟨szSec, hszSec⟩ := ho_ok.1.1.1.1.2
      obtain ⟨szSy, hszSy⟩ := ho_ok.1.1.1.2
      have hsec_elem : io.sections.toList[o.si]? = some sec := by
        rw [← IdxTree.get?_eq_getElem? hszSec o.si]; exact hsec
      refine ⟨io.toExtractedObj names, sec.toRawSec names, ?_, ?_, hnd_disc _ _,
        hexec, hro, hnob, htls, hlen_pos, hst4, hln4, hend_le, hsec_len, ?_, hsal, ?_, ?_⟩
      · simp [List.getElem?_map, hio_elem]
      · simp [IObj.toExtractedObj, List.getElem?_map, hsec_elem]
      · simpa [IMultiLib.toMultiPlacedLib, IBlock.toCodeBlock, ISec.toRawSec] using hcode_eq
      · simpa [IMultiLib.toMultiPlacedLib, IBlock.toCodeBlock, ISec.toRawSec] using hbal
      · intro sym off hmem_sym
        simp only [IBlock.toCodeBlock, List.mem_map] at hmem_sym
        obtain ⟨⟨s, off', wit?⟩, hmem_s, hpair_eq⟩ := hmem_sym
        dsimp only at hpair_eq
        rcases Prod.mk.inj hpair_eq with ⟨rfl, rfl⟩
        rw [List.all_eq_true] at hsyms
        have hs_ok := hsyms (s, off', wit?) hmem_s
        dsimp only at hs_ok
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs_ok
        refine ⟨hs_ok.1.1.2, hs_ok.1.2, ?_⟩
        cases wit? with
        | none =>
          exact Or.inr (unclaimed_of_rawClaimed_false hsz hcsz heq hnd h0 hobjs_orig
            hs_ok.1.1.1 (by simpa only [beq_iff_eq] using hs_ok.2))
        | some k =>
          have hwk := hs_ok.2; dsimp only at hwk
          cases hsy : io.symbols.get? k with
          | none => rw [hsy] at hwk; exact nomatch hwk
          | some sy =>
            rw [hsy] at hwk; dsimp only at hwk
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hwk
            have hsy_elem : io.symbols.toList[k]? = some sy := by
              rw [← IdxTree.get?_eq_getElem? hszSy k]; exact hsy
            have hk_lt : k < io.symbols.toList.length := (List.getElem?_eq_some_iff.1 hsy_elem).1
            have hsy_eq : io.symbols.toList[k] = sy := by
              rw [List.getElem?_eq_getElem hk_lt] at hsy_elem; exact Option.some.inj hsy_elem
            have hsy_chk := allIdx_toList_getElem hszSy ho_ok.2 hk_lt
            rw [hsy_eq] at hsy_chk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy_chk
            left
            refine ⟨sy.toRawSym names,
              List.mem_map.2 ⟨sy, IdxTree.mem_toList_of_get? hsy, rfl⟩,
              hwk.1.1.1.1, hwk.1.1.1.2,
              (symAt_ne_empty_iff hsz hnd h0 hsy_chk.1.1.1).2 hwk.1.1.2,
              hwk.1.2, ?_⟩
            have hder := symNameDerived_of_isym hsz hcsz heq hobjs_orig hoi_lt
              (by simp only [hio_eq]; exact hk_lt)
              (by simp only [hio_eq, hsy_eq]; exact hwk.1.1.2)
              (symId := s) (by simp only [hio_eq, hsy_eq]; exact hwk.2)
            simpa [hio_eq, hsy_eq] using hder

/-- Per-group single-pass byte check for non-`SHT_NOBITS` data slices. -/
def checkDataGroupsBytesB (objsTree : IdxTree IObj) (dataTree : IdxTree IData)
    (dOTree : IdxTree SliceOrigin) (dataGroups : IdxTree SliceGroup) : Bool :=
  dataGroups.all fun g =>
    match objsTree.get? g.oi with
    | none => false
    | some io =>
      match io.sections.get? g.si with
      | none => false
      | some sec =>
        if sec.isNobits then true
        else
          let slices := g.indices.toList.map fun di =>
            match dOTree.get? di, dataTree.get? di with
            | some o, some d => (o.start, o.len, d.bytes)
            | _, _ => (0, 0, [])
          checkByteSlicesWalk slices sec.size 0 sec.bytes

/-- Per-data metadata, `.bss` zero-tail, alignment, and `CoversDataSlice` / `UnclaimedSymName`
    check. -/
def checkDataSlicesMetaB (N : Nat) (objsTree : IdxTree IObj) (dataTree : IdxTree IData)
    (dOTree : IdxTree SliceOrigin) (rawClaimed : IdxTree Bool) : Bool :=
  IdxTree.allIdx (fun di d =>
    match dOTree.get? di with
    | none => false
    | some o =>
      match objsTree.get? o.oi with
      | none => false
      | some io =>
        match io.sections.get? o.si with
        | none => false
        | some sec =>
          (!sec.isExec) && (!sec.isTls) && decide (o.start + o.len ≤ sec.size) &&
          (d.readOnly == sec.readOnly) &&
          (if sec.isNobits then d.bytes.isEmpty && (d.zeroTail == o.len)
           else d.zeroTail == 0) &&
          decide (0 < sec.align) && (d.align % Nat.gcd sec.align o.start == 0) &&
          decide (d.sym < N) &&
          match d.covWit with
          | some k =>
            match io.symbols.get? k with
            | none => false
            | some sy =>
              (sy.kind == .object) && (sy.sec == .sec o.si) &&
              (sy.value == o.start) && (sy.size == o.len) && (sy.rawId != 0) &&
              ((d.sym == sy.nameId) || (d.sym == sy.derivedId))
          | none =>
            (rawClaimed.get? d.sym == some false) &&
            io.symbols.all fun sy =>
              !((sy.kind == .object) && (sy.sec == .sec o.si) &&
                (sy.value == o.start) && (sy.size == o.len) && (sy.rawId != 0))) 0 dataTree

theorem validDataSlices_of_check {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N D : Nat} (hsz : names.size? = some N) (hcsz : charsTree.size? = some N)
    (heq : names.toList = charsTree.toList.map String.ofList)
    (hnd : names.toList.Nodup) (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {L : IMultiLib}
    {dOTree : IdxTree SliceOrigin} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    {dataGroups : IdxTree SliceGroup} {dataToGroup : IdxTree (Nat × Nat)}
    (hD : L.data.size? = some D)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    (hddisj : checkGroupsDisjointB D dOTree dataGroups dataToGroup = true)
    (hdbytes : checkDataGroupsBytesB objsTree L.data dOTree dataGroups = true)
    (hdmeta : checkDataSlicesMetaB N objsTree L.data dOTree rawClaimed = true) :
    ∀ i : Fin (L.toMultiPlacedLib names).data.length,
      ValidDataSlice (objsTree.toList.map (IObj.toExtractedObj names))
        (L.toMultiPlacedLib names).data[i] (originAt dOTree i) := by
  intro i
  have hlenD : L.data.toList.length = D := IdxTree.length_toList_of_size? hD
  have hiD : i.1 < D := by
    have hiL : i.1 < L.data.toList.length := by simpa [IMultiLib.toMultiPlacedLib] using i.2
    omega
  have hiL : i.1 < L.data.toList.length := hlenD ▸ hiD
  obtain ⟨gi, _, o, g, ho_get, horig, hg_get, hgoi, hgsi, _, hi_mem⟩ :=
    group_mem_of_toGroup hddisj ⟨i.1, hiD⟩
  have horig_i : originAt dOTree i = o := horig
  have hdi_eq : (L.toMultiPlacedLib names).data[i] = L.data.toList[i.1].toSymDataInfo names := by
    change (L.toMultiPlacedLib names).data[i.1] = _
    simp [IMultiLib.toMultiPlacedLib]
  rw [horig_i, hdi_eq]
  have hd_get : L.data.get? i.1 = some L.data.toList[i.1] := by
    rw [IdxTree.get?_eq_getElem? hD i.1, List.getElem?_eq_getElem hiL]
  have hm := allIdx_toList_getElem hD hdmeta hiL
  rw [ho_get] at hm; dsimp only at hm
  cases hio : objsTree.get? o.oi with
  | none => rw [hio] at hm; exact nomatch hm
  | some io =>
    rw [hio] at hm; dsimp only at hm
    cases hsec : io.sections.get? o.si with
    | none => rw [hsec] at hm; exact nomatch hm
    | some sec =>
      rw [hsec] at hm; dsimp only at hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hm
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hnexec, hntls⟩, hend_le⟩, hro⟩, hnob_branch⟩, hsal⟩, hdal⟩, hdsym_lt⟩, hcov⟩ := hm
      unfold checkObjSymsB at hobjs
      have hobjs_orig := hobjs
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
      obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
      have hio_elem : objsTree.toList[o.oi]? = some io := by
        rw [← IdxTree.get?_eq_getElem? hszO o.oi]; exact hio
      have hoi_lt : o.oi < objsTree.toList.length := (List.getElem?_eq_some_iff.1 hio_elem).1
      have hio_eq : objsTree.toList[o.oi] = io := by
        rw [List.getElem?_eq_getElem hoi_lt] at hio_elem; exact Option.some.inj hio_elem
      have ho_ok := allIdx_toList_getElem hszO hobjs.1.2 hoi_lt
      rw [hio_eq] at ho_ok
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_ok
      obtain ⟨szSec, hszSec⟩ := ho_ok.1.1.1.1.2
      obtain ⟨szSy, hszSy⟩ := ho_ok.1.1.1.2
      have hsec_elem : io.sections.toList[o.si]? = some sec := by
        rw [← IdxTree.get?_eq_getElem? hszSec o.si]; exact hsec
      refine ⟨io.toExtractedObj names, sec.toRawSec names, ?_, ?_, hnd_disc _ _,
        hnexec, hntls, hend_le, ?_, ?_, hsal, ?_, ?_⟩
      · simp [List.getElem?_map, hio_elem]
      · simp [IObj.toExtractedObj, List.getElem?_map, hsec_elem]
      · simpa [IData.toSymDataInfo, ISec.toRawSec] using hro
      · dsimp only [IData.toSymDataInfo, ISec.toRawSec]
        by_cases hnb : sec.isNobits = true
        · simp only [hnb, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hnob_branch ⊢
          exact hnob_branch
        · have hnbf : sec.isNobits = false := Bool.eq_false_iff.2 hnb
          simp only [hnbf, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hnob_branch ⊢
          have hgb := hdbytes
          unfold checkDataGroupsBytesB at hgb
          rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hgb
          have hgb_i := hgb g (IdxTree.mem_toList_of_get? hg_get)
          rw [← hgoi, ← hgsi, hio] at hgb_i; dsimp only at hgb_i
          rw [hsec] at hgb_i; dsimp only at hgb_i
          simp only [hnbf, Bool.false_eq_true, ↓reduceIte] at hgb_i
          obtain ⟨hsec_len, hwalk⟩ := checkByteSlicesWalk_spec hgb_i
          have hmem_slice : (o.start, o.len, L.data.toList[i.1].bytes) ∈
              (g.indices.toList.map fun di =>
                match dOTree.get? di, L.data.get? di with
                | some o', some d' => (o'.start, o'.len, d'.bytes)
                | _, _ => (0, 0, [])) := by
            refine List.mem_map.2 ⟨i.1, hi_mem, ?_⟩
            rw [ho_get, hd_get]
          obtain ⟨_, hbytes_eq⟩ := hwalk o.start o.len L.data.toList[i.1].bytes hmem_slice
          exact ⟨hsec_len, hbytes_eq, hnob_branch⟩
      · simpa [IData.toSymDataInfo, ISec.toRawSec] using hdal
      · dsimp only [IData.toSymDataInfo]
        cases hcw : L.data.toList[i.1].covWit with
        | some k =>
          rw [hcw] at hcov; dsimp only at hcov
          cases hsy : io.symbols.get? k with
          | none => rw [hsy] at hcov; exact nomatch hcov
          | some sy =>
            rw [hsy] at hcov; dsimp only at hcov
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hcov
            have hsy_elem : io.symbols.toList[k]? = some sy := by
              rw [← IdxTree.get?_eq_getElem? hszSy k]; exact hsy
            have hk_lt : k < io.symbols.toList.length := (List.getElem?_eq_some_iff.1 hsy_elem).1
            have hsy_eq : io.symbols.toList[k] = sy := by
              rw [List.getElem?_eq_getElem hk_lt] at hsy_elem; exact Option.some.inj hsy_elem
            have hsy_chk := allIdx_toList_getElem hszSy ho_ok.2 hk_lt
            rw [hsy_eq] at hsy_chk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy_chk
            left
            refine ⟨sy.toRawSym names,
              List.mem_map.2 ⟨sy, IdxTree.mem_toList_of_get? hsy, rfl⟩,
              ⟨hcov.1.1.1.1.1, hcov.1.1.1.1.2, hcov.1.1.1.2, hcov.1.1.2,
                (symAt_ne_empty_iff hsz hnd h0 hsy_chk.1.1.1).2 hcov.1.2⟩,
              ?_⟩
            have hder := symNameDerived_of_isym hsz hcsz heq hobjs_orig hoi_lt
              (by simp only [hio_eq]; exact hk_lt)
              (by simp only [hio_eq, hsy_eq]; exact hcov.1.2)
              (symId := L.data.toList[i.1].sym) (by simp only [hio_eq, hsy_eq]; exact hcov.2)
            simpa [hio_eq, hsy_eq] using hder
        | none =>
          rw [hcw] at hcov; dsimp only at hcov
          simp only [Bool.and_eq_true, beq_iff_eq] at hcov
          right
          refine ⟨?_, unclaimed_of_rawClaimed_false hsz hcsz heq hnd h0 hobjs_orig
            hdsym_lt hcov.1⟩
          rintro ⟨sy, hsy_mem, hcd⟩
          simp only [IObj.toExtractedObj, List.mem_map] at hsy_mem
          obtain ⟨isy, hisy_mem, rfl⟩ := hsy_mem
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hisy_mem
          have hisy_chk := allIdx_toList_getElem hszSy ho_ok.2 hk
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hisy_chk
          have hno := hcov.2
          rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hno
          have hno_k := hno io.symbols.toList[k] (List.getElem_mem hk)
          have hraw_ne : io.symbols.toList[k].rawId ≠ 0 :=
            (symAt_ne_empty_iff hsz hnd h0 hisy_chk.1.1.1).1 hcd.2.2.2.2
          dsimp only [CoversDataSlice, ISym.toRawSym] at hcd
          simp [hcd.1, hcd.2.1, hcd.2.2.1, hcd.2.2.2.1, hraw_ne] at hno_k

/-! ## Relocations, exports, externs, and `LabelsFromObjects` soundness -/

/-- Certify `perm` is a bijection on `0 ..< n` via left-inverse `invPerm : IdxTree Nat`. -/
def checkPermBij (n : Nat) (perm : List Nat) (invPerm : IdxTree Nat) : Bool :=
  (perm.length == n) && (invPerm.size? == some n) &&
  checkListIdx (fun k pk => decide (pk < n) && (invPerm.get? pk == some k)) 0 perm

theorem permBij_of_check {n : Nat} {perm : List Nat} {invPerm : IdxTree Nat}
    (h : checkPermBij n perm invPerm = true) :
    perm.length = n ∧ perm.Nodup ∧ ∀ k (hk : k < perm.length), perm[k] < n := by
  unfold checkPermBij at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hlen, _⟩, hchk⟩ := h
  have hall := (checkListIdx_eq_true_iff _ 0 perm).1 hchk
  refine ⟨hlen, List.nodup_iff_eq_of_getElem_eq.2 ?_, ?_⟩
  · intro i j hi hj heq
    have hi_ok := hall i hi
    have hj_ok := hall j hj
    simp only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi_ok hj_ok
    have hinv := hi_ok.2
    rw [heq, hj_ok.2] at hinv
    exact (Option.some.inj hinv).symm
  · intro k hk
    have hk_ok := hall k hk
    simp only [Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq] at hk_ok
    exact hk_ok.1

/-- Resolve an internal raw relocation target `(oj, sj, t)` from `(oi, symIdx, sy)` and
    `rawSummary`: `STB_LOCAL` definitions resolve in place, and non-local references resolve only
    to the unique non-local definition across `objs` recorded in `rawSummary` (failing closed on
    every other precedence situation). -/
def resolveIRelocInternal? (objsTree : IdxTree IObj) (rawSummary : IdxTree RawIdStatus)
    (oi symIdx : Nat) (sy : ISym) (rrAddend : Int) : Option (Nat × Nat × Int) :=
  match sy.sec with
  | .sec sj =>
    if sy.bind == .local then
      some (oi, sj, (sy.value : Int) + rrAddend)
    else
      match rawSummary.get? sy.rawId with
      | some (.globalDef oj k sj') =>
        if (oj == oi) && (k == symIdx) && (sj' == sj) then
          some (oi, sj, (sy.value : Int) + rrAddend)
        else none
      | _ => none
  | .undef =>
    if sy.bind == .local then none
    else
      match rawSummary.get? sy.rawId with
      | some (.globalDef oj k sj) =>
        match objsTree.get? oj with
        | none => none
        | some ojObj =>
          match ojObj.symbols.get? k with
          | none => none
          | some tSym => some (oj, sj, (tSym.value : Int) + rrAddend)
      | _ => none
  | .other => none

private theorem resolveIRelocInternal?_spec {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup) (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    {oi symIdx : Nat} {o : IObj} {sy : ISym}
    (ho : objsTree.get? oi = some o) (hsy : o.symbols.get? symIdx = some sy)
    (hsy_raw : sy.rawId < N) {rrAddend : Int}
    {oj sj : Nat} {t : Int}
    (hres : resolveIRelocInternal? objsTree rawSummary oi symIdx sy rrAddend = some (oj, sj, t)) :
    ∃ tSym : RawSym,
      ((sy.toRawSym names).bind = .local ∧ oj = oi ∧ (sy.toRawSym names).sec = .sec sj ∧
          ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi sj ∧
          tSym = sy.toRawSym names ∧ t = ((sy.toRawSym names).value : Int) + rrAddend) ∨
        ((sy.toRawSym names).bind ≠ .local ∧
          ∃ k, Resolves (objsTree.toList.map (IObj.toExtractedObj names))
            (sy.toRawSym names).rawName oj k sj tSym ∧
          t = (tSym.value : Int) + rrAddend) := by
  unfold resolveIRelocInternal? at hres
  cases hsec : sy.sec with
  | sec sj' =>
    rw [hsec] at hres; dsimp only at hres
    cases hloc : (sy.bind == .local) with
    | true =>
      rw [hloc] at hres; simp only [↓reduceIte] at hres
      injection hres with htuple
      injection htuple with hoj hrest
      injection hrest with hsj ht
      subst hoj; subst hsj; subst ht
      exact ⟨sy.toRawSym names,
        Or.inl ⟨beq_iff_eq.1 hloc, rfl, hsec, hnd_disc _ _, rfl, rfl⟩⟩
    | false =>
      rw [hloc] at hres; simp only [Bool.false_eq_true, ↓reduceIte] at hres
      have hloc' : (sy.toRawSym names).bind ≠ .local := by
        intro h; dsimp only [ISym.toRawSym] at h; rw [h] at hloc; exact nomatch hloc
      cases hrs : rawSummary.get? sy.rawId with
      | none => rw [hrs] at hres; exact nomatch hres
      | some st =>
        rw [hrs] at hres
        cases st with
        | other => exact nomatch hres
        | allNonLocalUndef => exact nomatch hres
        | weakOnlyUndef _ _ => exact nomatch hres
        | globalDef oj' k sj'' =>
          dsimp only at hres
          cases hcond : ((oj' == oi) && (k == symIdx) && (sj'' == sj')) with
          | false => rw [hcond] at hres; exact nomatch hres
          | true =>
            rw [hcond] at hres; simp only [↓reduceIte] at hres
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            rcases hcond with ⟨⟨rfl, rfl⟩, rfl⟩
            obtain ⟨oDef, syDef, hoDef, hsyDef, hrgd⟩ :=
              resolves_of_summary hsz hnd h0 hobjs hnd_disc hsy_raw hrs
            rw [ho] at hoDef; cases hoDef
            rw [hsy] at hsyDef; cases hsyDef
            injection hres with htuple
            injection htuple with hoj hrest
            injection hrest with hsj ht
            subst hoj; subst hsj; subst ht
            exact ⟨sy.toRawSym names, Or.inr ⟨hloc', k, hrgd, rfl⟩⟩
  | other => rw [hsec] at hres; exact nomatch hres
  | undef =>
    rw [hsec] at hres; dsimp only at hres
    cases hloc : (sy.bind == .local) with
    | true => rw [hloc] at hres; simp only [↓reduceIte] at hres; exact nomatch hres
    | false =>
      rw [hloc] at hres; simp only [Bool.false_eq_true, ↓reduceIte] at hres
      have hloc' : (sy.toRawSym names).bind ≠ .local := by
        intro h; dsimp only [ISym.toRawSym] at h; rw [h] at hloc; exact nomatch hloc
      cases hrs : rawSummary.get? sy.rawId with
      | none => rw [hrs] at hres; exact nomatch hres
      | some st =>
        rw [hrs] at hres
        cases st with
        | other => exact nomatch hres
        | allNonLocalUndef => exact nomatch hres
        | weakOnlyUndef _ _ => exact nomatch hres
        | globalDef oj' k sj' =>
          dsimp only at hres
          obtain ⟨oDef, syDef, hoDef, hsyDef, hrgd⟩ :=
            resolves_of_summary hsz hnd h0 hobjs hnd_disc hsy_raw hrs
          rw [hoDef] at hres; dsimp only at hres
          rw [hsyDef] at hres; dsimp only at hres
          injection hres with htuple
          injection htuple with hoj hrest
          injection hrest with hsj ht
          subst hoj; subst hsj; subst ht
          exact ⟨syDef.toRawSym names, Or.inr ⟨hloc', k, hrgd, rfl⟩⟩

/-- Interned $O(\log N)$ relocation-match check corresponding to `Arm64.Obj.RelocMatches`. -/
def checkIRelocMatchesB (N : Nat) (objsTree : IdxTree IObj)
    (bOTree dOTree : IdxTree SliceOrigin) (symRole : IdxTree SymRole)
    (rawSummary : IdxTree RawIdStatus) (oi sliceStart : Nat)
    (rr : RawReloc) (ir : IReloc) : Bool :=
  decide (ir.sym < N) && (ir.off + sliceStart == rr.off) && (rr.kind == some ir.kind) &&
  match objsTree.get? oi with
  | none => false
  | some o =>
    match o.symbols.get? rr.symIdx with
    | none => false
    | some sy =>
      match resolveIRelocInternal? objsTree rawSummary oi rr.symIdx sy rr.addend with
      | some (oj, sj, t) =>
        match objsTree.get? oj with
        | none => false
        | some ojObj =>
          match ojObj.sections.get? sj with
          | none => false
          | some secT =>
            if secT.isExec then
              match symRole.get? ir.sym with
              | some (.blockSym bj _ off) =>
                match bOTree.get? bj with
                | none => false
                | some bo =>
                  (bo.oi == oj) && (bo.si == sj) &&
                  decide (0 ≤ (off : Int) + ir.addend) &&
                  decide ((off : Int) + ir.addend ≤ (bo.len : Int)) &&
                  (((bo.start + off : Int) + ir.addend) == t)
              | _ => false
            else if !secT.isTls then
              match symRole.get? ir.sym with
              | some (.dataSym dj) =>
                match dOTree.get? dj with
                | none => false
                | some do_ =>
                  (do_.oi == oj) && (do_.si == sj) &&
                  decide (0 ≤ ir.addend) &&
                  decide (ir.addend ≤ (do_.len : Int)) &&
                  (((do_.start : Int) + ir.addend) == t)
              | _ => false
            else
              (symRole.get? ir.sym == some .other) &&
              match ojObj.symbols.get? ir.tlsSymWit with
              | none => false
              | some ts =>
                (ts.sec == .sec sj) && (ts.kind == .tls) && (ts.rawId != 0) &&
                (ir.sym == ts.rawId) && (((ts.value : Int) + ir.addend) == t)
      | none =>
        (sy.sec == .undef) && (sy.rawId == ir.sym) && (ir.sym != 0) &&
        (ir.addend == rr.addend) && (symRole.get? ir.sym == some .other) &&
        match rawSummary.get? ir.sym with
        | some .allNonLocalUndef | some (.weakOnlyUndef _ _) => true
        | _ => false

theorem relocMatches_of_checkI {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N B D : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {L : IMultiLib} {bOTree dOTree : IdxTree SliceOrigin}
    {symRole : IdxTree SymRole} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hB : L.blocks.size? = some B) (hD : L.data.size? = some D)
    (hbO_sz : bOTree.size? = some B) (hdO_sz : dOTree.size? = some D)
    (hroles : checkSymRolesB N L symRole = true)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    {oi sliceStart : Nat} {rr : RawReloc} {ir : IReloc}
    (hchk : checkIRelocMatchesB N objsTree bOTree dOTree symRole rawSummary oi sliceStart rr ir = true) :
    RelocMatches (objsTree.toList.map (IObj.toExtractedObj names))
      (L.toMultiPlacedLib names) (originAt bOTree) (originAt dOTree)
      oi sliceStart rr (ir.toEntry names) := by
  unfold checkIRelocMatchesB at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  obtain ⟨⟨⟨hir_lt, hoff_eq⟩, hkind_eq⟩, hrest⟩ := hchk
  cases ho : objsTree.get? oi with
  | none => rw [ho] at hrest; exact nomatch hrest
  | some o =>
    rw [ho] at hrest; dsimp only at hrest
    cases hsy : o.symbols.get? rr.symIdx with
    | none => rw [hsy] at hrest; exact nomatch hrest
    | some sy =>
      rw [hsy] at hrest; dsimp only at hrest
      have hobjs_orig := hobjs
      unfold checkObjSymsB at hobjs
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
      obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
      have ho_elem : objsTree.toList[oi]? = some o := by
        rw [← IdxTree.get?_eq_getElem? hszO oi]; exact ho
      have hoi_lt : oi < objsTree.toList.length := (List.getElem?_eq_some_iff.1 ho_elem).1
      have ho_eq : objsTree.toList[oi] = o := by
        rw [List.getElem?_eq_getElem hoi_lt] at ho_elem; exact Option.some.inj ho_elem
      have ho_ok := allIdx_toList_getElem hszO hobjs.1.2 hoi_lt
      rw [ho_eq] at ho_ok
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_ok
      obtain ⟨szSy, hszSy⟩ := ho_ok.1.1.1.2
      have hsy_elem : o.symbols.toList[rr.symIdx]? = some sy := by
        rw [← IdxTree.get?_eq_getElem? hszSy rr.symIdx]; exact hsy
      have hsymIdx_lt : rr.symIdx < o.symbols.toList.length :=
        (List.getElem?_eq_some_iff.1 hsy_elem).1
      have hsy_eq : o.symbols.toList[rr.symIdx] = sy := by
        rw [List.getElem?_eq_getElem hsymIdx_lt] at hsy_elem; exact Option.some.inj hsy_elem
      have hsy_chk := allIdx_toList_getElem hszSy ho_ok.2 hsymIdx_lt
      rw [hsy_eq] at hsy_chk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsy_chk
      have hsy_raw_lt : sy.rawId < N := hsy_chk.1.1.1
      refine ⟨hoff_eq, hkind_eq, o.toExtractedObj names, sy.toRawSym names, ?_, ?_, ?_⟩
      · simp [List.getElem?_map, ho_elem]
      · simp [IObj.toExtractedObj, List.getElem?_map, hsy_elem]
      · cases hres : resolveIRelocInternal? objsTree rawSummary oi rr.symIdx sy rr.addend with
        | some triple =>
          rcases triple with ⟨oj, sj, t⟩
          rw [hres] at hrest; dsimp only at hrest
          obtain ⟨tSym, htSym⟩ :=
            resolveIRelocInternal?_spec hsz hnd h0 hobjs_orig hnd_disc ho hsy hsy_raw_lt hres
          cases hoj : objsTree.get? oj with
          | none => rw [hoj] at hrest; exact nomatch hrest
          | some ojObj =>
            rw [hoj] at hrest; dsimp only at hrest
            cases hsj : ojObj.sections.get? sj with
            | none => rw [hsj] at hrest; exact nomatch hrest
            | some secT =>
              rw [hsj] at hrest; dsimp only at hrest
              have hoj_elem : objsTree.toList[oj]? = some ojObj := by
                rw [← IdxTree.get?_eq_getElem? hszO oj]; exact hoj
              have hoj_lt : oj < objsTree.toList.length :=
                (List.getElem?_eq_some_iff.1 hoj_elem).1
              have hoj_eq : objsTree.toList[oj] = ojObj := by
                rw [List.getElem?_eq_getElem hoj_lt] at hoj_elem; exact Option.some.inj hoj_elem
              have hoj_ok := allIdx_toList_getElem hszO hobjs.1.2 hoj_lt
              rw [hoj_eq] at hoj_ok
              simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hoj_ok
              obtain ⟨szSecT, hszSecT⟩ := hoj_ok.1.1.1.1.2
              obtain ⟨szSyT, hszSyT⟩ := hoj_ok.1.1.1.2
              have hsj_elem : ojObj.sections.toList[sj]? = some secT := by
                rw [← IdxTree.get?_eq_getElem? hszSecT sj]; exact hsj
              left
              refine ⟨oj, sj, ojObj.toExtractedObj names, secT.toRawSec names, tSym, t,
                htSym, ?_, ?_, ?_⟩
              · simp [List.getElem?_map, hoj_elem]
              · simp [IObj.toExtractedObj, List.getElem?_map, hsj_elem]
              · by_cases hex : secT.isExec = true
                · simp only [hex, ↓reduceIte] at hrest
                  left
                  refine ⟨hex, ?_⟩
                  cases hrg : symRole.get? ir.sym with
                  | none => rw [hrg] at hrest; exact nomatch hrest
                  | some role =>
                    rw [hrg] at hrest
                    cases role with
                    | other => exact nomatch hrest
                    | dataSym _ => exact nomatch hrest
                    | blockSym bj j off =>
                      dsimp only at hrest
                      cases hbo : bOTree.get? bj with
                      | none => rw [hbo] at hrest; exact nomatch hrest
                      | some bo =>
                        rw [hbo] at hrest; dsimp only at hrest
                        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrest
                        have hlk := lookupBlockSym_eq_of_role hsz hnd hroles hir_lt
                        rw [hrg] at hlk
                        have hbo_elem : bOTree.toList[bj]? = some bo := by
                          rw [← IdxTree.get?_eq_getElem? hbO_sz bj]; exact hbo
                        have hbj_B : bj < B := by
                          have hlt := (List.getElem?_eq_some_iff.1 hbo_elem).1
                          rw [IdxTree.length_toList_of_size? hbO_sz] at hlt
                          exact hlt
                        have hbj_lib : bj < (L.toMultiPlacedLib names).blocks.length := by
                          simp [IMultiLib.toMultiPlacedLib, IdxTree.length_toList_of_size? hB, hbj_B]
                        have horig_bo : originAt bOTree ⟨bj, hbj_lib⟩ = bo := by
                          unfold originAt; rw [hbo]; rfl
                        refine ⟨bj, off, hlk, hbj_lib, ?_⟩
                        rw [horig_bo]
                        exact ⟨hrest.1.1.1.1, hrest.1.1.1.2, hrest.1.1.2, hrest.1.2, hrest.2⟩
                · have hexf : secT.isExec = false := Bool.eq_false_iff.2 hex
                  simp only [hexf, Bool.false_eq_true, ↓reduceIte] at hrest
                  right
                  by_cases htls : secT.isTls = false
                  · have hntls : (!secT.isTls) = true := by simp [htls]
                    simp only [hntls, ↓reduceIte] at hrest
                    left
                    refine ⟨hexf, htls, ?_, ?_⟩
                    · cases hrg : symRole.get? ir.sym with
                      | none => rw [hrg] at hrest; exact nomatch hrest
                      | some role =>
                        rw [hrg] at hrest
                        cases role with
                        | other => exact nomatch hrest
                        | blockSym _ _ _ => exact nomatch hrest
                        | dataSym _ =>
                          have hlk := lookupBlockSym_eq_of_role hsz hnd hroles hir_lt
                          rw [hrg] at hlk; exact hlk
                    · cases hrg : symRole.get? ir.sym with
                      | none => rw [hrg] at hrest; exact nomatch hrest
                      | some role =>
                        rw [hrg] at hrest
                        cases role with
                        | other => exact nomatch hrest
                        | blockSym _ _ _ => exact nomatch hrest
                        | dataSym dj =>
                          dsimp only at hrest
                          cases hdo : dOTree.get? dj with
                          | none => rw [hdo] at hrest; exact nomatch hrest
                          | some do_ =>
                            rw [hdo] at hrest; dsimp only at hrest
                            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrest
                            have hdo_elem : dOTree.toList[dj]? = some do_ := by
                              rw [← IdxTree.get?_eq_getElem? hdO_sz dj]; exact hdo
                            have hdj_D : dj < D := by
                              have hlt := (List.getElem?_eq_some_iff.1 hdo_elem).1
                              rw [IdxTree.length_toList_of_size? hdO_sz] at hlt
                              exact hlt
                            have hdj_L : dj < L.data.toList.length := by
                              rw [IdxTree.length_toList_of_size? hD]; exact hdj_D
                            have hdj_lib : dj < (L.toMultiPlacedLib names).data.length := by
                              simp [IMultiLib.toMultiPlacedLib, hdj_L]
                            have horig_do : originAt dOTree ⟨dj, hdj_lib⟩ = do_ := by
                              unfold originAt; rw [hdo]; rfl
                            have hroles_orig := hroles
                            unfold checkSymRolesB at hroles
                            simp only [Bool.and_eq_true] at hroles
                            have hszR : symRole.size? = some N := by
                              simpa only [beq_iff_eq] using hroles.1.1.1.1.1
                            have hlenR : symRole.toList.length = N :=
                              IdxTree.length_toList_of_size? hszR
                            have hinv := allIdx_toList_getElem hszR hroles.2 (hlenR ▸ hir_lt)
                            have hrg_eq : symRole.toList[ir.sym]'(hlenR ▸ hir_lt) = .dataSym dj := by
                              rw [IdxTree.get?_eq_getElem? hszR ir.sym,
                                List.getElem?_eq_getElem (hlenR ▸ hir_lt)] at hrg
                              exact Option.some.inj hrg
                            rw [hrg_eq] at hinv; dsimp only at hinv
                            rw [IdxTree.get?_eq_getElem? hD dj,
                              List.getElem?_eq_getElem hdj_L] at hinv
                            dsimp only at hinv
                            have hdsym_id : L.data.toList[dj].sym = ir.sym := beq_iff_eq.1 hinv
                            refine ⟨⟨dj, hdj_lib⟩, ?_, ?_⟩
                            · change ((L.toMultiPlacedLib names).data[dj]'hdj_lib).sym = _
                              simp [IMultiLib.toMultiPlacedLib, IData.toSymDataInfo, hdsym_id,
                                IReloc.toEntry]
                            · rw [horig_do]
                              exact ⟨hrest.1.1.1.1, hrest.1.1.1.2, hrest.1.1.2, hrest.1.2, hrest.2⟩
                  · have htlst : secT.isTls = true := by
                      cases htl : secT.isTls with
                      | true => rfl
                      | false => exact False.elim (htls htl)
                    have hntls : (!secT.isTls) = false := by simp [htlst]
                    simp only [hntls, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
                      beq_iff_eq] at hrest
                    obtain ⟨hrg_oth, htls_rest⟩ := hrest
                    right
                    have hlk := lookupBlockSym_eq_of_role hsz hnd hroles hir_lt
                    rw [hrg_oth] at hlk
                    have hnod := not_mem_data_of_role hsz hnd hroles hir_lt (by simp [hrg_oth])
                    refine ⟨hexf, htlst, hlk, hnod, ?_⟩
                    cases hts : ojObj.symbols.get? ir.tlsSymWit with
                    | none => rw [hts] at htls_rest; exact nomatch htls_rest
                    | some ts =>
                      rw [hts] at htls_rest; dsimp only at htls_rest
                      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at htls_rest
                      have hts_elem : ojObj.symbols.toList[ir.tlsSymWit]? = some ts := by
                        rw [← IdxTree.get?_eq_getElem? hszSyT ir.tlsSymWit]; exact hts
                      have hts_lt : ir.tlsSymWit < ojObj.symbols.toList.length :=
                        (List.getElem?_eq_some_iff.1 hts_elem).1
                      have hts_eq : ojObj.symbols.toList[ir.tlsSymWit] = ts := by
                        rw [List.getElem?_eq_getElem hts_lt] at hts_elem
                        exact Option.some.inj hts_elem
                      have hts_chk := allIdx_toList_getElem hszSyT hoj_ok.2 hts_lt
                      rw [hts_eq] at hts_chk
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hts_chk
                      refine ⟨ts.toRawSym names,
                        List.mem_map.2 ⟨ts, IdxTree.mem_toList_of_get? hts, rfl⟩,
                        htls_rest.1.1.1.1, htls_rest.1.1.1.2,
                        (symAt_ne_empty_iff hsz hnd h0 hts_chk.1.1.1).2 htls_rest.1.1.2,
                        by dsimp only [IReloc.toEntry, ISym.toRawSym]; rw [htls_rest.1.2],
                        htls_rest.2⟩
        | none =>
          rw [hres] at hrest; dsimp only at hrest
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hrest
          obtain ⟨⟨⟨⟨⟨hsec_u, hraw_id⟩, hir_ne0⟩, hadd⟩, hrg_oth⟩, hsum⟩ := hrest
          right
          have hlk := lookupBlockSym_eq_of_role hsz hnd hroles hir_lt
          rw [hrg_oth] at hlk
          have hnod := not_mem_data_of_role hsz hnd hroles hir_lt (by simp [hrg_oth])
          refine ⟨hsec_u, ?_, (symAt_ne_empty_iff hsz hnd h0 hir_lt).2 hir_ne0,
            hadd, hlk, hnod, allNonLocalUndef_of_summary hsz hnd hobjs_orig hir_lt hsum⟩
          dsimp only [ISym.toRawSym, IReloc.toEntry]; rw [hraw_id]

/-- Linear simultaneous walk over filtered `raw` relocations and permutation indices `perm`. -/
def checkRawPermLoop (chk : RawReloc → IReloc → Bool) (irs : IdxTree IReloc) :
    List RawReloc → List Nat → Bool
  | [], [] => true
  | rr :: rrs, pk :: pks =>
    match irs.get? pk with
    | none => false
    | some ir => chk rr ir && checkRawPermLoop chk irs rrs pks
  | _, _ => false

private theorem checkRawPermLoop_getElem {chk : RawReloc → IReloc → Bool} {irs : IdxTree IReloc} :
    ∀ {raw : List RawReloc} {perm : List Nat}
      (_ : checkRawPermLoop chk irs raw perm = true)
      (k : Nat) (hk : k < raw.length) (hp : k < perm.length),
      ∃ ir, irs.get? perm[k] = some ir ∧ chk raw[k] ir = true
  | [], _, _, _, hk, _ => nomatch hk
  | _ :: _, [], _, _, _, hp => nomatch hp
  | rr :: rrs, pk :: pks, h, 0, _, _ => by
    simp only [checkRawPermLoop] at h
    cases hir : irs.get? pk with
    | none => rw [hir] at h; exact nomatch h
    | some ir =>
      rw [hir] at h; dsimp only at h
      simp only [Bool.and_eq_true] at h
      exact ⟨ir, hir, h.1⟩
  | _ :: rrs, pk :: pks, h, k + 1, hk, hp => by
    simp only [checkRawPermLoop] at h
    cases hir : irs.get? pk with
    | none => rw [hir] at h; exact nomatch h
    | some _ =>
      rw [hir] at h; dsimp only at h
      simp only [Bool.and_eq_true] at h
      exact checkRawPermLoop_getElem h.2 k (by simp at hk; omega) (by simp at hp; omega)

/-- Interned slice relocation check corresponding to `Arm64.Obj.SliceRelocsMatch`. -/
def checkISliceRelocsB (N : Nat) (objsTree : IdxTree IObj)
    (bOTree dOTree : IdxTree SliceOrigin) (symRole : IdxTree SymRole)
    (rawSummary : IdxTree RawIdStatus)
    (o : SliceOrigin) (irs : IdxTree IReloc) (perm : List Nat) (invPerm : IdxTree Nat) : Bool :=
  match objsTree.get? o.oi with
  | none => false
  | some io =>
    match io.sections.get? o.si with
    | none => false
    | some sec =>
      let raw := sec.relocs.filter fun rr => decide (o.start ≤ rr.off ∧ rr.off < o.start + o.len)
      (irs.size? == some raw.length) &&
      checkPermBij raw.length perm invPerm &&
      checkRawPermLoop
        (checkIRelocMatchesB N objsTree bOTree dOTree symRole rawSummary o.oi o.start)
        irs raw perm

theorem sliceRelocsMatch_of_checkI {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N B D : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {L : IMultiLib} {bOTree dOTree : IdxTree SliceOrigin}
    {symRole : IdxTree SymRole} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hB : L.blocks.size? = some B) (hD : L.data.size? = some D)
    (hbO_sz : bOTree.size? = some B) (hdO_sz : dOTree.size? = some D)
    (hroles : checkSymRolesB N L symRole = true)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    {o : SliceOrigin} {irs : IdxTree IReloc} {perm : List Nat} {invPerm : IdxTree Nat}
    (hchk : checkISliceRelocsB N objsTree bOTree dOTree symRole rawSummary o irs perm invPerm = true) :
    SliceRelocsMatch (objsTree.toList.map (IObj.toExtractedObj names))
      (L.toMultiPlacedLib names) (originAt bOTree) (originAt dOTree)
      o (irs.toList.map (IReloc.toEntry names)) := by
  unfold checkISliceRelocsB at hchk
  cases hio : objsTree.get? o.oi with
  | none => rw [hio] at hchk; exact nomatch hchk
  | some io =>
    rw [hio] at hchk; dsimp only at hchk
    cases hsec : io.sections.get? o.si with
    | none => rw [hsec] at hchk; exact nomatch hchk
    | some sec =>
      rw [hsec] at hchk; dsimp only at hchk
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨hirs_sz, hbij⟩, hloop⟩ := hchk
      obtain ⟨hplen, hpnd, hplt⟩ := permBij_of_check hbij
      have hobjs_orig := hobjs
      unfold checkObjSymsB at hobjs
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hobjs
      obtain ⟨szO, hszO⟩ := hobjs.1.1.1.1
      have hio_elem : objsTree.toList[o.oi]? = some io := by
        rw [← IdxTree.get?_eq_getElem? hszO o.oi]; exact hio
      have hoi_lt : o.oi < objsTree.toList.length := (List.getElem?_eq_some_iff.1 hio_elem).1
      have hio_eq : objsTree.toList[o.oi] = io := by
        rw [List.getElem?_eq_getElem hoi_lt] at hio_elem; exact Option.some.inj hio_elem
      have ho_ok := allIdx_toList_getElem hszO hobjs.1.2 hoi_lt
      rw [hio_eq] at ho_ok
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at ho_ok
      obtain ⟨szSec, hszSec⟩ := ho_ok.1.1.1.1.2
      have hsec_elem : io.sections.toList[o.si]? = some sec := by
        rw [← IdxTree.get?_eq_getElem? hszSec o.si]; exact hsec
      have hirs_len : irs.toList.length =
          (sec.relocs.filter fun rr => decide (o.start ≤ rr.off ∧ rr.off < o.start + o.len)).length :=
        IdxTree.length_toList_of_size? hirs_sz
      refine ⟨io.toExtractedObj names, sec.toRawSec names, ?_, ?_, perm,
        hplen, hpnd, by simp [ISec.toRawSec, hirs_len], ?_⟩
      · simp [List.getElem?_map, hio_elem]
      · simp [IObj.toExtractedObj, List.getElem?_map, hsec_elem]
      · intro k hk hp
        dsimp only [ISec.toRawSec] at hk ⊢
        obtain ⟨ir, hir_get, hir_chk⟩ := checkRawPermLoop_getElem hloop k hk hp
        have hpk_raw : perm[k] < _ := hplt k hp
        have hpk_irs : perm[k] < irs.toList.length := hirs_len ▸ hpk_raw
        have hir_eq : irs.toList[perm[k]] = ir := by
          rw [IdxTree.get?_eq_getElem? hirs_sz perm[k],
            List.getElem?_eq_getElem hpk_irs] at hir_get
          exact Option.some.inj hir_get
        refine ⟨by simp [hpk_irs], ?_⟩
        simp only [List.getElem_map, hir_eq]
        exact relocMatches_of_checkI hsz hnd h0 hB hD hbO_sz hdO_sz hroles hobjs_orig hnd_disc hir_chk

/-- Check `SliceRelocsMatch` on every block in `L.blocks`. -/
def checkAllBlockRelocsB (N : Nat) (objsTree : IdxTree IObj) (L : IMultiLib)
    (bOTree dOTree : IdxTree SliceOrigin) (symRole : IdxTree SymRole)
    (rawSummary : IdxTree RawIdStatus) : Bool :=
  IdxTree.allIdx (fun bi b =>
    match bOTree.get? bi with
    | none => false
    | some o =>
      checkISliceRelocsB N objsTree bOTree dOTree symRole rawSummary
        o b.relocs b.relocPerm b.relocInvPerm) 0 L.blocks

/-- Check `SliceRelocsMatch` on every data object in `L.data`. -/
def checkAllDataRelocsB (N : Nat) (objsTree : IdxTree IObj) (L : IMultiLib)
    (bOTree dOTree : IdxTree SliceOrigin) (symRole : IdxTree SymRole)
    (rawSummary : IdxTree RawIdStatus) : Bool :=
  IdxTree.allIdx (fun di d =>
    match dOTree.get? di with
    | none => false
    | some o =>
      checkISliceRelocsB N objsTree bOTree dOTree symRole rawSummary
        o d.relocs d.relocPerm d.relocInvPerm) 0 L.data

/-- Association-list lookup keyed by `Nat`. -/
def lookupNat {α : Type} (k : Nat) (xs : List (Nat × α)) : Option α :=
  (xs.find? fun p => p.1 == k).map Prod.snd

/-- Check `exports_valid` in $O(|exports| \cdot \log N)$. -/
def checkIExportsB (N : Nat) (objsTree : IdxTree IObj) (L : IMultiLib)
    (bOTree : IdxTree SliceOrigin) (symRole : IdxTree SymRole)
    (rawSummary : IdxTree RawIdStatus) : Bool :=
  L.exportSyms.all (fun (a, b) => decide (a < N) && decide (b < N)) &&
  L.exports.all fun eId =>
    let rawId := (lookupNat eId L.exportSyms).getD eId
    decide (eId < N) && decide (rawId < N) &&
    match symRole.get? eId with
    | some (.blockSym bi _ off) =>
      match bOTree.get? bi, rawSummary.get? rawId with
      | some bo, some (.globalDef oi k si) =>
        (oi == bo.oi) && (si == bo.si) &&
        match objsTree.get? oi with
        | none => false
        | some o =>
          match o.symbols.get? k with
          | none => false
          | some sy =>
            (sy.kind == .func) && (sy.nameId == eId) && (sy.value == bo.start + off)
      | _, _ => false
    | _ => false

private theorem lookup_exportSyms_map {names : IdxTree String} {N : Nat}
    (hsz : names.size? = some N) (hnd : names.toList.Nodup) :
    ∀ {pairs : List (Nat × Nat)}
      (_ : pairs.all (fun (a, b) => decide (a < N) && decide (b < N)) = true)
      {eId : Nat} (_ : eId < N),
      lookup (symAt names eId) (pairs.map fun (a, b) => (symAt names a, symAt names b)) =
        (lookupNat eId pairs).map (symAt names)
  | [], _, _, _ => rfl
  | (a, b) :: rest, hp, eId, he => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    have hbeq : (symAt names a == symAt names eId) = (a == eId) := by
      cases hae : a == eId with
      | true =>
        have heq : a = eId := beq_iff_eq.1 hae
        subst heq; simp
      | false =>
        apply beq_eq_false_iff_ne.2
        intro heq
        exact beq_eq_false_iff_ne.1 hae (symAt_inj hsz hnd hp.1.1 he heq)
    simp only [List.map_cons, lookup, lookupNat, List.find?_cons, hbeq]
    cases a == eId with
    | true => rfl
    | false =>
      dsimp only
      exact lookup_exportSyms_map hsz hnd hp.2 he

theorem exportsValid_of_checkI {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N B : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    (h0 : names.get? 0 = some "")
    {objsTree : IdxTree IObj} {L : IMultiLib} {bOTree : IdxTree SliceOrigin}
    {symRole : IdxTree SymRole} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    (hB : L.blocks.size? = some B) (hbO_sz : bOTree.size? = some B)
    (hroles : checkSymRolesB N L symRole = true)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hnd_disc : ∀ oi si, ¬Discarded (objsTree.toList.map (IObj.toExtractedObj names)) oi si)
    (hexp : checkIExportsB N objsTree L bOTree symRole rawSummary = true) :
    ∀ e ∈ (L.toMultiPlacedLib names).exports,
      ∃ bi off, lookupBlockSym e (L.toMultiPlacedLib names).blocks = some (bi, off) ∧
        ∃ h : bi < (L.toMultiPlacedLib names).blocks.length,
          ∃ k sy,
            Resolves (objsTree.toList.map (IObj.toExtractedObj names))
              ((L.toMultiPlacedLib names).elfSym e)
              (originAt bOTree ⟨bi, h⟩).oi k (originAt bOTree ⟨bi, h⟩).si sy ∧
            sy.kind = .func ∧ sy.name = e ∧
            sy.value = (originAt bOTree ⟨bi, h⟩).start + off := by
  unfold checkIExportsB at hexp
  simp only [Bool.and_eq_true] at hexp
  obtain ⟨hpairs, hallE⟩ := hexp
  rw [List.all_eq_true] at hallE
  intro e he
  simp only [IMultiLib.toMultiPlacedLib, List.mem_map] at he
  obtain ⟨eId, heId_mem, rfl⟩ := he
  have he_ok := hallE eId heId_mem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he_ok
  obtain ⟨⟨he_lt, hraw_lt⟩, hrest⟩ := he_ok
  cases hrg : symRole.get? eId with
  | none => rw [hrg] at hrest; exact nomatch hrest
  | some role =>
    rw [hrg] at hrest
    cases role with
    | other => exact nomatch hrest
    | dataSym _ => exact nomatch hrest
    | blockSym bi j off =>
      dsimp only at hrest
      cases hbo : bOTree.get? bi with
      | none => rw [hbo] at hrest; exact nomatch hrest
      | some bo =>
        rw [hbo] at hrest
        cases hrs : rawSummary.get? ((lookupNat eId L.exportSyms).getD eId) with
        | none => rw [hrs] at hrest; exact nomatch hrest
        | some st =>
          rw [hrs] at hrest
          cases st with
          | other => exact nomatch hrest
          | allNonLocalUndef => exact nomatch hrest
          | weakOnlyUndef _ _ => exact nomatch hrest
          | globalDef oi k si =>
            dsimp only at hrest
            simp only [Bool.and_eq_true, beq_iff_eq] at hrest
            obtain ⟨⟨hoi_eq, hsi_eq⟩, hsym_chk⟩ := hrest
            obtain ⟨oDef, syDef, hoDef, hsyDef, hrgd⟩ :=
              resolves_of_summary hsz hnd h0 hobjs hnd_disc hraw_lt hrs
            rw [hoDef] at hsym_chk; dsimp only at hsym_chk
            rw [hsyDef] at hsym_chk; dsimp only at hsym_chk
            simp only [Bool.and_eq_true, beq_iff_eq] at hsym_chk
            have hlk := lookupBlockSym_eq_of_role hsz hnd hroles he_lt
            rw [hrg] at hlk
            have hbo_elem : bOTree.toList[bi]? = some bo := by
              rw [← IdxTree.get?_eq_getElem? hbO_sz bi]; exact hbo
            have hbi_B : bi < B := by
              have hlt := (List.getElem?_eq_some_iff.1 hbo_elem).1
              rw [IdxTree.length_toList_of_size? hbO_sz] at hlt
              exact hlt
            have hbi_lib : bi < (L.toMultiPlacedLib names).blocks.length := by
              simp [IMultiLib.toMultiPlacedLib, IdxTree.length_toList_of_size? hB, hbi_B]
            have horig_bo : originAt bOTree ⟨bi, hbi_lib⟩ = bo := by
              unfold originAt; rw [hbo]; rfl
            have helf : (L.toMultiPlacedLib names).elfSym (symAt names eId) =
                symAt names ((lookupNat eId L.exportSyms).getD eId) := by
              unfold MultiPlacedLib.elfSym
              dsimp only [IMultiLib.toMultiPlacedLib]
              rw [lookup_exportSyms_map hsz hnd hpairs he_lt]
              cases lookupNat eId L.exportSyms <;> rfl
            refine ⟨bi, off, hlk, hbi_lib, k, syDef.toRawSym names, ?_,
              hsym_chk.1.1, by dsimp only [ISym.toRawSym]; rw [hsym_chk.1.2], ?_⟩
            · rw [helf, horig_bo, ← hoi_eq, ← hsi_eq]; exact hrgd
            · rw [horig_bo]; exact hsym_chk.2

/-- Check `externs_valid` across all blocks in $O((E + R_{\text{call}}) \log N)$ when blocks share
    `commonExterns` / `commonWeakRefs`. -/
def checkIExternsB (N : Nat) (L : IMultiLib) (symRole : IdxTree SymRole)
    (rawSummary : IdxTree RawIdStatus)
    (branchCalled : IdxTree (Option (Nat × Nat)))
    (commonExtSet : IdxTree Bool) : Bool :=
  let checkExtList (extIds : List Nat) : Bool :=
    extIds.all fun x =>
      decide (x < N) && (symRole.get? x == some .other) &&
      match branchCalled.get? x with
      | some (some _) => true
      | _ => false
  let checkWeakList (weakIds : List Nat) (inExt : Nat → Bool) : Bool :=
    weakIds.all fun w =>
      decide (w < N) && inExt w &&
      match rawSummary.get? w with
      | some (.weakOnlyUndef _ _) => true
      | _ => false
  (commonExtSet.size? == some N) &&
  IdxTree.allIdx (fun id isMem =>
    if isMem then Arm64.Obj.Interned.memNat id L.commonExterns else true) 0 commonExtSet &&
  (branchCalled.size? == some N) &&
  IdxTree.allIdx (fun id w =>
    match w with
    | none => true
    | some (bi, ri) =>
      match L.blocks.get? bi with
      | none => false
      | some b' =>
        match b'.relocs.get? ri with
        | none => false
        | some r => ((r.kind == .call26) || (r.kind == .jump26)) && (r.sym == id)) 0 branchCalled &&
  checkExtList L.commonExterns &&
  checkWeakList L.commonWeakRefs (fun w => commonExtSet.get? w == some true) &&
  L.blocks.all fun b =>
    let inExt (s : Nat) : Bool :=
      match b.externsOverride with
      | none => commonExtSet.get? s == some true
      | some ids => Arm64.Obj.Interned.memNat s ids
    b.relocs.all (fun r =>
      decide (r.sym < N) &&
      if (r.kind == .call26) || (r.kind == .jump26) then
        match symRole.get? r.sym with
        | some (.blockSym _ _ _) => true
        | _ => inExt r.sym
      else true) &&
    (match b.externsOverride with
     | none => true
     | some ids => checkExtList ids) &&
    (match b.externsOverride, b.weakRefsOverride with
     | none, none => true
     | _, _ => checkWeakList (b.weakRefIds L.commonWeakRefs) inExt)

theorem externsValid_of_checkI {names : IdxTree String} {charsTree : IdxTree (List Char)}
    {N : Nat} (hsz : names.size? = some N) (hnd : names.toList.Nodup)
    {objsTree : IdxTree IObj} {L : IMultiLib}
    {symRole : IdxTree SymRole} {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    {branchCalled : IdxTree (Option (Nat × Nat))} {commonExtSet : IdxTree Bool}
    (hroles : checkSymRolesB N L symRole = true)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hext : checkIExternsB N L symRole rawSummary branchCalled commonExtSet = true) :
    ∀ b ∈ (L.toMultiPlacedLib names).blocks,
      (∀ r ∈ b.relocs, (r.kind = .call26 ∨ r.kind = .jump26) →
        lookupBlockSym r.sym (L.toMultiPlacedLib names).blocks = none → r.sym ∈ b.externs) ∧
      (∀ x ∈ b.externs, lookupBlockSym x (L.toMultiPlacedLib names).blocks = none ∧
        (∀ d ∈ (L.toMultiPlacedLib names).data, d.sym ≠ x) ∧
        ∃ b' ∈ (L.toMultiPlacedLib names).blocks, ∃ r ∈ b'.relocs,
          (r.kind = .call26 ∨ r.kind = .jump26) ∧ r.sym = x) ∧
      (∀ w ∈ b.weakRefs, w ∈ b.externs ∧
        WeakOnlyUndef (objsTree.toList.map (IObj.toExtractedObj names)) w) := by
  unfold checkIExternsB at hext
  simp only [Bool.and_eq_true, beq_iff_eq] at hext
  obtain ⟨⟨⟨⟨⟨⟨hszCE, hallCE⟩, hszBC⟩, hallBC⟩, hcomExt⟩, hcomWeak⟩, hallB⟩ := hext
  have hce_mem : ∀ {s : Nat}, s < N → commonExtSet.get? s = some true → s ∈ L.commonExterns := by
    intro s hs hget
    have hlenCE : commonExtSet.toList.length = N := IdxTree.length_toList_of_size? hszCE
    have h1 := allIdx_toList_getElem hszCE hallCE (hlenCE ▸ hs)
    have hval : commonExtSet.toList[s]'(hlenCE ▸ hs) = true := by
      rw [IdxTree.get?_eq_getElem? hszCE s, List.getElem?_eq_getElem (hlenCE ▸ hs)] at hget
      exact Option.some.inj hget
    rw [hval] at h1; simp only [↓reduceIte] at h1
    exact Arm64.Obj.Interned.memNat_iff.1 h1
  have hbc_wit : ∀ {x : Nat}, x < N →
      (match branchCalled.get? x with | some (some _) => true | _ => false) = true →
      ∃ b' ∈ (L.toMultiPlacedLib names).blocks, ∃ r ∈ b'.relocs,
        (r.kind = .call26 ∨ r.kind = .jump26) ∧ r.sym = symAt names x := by
    intro x hx hsome
    have hlenBC : branchCalled.toList.length = N := IdxTree.length_toList_of_size? hszBC
    have hbc := allIdx_toList_getElem hszBC hallBC (hlenBC ▸ hx)
    cases hget : branchCalled.get? x with
    | none => rw [hget] at hsome; exact nomatch hsome
    | some opt =>
      rw [hget] at hsome
      cases opt with
      | none => exact nomatch hsome
      | some pair =>
        rcases pair with ⟨bi, ri⟩
        have hval : branchCalled.toList[x]'(hlenBC ▸ hx) = some (bi, ri) := by
          rw [IdxTree.get?_eq_getElem? hszBC x, List.getElem?_eq_getElem (hlenBC ▸ hx)] at hget
          exact Option.some.inj hget
        rw [hval] at hbc; dsimp only at hbc
        cases hb' : L.blocks.get? bi with
        | none => rw [hb'] at hbc; exact nomatch hbc
        | some ib' =>
          rw [hb'] at hbc; dsimp only at hbc
          cases hr' : ib'.relocs.get? ri with
          | none => rw [hr'] at hbc; exact nomatch hbc
          | some ir' =>
            rw [hr'] at hbc; dsimp only at hbc
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hbc
            refine ⟨ib'.toCodeBlock names (L.commonExterns.map (symAt names))
                (L.commonWeakRefs.map (symAt names)),
              List.mem_map.2 ⟨ib', IdxTree.mem_toList_of_get? hb', rfl⟩,
              ir'.toEntry names,
              List.mem_map.2 ⟨ir', IdxTree.mem_toList_of_get? hr', rfl⟩,
              hbc.1, by dsimp only [IReloc.toEntry]; rw [hbc.2]⟩
  have hext_list_ok : ∀ {extIds : List Nat},
      (extIds.all fun x =>
        decide (x < N) && (symRole.get? x == some .other) &&
        match branchCalled.get? x with | some (some _) => true | _ => false) = true →
      ∀ x ∈ extIds.map (symAt names),
        lookupBlockSym x (L.toMultiPlacedLib names).blocks = none ∧
        (∀ d ∈ (L.toMultiPlacedLib names).data, d.sym ≠ x) ∧
        ∃ b' ∈ (L.toMultiPlacedLib names).blocks, ∃ r ∈ b'.relocs,
          (r.kind = .call26 ∨ r.kind = .jump26) ∧ r.sym = x := by
    intro extIds hall x hx
    rw [List.all_eq_true] at hall
    obtain ⟨xId, hxId_mem, rfl⟩ := List.mem_map.1 hx
    have hx_ok := hall xId hxId_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx_ok
    have hlk := lookupBlockSym_eq_of_role hsz hnd hroles hx_ok.1.1
    rw [hx_ok.1.2] at hlk
    have hnod := not_mem_data_of_role hsz hnd hroles hx_ok.1.1 (by simp [hx_ok.1.2])
    exact ⟨hlk, hnod, hbc_wit hx_ok.1.1 hx_ok.2⟩
  rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hallB
  intro b hb
  simp only [IMultiLib.toMultiPlacedLib, List.mem_map] at hb
  obtain ⟨ib, hib_mem, rfl⟩ := hb
  have hb_ok := hallB ib hib_mem
  simp only [Bool.and_eq_true] at hb_ok
  obtain ⟨⟨hrel_ok, hext_ov⟩, hweak_ov⟩ := hb_ok
  have hinExt_mem : ∀ {s : Nat}, s < N →
      (match ib.externsOverride with
       | none => commonExtSet.get? s == some true
       | some ids => Arm64.Obj.Interned.memNat s ids) = true →
      symAt names s ∈ (ib.toCodeBlock names (L.commonExterns.map (symAt names))
        (L.commonWeakRefs.map (symAt names))).externs := by
    intro s hs hin
    rw [IBlock.toCodeBlock_externs]
    apply List.mem_map_of_mem
    unfold IBlock.externIds
    cases hov : ib.externsOverride with
    | none =>
      rw [hov] at hin; dsimp only at hin
      exact hce_mem hs (beq_iff_eq.1 hin)
    | some ids =>
      rw [hov] at hin; dsimp only at hin
      exact Arm64.Obj.Interned.memNat_iff.1 hin
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hkind hnone
    simp only [IBlock.toCodeBlock, List.mem_map] at hr
    obtain ⟨ir, hir_mem, rfl⟩ := hr
    rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hrel_ok
    have hir_ok := hrel_ok ir hir_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hir_ok
    obtain ⟨hir_lt, hir_br⟩ := hir_ok
    have hk_b : ((ir.kind == .call26) || (ir.kind == .jump26)) = true := by
      dsimp only [IReloc.toEntry] at hkind
      rcases hkind with h | h <;> simp [h]
    simp only [hk_b, ↓reduceIte] at hir_br
    have hlk := lookupBlockSym_eq_of_role hsz hnd hroles hir_lt
    dsimp only [IReloc.toEntry] at hnone ⊢
    rw [hnone] at hlk
    have hin : (match ib.externsOverride with
        | none => commonExtSet.get? ir.sym == some true
        | some ids => Arm64.Obj.Interned.memNat ir.sym ids) = true := by
      cases hrg : symRole.get? ir.sym with
      | none => rw [hrg] at hir_br; exact hir_br
      | some role =>
        rw [hrg] at hir_br hlk
        cases role with
        | other => exact hir_br
        | dataSym _ => exact hir_br
        | blockSym _ _ _ => exact nomatch hlk
    exact hinExt_mem hir_lt hin
  · rw [IBlock.toCodeBlock_externs]
    unfold IBlock.externIds
    cases hov : ib.externsOverride with
    | none => exact hext_list_ok hcomExt
    | some ids =>
      rw [hov] at hext_ov; exact hext_list_ok hext_ov
  · have hweak_all :
        ((ib.weakRefIds L.commonWeakRefs).all fun w =>
          decide (w < N) &&
          (match ib.externsOverride with
           | none => commonExtSet.get? w == some true
           | some ids => Arm64.Obj.Interned.memNat w ids) &&
          match rawSummary.get? w with
          | some (.weakOnlyUndef _ _) => true
          | _ => false) = true := by
      cases hovE : ib.externsOverride with
      | none =>
        cases hovW : ib.weakRefsOverride with
        | none =>
          unfold IBlock.weakRefIds
          rw [hovW]; exact hcomWeak
        | some wids =>
          rw [hovE, hovW] at hweak_ov; exact hweak_ov
      | some eids =>
        rw [hovE] at hweak_ov; exact hweak_ov
    rw [List.all_eq_true] at hweak_all
    intro w hw
    rw [IBlock.toCodeBlock_weakRefs] at hw
    obtain ⟨wId, hwId_mem, rfl⟩ := List.mem_map.1 hw
    have hw_ok := hweak_all wId hwId_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw_ok
    refine ⟨hinExt_mem hw_ok.1.1 hw_ok.1.2, ?_⟩
    cases hrs : rawSummary.get? wId with
    | none => rw [hrs] at hw_ok; exact nomatch hw_ok.2
    | some st =>
      rw [hrs] at hw_ok
      cases st with
      | other => exact nomatch hw_ok.2
      | globalDef _ _ _ => exact nomatch hw_ok.2
      | allNonLocalUndef => exact nomatch hw_ok.2
      | weakOnlyUndef wOi wKi =>
        exact weakOnlyUndef_of_summary hsz hnd hobjs hw_ok.1.1 hrs

/-- Split-checks soundness theorem for `LabelsFromObjects`: combines independent
    `rfl_kernel`-checkable sub-certificates into `LabelsFromObjects objs lib (originAt bOTree)
    (originAt dOTree)`. -/
theorem labelsFromObjects_of_split_checks
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {N B D : Nat}
    {namesTree : IdxTree String} {charsTree : IdxTree (List Char)}
    {objsTree : IdxTree IObj} {L : IMultiLib}
    {bOTree dOTree : IdxTree SliceOrigin}
    {symRole : IdxTree SymRole}
    {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    {textGroups dataGroups : IdxTree SliceGroup}
    {textToGroup dataToGroup : IdxTree (Nat × Nat)}
    {branchCalled : IdxTree (Option (Nat × Nat))} {commonExtSet : IdxTree Bool}
    (hobjs_eq : objs = objsTree.toList.map (IObj.toExtractedObj namesTree))
    (hlib_eq : lib = L.toMultiPlacedLib namesTree)
    (hsz : namesTree.size? = some N)
    (hcsz : charsTree.size? = some N)
    (hnames_eq : namesTree.toList = charsTree.toList.map String.ofList)
    (hnn : Arm64.Obj.Interned.namesNodup charsTree.toList = true)
    (h0 : namesTree.get? 0 = some "")
    (hB : L.blocks.size? = some B)
    (hD : L.data.size? = some D)
    (hroles : checkSymRolesB N L symRole = true)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hgroups : checkNoDiscardedB objs = true)
    (hbdisj : checkGroupsDisjointB B bOTree textGroups textToGroup = true)
    (hddisj : checkGroupsDisjointB D dOTree dataGroups dataToGroup = true)
    (htbytes : checkTextGroupsBytesB objsTree L.blocks bOTree textGroups = true)
    (htmeta : checkTextSlicesMetaB N objsTree L.blocks bOTree rawClaimed = true)
    (hdbytes : checkDataGroupsBytesB objsTree L.data dOTree dataGroups = true)
    (hdmeta : checkDataSlicesMetaB N objsTree L.data dOTree rawClaimed = true)
    (hbrelocs : checkAllBlockRelocsB N objsTree L bOTree dOTree symRole rawSummary = true)
    (hdrelocs : checkAllDataRelocsB N objsTree L bOTree dOTree symRole rawSummary = true)
    (hexports : checkIExportsB N objsTree L bOTree symRole rawSummary = true)
    (hexterns : checkIExternsB N L symRole rawSummary branchCalled commonExtSet = true) :
    LabelsFromObjects objs lib (originAt bOTree) (originAt dOTree) := by
  have hnd_disc := not_discarded_of_checkNoDiscarded hgroups
  subst hobjs_eq; subst hlib_eq
  have hnd : namesTree.toList.Nodup := Arm64.Obj.Interned.nodup_of_namesNodup hnames_eq hnn
  have hbO_sz : bOTree.size? = some B := by
    unfold checkGroupsDisjointB at hbdisj
    simp only [Bool.and_eq_true, beq_iff_eq] at hbdisj
    exact hbdisj.1.1.1.1.1
  have hdO_sz : dOTree.size? = some D := by
    unfold checkGroupsDisjointB at hddisj
    simp only [Bool.and_eq_true, beq_iff_eq] at hddisj
    exact hddisj.1.1.1.1.1
  have hlenB : (L.toMultiPlacedLib namesTree).blocks.length = B := by
    simp [IMultiLib.toMultiPlacedLib, IdxTree.length_toList_of_size? hB]
  have hlenD : (L.toMultiPlacedLib namesTree).data.length = D := by
    simp [IMultiLib.toMultiPlacedLib, IdxTree.length_toList_of_size? hD]
  refine
    { blocks_valid := validTextSlices_of_check hsz hcsz hnames_eq hnd h0 hB hobjs hnd_disc hbdisj htbytes htmeta
      data_valid := validDataSlices_of_check hsz hcsz hnames_eq hnd h0 hD hobjs hnd_disc hddisj hdbytes hdmeta
      blocks_disjoint := ?_
      data_disjoint := ?_
      names_nodup := ⟨blockSymbols_nodup_of_roles hsz hnd hroles,
        dataSyms_nodup_of_roles hsz hnd hroles,
        fun _ hd => data_lookup_none_of_roles hsz hnd hroles hd⟩
      block_relocs := ?_
      data_relocs := ?_
      exports_valid := exportsValid_of_checkI hsz hnd h0 hB hbO_sz hroles hobjs hnd_disc hexports
      externs_valid := externsValid_of_checkI hsz hnd hroles hobjs hexterns }
  · intro i j hij hoi hsi
    have hdisj := groups_disjoint_of_check hbdisj ⟨i.1, hlenB ▸ i.2⟩ ⟨j.1, hlenB ▸ j.2⟩
      (fun heq => hij (Fin.ext (Fin.mk.inj heq))) hoi hsi
    exact hdisj
  · intro i j hij hoi hsi
    have hdisj := groups_disjoint_of_check hddisj ⟨i.1, hlenD ▸ i.2⟩ ⟨j.1, hlenD ▸ j.2⟩
      (fun heq => hij (Fin.ext (Fin.mk.inj heq))) hoi hsi
    exact hdisj
  · intro i
    have hiL : i.1 < L.blocks.toList.length := by simpa [IMultiLib.toMultiPlacedLib] using i.2
    have hbr := allIdx_toList_getElem hB hbrelocs hiL
    have ho_elem : bOTree.get? i.1 = some (originAt bOTree i) := by
      have hiB : i.1 < B := hlenB ▸ i.2
      have hlenbO : bOTree.toList.length = B := IdxTree.length_toList_of_size? hbO_sz
      unfold originAt
      rw [IdxTree.get?_eq_getElem? hbO_sz i.1, List.getElem?_eq_getElem (hlenbO ▸ hiB)]
      rfl
    rw [ho_elem] at hbr; dsimp only at hbr
    have hrel_eq : (L.toMultiPlacedLib namesTree).blocks[i].relocs =
        L.blocks.toList[i.1].relocs.toList.map (IReloc.toEntry namesTree) := by
      change ((L.toMultiPlacedLib namesTree).blocks[i.1]'i.2).relocs = _
      simp [IMultiLib.toMultiPlacedLib, IBlock.toCodeBlock]
    rw [hrel_eq]
    exact sliceRelocsMatch_of_checkI hsz hnd h0 hB hD hbO_sz hdO_sz hroles hobjs hnd_disc hbr
  · intro i
    have hiL : i.1 < L.data.toList.length := by simpa [IMultiLib.toMultiPlacedLib] using i.2
    have hdr := allIdx_toList_getElem hD hdrelocs hiL
    have ho_elem : dOTree.get? i.1 = some (originAt dOTree i) := by
      have hiD : i.1 < D := hlenD ▸ i.2
      have hlendO : dOTree.toList.length = D := IdxTree.length_toList_of_size? hdO_sz
      unfold originAt
      rw [IdxTree.get?_eq_getElem? hdO_sz i.1, List.getElem?_eq_getElem (hlendO ▸ hiD)]
      rfl
    rw [ho_elem] at hdr; dsimp only at hdr
    have hrel_eq : (L.toMultiPlacedLib namesTree).data[i].relocs =
        L.data.toList[i.1].relocs.toList.map (IReloc.toEntry namesTree) := by
      change ((L.toMultiPlacedLib namesTree).data[i.1]'i.2).relocs = _
      simp [IMultiLib.toMultiPlacedLib, IData.toSymDataInfo]
    rw [hrel_eq]
    exact sliceRelocsMatch_of_checkI hsz hnd h0 hB hD hbO_sz hdO_sz hroles hobjs hnd_disc hdr

end Arm64.Obj.LabelsInterned

end

/-! ## `gen_labels_from_objects` command elaborator -/

public meta section

namespace Arm64.Obj.LabelsInterned

open Lean Elab Command Term Meta ProofLib.ProgramReflection

private instance : Inhabited SymSec := ⟨.undef⟩
private instance : Inhabited SymKind := ⟨.other⟩
private instance : Inhabited SymBind := ⟨.other⟩
private instance : Inhabited SliceOrigin := ⟨⟨0, 0, 0, 0⟩⟩

private inductive MSymRole where
  | other
  | blockSym (bi j off : Nat)
  | dataSym (di : Nat)
  deriving DecidableEq, BEq, Inhabited

private inductive MRawIdStatus where
  | other
  | globalDef (oi k si : Nat)
  | allNonLocalUndef
  | weakOnlyUndef (wOi wKi : Nat)
  deriving DecidableEq, BEq, Inhabited

private structure DecRawReloc where
  off : Nat
  kindName? : Option Name
  symIdx : Nat
  addend : Int
  deriving Inhabited

private structure DecRawSec where
  name : String
  bytes : ByteArray
  bytesE : Expr
  size : Nat
  align : Nat
  isExec : Bool
  readOnly : Bool
  isNobits : Bool
  isTls : Bool
  relocs : Array DecRawReloc
  relocsE : Expr
  deriving Inhabited

private structure DecRawSym where
  rawName : String
  name : String
  sec : SymSec
  value : Nat
  size : Nat
  kind : SymKind
  bind : SymBind
  deriving Inhabited

private structure DecObj where
  name : String
  sections : Array DecRawSec
  symbols : Array DecRawSym
  groupsE : Expr
  deriving Inhabited

private structure DecReloc where
  off : Nat
  kindName : Name
  kindE : Expr
  sym : String
  addend : Int
  localSym : Bool
  deriving Inhabited

private structure DecBlock where
  code : ByteArray
  codeE : Expr
  align : Nat
  symbols : Array (String × Nat)
  relocs : Array DecReloc
  externs : Array String
  weakRefs : Array String
  deriving Inhabited

private structure DecData where
  sym : String
  align : Nat
  readOnly : Bool
  bytes : ByteArray
  bytesE : Expr
  zeroTail : Nat
  relocs : Array DecReloc
  deriving Inhabited

private structure DecMultiLib where
  name : String
  blocks : Array DecBlock
  data : Array DecData
  exports : Array String
  exportSyms : Array (String × String)
  deriving Inhabited

private def decodeNatVal (e : Expr) : MetaM Nat := do
  if let some n := e.rawNatLit? then return n
  if let some n ← (evalNat e).run then return n
  let e ← whnf e
  match e.rawNatLit? with
  | some n => return n
  | none =>
    if let some n ← (evalNat e).run then return n
    throwError "gen_labels_from_objects: expected Nat literal, got{indentExpr e}"

private def decodeBoolVal (e : Expr) : MetaM Bool := do
  let c := e.consumeMData
  if c.isConstOf ``Bool.true then return true
  if c.isConstOf ``Bool.false then return false
  let w ← whnf c
  if w.isConstOf ``Bool.true then return true
  if w.isConstOf ``Bool.false then return false
  throwError "gen_labels_from_objects: expected Bool literal, got{indentExpr e}"

private def decodeStrVal (e : Expr) : MetaM String := do
  let c := e.consumeMData
  if let .lit (.strVal s) := c then return s
  match (← whnf c) with
  | .lit (.strVal s) => return s
  | w => throwError "gen_labels_from_objects: expected String literal, got{indentExpr w}"

private partial def decodeIntVal (e : Expr) : MetaM Int := do
  let c := e.consumeMData
  if c.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (c.getArg! 1).rawNatLit? then
      return (n : Int)
  if c.isAppOfArity ``Neg.neg 3 then
    let v ← decodeIntVal (c.getArg! 2)
    return -v
  let w ← whnf c
  if w.isAppOfArity ``Int.ofNat 1 then
    let n ← decodeNatVal (w.getArg! 0)
    return (n : Int)
  if w.isAppOfArity ``Int.negSucc 1 then
    let n ← decodeNatVal (w.getArg! 0)
    return -((n + 1 : Nat) : Int)
  throwError "gen_labels_from_objects: expected Int literal, got{indentExpr w}"

private partial def decodeListElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (cur : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then
      return acc
    else if c.isAppOfArity ``List.cons 3 then
      go (c.getArg! 2) (acc.push (c.getArg! 1))
    else if c.isAppOfArity ``HAppend.hAppend 6 then
      let acc' ← go (c.getArg! 4) acc
      go (c.getArg! 5) acc'
    else if c.isAppOfArity ``List.append 3 then
      let acc' ← go (c.getArg! 1) acc
      go (c.getArg! 2) acc'
    else if let some c' ← unfoldDefinition? c then
      go c' acc
    else
      let w ← whnf c
      if w == c then
        throwError "gen_labels_from_objects: expected concrete List, got{indentExpr w}"
      go w acc
  go e #[]

private def decodeByteVal (hd : Expr) : MetaM UInt8 := do
  let c := hd.consumeMData
  if c.isAppOfArity ``BitVec.ofNat 2 then
    if let some n := (c.getArg! 1).rawNatLit? then
      return n.toUInt8
  if c.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (c.getArg! 1).rawNatLit? then
      return n.toUInt8
  let w ← whnf c
  if w.isAppOfArity ``BitVec.ofFin 2 then
    let finE ← whnf (w.getArg! 1)
    if finE.isAppOfArity ``Fin.mk 3 then
      let n ← decodeNatVal (finE.getArg! 1)
      return n.toUInt8
  if w.isAppOfArity ``BitVec.ofNat 2 then
    let n ← decodeNatVal (w.getArg! 1)
    return n.toUInt8
  throwError "gen_labels_from_objects: expected BitVec 8 literal, got{indentExpr w}"

private partial def decodeBytes (e : Expr) : MetaM ByteArray := do
  let rec go (cur : Expr) (acc : ByteArray) : MetaM ByteArray := do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then
      return acc
    else if c.isAppOfArity ``List.cons 3 then
      let b ← decodeByteVal (c.getArg! 1)
      go (c.getArg! 2) (acc.push b)
    else if c.isAppOfArity ``List.flatten 2 then
      let chunks ← decodeListElems (c.getArg! 1)
      let mut out := acc
      for ch in chunks do
        out ← go ch out
      return out
    else if c.isAppOfArity ``HAppend.hAppend 6 then
      let out ← go (c.getArg! 4) acc
      go (c.getArg! 5) out
    else if c.isAppOfArity ``List.append 3 then
      let out ← go (c.getArg! 1) acc
      go (c.getArg! 2) out
    else if let some c' ← unfoldDefinition? c then
      go c' acc
    else
      let w ← whnf c
      if w == c then
        throwError "gen_labels_from_objects: expected List (BitVec 8) literal, got{indentExpr w}"
      go w acc
  go e ByteArray.empty

private partial def unfoldToCtor (ctorName : Name) (arity : Nat) (e : Expr) : MetaM Expr := do
  let c := e.consumeMData
  if c.isAppOfArity ctorName arity then
    return c
  if let some c' ← unfoldDefinition? c then
    return ← unfoldToCtor ctorName arity c'
  let w ← whnf c
  if w.isAppOfArity ctorName arity then
    return w
  throwError "gen_labels_from_objects: expected {ctorName}, got{indentExpr w}"

private def decodeSymSec (e : Expr) : MetaM SymSec := do
  let w ← whnf e
  if w.isConstOf ``SymSec.undef then return .undef
  if w.isConstOf ``SymSec.other then return .other
  if w.isAppOfArity ``SymSec.sec 1 then
    return .sec (← decodeNatVal (w.getArg! 0))
  throwError "gen_labels_from_objects: expected SymSec, got{indentExpr w}"

private def decodeSymKind (e : Expr) : MetaM SymKind := do
  let w ← whnf e
  if w.isConstOf ``SymKind.func then return .func
  if w.isConstOf ``SymKind.object then return .object
  if w.isConstOf ``SymKind.tls then return .tls
  if w.isConstOf ``SymKind.section then return .section
  if w.isConstOf ``SymKind.other then return .other
  throwError "gen_labels_from_objects: expected SymKind, got{indentExpr w}"

private def decodeSymBind (e : Expr) : MetaM SymBind := do
  let w ← whnf e
  if w.isConstOf ``SymBind.local then return .local
  if w.isConstOf ``SymBind.global then return .global
  if w.isConstOf ``SymBind.weak then return .weak
  if w.isConstOf ``SymBind.other then return .other
  throwError "gen_labels_from_objects: expected SymBind, got{indentExpr w}"

private def decodeRelocKindName (e : Expr) : MetaM (Name × Expr) := do
  let c := e.consumeMData
  if let some nm := c.constName? then
    if nm.getPrefix == ``RelocKind then
      return (nm, c)
  let w ← whnf c
  if let some nm := w.constName? then
    return (nm, Lean.mkConst nm)
  throwError "gen_labels_from_objects: expected RelocKind constructor, got{indentExpr w}"

private def decodeRawReloc (e : Expr) : MetaM DecRawReloc := do
  let c ← unfoldToCtor ``RawReloc.mk 4 e
  let off ← decodeNatVal (c.getArg! 0)
  let kOpt ← whnf (c.getArg! 1)
  let kindName? ←
    if kOpt.isAppOfArity ``Option.none 1 then
      pure none
    else if kOpt.isAppOfArity ``Option.some 2 then
      let (kn, _) ← decodeRelocKindName (kOpt.getArg! 1)
      pure (some kn)
    else
      throwError "gen_labels_from_objects: expected Option RelocKind, got{indentExpr kOpt}"
  let symIdx ← decodeNatVal (c.getArg! 2)
  let addend ← decodeIntVal (c.getArg! 3)
  return { off, kindName?, symIdx, addend }

private def decodeRawSec (e : Expr) : MetaM DecRawSec := do
  let c ← unfoldToCtor ``RawSec.mk 9 e
  let name ← decodeStrVal (c.getArg! 0)
  let bytesE := c.getArg! 1
  let bytes ← decodeBytes bytesE
  let size ← decodeNatVal (c.getArg! 2)
  let align ← decodeNatVal (c.getArg! 3)
  let isExec ← decodeBoolVal (c.getArg! 4)
  let readOnly ← decodeBoolVal (c.getArg! 5)
  let isNobits ← decodeBoolVal (c.getArg! 6)
  let isTls ← decodeBoolVal (c.getArg! 7)
  let relocsE := c.getArg! 8
  let relocEs ← decodeListElems relocsE
  let relocs ← relocEs.mapM decodeRawReloc
  return { name, bytes, bytesE, size, align, isExec, readOnly, isNobits, isTls, relocs, relocsE }

private def decodeRawSym (e : Expr) : MetaM DecRawSym := do
  let c ← unfoldToCtor ``RawSym.mk 7 e
  let rawName ← decodeStrVal (c.getArg! 0)
  let name ← decodeStrVal (c.getArg! 1)
  let sec ← decodeSymSec (c.getArg! 2)
  let value ← decodeNatVal (c.getArg! 3)
  let size ← decodeNatVal (c.getArg! 4)
  let kind ← decodeSymKind (c.getArg! 5)
  let bind ← decodeSymBind (c.getArg! 6)
  return { rawName, name, sec, value, size, kind, bind }

private def decodeExtractedObj (e : Expr) : MetaM DecObj := do
  let c ← unfoldToCtor ``ExtractedObj.mk 4 e
  let name ← decodeStrVal (c.getArg! 0)
  let secEs ← decodeListElems (c.getArg! 1)
  let symEs ← decodeListElems (c.getArg! 2)
  let sections ← secEs.mapM decodeRawSec
  let symbols ← symEs.mapM decodeRawSym
  return { name, sections, symbols, groupsE := c.getArg! 3 }

private def decodeRelocEntry (e : Expr) : MetaM DecReloc := do
  let c ← unfoldToCtor ``RelocEntry.mk 5 e
  let off ← decodeNatVal (c.getArg! 0)
  let (kindName, kindE) ← decodeRelocKindName (c.getArg! 1)
  let sym ← decodeStrVal (c.getArg! 2)
  let addend ← decodeIntVal (c.getArg! 3)
  let localSym ← decodeBoolVal (c.getArg! 4)
  return { off, kindName, kindE, sym, addend, localSym }

private def decodeStrNatPair (e : Expr) : MetaM (String × Nat) := do
  let c ← unfoldToCtor ``Prod.mk 4 e
  return (← decodeStrVal (c.getArg! 2), ← decodeNatVal (c.getArg! 3))

private def decodeStrStrPair (e : Expr) : MetaM (String × String) := do
  let c ← unfoldToCtor ``Prod.mk 4 e
  return (← decodeStrVal (c.getArg! 2), ← decodeStrVal (c.getArg! 3))

private def decodeCodeBlock (e : Expr) : MetaM DecBlock := do
  let c ← unfoldToCtor ``CodeBlock.mk 6 e
  let codeE := c.getArg! 0
  let code ← decodeBytes codeE
  let align ← decodeNatVal (c.getArg! 1)
  let symEs ← decodeListElems (c.getArg! 2)
  let relEs ← decodeListElems (c.getArg! 3)
  let extEs ← decodeListElems (c.getArg! 4)
  let weakEs ← decodeListElems (c.getArg! 5)
  let symbols ← symEs.mapM decodeStrNatPair
  let relocs ← relEs.mapM decodeRelocEntry
  let externs ← extEs.mapM decodeStrVal
  let weakRefs ← weakEs.mapM decodeStrVal
  return { code, codeE, align, symbols, relocs, externs, weakRefs }

private def decodeSymDataInfo (e : Expr) : MetaM DecData := do
  let c ← unfoldToCtor ``SymDataInfo.mk 6 e
  let sym ← decodeStrVal (c.getArg! 0)
  let align ← decodeNatVal (c.getArg! 1)
  let readOnly ← decodeBoolVal (c.getArg! 2)
  let bytesE := c.getArg! 3
  let bytes ← decodeBytes bytesE
  let zeroTail ← decodeNatVal (c.getArg! 4)
  let relEs ← decodeListElems (c.getArg! 5)
  let relocs ← relEs.mapM decodeRelocEntry
  return { sym, align, readOnly, bytes, bytesE, zeroTail, relocs }

private def decodeMultiPlacedLib (e : Expr) : MetaM DecMultiLib := do
  let c ← unfoldToCtor ``MultiPlacedLib.mk 5 e
  let name ← decodeStrVal (c.getArg! 0)
  let blkEs ← decodeListElems (c.getArg! 1)
  let datEs ← decodeListElems (c.getArg! 2)
  let expEs ← decodeListElems (c.getArg! 3)
  let expSymEs ← decodeListElems (c.getArg! 4)
  let blocks ← blkEs.mapM decodeCodeBlock
  let data ← datEs.mapM decodeSymDataInfo
  let exports ← expEs.mapM decodeStrVal
  let exportSyms ← expSymEs.mapM decodeStrStrPair
  return { name, blocks, data, exports, exportSyms }

private def bytesSubEq (full : ByteArray) (start : Nat) (sub : ByteArray) : Bool := Id.run do
  if start + sub.size > full.size then return false
  for k in [:sub.size] do
    if full.get! (start + k) != sub.get! k then return false
  return true

private def rangesDisjointB (s1 l1 s2 l2 : Nat) : Bool :=
  s1 + l1 ≤ s2 || s2 + l2 ≤ s1

private def sliceFreeIn (claimed : Array (Nat × Nat)) (start len : Nat) : Bool :=
  claimed.all fun (cs, cl) => rangesDisjointB start len cs cl

private def countRawRelocsIn (sec : DecRawSec) (start len : Nat) : Nat := Id.run do
  let mut cnt := 0
  for rr in sec.relocs do
    if start ≤ rr.off && rr.off < start + len then
      cnt := cnt + 1
  return cnt

private def rawRelocOffsetsMatch (sec : DecRawSec) (start len : Nat)
    (rs : Array DecReloc) : Bool := Id.run do
  let rawOffs := (sec.relocs.filter fun rr => start ≤ rr.off && rr.off < start + len).map
    (fun rr => rr.off - start)
  if rawOffs.size != rs.size then return false
  let sortedRaw := rawOffs.qsort (· < ·)
  let sortedPlaced := (rs.map (·.off)).qsort (· < ·)
  return sortedRaw == sortedPlaced

private def symDerivedFrom (sym base objName : String) : Bool :=
  sym == base || sym == s!"{base} [{objName}]"

private def hasCoveringObjSym (obj : DecObj) (si start len : Nat) : Bool :=
  obj.symbols.any fun sy =>
    sy.kind == .object && sy.sec == .sec si &&
    sy.value == start && sy.size == len && sy.rawName != ""

private def addPrebuiltDef (declName : Name) (ty val : Expr) : TermElabM Unit := do
  let env ← getEnv
  addDecl (.defnDecl {
    name := declName
    levelParams := []
    type := ty
    value := val
    hints := .regular (getMaxHeight env val + 1)
    safety := .safe
  })
  modifyEnv (addNoncomputable · declName)

private def mkBoolE (b : Bool) : Expr :=
  Lean.mkConst (if b then ``Bool.true else ``Bool.false)

private def mkListE (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [0]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [0]) ty)

private def mkOptE (ty : Expr) : Option Expr → Expr
  | none => mkApp (Lean.mkConst ``Option.none [0]) ty
  | some e => mkApp2 (Lean.mkConst ``Option.some [0]) ty e

private def mkPairE (t1 t2 e1 e2 : Expr) : Expr :=
  mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) t1 t2 e1 e2

private def mkSymBindE : SymBind → Expr
  | .local => Lean.mkConst ``SymBind.local
  | .global => Lean.mkConst ``SymBind.global
  | .weak => Lean.mkConst ``SymBind.weak
  | .other => Lean.mkConst ``SymBind.other

private def mkSymKindE : SymKind → Expr
  | .func => Lean.mkConst ``SymKind.func
  | .object => Lean.mkConst ``SymKind.object
  | .tls => Lean.mkConst ``SymKind.tls
  | .section => Lean.mkConst ``SymKind.section
  | .other => Lean.mkConst ``SymKind.other

private def mkSymSecE : SymSec → Expr
  | .undef => Lean.mkConst ``SymSec.undef
  | .sec idx => mkApp (Lean.mkConst ``SymSec.sec) (mkRawNatLit idx)
  | .other => Lean.mkConst ``SymSec.other

private def mkSliceOriginE (o : SliceOrigin) : Expr :=
  mkApp4 (Lean.mkConst ``SliceOrigin.mk)
    (mkRawNatLit o.oi) (mkRawNatLit o.si) (mkRawNatLit o.start) (mkRawNatLit o.len)

private def mkSymRoleE : MSymRole → Expr
  | .other => Lean.mkConst ``SymRole.other
  | .blockSym bi j off =>
    mkApp3 (Lean.mkConst ``SymRole.blockSym)
      (mkRawNatLit bi) (mkRawNatLit j) (mkRawNatLit off)
  | .dataSym di =>
    mkApp (Lean.mkConst ``SymRole.dataSym) (mkRawNatLit di)

private def mkRawIdStatusE : MRawIdStatus → Expr
  | .other => Lean.mkConst ``RawIdStatus.other
  | .globalDef oi k si =>
    mkApp3 (Lean.mkConst ``RawIdStatus.globalDef)
      (mkRawNatLit oi) (mkRawNatLit k) (mkRawNatLit si)
  | .allNonLocalUndef => Lean.mkConst ``RawIdStatus.allNonLocalUndef
  | .weakOnlyUndef wOi wKi =>
    mkApp2 (Lean.mkConst ``RawIdStatus.weakOnlyUndef)
      (mkRawNatLit wOi) (mkRawNatLit wKi)

/-- `gen_labels_from_objects <thmName> <objs> <lib>`: synthesize an interned `IdxTree`
    provenance certificate and kernel-prove:
    - `<thmName>_bO : Fin (<lib>).blocks.length → Obj.SliceOrigin`
    - `<thmName>_dO : Fin (<lib>).data.length → Obj.SliceOrigin`
    - `<thmName>_spec : Obj.LabelsFromObjects (<objs>) (<lib>) <thmName>_bO <thmName>_dO`
    - `<thmName> : ∃ bO dO, Obj.LabelsFromObjects (<objs>) (<lib>) bO dO` -/
syntax (name := genLabelsFromObjects)
  "gen_labels_from_objects " ident ppSpace term:max ppSpace term:max : command

@[command_elab genLabelsFromObjects]
def elabGenLabelsFromObjects : CommandElab := fun stx => do
  match stx with
  | `(gen_labels_from_objects $thmId:ident $objsTerm:term $libTerm:term) =>
    let currNs ← getCurrNamespace
    let base := thmId.getId
    let mkHelper (sfx : String) : Name × Name × Ident :=
      let s := base.appendAfter sfx
      (s, currNs ++ s, mkIdentFrom thmId s)
    let (_, namesTreeFull, namesTreeId) := mkHelper "_namesTree"
    let (_, charsTreeFull, charsTreeId) := mkHelper "_charsTree"
    let (_, objsTreeFull, objsTreeId) := mkHelper "_objsTree"
    let (_, iLibFull, iLibId) := mkHelper "_iLib"
    let (_, bOTreeFull, bOTreeId) := mkHelper "_bOTree"
    let (_, dOTreeFull, dOTreeId) := mkHelper "_dOTree"
    let (_, _, bOId) := mkHelper "_bO"
    let (_, _, dOId) := mkHelper "_dO"
    let (_, symRoleFull, symRoleId) := mkHelper "_symRole"
    let (_, rawSummaryFull, rawSummaryId) := mkHelper "_rawSummary"
    let (_, rawClaimedFull, rawClaimedId) := mkHelper "_rawClaimed"
    let (_, textGroupsFull, textGroupsId) := mkHelper "_textGroups"
    let (_, dataGroupsFull, dataGroupsId) := mkHelper "_dataGroups"
    let (_, textToGroupFull, textToGroupId) := mkHelper "_textToGroup"
    let (_, dataToGroupFull, dataToGroupId) := mkHelper "_dataToGroup"
    let (_, branchCalledFull, branchCalledId) := mkHelper "_branchCalled"
    let (_, commonExtSetFull, commonExtSetId) := mkHelper "_commonExtSet"
    let (_, _, hobjsEqId) := mkHelper "_objs_eq"
    let (_, _, hlibEqId) := mkHelper "_lib_eq"
    let (_, _, hszId) := mkHelper "_names_sz"
    let (_, _, hcszId) := mkHelper "_chars_sz"
    let (_, _, hnamesEqId) := mkHelper "_names_eq"
    let (_, _, hnnId) := mkHelper "_names_nodup"
    let (_, _, h0Id) := mkHelper "_names_zero"
    let (_, _, hBId) := mkHelper "_blocks_sz"
    let (_, _, hDId) := mkHelper "_data_sz"
    let (_, _, hrolesId) := mkHelper "_roles_ok"
    let (_, _, hobjsOkId) := mkHelper "_objs_ok"
    let (_, _, hgroupsId) := mkHelper "_groups_ok"
    let (_, _, hbdisjId) := mkHelper "_bdisj_ok"
    let (_, _, hddisjId) := mkHelper "_ddisj_ok"
    let (_, _, htbytesId) := mkHelper "_tbytes_ok"
    let (_, _, htmetaId) := mkHelper "_tmeta_ok"
    let (_, _, hdbytesId) := mkHelper "_dbytes_ok"
    let (_, _, hdmetaId) := mkHelper "_dmeta_ok"
    let (_, _, hbrelocsId) := mkHelper "_brelocs_ok"
    let (_, _, hdrelocsId) := mkHelper "_drelocs_ok"
    let (_, _, hexportsId) := mkHelper "_exports_ok"
    let (_, _, hexternsId) := mkHelper "_externs_ok"
    let (_, _, specId) := mkHelper "_spec"

    let (numNames, numBlocks, numData) ← liftTermElabM do
      let listObjTy := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``ExtractedObj)
      let objsE ← instantiateMVars (← elabTerm objsTerm (some listObjTy))
      let libE ← instantiateMVars (← elabTerm libTerm (some (Lean.mkConst ``MultiPlacedLib)))
      let objElemEs ← decodeListElems objsE
      let objs ← (objElemEs.mapM decodeExtractedObj : MetaM _)
      let lib ← decodeMultiPlacedLib libE

      let mut strSet : Std.HashSet String := {}
      strSet := strSet.insert ""
      strSet := strSet.insert lib.name
      for e in lib.exports do strSet := strSet.insert e
      for (a, b) in lib.exportSyms do
        strSet := strSet.insert a
        strSet := strSet.insert b
      for blk in lib.blocks do
        for (s, _) in blk.symbols do strSet := strSet.insert s
        for r in blk.relocs do strSet := strSet.insert r.sym
        for x in blk.externs do strSet := strSet.insert x
        for w in blk.weakRefs do strSet := strSet.insert w
      for d in lib.data do
        strSet := strSet.insert d.sym
        for r in d.relocs do strSet := strSet.insert r.sym
      for obj in objs do
        strSet := strSet.insert obj.name
        for sec in obj.sections do strSet := strSet.insert sec.name
        for sy in obj.symbols do
          strSet := strSet.insert sy.rawName
          strSet := strSet.insert sy.name
          if sy.rawName != "" then
            strSet := strSet.insert s!"{sy.name} [{obj.name}]"

      let mut nameItems : Array (List Char × String) := Array.mkEmpty strSet.size
      for s in strSet do
        nameItems := nameItems.push (s.toList, s)
      let sortedNames := nameItems.qsort fun a b => charListLt a.1 b.1
      let N := sortedNames.size
      let mut strToId : Std.HashMap String Nat := {}
      for i in [:N] do
        strToId := strToId.insert sortedNames[i]!.2 i
      let idOf (s : String) : Nat := strToId[s]!

      let B := lib.blocks.size
      let D := lib.data.size
      let mut symRoleArr : Array MSymRole := Array.replicate N .other
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        for j in [:blk.symbols.size] do
          let (s, off) := blk.symbols[j]!
          let sid := idOf s
          if symRoleArr[sid]! != .other then
            throwError "gen_labels_from_objects: duplicate block symbol {repr s} at block {bi}"
          symRoleArr := symRoleArr.set! sid (.blockSym bi j off)
      for di in [:D] do
        let d := lib.data[di]!
        let sid := idOf d.sym
        if symRoleArr[sid]! != .other then
          throwError "gen_labels_from_objects: data symbol {repr d.sym} collides with existing symbol"
        symRoleArr := symRoleArr.set! sid (.dataSym di)

      let mut rawClaimedArr : Array Bool := Array.replicate N false
      for obj in objs do
        for sy in obj.symbols do
          if sy.rawName != "" then
            rawClaimedArr := rawClaimedArr.set! (idOf sy.rawName) true
            rawClaimedArr := rawClaimedArr.set! (idOf sy.name) true
            rawClaimedArr := rawClaimedArr.set! (idOf s!"{sy.name} [{obj.name}]") true

      let mut rawOccs : Array (Array (Nat × Nat × DecRawSym)) := Array.replicate N #[]
      for oi in [:objs.size] do
        let obj := objs[oi]!
        for k in [:obj.symbols.size] do
          let sy := obj.symbols[k]!
          let rid := idOf sy.rawName
          if rid != 0 then
            rawOccs := rawOccs.set! rid (rawOccs[rid]!.push (oi, k, sy))
      let mut rawSummaryArr : Array MRawIdStatus := Array.replicate N .other
      for rid in [1:N] do
        let occs := rawOccs[rid]!
        if !occs.isEmpty then
          let nonLocalDefs := occs.filter fun (_, _, sy) =>
            sy.bind != .local && sy.sec != .undef
          if nonLocalDefs.size == 1 then
            let (oi, k, sy) := nonLocalDefs[0]!
            if let .sec si := sy.sec then
              if sy.bind == .global || sy.bind == .weak then
                rawSummaryArr := rawSummaryArr.set! rid (.globalDef oi k si)
          else if nonLocalDefs.isEmpty then
            let weakWit? := occs.findSome? fun (oi, k, sy) =>
              if sy.sec == .undef && sy.bind == .weak then some (oi, k) else none
            let allWeakOk := occs.all fun (_, _, sy) =>
              (if sy.sec == .undef then sy.bind == .weak else true) &&
              (match sy.sec with | .sec _ => false | _ => true)
            match weakWit?, allWeakOk with
            | some (wOi, wKi), true =>
              rawSummaryArr := rawSummaryArr.set! rid (.weakOnlyUndef wOi wKi)
            | _, _ =>
              rawSummaryArr := rawSummaryArr.set! rid .allNonLocalUndef

      let mut claimedText : Std.HashMap (Nat × Nat) (Array (Nat × Nat)) := {}
      let mut bOArr : Array SliceOrigin := Array.mkEmpty B
      let mut blkSymWits : Array (Array (Nat × Nat × Option Nat)) := Array.mkEmpty B

      for bi in [:B] do
        let blk := lib.blocks[bi]!
        let len := blk.code.size
        let mut found? : Option SliceOrigin := none
        -- Anchor by first STT_FUNC symbol in `blk.symbols`; fall back to scanning `.text` below.
        for (sym0, off0) in blk.symbols do
          if found?.isNone then
            for oi in [:objs.size] do
              if found?.isNone then
                let obj := objs[oi]!
                for sy in obj.symbols do
                  if found?.isNone then
                    if let .sec si := sy.sec then
                      if sy.kind == .func && sy.rawName != "" && sy.value ≥ off0 &&
                         symDerivedFrom sym0 sy.name obj.name && si < obj.sections.size then
                        let sec := obj.sections[si]!
                        let start := sy.value - off0
                        let prev := claimedText.getD (oi, si) #[]
                        if sec.isExec && sec.readOnly && !sec.isNobits && !sec.isTls &&
                           len > 0 && start % 4 == 0 && len % 4 == 0 &&
                           start + len ≤ sec.size && sec.bytes.size == sec.size &&
                           sec.align > 0 && blk.align % Nat.gcd sec.align start == 0 &&
                           sliceFreeIn prev start len &&
                           bytesSubEq sec.bytes start blk.code &&
                           rawRelocOffsetsMatch sec start len blk.relocs then
                          found? := some { oi, si, start, len }
        if found?.isNone then
          for oi in [:objs.size] do
            if found?.isNone then
              let obj := objs[oi]!
              for si in [:obj.sections.size] do
                if found?.isNone then
                  let sec := obj.sections[si]!
                  if sec.isExec && sec.readOnly && !sec.isNobits && !sec.isTls &&
                     len > 0 && len % 4 == 0 && len ≤ sec.size && sec.bytes.size == sec.size &&
                     sec.align > 0 then
                    let prev := claimedText.getD (oi, si) #[]
                    let mut start := 0
                    while start + len ≤ sec.size && found?.isNone do
                      if blk.align % Nat.gcd sec.align start == 0 &&
                         sliceFreeIn prev start len &&
                         bytesSubEq sec.bytes start blk.code &&
                         rawRelocOffsetsMatch sec start len blk.relocs then
                        found? := some { oi, si, start, len }
                      start := start + 4
        let some o := found?
          | throwError "gen_labels_from_objects: could not locate SliceOrigin for block {bi} \
              (first symbol: {repr (blk.symbols[0]?.map Prod.fst)})"
        bOArr := bOArr.push o
        claimedText := claimedText.insert (o.oi, o.si)
          ((claimedText.getD (o.oi, o.si) #[]).push (o.start, o.len))

        let obj := objs[o.oi]!
        let mut swArr : Array (Nat × Nat × Option Nat) := Array.mkEmpty blk.symbols.size
        for (sym, off) in blk.symbols do
          let sid := idOf sym
          let mut wit? : Option Nat := none
          for k in [:obj.symbols.size] do
            if wit?.isNone then
              let sy := obj.symbols[k]!
              if sy.kind == .func && sy.sec == .sec o.si && sy.rawName != "" &&
                 sy.value == o.start + off && symDerivedFrom sym sy.name obj.name then
                wit? := some k
          if wit?.isNone && rawClaimedArr[sid]! then
            throwError "gen_labels_from_objects: block {bi} symbol {repr sym} at +{off} has no \
              matching STT_FUNC in {obj.name} section {o.si} and is claimed in .symtab"
          swArr := swArr.push (sid, off, wit?)
        blkSymWits := blkSymWits.push swArr

      let mut claimedData : Std.HashMap (Nat × Nat) (Array (Nat × Nat)) := {}
      let mut dOArr : Array SliceOrigin := Array.mkEmpty D
      let mut dataCovWits : Array (Option Nat) := Array.mkEmpty D

      for di in [:D] do
        let d := lib.data[di]!
        let mut foundD? : Option (SliceOrigin × Option Nat) := none
        -- Named covering STT_OBJECT symbol; fall back to uncovered synthetic slices below.
        for oi in [:objs.size] do
          if foundD?.isNone then
            let obj := objs[oi]!
            for k in [:obj.symbols.size] do
              if foundD?.isNone then
                let sy := obj.symbols[k]!
                if let .sec si := sy.sec then
                  if sy.kind == .object && sy.rawName != "" &&
                     symDerivedFrom d.sym sy.name obj.name && si < obj.sections.size then
                    let sec := obj.sections[si]!
                    let start := sy.value
                    let len := sy.size
                    let prev := claimedData.getD (oi, si) #[]
                    let bytesOk :=
                      if sec.isNobits then d.bytes.isEmpty && d.zeroTail == len
                      else sec.bytes.size == sec.size && d.zeroTail == 0 &&
                        d.bytes.size == len && bytesSubEq sec.bytes start d.bytes
                    if !sec.isExec && !sec.isTls && sec.readOnly == d.readOnly &&
                       start + len ≤ sec.size && sec.align > 0 &&
                       d.align % Nat.gcd sec.align start == 0 &&
                       bytesOk && sliceFreeIn prev start len &&
                       rawRelocOffsetsMatch sec start len d.relocs then
                      foundD? := some ({ oi, si, start, len }, some k)
        if foundD?.isNone then
          let sid := idOf d.sym
          if !rawClaimedArr[sid]! then
            for oi in [:objs.size] do
              if foundD?.isNone then
                let obj := objs[oi]!
                for si in [:obj.sections.size] do
                  if foundD?.isNone then
                    let sec := obj.sections[si]!
                    let len := if sec.isNobits then d.zeroTail else d.bytes.size
                    if !sec.isExec && !sec.isTls && sec.readOnly == d.readOnly &&
                       len ≤ sec.size && sec.align > 0 &&
                       (if sec.isNobits then d.bytes.isEmpty else sec.bytes.size == sec.size && d.zeroTail == 0) then
                      let prev := claimedData.getD (oi, si) #[]
                      let mut start := 0
                      while start + len ≤ sec.size && foundD?.isNone do
                        let bytesOk := if sec.isNobits then true else bytesSubEq sec.bytes start d.bytes
                        if d.align % Nat.gcd sec.align start == 0 &&
                           bytesOk && sliceFreeIn prev start len &&
                           !hasCoveringObjSym obj si start len &&
                           rawRelocOffsetsMatch sec start len d.relocs then
                          foundD? := some ({ oi, si, start, len }, none)
                        start := start + 1
        let some (o, covWit) := foundD?
          | throwError "gen_labels_from_objects: could not locate SliceOrigin for data[{di}] \
              ({repr d.sym})"
        dOArr := dOArr.push o
        dataCovWits := dataCovWits.push covWit
        claimedData := claimedData.insert (o.oi, o.si)
          ((claimedData.getD (o.oi, o.si) #[]).push (o.start, o.len))

      let matchSliceRelocs (sliceLabel : String) (o : SliceOrigin) (rs : Array DecReloc) :
          MetaM (Array Nat × Array Nat × Array Nat) := do
        let obj := objs[o.oi]!
        let sec := obj.sections[o.si]!
        let raw := sec.relocs.filter fun rr => o.start ≤ rr.off && rr.off < o.start + o.len
        if raw.size != rs.size then
          throwError "gen_labels_from_objects: {sliceLabel} has {rs.size} relocs, \
            raw slice has {raw.size}"
        let mut tlsWits : Array Nat := Array.replicate rs.size 0
        let mut perm : Array Nat := Array.mkEmpty raw.size
        let mut invPerm : Array Nat := Array.replicate raw.size 0
        let mut used : Array Bool := Array.replicate rs.size false
        for k in [:raw.size] do
          let rr := raw[k]!
          let mut hit? : Option (Nat × Nat) := none
          for pk in [:rs.size] do
            if hit?.isNone && !used[pk]! then
              let r := rs[pk]!
              if r.off + o.start == rr.off && rr.kindName? == some r.kindName &&
                 rr.symIdx < obj.symbols.size then
                let sy := obj.symbols[rr.symIdx]!
                let rSymId := idOf r.sym
                let internalTarget? : Option (Nat × Nat × Int) :=
                  match sy.sec with
                  | .sec sj =>
                    if sy.bind == .local then
                      some (o.oi, sj, (sy.value : Int) + rr.addend)
                    else
                      match rawSummaryArr[idOf sy.rawName]! with
                      | .globalDef oj gk sj' =>
                        if oj == o.oi && gk == rr.symIdx && sj' == sj then
                          some (o.oi, sj, (sy.value : Int) + rr.addend)
                        else none
                      | _ => none
                  | .undef =>
                    if sy.bind == .local then none
                    else
                      match rawSummaryArr[idOf sy.rawName]! with
                      | .globalDef oj gk sj =>
                        let tSym := objs[oj]!.symbols[gk]!
                        some (oj, sj, (tSym.value : Int) + rr.addend)
                      | _ => none
                  | .other => none
                match internalTarget? with
                | some (oj, sj, t) =>
                  if oj < objs.size && sj < objs[oj]!.sections.size then
                    let ojObj := objs[oj]!
                    let secT := ojObj.sections[sj]!
                    if secT.isExec then
                      if let .blockSym bj _ off := symRoleArr[rSymId]! then
                        let bo := bOArr[bj]!
                        if bo.oi == oj && bo.si == sj &&
                           (0 : Int) ≤ (off : Int) + r.addend &&
                           (off : Int) + r.addend ≤ (bo.len : Int) &&
                           ((bo.start + off : Int) + r.addend) == t then
                          hit? := some (pk, 0)
                    else if !secT.isTls then
                      if let .dataSym dj := symRoleArr[rSymId]! then
                        let do_ := dOArr[dj]!
                        if do_.oi == oj && do_.si == sj &&
                           (0 : Int) ≤ r.addend && r.addend ≤ (do_.len : Int) &&
                           ((do_.start : Int) + r.addend) == t then
                          hit? := some (pk, 0)
                    else if symRoleArr[rSymId]! == .other then
                      for tk in [:ojObj.symbols.size] do
                        if hit?.isNone then
                          let ts := ojObj.symbols[tk]!
                          if ts.sec == .sec sj && ts.kind == .tls && ts.rawName != "" &&
                             r.sym == ts.rawName && ((ts.value : Int) + r.addend) == t then
                            hit? := some (pk, tk)
                | none =>
                  if sy.sec == .undef && sy.rawName == r.sym && rSymId != 0 &&
                     r.addend == rr.addend && symRoleArr[rSymId]! == .other then
                    match rawSummaryArr[rSymId]! with
                    | .allNonLocalUndef | .weakOnlyUndef _ _ => hit? := some (pk, 0)
                    | _ => pure ()
          let some (pk, tw) := hit?
            | throwError "gen_labels_from_objects: {sliceLabel} raw relocation #{k} at \
                off={rr.off} has no matching placed RelocEntry"
          used := used.set! pk true
          perm := perm.push pk
          invPerm := invPerm.set! pk k
          tlsWits := tlsWits.set! pk tw
        return (perm, invPerm, tlsWits)

      let mut blkPerms : Array (Array Nat × Array Nat × Array Nat) := Array.mkEmpty B
      for bi in [:B] do
        blkPerms := blkPerms.push
          (← matchSliceRelocs s!"block[{bi}]" bOArr[bi]! lib.blocks[bi]!.relocs)
      let mut dataPerms : Array (Array Nat × Array Nat × Array Nat) := Array.mkEmpty D
      for di in [:D] do
        dataPerms := dataPerms.push
          (← matchSliceRelocs s!"data[{di}]" dOArr[di]! lib.data[di]!.relocs)

      let buildGroups (origins : Array SliceOrigin) :
          Array (Nat × Nat × Array Nat) × Array (Nat × Nat) := Id.run do
        let M := origins.size
        let mut bySec : Std.HashMap (Nat × Nat) (Array Nat) := {}
        for i in [:M] do
          let o := origins[i]!
          bySec := bySec.insert (o.oi, o.si) ((bySec.getD (o.oi, o.si) #[]).push i)
        let mut keys : Array (Nat × Nat) := Array.mkEmpty bySec.size
        for (k, _) in bySec do keys := keys.push k
        let sortedKeys := keys.qsort fun a b =>
          if a.1 == b.1 then a.2 < b.2 else a.1 < b.1
        let mut groups : Array (Nat × Nat × Array Nat) := Array.mkEmpty sortedKeys.size
        let mut toGroup : Array (Nat × Nat) := Array.replicate M (0, 0)
        for gi in [:sortedKeys.size] do
          let (oi, si) := sortedKeys[gi]!
          let rawIdxs := bySec[(oi, si)]!
          let sortedIdxs := rawIdxs.qsort fun i1 i2 =>
            let o1 := origins[i1]!
            let o2 := origins[i2]!
            if o1.start == o2.start then o1.len < o2.len else o1.start < o2.start
          for pi in [:sortedIdxs.size] do
            toGroup := toGroup.set! sortedIdxs[pi]! (gi, pi)
          groups := groups.push (oi, si, sortedIdxs)
        return (groups, toGroup)

      let (tGroups, tToGroup) := buildGroups bOArr
      let (dGroups, dToGroup) := buildGroups dOArr

      let commonExterns : Array Nat :=
        if B > 0 then lib.blocks[0]!.externs.map idOf else #[]
      let commonWeakRefs : Array Nat :=
        if B > 0 then lib.blocks[0]!.weakRefs.map idOf else #[]
      let mut commonExtSetArr : Array Bool := Array.replicate N false
      for eid in commonExterns do
        commonExtSetArr := commonExtSetArr.set! eid true
      let mut branchCalledArr : Array (Option (Nat × Nat)) := Array.replicate N none
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        for ri in [:blk.relocs.size] do
          let r := blk.relocs[ri]!
          if r.kindName == ``RelocKind.call26 || r.kindName == ``RelocKind.jump26 then
            let sid := idOf r.sym
            if branchCalledArr[sid]!.isNone then
              branchCalledArr := branchCalledArr.set! sid (some (bi, ri))

      let mkTreeTy (t : Expr) := mkApp (Lean.mkConst ``IdxTree [0]) t
      let natTy := Lean.mkConst ``Nat
      let boolTy := Lean.mkConst ``Bool
      let strTy := Lean.mkConst ``String
      let charTy := Lean.mkConst ``Char
      let listCharTy := mkApp (Lean.mkConst ``List [0]) charTy
      let listNatTy := mkApp (Lean.mkConst ``List [0]) natTy
      let optNatTy := mkApp (Lean.mkConst ``Option [0]) natTy
      let natOptNatTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy optNatTy
      let symTripleTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natOptNatTy
      let natNatTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natTy
      let optNatNatTy := mkApp (Lean.mkConst ``Option [0]) natNatTy
      let sliceOriginTy := Lean.mkConst ``SliceOrigin
      let iSymTy := Lean.mkConst ``ISym
      let iSecTy := Lean.mkConst ``ISec
      let iObjTy := Lean.mkConst ``IObj
      let iRelocTy := Lean.mkConst ``IReloc
      let iBlockTy := Lean.mkConst ``IBlock
      let iDataTy := Lean.mkConst ``IData
      let symRoleTy := Lean.mkConst ``SymRole
      let rawStatusTy := Lean.mkConst ``RawIdStatus
      let sliceGroupTy := Lean.mkConst ``SliceGroup

      let nameExprs := sortedNames.map fun (_, s) => mkStrLit s
      let charExprs := sortedNames.map fun (_, s) => ProofLib.ProgramReflection.mkCharListExpr s
      addPrebuiltDef namesTreeFull (mkTreeTy strTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero strTy nameExprs)
      addPrebuiltDef charsTreeFull (mkTreeTy listCharTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero listCharTy charExprs)

      let mut iObjExprs : Array Expr := Array.mkEmpty objs.size
      for oi in [:objs.size] do
        let obj := objs[oi]!
        let secExprs := obj.sections.map fun sec =>
          mkAppN (Lean.mkConst ``ISec.mk) #[
            mkRawNatLit (idOf sec.name),
            mkBoolE sec.isExec, mkBoolE sec.readOnly, mkBoolE sec.isNobits, mkBoolE sec.isTls,
            mkRawNatLit sec.align, mkRawNatLit sec.size,
            sec.bytesE, sec.relocsE
          ]
        let symExprs := obj.symbols.map fun sy =>
          let rid := idOf sy.rawName
          let did := if rid != 0 then idOf s!"{sy.name} [{obj.name}]" else 0
          mkAppN (Lean.mkConst ``ISym.mk) #[
            mkRawNatLit rid, mkRawNatLit (idOf sy.name), mkRawNatLit did,
            mkSymBindE sy.bind, mkSymKindE sy.kind, mkSymSecE sy.sec,
            mkRawNatLit sy.value, mkRawNatLit sy.size
          ]
        let secTreeE := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSecTy secExprs
        let symTreeE := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy symExprs
        iObjExprs := iObjExprs.push (mkApp5 (Lean.mkConst ``IObj.mk)
          (mkRawNatLit (idOf obj.name))
          (ProofLib.ProgramReflection.mkCharListExpr obj.name)
          secTreeE symTreeE obj.groupsE)
      addPrebuiltDef objsTreeFull (mkTreeTy iObjTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iObjTy iObjExprs)

      let mut iBlockExprs : Array Expr := Array.mkEmpty B
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        let (perm, invPerm, tlsWits) := blkPerms[bi]!
        let swExprs := blkSymWits[bi]!.map fun (s, off, w?) =>
          mkPairE natTy natOptNatTy (mkRawNatLit s)
            (mkPairE natTy optNatTy (mkRawNatLit off) (mkOptE natTy (w?.map mkRawNatLit)))
        let mut relExprs : Array Expr := Array.mkEmpty blk.relocs.size
        for ri in [:blk.relocs.size] do
          let r := blk.relocs[ri]!
          relExprs := relExprs.push (mkAppN (Lean.mkConst ``IReloc.mk) #[
            mkRawNatLit r.off, r.kindE, mkRawNatLit (idOf r.sym),
            toExpr r.addend, mkBoolE r.localSym, mkRawNatLit tlsWits[ri]!
          ])
        let extIds := blk.externs.map idOf
        let weakIds := blk.weakRefs.map idOf
        let extOvE :=
          if extIds == commonExterns then mkOptE listNatTy none
          else mkOptE listNatTy (some (mkListE natTy (extIds.map mkRawNatLit)))
        let weakOvE :=
          if weakIds == commonWeakRefs then mkOptE listNatTy none
          else mkOptE listNatTy (some (mkListE natTy (weakIds.map mkRawNatLit)))
        iBlockExprs := iBlockExprs.push (mkAppN (Lean.mkConst ``IBlock.mk) #[
          blk.codeE, mkRawNatLit blk.align,
          mkListE symTripleTy swExprs,
          ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iRelocTy relExprs,
          extOvE, weakOvE,
          mkListE natTy (perm.map mkRawNatLit),
          ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natTy (invPerm.map mkRawNatLit)
        ])

      let mut iDataExprs : Array Expr := Array.mkEmpty D
      for di in [:D] do
        let d := lib.data[di]!
        let (perm, invPerm, tlsWits) := dataPerms[di]!
        let mut relExprs : Array Expr := Array.mkEmpty d.relocs.size
        for ri in [:d.relocs.size] do
          let r := d.relocs[ri]!
          relExprs := relExprs.push (mkAppN (Lean.mkConst ``IReloc.mk) #[
            mkRawNatLit r.off, r.kindE, mkRawNatLit (idOf r.sym),
            toExpr r.addend, mkBoolE r.localSym, mkRawNatLit tlsWits[ri]!
          ])
        iDataExprs := iDataExprs.push (mkAppN (Lean.mkConst ``IData.mk) #[
          mkRawNatLit (idOf d.sym), mkRawNatLit d.align, mkBoolE d.readOnly,
          d.bytesE, mkRawNatLit d.zeroTail,
          ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iRelocTy relExprs,
          mkOptE natTy (dataCovWits[di]!.map mkRawNatLit),
          mkListE natTy (perm.map mkRawNatLit),
          ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natTy (invPerm.map mkRawNatLit)
        ])

      let iLibVal := mkAppN (Lean.mkConst ``IMultiLib.mk) #[
        mkRawNatLit (idOf lib.name),
        mkListE natTy (commonExterns.map mkRawNatLit),
        mkListE natTy (commonWeakRefs.map mkRawNatLit),
        ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iBlockTy iBlockExprs,
        ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iDataTy iDataExprs,
        mkListE natTy (lib.exports.map (mkRawNatLit ∘ idOf)),
        mkListE natNatTy (lib.exportSyms.map fun (a, b) =>
          mkPairE natTy natTy (mkRawNatLit (idOf a)) (mkRawNatLit (idOf b)))
      ]
      addPrebuiltDef iLibFull (Lean.mkConst ``IMultiLib) iLibVal

      addPrebuiltDef bOTreeFull (mkTreeTy sliceOriginTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero sliceOriginTy
          (bOArr.map mkSliceOriginE))
      addPrebuiltDef dOTreeFull (mkTreeTy sliceOriginTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero sliceOriginTy
          (dOArr.map mkSliceOriginE))

      addPrebuiltDef symRoleFull (mkTreeTy symRoleTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero symRoleTy
          (symRoleArr.map mkSymRoleE))
      addPrebuiltDef rawSummaryFull (mkTreeTy rawStatusTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero rawStatusTy
          (rawSummaryArr.map mkRawIdStatusE))
      addPrebuiltDef rawClaimedFull (mkTreeTy boolTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero boolTy
          (rawClaimedArr.map mkBoolE))

      let mkGroupExprs (gs : Array (Nat × Nat × Array Nat)) : Array Expr :=
        gs.map fun (oi, si, idxs) =>
          mkApp3 (Lean.mkConst ``SliceGroup.mk)
            (mkRawNatLit oi) (mkRawNatLit si)
            (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natTy (idxs.map mkRawNatLit))
      let mkToGroupExprs (tg : Array (Nat × Nat)) : Array Expr :=
        tg.map fun (gi, pi) => mkPairE natTy natTy (mkRawNatLit gi) (mkRawNatLit pi)

      addPrebuiltDef textGroupsFull (mkTreeTy sliceGroupTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero sliceGroupTy (mkGroupExprs tGroups))
      addPrebuiltDef dataGroupsFull (mkTreeTy sliceGroupTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero sliceGroupTy (mkGroupExprs dGroups))
      addPrebuiltDef textToGroupFull (mkTreeTy natNatTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natNatTy (mkToGroupExprs tToGroup))
      addPrebuiltDef dataToGroupFull (mkTreeTy natNatTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natNatTy (mkToGroupExprs dToGroup))

      let bcExprs := branchCalledArr.map fun w? =>
        mkOptE natNatTy (w?.map fun (bi, ri) =>
          mkPairE natTy natTy (mkRawNatLit bi) (mkRawNatLit ri))
      addPrebuiltDef branchCalledFull (mkTreeTy optNatNatTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero optNatNatTy bcExprs)
      addPrebuiltDef commonExtSetFull (mkTreeTy boolTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero boolTy
          (commonExtSetArr.map mkBoolE))

      return (N, B, D)

    let nLit := Syntax.mkNumLit (toString numNames)
    let bLit := Syntax.mkNumLit (toString numBlocks)
    let dLit := Syntax.mkNumLit (toString numData)

    elabCommand (← `(command|
      noncomputable def $bOId (i : Fin ($libTerm : Arm64.Obj.MultiPlacedLib).blocks.length) :
          Arm64.Obj.SliceOrigin :=
        Arm64.Obj.LabelsInterned.originAt $bOTreeId i))
    elabCommand (← `(command|
      noncomputable def $dOId (i : Fin ($libTerm : Arm64.Obj.MultiPlacedLib).data.length) :
          Arm64.Obj.SliceOrigin :=
        Arm64.Obj.LabelsInterned.originAt $dOTreeId i))

    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hobjsEqId :
          ($objsTerm : List Arm64.Obj.ExtractedObj) =
            ($objsTreeId).toList.map (Arm64.Obj.LabelsInterned.IObj.toExtractedObj $namesTreeId) := by
        rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hlibEqId :
          ($libTerm : Arm64.Obj.MultiPlacedLib) =
            ($iLibId).toMultiPlacedLib $namesTreeId := by
        rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hszId : ($namesTreeId).size? = some $nLit := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hcszId : ($charsTreeId).size? = some $nLit := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hnamesEqId :
          ($namesTreeId).toList = ($charsTreeId).toList.map String.ofList := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hnnId :
          Arm64.Obj.Interned.namesNodup ($charsTreeId).toList = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $h0Id : ($namesTreeId).get? 0 = some "" := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hBId : ($iLibId).blocks.size? = some $bLit := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hDId : ($iLibId).data.size? = some $dLit := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hrolesId :
          Arm64.Obj.LabelsInterned.checkSymRolesB $nLit $iLibId $symRoleId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hobjsOkId :
          Arm64.Obj.LabelsInterned.checkObjSymsB $nLit $charsTreeId $objsTreeId
            $rawSummaryId $rawClaimedId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hgroupsId :
          Arm64.Obj.checkNoDiscardedB ($objsTerm) = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hbdisjId :
          Arm64.Obj.LabelsInterned.checkGroupsDisjointB $bLit $bOTreeId
            $textGroupsId $textToGroupId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hddisjId :
          Arm64.Obj.LabelsInterned.checkGroupsDisjointB $dLit $dOTreeId
            $dataGroupsId $dataToGroupId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $htbytesId :
          Arm64.Obj.LabelsInterned.checkTextGroupsBytesB $objsTreeId ($iLibId).blocks
            $bOTreeId $textGroupsId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $htmetaId :
          Arm64.Obj.LabelsInterned.checkTextSlicesMetaB $nLit $objsTreeId ($iLibId).blocks
            $bOTreeId $rawClaimedId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hdbytesId :
          Arm64.Obj.LabelsInterned.checkDataGroupsBytesB $objsTreeId ($iLibId).data
            $dOTreeId $dataGroupsId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hdmetaId :
          Arm64.Obj.LabelsInterned.checkDataSlicesMetaB $nLit $objsTreeId ($iLibId).data
            $dOTreeId $rawClaimedId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hbrelocsId :
          Arm64.Obj.LabelsInterned.checkAllBlockRelocsB $nLit $objsTreeId $iLibId
            $bOTreeId $dOTreeId $symRoleId $rawSummaryId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hdrelocsId :
          Arm64.Obj.LabelsInterned.checkAllDataRelocsB $nLit $objsTreeId $iLibId
            $bOTreeId $dOTreeId $symRoleId $rawSummaryId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hexportsId :
          Arm64.Obj.LabelsInterned.checkIExportsB $nLit $objsTreeId $iLibId
            $bOTreeId $symRoleId $rawSummaryId = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      private theorem $hexternsId :
          Arm64.Obj.LabelsInterned.checkIExternsB $nLit $iLibId $symRoleId $rawSummaryId
            $branchCalledId $commonExtSetId = true := by rfl_kernel))

    elabCommand (← `(command|
      theorem $specId :
          Arm64.Obj.LabelsFromObjects ($objsTerm) ($libTerm) $bOId $dOId :=
        Arm64.Obj.LabelsInterned.labelsFromObjects_of_split_checks
          $hobjsEqId $hlibEqId $hszId $hcszId $hnamesEqId $hnnId $h0Id $hBId $hDId
          $hrolesId $hobjsOkId $hgroupsId $hbdisjId $hddisjId $htbytesId $htmetaId $hdbytesId $hdmetaId
          $hbrelocsId $hdrelocsId $hexportsId $hexternsId))
    elabCommand (← `(command|
      theorem $thmId :
          ∃ bO dO, Arm64.Obj.LabelsFromObjects ($objsTerm) ($libTerm) bO dO :=
        ⟨$bOId, $dOId, $specId⟩))
  | _ => throwUnsupportedSyntax

end Arm64.Obj.LabelsInterned

end
