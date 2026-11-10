/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SimpAttrs
public import ProofLib.Placed.Fetch
public import ProofLib.ProgramReflection
public import ProofLib.SepLogic.WP.ProjGuardAttr

/-!
# Placed Libraries with Interned Symbol Names

Represents symbol names in a placed library (`Obj.Interned.Lib`, `Reloc`, `Data`, `Layout`)
as `Nat` indices into a duplicate-free names table (`namesNodup`, `Lib.idsOk`), avoiding
UTF-8 `String` comparisons during kernel decision procedures and bridging back to
`CodeBlock` and `PlacedLib`.
-/

@[expose] public section

namespace Arm64.Obj.Interned

open ProofLib.ProgramReflection

/-! ## Interned records -/

/-- A code or data relocation whose symbol is the name with index `sym`. -/
structure Reloc where
  off : Nat
  kind : RelocKind
  sym : Nat
  addend : Int := 0
  localSym : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The `RelocEntry` of an interned relocation under the names table `names`. -/
def Reloc.toEntry (names : List String) (r : Reloc) : RelocEntry :=
  { off := r.off, kind := r.kind, sym := names.getD r.sym "", addend := r.addend,
    localSym := r.localSym }

/-- A data object whose symbol is the name with index `sym`. -/
structure Data where
  sym : Nat
  align : Nat := 1
  readOnly : Bool := true
  bytes : List (BitVec 8) := []
  zeroTail : Nat := 0
  relocs : List Reloc := []
  deriving Inhabited

/-- The `SymDataInfo` of an interned data object under the names table `names`. -/
def Data.toInfo (names : List String) (d : Data) : SymDataInfo :=
  { sym := names.getD d.sym "", align := d.align, readOnly := d.readOnly, bytes := d.bytes,
    zeroTail := d.zeroTail, relocs := d.relocs.map (Reloc.toEntry names) }

/-- A placed library with interned symbol names: `names` is the names table, and every other
    field mirrors `PlacedLib` / `CodeBlock` with a name index in place of each name. -/
structure Lib where
  name : String
  names : List String
  code : List (BitVec 8)
  align : Nat := 4
  symbols : List (Nat × Nat) := []
  relocs : List Reloc := []
  externs : List Nat := []
  weakRefs : List Nat := []
  data : List Data := []
  exports : List Nat := []
  deriving Inhabited

/-- The text block of an interned library. -/
def Lib.block (L : Lib) : CodeBlock :=
  { code := L.code, align := L.align,
    symbols := L.symbols.map fun s => (L.names.getD s.1 "", s.2),
    relocs := L.relocs.map (Reloc.toEntry L.names),
    externs := L.externs.map fun e => L.names.getD e "",
    weakRefs := L.weakRefs.map fun e => L.names.getD e "" }

/-- The `PlacedLib` of an interned library. -/
def Lib.toLib (L : Lib) : PlacedLib :=
  { name := L.name, text := L.block, data := L.data.map (Data.toInfo L.names),
    exports := L.exports.map fun e => L.names.getD e "" }

@[simp] theorem Lib.toLib_text (L : Lib) : L.toLib.text = L.block := rfl
@[simp] theorem Lib.block_code (L : Lib) : L.block.code = L.code := rfl
@[simp] theorem Lib.block_align (L : Lib) : L.block.align = L.align := rfl
@[simp] theorem Lib.block_relocs (L : Lib) :
    L.block.relocs = L.relocs.map (Reloc.toEntry L.names) := rfl
@[simp] theorem Reloc.toEntry_off (names : List String) (r : Reloc) :
    (r.toEntry names).off = r.off := rfl
@[simp] theorem Reloc.toEntry_kind (names : List String) (r : Reloc) :
    (r.toEntry names).kind = r.kind := rfl
@[simp] theorem Reloc.toEntry_addend (names : List String) (r : Reloc) :
    (r.toEntry names).addend = r.addend := rfl
@[simp] theorem Reloc.toEntry_sym (names : List String) (r : Reloc) :
    (r.toEntry names).sym = names.getD r.sym "" := rfl

/-- `Nat` list membership by primitive `Nat.beq` (kernel-fast). -/
def memNat (n : Nat) : List Nat → Bool
  | [] => false
  | m :: ms => if Nat.beq n m then true else memNat n ms

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem memNat_iff {n : Nat} : ∀ {l : List Nat}, memNat n l = true ↔ n ∈ l
  | [] => by simp [memNat]
  | m :: ms => by
    simp only [memNat, List.mem_cons]
    by_cases h : n = m
    · subst h; simp [Nat.beq_refl]
    · simp [nat_beq_false_of_ne h, h, memNat_iff]

/-- A placement given by the generator for an interned library: `addrs[i]` is the address of
    `names[i]` (block symbols' entries are unused), `relax` lists the byte offsets of relaxed
    `ADRP` instructions, `b2b` lists the offsets of retargeted branches, and `undefWeak` lists
    the indices of weak references left undefined. -/
structure Layout where
  base : BitVec 64
  addrs : List (BitVec 64)
  relax : List Nat := []
  b2b : List Nat := []
  undefWeak : List Nat := []
  deriving Inhabited

/-- The `Placement` of a layout under the names table `names`. -/
def Layout.toPlacement (ly : Layout) (names : List String) : Placement :=
  { base := ly.base
    ρ := fun s => ly.addrs.getD (names.idxOf s) 0#64
    relax := fun o => memNat o ly.relax
    b2b := fun o => memNat o ly.b2b
    undefWeak := fun s => memNat (names.idxOf s) ly.undefWeak }

/-! ## Names tables -/

/-- Linear certificate that a names table has no duplicates: its `List Char` reflection
    `cs` (with `names = cs.map String.ofList`) is strictly increasing in codepoint order. -/
def namesNodup (cs : List (List Char)) : Bool := strictChain charListLt cs

theorem nodup_of_namesNodup {names : List String} {cs : List (List Char)}
    (hcs : names = cs.map String.ofList) (h : namesNodup cs = true) : names.Nodup := by
  subst hcs
  have hp := strictChain_pairwise charListLt (fun h₁ h₂ => charListLt_trans h₁ h₂) cs h
  refine List.pairwise_map.mpr (hp.imp fun {a b} hab heq => ?_)
  rw [String.ofList_inj.mp heq, charListLt_irrefl] at hab
  exact Bool.false_ne_true hab

theorem getD_inj {names : List String} (hnd : names.Nodup) :
    ∀ {i j : Nat}, i < names.length → j < names.length →
      names.getD i "" = names.getD j "" → i = j := by
  induction names with
  | nil => intro i j hi; simp at hi
  | cons a as ih =>
    intro i j hi hj h
    have ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h
        simp only [List.length_cons] at hj
        have hj' : j < as.length := by omega
        exact absurd (by rw [h, getD_of_lt hj']; exact List.getElem_mem hj') hna
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h
        simp only [List.length_cons] at hi
        have hi' : i < as.length := by omega
        exact absurd (by rw [← h, getD_of_lt hi']; exact List.getElem_mem hi') hna
      | succ j =>
        simp only [List.getD_cons_succ, List.length_cons] at h hi hj
        exact congrArg (· + 1) (ih hnd' (by omega) (by omega) h)

theorem idxOf_getD {names : List String} (hnd : names.Nodup) {i : Nat}
    (hi : i < names.length) : names.idxOf (names.getD i "") = i := by
  have hmem : names.getD i "" ∈ names := by
    rw [getD_of_lt hi]; exact List.getElem_mem hi
  have hlt := List.idxOf_lt_length_of_mem hmem
  apply getD_inj hnd hlt hi
  rw [getD_of_lt hlt]
  exact List.getElem_idxOf hlt

theorem toPlacement_ρ {ly : Layout} {names : List String} (hnd : names.Nodup) {i : Nat}
    (hi : i < names.length) :
    (ly.toPlacement names).ρ (names.getD i "") = ly.addrs.getD i 0#64 := by
  simp only [Layout.toPlacement, idxOf_getD hnd hi]

@[simp] theorem toPlacement_base (ly : Layout) (names : List String) :
    (ly.toPlacement names).base = ly.base := rfl
@[simp] theorem toPlacement_relax (ly : Layout) (names : List String) (o : Nat) :
    (ly.toPlacement names).relax o = memNat o ly.relax := rfl
@[simp] theorem toPlacement_b2b (ly : Layout) (names : List String) (o : Nat) :
    (ly.toPlacement names).b2b o = memNat o ly.b2b := rfl

/-! ## Index-keyed lookup -/

/-- `Nat`-keyed association-list lookup (first match). -/
def lookupId {α : Type} (i : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k, v) :: rest => if Nat.beq k i then some v else lookupId i rest

theorem lookup_map_getD {α : Type} {names : List String} (hnd : names.Nodup) {i : Nat}
    (hi : i < names.length) :
    ∀ (syms : List (Nat × α)), (∀ s ∈ syms, s.1 < names.length) →
      lookup (names.getD i "") (syms.map fun s => (names.getD s.1 "", s.2)) = lookupId i syms
  | [], _ => rfl
  | (k, v) :: rest, hok => by
    have hk : k < names.length := hok _ List.mem_cons_self
    have ih := lookup_map_getD hnd hi rest (fun s hs => hok s (List.mem_cons_of_mem _ hs))
    simp only [lookup, List.map_cons, List.find?_cons, lookupId] at ih ⊢
    by_cases hki : k = i
    · subst hki; simp [Nat.beq_refl]
    · have h1 : (names.getD k "" == names.getD i "") = false := by
        simp only [beq_eq_false_iff_ne]; exact fun h => hki (getD_inj hnd hk hi h)
      simp only [h1, nat_beq_false_of_ne hki]
      exact ih

/-! ## Well-formedness -/

/-- Every name index of `L` is in range of `L.names` (kernel-fast). -/
def Lib.idsOk (L : Lib) : Bool :=
  let n := L.names.length
  L.symbols.all (fun s => Nat.blt s.1 n) && L.relocs.all (fun r => Nat.blt r.sym n) &&
  L.externs.all (fun e => Nat.blt e n) && L.exports.all (fun e => Nat.blt e n) &&
  L.data.all fun d => Nat.blt d.sym n && d.relocs.all fun r => Nat.blt r.sym n

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

structure Lib.IdsOk (L : Lib) : Prop where
  symbols : ∀ s ∈ L.symbols, s.1 < L.names.length
  relocs : ∀ r ∈ L.relocs, r.sym < L.names.length
  externs : ∀ e ∈ L.externs, e < L.names.length
  exports : ∀ e ∈ L.exports, e < L.names.length
  data : ∀ d ∈ L.data, d.sym < L.names.length ∧ ∀ r ∈ d.relocs, r.sym < L.names.length

theorem Lib.idsOk_spec {L : Lib} (h : L.idsOk = true) : L.IdsOk := by
  simp only [Lib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun d hd => ⟨(h5 d hd).1, (h5 d hd).2⟩⟩

/-! ## Resolution by index -/

/-- Address of the name with index `i` under `ly`: its block offset if it is a block symbol,
    else `ly.addrs[i]`. -/
def resolveId (L : Lib) (ly : Layout) (i : Nat) : BitVec 64 :=
  match lookupId i L.symbols with
  | some off => ly.base + BitVec.ofNat 64 off
  | none => ly.addrs.getD i 0#64

/-- Target `sym + addend` of an interned relocation under `ly`. -/
def targetId (L : Lib) (ly : Layout) (r : Reloc) : BitVec 64 :=
  addSignedAddr (resolveId L ly r.sym) r.addend

theorem resolve_block {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk) {i : Nat}
    (hi : i < L.names.length) :
    L.block.resolve (ly.toPlacement L.names) (L.names.getD i "") = resolveId L ly i := by
  simp only [CodeBlock.resolve, Lib.block, resolveId,
    lookup_map_getD hnd hi L.symbols hok.symbols]
  cases lookupId i L.symbols with
  | some off => rfl
  | none => exact toPlacement_ρ hnd hi

theorem target_block {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk) {r : Reloc}
    (hr : r.sym < L.names.length) :
    L.block.target (ly.toPlacement L.names) (r.toEntry L.names) = targetId L ly r := by
  simp only [CodeBlock.target, Reloc.toEntry_sym, Reloc.toEntry_addend, targetId,
    resolve_block hnd hok hr]

/-- `Nat`-keyed relocation lookup by offset. -/
def relocAtId? (rs : List Reloc) (off : Nat) : Option Reloc := rs.find? fun r => Nat.beq r.off off

theorem relocAt?_block (L : Lib) (off : Nat) :
    L.block.relocAt? off = (relocAtId? L.relocs off).map (Reloc.toEntry L.names) := by
  simp only [CodeBlock.relocAt?, Lib.block_relocs, relocAtId?, List.find?_map]
  congr 1
  have : ((fun r : RelocEntry => r.off == off) ∘ Reloc.toEntry L.names) =
      fun r : Reloc => Nat.beq r.off off := by
    funext r
    simp only [Function.comp, Reloc.toEntry_off]
    cases h : Nat.beq r.off off
    · simp only [beq_eq_false_iff_ne]
      intro h'; subst h'; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
    · simpa using Nat.eq_of_beq_eq_true h
  rw [this]

theorem relocAtId?_mem {rs : List Reloc} {off : Nat} {r : Reloc}
    (h : relocAtId? rs off = some r) : r ∈ rs :=
  List.mem_of_find?_eq_some h

theorem relocAtId?_off {rs : List Reloc} {off : Nat} {r : Reloc}
    (h : relocAtId? rs off = some r) : r.off = off := by
  unfold relocAtId? at h
  exact Nat.eq_of_beq_eq_true (List.find?_some (p := fun (r : Reloc) => Nat.beq r.off off) h)

/-! ## Relaxation, branch-to-branch, and patched words by index -/

theorem getD_beq_getD {names : List String} (hnd : names.Nodup) {a b : Nat}
    (ha : a < names.length) (hb : b < names.length) :
    (names.getD a "" == names.getD b "") = Nat.beq a b := by
  by_cases h : a = b
  · subst h; simp [Nat.beq_refl]
  · rw [nat_beq_false_of_ne h]
    simp only [beq_eq_false_iff_ne]
    exact fun h' => h (getD_inj hnd ha hb h')

/-- The relaxable-pair condition of `CodeBlock.relaxableAt` on two interned relocations `r1`
    (at `off`) and `r2` (at `off + 4`), with symbols compared by index. -/
def pairOk (code : List (BitVec 8)) (off : Nat) (r1 r2 : Reloc) : Bool :=
  r1.kind == .adrpHi21 && r2.kind == .addLo12 && Nat.beq r1.sym r2.sym &&
    r1.addend == r2.addend &&
    isAdrpWord (wordOfBytesLE code off) && isAddImm64Word (wordOfBytesLE code (off + 4)) &&
    (wordOfBytesLE code off &&& 0x1f#32) == (wordOfBytesLE code (off + 4) &&& 0x1f#32) &&
    ((wordOfBytesLE code (off + 4) >>> 5) &&& 0x1f#32) == (wordOfBytesLE code off &&& 0x1f#32) &&
    (wordOfBytesLE code off &&& 0x1f#32) != 0x1f#32

/-- `CodeBlock.relaxableAt` by index. -/
def relaxableId (L : Lib) (off : Nat) : Bool :=
  match relocAtId? L.relocs off, relocAtId? L.relocs (off + 4) with
  | some r1, some r2 => pairOk L.code off r1 r2
  | _, _ => false

theorem relaxableAt_block {L : Lib} (hnd : L.names.Nodup) (hok : L.IdsOk) (off : Nat) :
    L.block.relaxableAt off = relaxableId L off := by
  unfold CodeBlock.relaxableAt relaxableId
  rw [relocAt?_block, relocAt?_block]
  cases h1 : relocAtId? L.relocs off with
  | none => rfl
  | some r1 =>
    cases h2 : relocAtId? L.relocs (off + 4) with
    | none => rfl
    | some r2 =>
      simp only [Option.map_some, pairOk, Reloc.toEntry_kind, Reloc.toEntry_sym,
        Reloc.toEntry_addend, CodeBlock.wordAt, Lib.block_code,
        getD_beq_getD hnd (hok.relocs _ (relocAtId?_mem h1)) (hok.relocs _ (relocAtId?_mem h2))]

/-- The GOT-pair condition of `CodeBlock.gotPairAt` on two interned relocations `r1` (at `off`)
    and `r2` (at `off + 4`), with symbols compared by index. -/
def gotPairOk (code : List (BitVec 8)) (off : Nat) (r1 r2 : Reloc) : Bool :=
  r1.kind == .adrGotPage && r2.kind == .ld64GotLo12Nc &&
    Nat.beq r1.sym r2.sym && r1.addend == 0 && r2.addend == 0 &&
    isAdrpWord (wordOfBytesLE code off) &&
    isLdr64UnsignedWord (wordOfBytesLE code (off + 4)) &&
    (wordOfBytesLE code off &&& 0x1f#32) == (wordOfBytesLE code (off + 4) &&& 0x1f#32) &&
    ((wordOfBytesLE code (off + 4) >>> 5) &&& 0x1f#32) == (wordOfBytesLE code off &&& 0x1f#32) &&
    (wordOfBytesLE code off &&& 0x1f#32) != 0x1f#32

/-- `CodeBlock.gotPairAt` by index. -/
def gotPairId (L : Lib) (off : Nat) : Bool :=
  match relocAtId? L.relocs off, relocAtId? L.relocs (off + 4) with
  | some r1, some r2 => gotPairOk L.code off r1 r2
  | _, _ => false

theorem gotPairAt_block {L : Lib} (hnd : L.names.Nodup) (hok : L.IdsOk) (off : Nat) :
    L.block.gotPairAt off = gotPairId L off := by
  unfold CodeBlock.gotPairAt gotPairId
  rw [relocAt?_block, relocAt?_block]
  cases h1 : relocAtId? L.relocs off with
  | none => rfl
  | some r1 =>
    cases h2 : relocAtId? L.relocs (off + 4) with
    | none => rfl
    | some r2 =>
      simp only [Option.map_some, gotPairOk, Reloc.toEntry_kind, Reloc.toEntry_sym,
        Reloc.toEntry_addend, CodeBlock.wordAt, Lib.block_code,
        getD_beq_getD hnd (hok.relocs _ (relocAtId?_mem h1)) (hok.relocs _ (relocAtId?_mem h2))]

/-- `CodeBlock.tlsieRelaxableAt` by index. -/
def tlsieRelaxableId (L : Lib) (off : Nat) : Bool :=
  match relocAtId? L.relocs off with
  | some r =>
    let w := wordOfBytesLE L.code off
    match r.kind with
    | .tlsieAdrGottprelPage21 => isAdrpWord w
    | .tlsieLd64GottprelLo12Nc =>
      isLdr64UnsignedWord w && ((w >>> 5) &&& 0x1f#32) == (w &&& 0x1f#32)
    | _ => false
  | none => false

theorem tlsieRelaxableAt_block {L : Lib} (off : Nat) :
    L.block.tlsieRelaxableAt off = tlsieRelaxableId L off := by
  unfold CodeBlock.tlsieRelaxableAt tlsieRelaxableId
  rw [relocAt?_block]
  cases relocAtId? L.relocs off <;> rfl

/-- `CodeBlock.b2bNext?` by index. -/
def b2bNextId (L : Lib) (r : Reloc) : Option Reloc :=
  if r.kind == .call26 || r.kind == .jump26 then
    match lookupId r.sym L.symbols with
    | some symOff =>
      let t : Int := (symOff : Int) + r.addend
      if 0 ≤ t then
        match relocAtId? L.relocs t.toNat with
        | some r2 =>
          if r2.kind == .jump26 && isBWord (wordOfBytesLE L.code t.toNat) then some r2 else none
        | none => none
      else none
    | none => none
  else none

theorem b2bNext?_block {L : Lib} (hnd : L.names.Nodup) (hok : L.IdsOk) {r : Reloc}
    (hr : r.sym < L.names.length) :
    L.block.b2bNext? (r.toEntry L.names) = (b2bNextId L r).map (Reloc.toEntry L.names) := by
  have hl : lookup (L.names.getD r.sym "") L.block.symbols = lookupId r.sym L.symbols :=
    lookup_map_getD hnd hr L.symbols hok.symbols
  unfold CodeBlock.b2bNext? b2bNextId
  simp only [Reloc.toEntry_kind, Reloc.toEntry_sym, Reloc.toEntry_addend, hl]
  cases (r.kind == .call26 || r.kind == .jump26) with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    cases lookupId r.sym L.symbols with
    | none => rfl
    | some symOff =>
      simp only
      by_cases ht : (0 : Int) ≤ symOff + r.addend
      · simp only [ht, ↓reduceIte, relocAt?_block]
        cases relocAtId? L.relocs (symOff + r.addend : Int).toNat with
        | none => rfl
        | some r2 =>
          simp only [Option.map_some, Reloc.toEntry_kind, CodeBlock.wordAt, Lib.block_code]
          split <;> simp_all
      · simp only [ht, ↓reduceIte, Option.map_none]

theorem b2bNextId_mem {L : Lib} {r r2 : Reloc} (h : b2bNextId L r = some r2) : r2 ∈ L.relocs := by
  unfold b2bNextId at h
  split at h
  · split at h
    · simp only at h
      split at h
      · split at h
        · rename_i hra
          split at h
          · cases h; exact relocAtId?_mem hra
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `CodeBlock.relocTarget` by index. -/
def relocTargetId (L : Lib) (ly : Layout) (off : Nat) (r : Reloc) : BitVec 64 :=
  match (if memNat off ly.b2b then b2bNextId L r else none) with
  | some r2 => targetId L ly r2
  | none => targetId L ly r

theorem relocTarget_block {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    {r : Reloc} (hr : r.sym < L.names.length) (off : Nat) :
    L.block.relocTarget (ly.toPlacement L.names) off (r.toEntry L.names) =
      relocTargetId L ly off r := by
  unfold CodeBlock.relocTarget relocTargetId
  rw [toPlacement_b2b]
  cases memNat off ly.b2b with
  | false => exact target_block hnd hok hr
  | true =>
    simp only [↓reduceIte, b2bNext?_block hnd hok hr]
    cases h2 : b2bNextId L r with
    | none => exact target_block hnd hok hr
    | some r2 => exact target_block hnd hok (hok.relocs _ (b2bNextId_mem h2))

/-- `CodeBlock.undefWeakBranch` by index (`memNat` checks first, so a library without undefined
    weak references never compares names). -/
def undefWeakId (L : Lib) (ly : Layout) (r : Reloc) : Bool :=
  memNat r.sym ly.undefWeak && (r.kind == .call26 || r.kind == .jump26) &&
    (L.weakRefs.map fun e => L.names.getD e "").contains (L.names.getD r.sym "")

theorem undefWeakBranch_block {L : Lib} {ly : Layout} (hnd : L.names.Nodup) {r : Reloc}
    (hr : r.sym < L.names.length) :
    L.block.undefWeakBranch (ly.toPlacement L.names) (r.toEntry L.names) = undefWeakId L ly r := by
  simp only [CodeBlock.undefWeakBranch, undefWeakId, Layout.toPlacement, Lib.block,
    Reloc.toEntry_sym, Reloc.toEntry_kind, idxOf_getD hnd hr]
  cases memNat r.sym ly.undefWeak <;> cases (r.kind == .call26 || r.kind == .jump26) <;> simp

/-- `CodeBlock.relaxedAt` by index, short-circuiting on `ly.relax` and empty `L.relocs` before
    scanning `L.relocs` and `L.code`. -/
def relaxedId (L : Lib) (ly : Layout) (off : Nat) : Bool :=
  memNat off ly.relax && !L.relocs.isEmpty && relaxableId L off

theorem relaxedAt_block {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    (off : Nat) : L.block.relaxedAt (ly.toPlacement L.names) off = relaxedId L ly off := by
  simp only [CodeBlock.relaxedAt, relaxedId, relaxableAt_block hnd hok, toPlacement_relax]
  cases hrel : L.relocs with
  | nil => simp [relaxableId, relocAtId?, hrel]
  | cons _ _ => cases memNat off ly.relax <;> simp

/-- The patched word at a relocated site `r` (at byte offset `off`), by index
    (`CodeBlock.patchedWord` when `relocAt? off = some r`). -/
def sitePatched (L : Lib) (ly : Layout) (off : Nat) (r : Reloc) : BitVec 32 :=
  let w := wordOfBytesLE L.code off
  let place := ly.base + BitVec.ofNat 64 off
  if relaxedId L ly off then nopWord
  else if 4 ≤ off && relaxedId L ly (off - 4) then adrWord (adrTemplate w) place (targetId L ly r)
  else if r.kind.isGotOrTlsIe && 4 ≤ off &&
      (memNat (off - 4) ly.relax && gotPairId L (off - 4)) then
    adrWord (adrTemplate w) place (targetId L ly r)
  else if r.kind.isGotOrTlsIe && memNat off ly.relax &&
      (gotPairId L off || tlsieRelaxableId L off ||
        (4 ≤ off && gotPairId L (off - 4))) then
    CodeBlock.patchGotOrTlsIeRelaxed w place (targetId L ly r) r.kind
  else patchRelocWord r.kind w place
    (if undefWeakId L ly r then place + 4 else relocTargetId L ly off r)

theorem patchedWord_block_some {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    {off : Nat} {r : Reloc} (h : relocAtId? L.relocs off = some r) :
    L.block.patchedWord (ly.toPlacement L.names) off = sitePatched L ly off r := by
  have hr := hok.relocs _ (relocAtId?_mem h)
  unfold CodeBlock.patchedWord sitePatched
  rw [relocAt?_block, h]
  simp only [Option.map_some, relaxedAt_block hnd hok, gotPairAt_block hnd hok,
    tlsieRelaxableAt_block, target_block hnd hok hr, relocTarget_block hnd hok hr,
    undefWeakBranch_block hnd hr, Reloc.toEntry_kind, CodeBlock.wordAt, Lib.block_code, toPlacement_base, toPlacement_relax]
  cases memNat (off - 4) ly.relax <;> cases memNat off ly.relax <;> simp

theorem patchedWord_block_none {L : Lib} {ly : Layout} {off : Nat}
    (h : relocAtId? L.relocs off = none) :
    L.block.patchedWord (ly.toPlacement L.names) off = wordOfBytesLE L.code off := by
  unfold CodeBlock.patchedWord
  rw [relocAt?_block, h]
  rfl

/-! ## Data objects by index -/

/-- `PlacedLib.patchDataReloc` by index. -/
def patchDataRelocId (L : Lib) (ly : Layout) (addr : BitVec 64) (bytes : List (BitVec 8))
    (r : Reloc) : List (BitVec 8) :=
  let t := targetId L ly r
  let put (n : Nat) (v : BitVec 64) := bytes.take r.off ++ bytesLE n v ++ bytes.drop (r.off + n)
  match r.kind with
  | .abs64 => put 8 t
  | .abs32 => put 4 t
  | .prel32 => put 4 (t - (addr + BitVec.ofNat 64 r.off))
  | _ => bytes

/-- `PlacedLib.patchedData` by index. -/
def patchedDataId (L : Lib) (ly : Layout) (d : Data) : List (BitVec 8) :=
  d.relocs.foldl (patchDataRelocId L ly (ly.addrs.getD d.sym 0#64)) d.bytes ++
    List.replicate d.zeroTail 0#8

theorem foldl_patchDataReloc {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    (addr : BitVec 64) :
    ∀ (rs : List Reloc), (∀ r ∈ rs, r.sym < L.names.length) → ∀ (bs : List (BitVec 8)),
      (rs.map (Reloc.toEntry L.names)).foldl
          (L.toLib.patchDataReloc (ly.toPlacement L.names) addr) bs =
        rs.foldl (patchDataRelocId L ly addr) bs
  | [], _, _ => rfl
  | r :: rs, hrs, bs => by
    simp only [List.map_cons, List.foldl_cons]
    have hr := hrs r List.mem_cons_self
    have : L.toLib.patchDataReloc (ly.toPlacement L.names) addr bs (r.toEntry L.names) =
        patchDataRelocId L ly addr bs r := by
      obtain ⟨off, kind, sym, addend, ls⟩ := r
      have hr' : sym < L.names.length := hr
      cases kind <;> simp only [PlacedLib.patchDataReloc, patchDataRelocId, Lib.toLib_text,
        Reloc.toEntry, resolve_block hnd hok hr', targetId]
    rw [this]
    exact foldl_patchDataReloc hnd hok addr rs (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) _

theorem patchedData_toLib {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    {d : Data} (hd : d ∈ L.data) :
    L.toLib.patchedData (ly.toPlacement L.names) (d.toInfo L.names) = patchedDataId L ly d := by
  have ⟨hs, hrs⟩ := hok.data d hd
  simp only [PlacedLib.patchedData, patchedDataId, Data.toInfo, toPlacement_ρ hnd hs,
    foldl_patchDataReloc hnd hok _ d.relocs hrs]

end Arm64.Obj.Interned

end

public meta section

namespace Arm64.Obj.Interned

def internedLibAllowHeads : Array Lean.Name :=
  #[`Arm64.Obj.Interned.MultiLib.blockLib]

def internedLayoutAllowHeads : Array Lean.Name :=
  #[`Arm64.Obj.Interned.MultiLayout.blockLayout, `Arm64.Obj.Interned.MultiLayout.dataLayout]

declare_wp_proj_guard guardInternedLibNames Lib names ``Lib.names ``Lib.mk internedLibAllowHeads
declare_wp_proj_guard guardInternedLibCode Lib code ``Lib.code ``Lib.mk internedLibAllowHeads
declare_wp_proj_guard guardInternedLibSymbols Lib symbols ``Lib.symbols ``Lib.mk internedLibAllowHeads
declare_wp_proj_guard guardInternedLibRelocs Lib relocs ``Lib.relocs ``Lib.mk internedLibAllowHeads
declare_wp_proj_guard guardInternedLibExterns Lib externs ``Lib.externs ``Lib.mk internedLibAllowHeads
declare_wp_proj_guard guardInternedLibData Lib data ``Lib.data ``Lib.mk internedLibAllowHeads
declare_wp_proj_guard guardInternedLibExports Lib exports ``Lib.exports ``Lib.mk internedLibAllowHeads

declare_wp_proj_guard guardInternedLayoutAddrs Layout addrs ``Layout.addrs ``Layout.mk internedLayoutAllowHeads
declare_wp_proj_guard guardInternedLayoutRelax Layout relax ``Layout.relax ``Layout.mk internedLayoutAllowHeads
declare_wp_proj_guard guardInternedLayoutB2b Layout b2b ``Layout.b2b ``Layout.mk internedLayoutAllowHeads

end Arm64.Obj.Interned

end
