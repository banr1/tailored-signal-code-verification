/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection
public import GeneratedLean.LibsignalSessionPlacedObj
public meta import ProofLib.ProgramReflection -- shake: keep
public import ProofLib.Lemmas
public import ProofLib.SepLogic
import ProofLib.Hoare.SubroutineHook
public import ProofLib.Placed.Multi -- shake: keep

/-!
# Relocatable `MultiPlacedLib` Bridge and Block-Override Invariance

Symbol-layout invariance (`SameSymbolLayout`, `MultiPlacedLib.replaceBlock`), placement typeclasses
(`LibsignalPlacement` on the 615 unmutated blocks and `LibsignalFullPlacement` on the full stock
library), $O(\log N)$ `IdxTree` lookup tables for block symbols and `.rodata`, and read-only data /
frozen-code memory invariants (`LibsignalRoLoaded`, `LibsignalFrozen`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Placed.Bridge

open _root_.Arm64 _root_.Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionBlocks libsignalSessionData libsignalSessionLib)

/-! ## 1. `SameSymbolLayout` and Block-Override Invariance -/

/-- Two `MultiPlacedLib`s have the same symbol layout when each block `i` defines the exact same
`(symbol, offset)` table. Replacing a block's `code` and `relocs` (including zeroing a
garbage-collected block with `code := []`, `relocs := []`) preserves `SameSymbolLayout`. -/
def SameSymbolLayout (lib' lib : MultiPlacedLib) : Prop :=
  lib'.blocks.map (·.symbols) = lib.blocks.map (·.symbols)

theorem SameSymbolLayout.refl (lib : MultiPlacedLib) : SameSymbolLayout lib lib := rfl

theorem SameSymbolLayout.symm {lib' lib : MultiPlacedLib} (h : SameSymbolLayout lib' lib) :
    SameSymbolLayout lib lib' := Eq.symm h

theorem SameSymbolLayout.trans {lib1 lib2 lib3 : MultiPlacedLib}
    (h12 : SameSymbolLayout lib1 lib2) (h23 : SameSymbolLayout lib2 lib3) :
    SameSymbolLayout lib1 lib3 := Eq.trans h12 h23

/-- Block symbol lookup formulated purely over `blocks.map (·.symbols)` so the kernel never
    inspects `CodeBlock.code` or `CodeBlock.relocs`. -/
def lookupSymInLists (name : String) (i : Nat) : List (List (String × Nat)) → Option (Nat × Nat)
  | [] => none
  | syms :: rest =>
    match lookup name syms with
    | some off => some (i, off)
    | none => lookupSymInLists name (i + 1) rest

theorem lookupBlockSymAux_eq_lookupSymInLists (name : String) :
    ∀ (i : Nat) (blocks : List CodeBlock),
      lookupBlockSymAux name i blocks = lookupSymInLists name i (blocks.map (·.symbols))
  | _, [] => rfl
  | i, blk :: rest => by
    simp only [lookupBlockSymAux, List.map_cons, lookupSymInLists]
    cases lookup name blk.symbols with
    | some _ => rfl
    | none => exact lookupBlockSymAux_eq_lookupSymInLists name (i + 1) rest

theorem lookupBlockSym_eq_lookupSymInLists (name : String) (blocks : List CodeBlock) :
    lookupBlockSym name blocks = lookupSymInLists name 0 (blocks.map (·.symbols)) :=
  lookupBlockSymAux_eq_lookupSymInLists name 0 blocks

theorem lookupBlockSym_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (h : SameSymbolLayout lib' lib) (name : String) :
    lookupBlockSym name lib'.blocks = lookupBlockSym name lib.blocks := by
  rw [lookupBlockSym_eq_lookupSymInLists, lookupBlockSym_eq_lookupSymInLists, h]

theorem resolve_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (h : SameSymbolLayout lib' lib) (mpl : MultiPlacement) :
    lib'.resolve mpl = lib.resolve mpl := by
  funext name
  simp only [MultiPlacedLib.resolve, lookupBlockSym_eq_of_sameSymbolLayout h name]

theorem fnAddr_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (h : SameSymbolLayout lib' lib) (mpl : MultiPlacement) :
    lib'.fnAddr mpl = lib.fnAddr mpl := by
  funext name
  simp only [MultiPlacedLib.fnAddr, lookupBlockSym_eq_of_sameSymbolLayout h name]

theorem blockPlacement_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (h : SameSymbolLayout lib' lib) (mpl : MultiPlacement) (i : Nat) :
    lib'.blockPlacement mpl i = lib.blockPlacement mpl i := by
  simp only [MultiPlacedLib.blockPlacement, resolve_eq_of_sameSymbolLayout h mpl]

theorem patchDataReloc_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (h : SameSymbolLayout lib' lib) (mpl : MultiPlacement) :
    lib'.patchDataReloc mpl = lib.patchDataReloc mpl := by
  funext addr bytes r
  simp only [MultiPlacedLib.patchDataReloc, resolve_eq_of_sameSymbolLayout h mpl]

theorem patchedData_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (h : SameSymbolLayout lib' lib) (mpl : MultiPlacement) (d : SymDataInfo) :
    lib'.patchedData mpl d = lib.patchedData mpl d := by
  simp only [MultiPlacedLib.patchedData, patchDataReloc_eq_of_sameSymbolLayout h mpl]

theorem blockLib_text_eq_of_block_eq {lib' lib : MultiPlacedLib} {i : Nat}
    (hblk : lib'.blocks.getD i { code := [] } = lib.blocks.getD i { code := [] }) :
    (lib'.blockLib i).text = (lib.blockLib i).text := by
  simp only [MultiPlacedLib.blockLib, hblk]

theorem blockProgram_eq_of_sameSymbolLayout {lib' lib : MultiPlacedLib}
    (hsym : SameSymbolLayout lib' lib) {i : Nat}
    (hblk : lib'.blocks.getD i { code := [] } = lib.blocks.getD i { code := [] })
    (mpl : MultiPlacement)
    (X O : String → Option (State → State)) (svc : State → State) :
    lib'.blockProgram mpl i X O svc = lib.blockProgram mpl i X O svc := by
  simp only [MultiPlacedLib.blockProgram, PlacedLib.program, blockLib_text_eq_of_block_eq hblk,
    blockPlacement_eq_of_sameSymbolLayout hsym mpl i]

/-- Replace the `code` and `relocs` of block `k` in `lib` while keeping `symbols` and `externs`
    unchanged. For a GC'd block in a mutant binary, pass `code := []` and `relocs := []`. -/
def _root_.Arm64.Obj.MultiPlacedLib.replaceBlock (lib : MultiPlacedLib) (k : Nat)
    (code : List (BitVec 8)) (relocs : List RelocEntry) : MultiPlacedLib :=
  { lib with
    blocks := lib.blocks.modify k fun blk => { blk with code := code, relocs := relocs } }

private theorem map_symbols_modify_code_relocs :
    ∀ (xs : List CodeBlock) (k : Nat) (code : List (BitVec 8)) (relocs : List RelocEntry),
      (xs.modify k fun blk => { blk with code := code, relocs := relocs }).map (·.symbols) =
        xs.map (·.symbols)
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => rfl
  | _ :: rest, k + 1, code, relocs =>
    congrArg (_ :: ·) (map_symbols_modify_code_relocs rest k code relocs)

theorem sameSymbolLayout_replaceBlock (lib : MultiPlacedLib) (k : Nat)
    (code : List (BitVec 8)) (relocs : List RelocEntry) :
    SameSymbolLayout (lib.replaceBlock k code relocs) lib :=
  map_symbols_modify_code_relocs lib.blocks k code relocs

private theorem getD_modify_ne {α : Type} :
    ∀ (xs : List α) (k i : Nat) (f : α → α) (d : α),
      i ≠ k → (xs.modify k f).getD i d = xs.getD i d
  | [], _, _, _, _, _ => by simp
  | _ :: _, 0, 0, _, _, hne => absurd rfl hne
  | _ :: _, 0, _ + 1, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _, _ => rfl
  | _ :: rest, k + 1, i + 1, f, d, hne =>
    getD_modify_ne rest k i f d (fun h => hne (congrArg (· + 1) h))

theorem replaceBlock_getD_ne (lib : MultiPlacedLib) {k i : Nat}
    (code : List (BitVec 8)) (relocs : List RelocEntry) (hne : i ≠ k) (d : CodeBlock) :
    (lib.replaceBlock k code relocs).blocks.getD i d = lib.blocks.getD i d :=
  getD_modify_ne lib.blocks k i _ d hne

/-! ## 2. `LibsignalPlacement` and `LibsignalFullPlacement` -/

public meta section

elab "first_block_externs_of% " listStx:term:max : term => do
  let listE ← Lean.Elab.Term.elabTerm listStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  Lean.Meta.withTransparency .all (Lean.Meta.whnf (Lean.mkApp (Lean.mkConst ``CodeBlock.externs) elems[0]!))

end

/-- The external hook symbols of `libsignalSessionLib` (shared across all 624 blocks). -/
def libsignalSessionExterns : List String :=
  first_block_externs_of% libsignalSessionBlocks

/-- Block indices mutated or garbage-collected across the `cheval26-small-subgroup` and
`cheval26-weak-state` bug-injection binaries:
- `79`: `<libsignal_protocol::pqxdh::Pqxdh as libsignal_protocol::handshake::Handshake>::accept`;
- `202`: `<libsignal_core::curve::PublicKey>::is_canonical` (GC'd in `cheval26-small-subgroup`);
- `55`: `<alloc::vec::Vec<u8>>::append_elements` (GC'd in `cheval26-small-subgroup`);
- `72, 77, 159, 462, 519`: `try_decrypt_from_record` closures and decryption-failure log helpers
  in `cheval26-weak-state`. -/
def libsignalMutatedBlocks : List Nat := [55, 72, 77, 79, 159, 202, 462, 519]

/-- Placement typeclass for `libsignalSessionLib` requiring single-block placeability on all
blocks outside `libsignalMutatedBlocks`, satisfied by both the stock binary and the
`cheval26-small-subgroup` / `cheval26-weak-state` mutant binaries. -/
class LibsignalPlacement where
  mpl : MultiPlacement
  -- 624 = libsignalSessionLib.blocks.length (libsignalSessionLib_blocks_length)
  block_placeable : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
    (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i)
  externsDistinct : (libsignalSessionExterns.map mpl.ρ).Nodup

/-- Full placement typeclass for the stock (unmutated) `libsignalSessionLib` binary. Automatically
    provides `[LibsignalPlacement]` via `toLibsignalPlacement`. -/
class LibsignalFullPlacement extends LibsignalPlacement where
  placeable : libsignalSessionLib.Placeable mpl

abbrev lsmpl [LibsignalPlacement] : MultiPlacement := LibsignalPlacement.mpl
abbrev lsρ [LibsignalPlacement] (e : String) : BitVec 64 := LibsignalPlacement.mpl.ρ e

abbrev LibsignalHooks := String → Option (State → State)

noncomputable abbrev lsBlkProg (pl : MultiPlacement) (i : Nat) (H : LibsignalHooks) : Program :=
  libsignalSessionLib.blockProgram pl i H

theorem _root_.Arm64.Obj.PlacedLib.program_rebase_self (lib : PlacedLib) (pl : Placement)
    (H : String → Option (State → State)) :
    (lib.program pl).rebase pl.base H = lib.program pl H :=
  rfl

theorem libsignalSessionLib_blockProgram_fnAddr {pl : MultiPlacement} {H : LibsignalHooks}
    {i : Nat} {name : String} (hsym : lookupBlockSym name libsignalSessionLib.blocks = some (i, 0)) :
    (libsignalSessionLib.blockProgram pl i H).fnAddr name = libsignalSessionLib.fnAddr pl name ∧
      libsignalSessionLib.fnAddr pl name = pl.base i := by
  obtain ⟨hi, hfind⟩ := lookupBlockSym_some hsym
  have hblk : (libsignalSessionLib.blockLib i).text = libsignalSessionLib.blocks[i] := by
    simp [MultiPlacedLib.blockLib, List.getD, List.getElem?_eq_getElem hi]
  have hl : lookup name (libsignalSessionLib.blockLib i).text.symbols = some 0 := hblk ▸ hfind
  have hfn1 := (PlacedLib.fnAddr_program (lib := libsignalSessionLib.blockLib i)
    (pl := libsignalSessionLib.blockPlacement pl i) (X := H) (O := fun _ => none)
    (svc := Syscall.standard) hl).1
  have hfn2 :
      (libsignalSessionLib.blockLib i).fnAddr (libsignalSessionLib.blockPlacement pl i) name =
        pl.base i := by
    simp [PlacedLib.fnAddr, MultiPlacedLib.blockPlacement, hl]
  have hfn3 : libsignalSessionLib.fnAddr pl name = pl.base i := by
    simp [MultiPlacedLib.fnAddr, hsym]
  exact ⟨hfn1.trans (hfn2.trans hfn3.symm), hfn3⟩

theorem extract_withCodeLoaded {α : Type} {lib : MultiPlacedLib} {pl : MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (lib.withCodeLoaded pl spec).pre x s0 ∗ R) :
    lib.CodeLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem subroutine_ok_withCodeLoaded_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {lib : MultiPlacedLib} {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (lib.withCodeLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withCodeLoaded hp).2) (fun _ _ _ _ hq => hq)

/-! ## 3. Balanced `IdxTree` Lookup for `.rodata` and Block Symbols -/

inductive IdxTree (α : Type) where
  | empty : IdxTree α
  | leaf (val : α) : IdxTree α
  | node (leftSz : Nat) (left right : IdxTree α) : IdxTree α

def IdxTree.get? {α : Type} : IdxTree α → Nat → Option α
  | .empty, _ => none
  | .leaf v, 0 => some v
  | .leaf _, _ + 1 => none
  | .node leftSz l r, i =>
    if i < leftSz then l.get? i else r.get? (i - leftSz)

def IdxTree.toList {α : Type} : IdxTree α → List α
  | .empty => []
  | .leaf v => [v]
  | .node _ l r => l.toList ++ r.toList

def IdxTree.size? {α : Type} : IdxTree α → Option Nat
  | .empty => some 0
  | .leaf _ => some 1
  | .node leftSz l r =>
    match l.size?, r.size? with
    | some ls, some rs => if leftSz == ls then some (ls + rs) else none
    | _, _ => none

def IdxTree.all {α : Type} (p : α → Bool) : IdxTree α → Bool
  | .empty => true
  | .leaf v => p v
  | .node _ l r => l.all p && r.all p

theorem IdxTree.mem_toList_of_get? {α : Type} {t : IdxTree α} {i : Nat} {x : α}
    (h : t.get? i = some x) : x ∈ t.toList := by
  induction t generalizing i with
  | empty => cases h
  | leaf v =>
    cases i with
    | zero =>
      simp only [IdxTree.get?, Option.some.injEq] at h
      subst h
      exact List.mem_singleton_self _
    | succ _ => cases h
  | node leftSz l r ihl ihr =>
    simp only [IdxTree.get?] at h
    split at h
    · exact List.mem_append_left _ (ihl h)
    · exact List.mem_append_right _ (ihr h)

theorem IdxTree.length_toList_of_size? {α : Type} :
    ∀ {t : IdxTree α} {n : Nat}, t.size? = some n → t.toList.length = n
  | .empty, _, h => by simp [IdxTree.size?] at h; simp [IdxTree.toList, ← h]
  | .leaf _, _, h => by simp [IdxTree.size?] at h; simp [IdxTree.toList, ← h]
  | .node leftSz l r, _, h => by
    simp only [IdxTree.size?] at h
    cases hl : l.size? with
    | none => simp [hl] at h
    | some ls =>
      cases hr : r.size? with
      | none => simp [hl, hr] at h
      | some rs =>
        simp only [hl, hr] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          simp [IdxTree.toList, IdxTree.length_toList_of_size? hl,
            IdxTree.length_toList_of_size? hr]
        · cases h

theorem IdxTree.get?_eq_toList_getElem? {α : Type} :
    ∀ {t : IdxTree α} {n : Nat}, t.size? = some n → ∀ (i : Nat), t.get? i = t.toList[i]?
  | .empty, _, _, _ => rfl
  | .leaf _, _, _, 0 => rfl
  | .leaf _, _, _, _ + 1 => rfl
  | .node leftSz l r, _, h, i => by
    simp only [IdxTree.size?] at h
    cases hl : l.size? with
    | none => simp [hl] at h
    | some ls =>
      cases hr : r.size? with
      | none => simp [hl, hr] at h
      | some rs =>
        simp only [hl, hr] at h
        split at h
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          have hllen := IdxTree.length_toList_of_size? hl
          simp only [IdxTree.get?, IdxTree.toList]
          split
          · rename_i hi
            rw [IdxTree.get?_eq_toList_getElem? hl i,
              List.getElem?_append_left (by omega)]
          · rename_i hi
            rw [IdxTree.get?_eq_toList_getElem? hr (i - leftSz),
              List.getElem?_append_right (by omega), hllen]
        · cases h

def IdxTree.getFast? {α : Type} : IdxTree α → Nat → Option α
  | .empty, _ => none
  | .leaf v, 0 => some v
  | .leaf _, _ + 1 => none
  | .node leftSz l r, i =>
    if Nat.blt i leftSz then l.getFast? i else r.getFast? (Nat.sub i leftSz)

theorem IdxTree.getFast?_eq_get? {α : Type} :
    ∀ (t : IdxTree α) (i : Nat), t.getFast? i = t.get? i
  | .empty, _ => rfl
  | .leaf _, 0 => rfl
  | .leaf _, _ + 1 => rfl
  | .node leftSz l r, i => by
    simp only [IdxTree.getFast?, IdxTree.get?, Nat.blt_eq]
    by_cases hi : i < leftSz
    · simp [hi, IdxTree.getFast?_eq_get? l i]
    · simp [hi, Nat.sub_eq, IdxTree.getFast?_eq_get? r (i - leftSz)]

def IdxTree.map {α β : Type} (f : α → β) : IdxTree α → IdxTree β
  | .empty => .empty
  | .leaf v => .leaf (f v)
  | .node leftSz l r => .node leftSz (l.map f) (r.map f)

theorem IdxTree.toList_map {α β : Type} (f : α → β) :
    ∀ (t : IdxTree α), (t.map f).toList = t.toList.map f
  | .empty => rfl
  | .leaf _ => rfl
  | .node _ l r => by
    simp [IdxTree.map, IdxTree.toList, IdxTree.toList_map f l, IdxTree.toList_map f r]

theorem IdxTree.get?_map {α β : Type} (f : α → β) :
    ∀ (t : IdxTree α) (i : Nat), (t.map f).get? i = (t.get? i).map f
  | .empty, _ => rfl
  | .leaf _, 0 => rfl
  | .leaf _, _ + 1 => rfl
  | .node leftSz l r, i => by
    simp only [IdxTree.map, IdxTree.get?]
    split
    · exact IdxTree.get?_map f l i
    · exact IdxTree.get?_map f r (i - leftSz)

def IdxTree.findSome? {α β : Type} (f : α → Option β) : IdxTree α → Option β
  | .empty => none
  | .leaf v => f v
  | .node _ l r =>
    match l.findSome? f with
    | some res => some res
    | none => r.findSome? f

theorem IdxTree.all_toList {α : Type} (p : α → Bool) :
    ∀ (t : IdxTree α), t.all p = t.toList.all p
  | .empty => rfl
  | .leaf v => by simp [IdxTree.all, IdxTree.toList]
  | .node _ l r => by
    simp [IdxTree.all, IdxTree.toList, List.all_append, IdxTree.all_toList p l,
      IdxTree.all_toList p r]

def IdxTree.getD {α : Type} (d : α) (t : IdxTree α) (i : Nat) : α :=
  (t.get? i).getD d

/-- Strided `List Char` hash into `1024` buckets using primitive `Nat.mul`/`Nat.add`/`Nat.mod`
    (hashes every 2nd codepoint to halve recursion steps without invoking `String` operations). -/
def lsHashCharsStep : List Char → Nat → Nat
  | [], h => Nat.mod h 1024
  | [c], h => Nat.mod (Nat.add (Nat.mul h 131) c.val.toNat) 1024
  | c1 :: _ :: cs, h =>
    lsHashCharsStep cs (Nat.mod (Nat.add (Nat.mul h 131) c1.val.toNat) 1048576)

def lsHashChars1024 (cs : List Char) : Nat :=
  lsHashCharsStep cs 5381

/-- Structural `List Char` equality using primitive `Nat.beq` on codepoints (`0` `String` ops). -/
def charListBeq : List Char → List Char → Bool
  | [], [] => true
  | c1 :: r1, c2 :: r2 => if Nat.beq c1.val.toNat c2.val.toNat then charListBeq r1 r2 else false
  | _, _ => false

private theorem char_eq_of_val_toNat_eq {c1 c2 : Char} (h : c1.val.toNat = c2.val.toNat) :
    c1 = c2 := by
  cases c1
  cases c2
  simp only [Char.mk.injEq] at *
  exact UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem charListBeq_iff_eq :
    ∀ {l1 l2 : List Char}, charListBeq l1 l2 = true ↔ l1 = l2
  | [], [] => by simp [charListBeq]
  | _ :: _, [] => by simp [charListBeq]
  | [], _ :: _ => by simp [charListBeq]
  | c1 :: r1, c2 :: r2 => by
    simp only [charListBeq, List.cons.injEq]
    cases hb : Nat.beq c1.val.toNat c2.val.toNat
    · have hc : c1 ≠ c2 := by
        intro heq
        subst heq
        simp [Nat.beq_refl] at hb
      simp [hc]
    · have hc : c1 = c2 := char_eq_of_val_toNat_eq (Nat.eq_of_beq_eq_true hb)
      subst hc
      simpa using charListBeq_iff_eq (l1 := r1) (l2 := r2)

def lookupCharSym (cs : List Char) : List (List Char × Nat) → Option Nat
  | [] => none
  | (s, off) :: rest => if charListBeq s cs then some off else lookupCharSym cs rest

theorem lookupCharSym_eq_lookup (cs : List Char) :
    ∀ (syms : List (List Char × Nat)),
      lookupCharSym cs syms = lookup (String.ofList cs) (toStringSymbols syms)
  | [] => rfl
  | (s, off) :: rest => by
    simp only [lookupCharSym, toStringSymbols, lookup, List.find?]
    have hb : charListBeq s cs = (String.ofList s == String.ofList cs) := by
      apply Bool.eq_iff_iff.mpr
      rw [charListBeq_iff_eq, beq_iff_eq, String.ofList_inj]
    rw [hb]
    cases (String.ofList s == String.ofList cs)
    · exact lookupCharSym_eq_lookup cs rest
    · rfl

def lookupCharBucket (cs : List Char) : List (List Char × Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | (s, i, off) :: rest => if charListBeq s cs then some (i, off) else lookupCharBucket cs rest

public meta section MetaBuilders
open Lean Meta Elab Term

partial def mkIdxTreeExpr (ty : Expr) (elems : Array Expr) (lo hi : Nat) : Expr :=
  if _h : lo < hi then
    if hi - lo == 1 then
      mkApp2 (Lean.mkConst ``IdxTree.leaf) ty elems[lo]!
    else
      let mid := (lo + hi) / 2
      let l := mkIdxTreeExpr ty elems lo mid
      let r := mkIdxTreeExpr ty elems mid hi
      mkApp4 (Lean.mkConst ``IdxTree.node) ty (mkRawNatLit (mid - lo)) l r
  else
    mkApp (Lean.mkConst ``IdxTree.empty) ty

def evalStrLit (e : Expr) : MetaM String := do
  let r ← withTransparency .all (whnf e)
  match r with
  | .lit (.strVal s) => return s
  | _ =>
    let r2 ← withTransparency .all (reduce e)
    match r2 with
    | .lit (.strVal s) => return s
    | _ => throwError "evalStrLit: expected string literal, got {r2}"

elab "idx_tree_of% " tyStx:term:max listStx:term:max : term => do
  let ty ← elabType tyStx
  let listE ← elabTerm listStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  return mkIdxTreeExpr ty elems 0 elems.size

elab "block_syms_tree_of% " blocksStx:term:max : term => do
  let blocksE ← elabTerm blocksStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf blocksE
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
  let symsListTy := mkApp (Lean.mkConst ``List [.zero]) pairTy
  let symLists ← elems.mapM fun blkE => do
    if blkE.isAppOfArity ``CodeBlock.mk 6 then return blkE.getArg! 2
    let blkW ← withTransparency .all (whnf blkE)
    if blkW.isAppOfArity ``CodeBlock.mk 6 then return blkW.getArg! 2
    return mkApp (Lean.mkConst ``CodeBlock.symbols) blkE
  return mkIdxTreeExpr symsListTy symLists 0 symLists.size

elab "block_sym_idx_tree_of% " blocksStx:term:max : term => do
  let blocksE ← elabTerm blocksStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf blocksE
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
  let mut pairs : Array Expr := #[]
  for idx in [0:elems.size] do
    let blkE ← withTransparency .all (whnf elems[idx]!)
    let symsE := mkApp (Lean.mkConst ``CodeBlock.symbols) blkE
    let symElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
    for pE in symElems do
      let pE ← withTransparency .all (whnf pE)
      let s ← evalStrLit (pE.getArg! 2)
      pairs := pairs.push (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natTy (mkStrLit s) (mkRawNatLit idx))
  return mkIdxTreeExpr pairTy pairs 0 pairs.size

end MetaBuilders

private meta def lsHashCharsStepMeta : List Char → Nat → Nat
  | [], h => Nat.mod h 1024
  | [c], h => Nat.mod (Nat.add (Nat.mul h 131) c.val.toNat) 1024
  | c1 :: _ :: cs, h =>
    lsHashCharsStepMeta cs (Nat.mod (Nat.add (Nat.mul h 131) c1.val.toNat) 1048576)

private meta def lsHashChars1024Meta (cs : List Char) : Nat :=
  lsHashCharsStepMeta cs 5381

open Lean Meta Elab Term in
private meta def evalNatLit (e : Expr) : MetaM Nat := do
  let r ← withTransparency .all (whnf e)
  if let some n := r.rawNatLit? then return n
  if let some n := r.nat? then return n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return n
  if let some n := r2.nat? then return n
  throwError "evalNatLit: expected Nat literal, got {r2}"

open Lean Meta Elab Term in
local elab "data_sym_bucket_tree_of% " listStx:term:max : term => do
  let listE ← elabTerm listStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
  let listPairTy := mkApp (Lean.mkConst ``List [.zero]) pairTy
  let mut bkts : Array (Array Expr) := Array.replicate 1024 #[]
  let mut seen : Std.HashSet String := {}
  for idx in [0:elems.size] do
    let dE ← withTransparency .all (whnf elems[idx]!)
    let symE := if dE.isAppOfArity ``SymDataInfo.mk 6 then dE.getArg! 0
      else mkApp (Lean.mkConst ``SymDataInfo.sym) dE
    let s ← evalStrLit symE
    if !seen.contains s then
      seen := seen.insert s
      let h := lsHashChars1024Meta s.toList
      let pE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natTy (mkStrLit s) (mkRawNatLit idx)
      bkts := bkts.modify h (·.push pE)
  let bktExprs ← bkts.mapM fun b => mkListLit pairTy b.toList
  return mkIdxTreeExpr listPairTy bktExprs 0 1024

open Lean Meta Elab Term in
local elab "block_char_syms_tree_of% " blocksStx:term:max : term => do
  let blocksE ← elabTerm blocksStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf blocksE
  let lcTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
  let natTy := Lean.mkConst ``Nat
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) lcTy natTy
  let symsListTy := mkApp (Lean.mkConst ``List [.zero]) pairTy
  let symLists ← elems.mapM fun blkE => do
    let blkW ← withTransparency .all (whnf blkE)
    let symsE := if blkW.isAppOfArity ``CodeBlock.mk 6 then blkW.getArg! 2
      else mkApp (Lean.mkConst ``CodeBlock.symbols) blkW
    let symElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
    let mut cPairs : Array Expr := #[]
    for pE in symElems do
      let pE ← withTransparency .all (whnf pE)
      let s ← evalStrLit (pE.getArg! 2)
      let off ← evalNatLit (pE.getArg! 3)
      cPairs := cPairs.push (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) lcTy natTy (mkStrCharsExpr s) (mkRawNatLit off))
    mkListLit pairTy cPairs.toList
  return mkIdxTreeExpr symsListTy symLists 0 symLists.size

open Lean Meta Elab Term in
local elab "block_char_sym_bucket_tree_of% " blocksStx:term:max : term => do
  let blocksE ← elabTerm blocksStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf blocksE
  let lcTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
  let natTy := Lean.mkConst ``Nat
  let natNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy
  let tripleTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) lcTy natNatTy
  let listTripleTy := mkApp (Lean.mkConst ``List [.zero]) tripleTy
  let mut bkts : Array (Array Expr) := Array.replicate 1024 #[]
  let mut seen : Std.HashSet String := {}
  for idx in [0:elems.size] do
    let blkE ← withTransparency .all (whnf elems[idx]!)
    let symsE := mkApp (Lean.mkConst ``CodeBlock.symbols) blkE
    let symElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
    for pE in symElems do
      let pE ← withTransparency .all (whnf pE)
      let s ← evalStrLit (pE.getArg! 2)
      let off ← evalNatLit (pE.getArg! 3)
      if !seen.contains s then
        seen := seen.insert s
        let h := lsHashChars1024Meta s.toList
        let ioE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy (mkRawNatLit idx) (mkRawNatLit off)
        let tE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) lcTy natNatTy (mkStrCharsExpr s) ioE
        bkts := bkts.modify h (·.push tE)
  let bktExprs ← bkts.mapM fun b => mkListLit tripleTy b.toList
  return mkIdxTreeExpr listTripleTy bktExprs 0 1024

/-- Balanced binary tree of the 1,248 `SymDataInfo` entries of `libsignalSessionData`. -/
def lsDataTree : IdxTree SymDataInfo := idx_tree_of% SymDataInfo libsignalSessionData

theorem lsDataTree_toList : lsDataTree.toList = libsignalSessionLib.data := by
  rfl_kernel

theorem lsDataTree_size : lsDataTree.size? = some 1248 := by decide +kernel

/-- 1024-bucket hash tree of `(sym, dataIdx)` pairs across `libsignalSessionData` (no `bytes`). -/
def lsDataSymBucketTree : IdxTree (List (String × Nat)) :=
  data_sym_bucket_tree_of% libsignalSessionData

/-- Balanced binary tree of `(blk.symbols)` across all 624 blocks of `libsignalSessionBlocks`. -/
noncomputable def lsBlockSymsTree : IdxTree (List (String × Nat)) :=
  block_syms_tree_of% libsignalSessionBlocks

theorem lsBlockSymsTree_toList :
    lsBlockSymsTree.toList = libsignalSessionLib.blocks.map CodeBlock.symbols := by
  rfl_kernel

theorem lsBlockSymsTree_size : lsBlockSymsTree.size? = some 624 := by decide +kernel

theorem libsignalSessionLib_blocks_length : libsignalSessionLib.blocks.length = 624 := by
  have h1 := IdxTree.length_toList_of_size? lsBlockSymsTree_size
  have h2 : (lsBlockSymsTree.toList).length = (libsignalSessionLib.blocks.map CodeBlock.symbols).length :=
    congrArg List.length lsBlockSymsTree_toList
  have h3 : (libsignalSessionLib.blocks.map CodeBlock.symbols).length = libsignalSessionLib.blocks.length :=
    List.length_map CodeBlock.symbols
  exact h3.symm.trans (h2.symm.trans h1)

/-- Balanced binary tree of reflected `(symChars, off)` lists across all 624 blocks. -/
noncomputable def lsBlockCharSymsTree : IdxTree (List (List Char × Nat)) :=
  block_char_syms_tree_of% libsignalSessionBlocks

theorem lsBlockCharSymsTree_map_eq :
    lsBlockCharSymsTree.map toStringSymbols = lsBlockSymsTree := by
  rfl_kernel

theorem lsBlockCharSymsTree_toList :
    lsBlockCharSymsTree.toList.map toStringSymbols =
      libsignalSessionLib.blocks.map CodeBlock.symbols :=
  (IdxTree.toList_map toStringSymbols lsBlockCharSymsTree).symm.trans
    ((congrArg IdxTree.toList lsBlockCharSymsTree_map_eq).trans lsBlockSymsTree_toList)

theorem lsBlockCharSymsTree_size : lsBlockCharSymsTree.size? = some 624 := by decide +kernel

@[instance_reducible]
def LibsignalFullPlacement.ofPlaceable (mpl : MultiPlacement)
    (hpl : libsignalSessionLib.Placeable mpl)
    (hext : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement where
  mpl := mpl
  block_placeable := fun i hi _ =>
    libsignalSessionLib.placeable_blockLib (by rw [libsignalSessionLib_blocks_length]; omega) hpl
  externsDistinct := hext
  placeable := hpl

/-- Balanced binary tree of `(sym, blockIdx)` across `libsignalSessionBlocks`. -/
noncomputable def lsBlockSymIdxTree : IdxTree (String × Nat) :=
  block_sym_idx_tree_of% libsignalSessionBlocks

/-- 1024-bucket hash tree of `(symChars, blockIdx, symOff)` across `libsignalSessionBlocks`. -/
noncomputable def lsCharBucketTree : IdxTree (List (List Char × Nat × Nat)) :=
  block_char_sym_bucket_tree_of% libsignalSessionBlocks

noncomputable def lsCharBucketLookup (cs : List Char) : Option (Nat × Nat) :=
  match lsCharBucketTree.getFast? (lsHashChars1024 cs) with
  | some bkt => lookupCharBucket cs bkt
  | none => none

noncomputable def lsNotBlockCharSym (cs : List Char) : Bool :=
  match lsCharBucketLookup cs with
  | none => true
  | some _ => false

noncomputable def checkBlockCharSymAt (cs : List Char) : Option (Nat × Nat) :=
  match lsCharBucketLookup cs with
  | some (i, off) =>
    match lsBlockCharSymsTree.getFast? i with
    | some syms =>
      match lookupCharSym cs syms with
      | some off' => if Nat.beq off' off then some (i, off) else none
      | none => none
    | none => none
  | none => none

noncomputable def lsNotBlockSym (name : String) : Bool :=
  lsNotBlockCharSym name.toList

/-- Fast $O(1)$-hash + $O(\log B)$-verified lookup of `name` in `libsignalSessionLib.blocks`
    without touching `CodeBlock.code` or `CodeBlock.relocs`. -/
noncomputable def fastLookupBlockSym (name : String) : Option (Nat × Nat) :=
  checkBlockCharSymAt name.toList

private def optPairEq (o : Option (Nat × Nat)) (i off : Nat) : Bool :=
  match o with
  | some (i', off') => if Nat.beq i' i then Nat.beq off' off else false
  | none => false

private theorem optPairEq_iff {o : Option (Nat × Nat)} {i off : Nat} :
    optPairEq o i off = true ↔ o = some (i, off) := by
  cases o with
  | none => simp [optPairEq]
  | some p =>
    rcases p with ⟨i', off'⟩
    simp only [optPairEq, Option.some.injEq, Prod.mk.injEq]
    by_cases hi : i' = i
    · subst hi
      simp [Nat.beq_refl, Nat.beq_eq]
    · have hne : Nat.beq i' i = false := by
        cases hb : Nat.beq i' i
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hi
      simp [hne, hi]

private def checkTreeIdx {α : Type} (f : Nat → α → Bool) : Nat → IdxTree α → Bool
  | _, .empty => true
  | base, .leaf v => f base v
  | base, .node leftSz l r =>
    if checkTreeIdx f base l then checkTreeIdx f (Nat.add base leftSz) r else false

private def checkListIdx {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | base, x :: xs =>
    if f base x then checkListIdx f (Nat.add base 1) xs else false

private theorem bool_ite_eq_and (a b : Bool) : (if a then b else false) = (a && b) := by
  cases a <;> rfl

private theorem checkListIdx_append {α : Type} (f : Nat → α → Bool) :
    ∀ (base : Nat) (l1 l2 : List α),
      checkListIdx f base (l1 ++ l2) =
        (checkListIdx f base l1 && checkListIdx f (base + l1.length) l2)
  | base, [], l2 => by simp [checkListIdx]
  | base, x :: xs, l2 => by
    simp [checkListIdx, Nat.add_eq, checkListIdx_append f (base + 1) xs l2,
      Bool.and_assoc, Nat.add_right_comm, Nat.add_assoc]

private theorem checkTreeIdx_eq_checkListIdx {α : Type} (f : Nat → α → Bool) :
    ∀ {t : IdxTree α} {n : Nat}, t.size? = some n →
      ∀ (base : Nat), checkTreeIdx f base t = checkListIdx f base t.toList
  | .empty, _, _, _ => rfl
  | .leaf v, _, _, base => by simp [checkTreeIdx, checkListIdx, IdxTree.toList]
  | .node leftSz l r, _, h, base => by
    simp only [IdxTree.size?] at h
    cases hl : l.size? with
    | none => simp [hl] at h
    | some ls =>
      cases hr : r.size? with
      | none => simp [hl, hr] at h
      | some rs =>
        simp only [hl, hr] at h
        split at h
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          have hllen := IdxTree.length_toList_of_size? hl
          simp [checkTreeIdx, Nat.add_eq, IdxTree.toList, checkListIdx_append,
            checkTreeIdx_eq_checkListIdx f hl base,
            checkTreeIdx_eq_checkListIdx f hr (base + leftSz), hllen]
        · cases h

private theorem lsBlockCharSyms_bucket_complete :
    checkTreeIdx (fun k syms => syms.all (fun p => optPairEq (lsCharBucketLookup p.1) k p.2))
      0 lsBlockCharSymsTree = true := by
  decide +kernel

private theorem lookupSymInLists_none_of_charBucketNone {cs : List Char}
    (hb : lsCharBucketLookup cs = none) :
    ∀ (base : Nat) (lists : List (List (List Char × Nat))),
      checkListIdx (fun k syms => syms.all (fun p => optPairEq (lsCharBucketLookup p.1) k p.2))
        base lists = true →
      lookupSymInLists (String.ofList cs) base (lists.map toStringSymbols) = none
  | _, [], _ => rfl
  | base, syms :: rest, hc => by
    simp only [checkListIdx, bool_ite_eq_and, Nat.add_eq, Bool.and_eq_true] at hc
    have hnone : lookup (String.ofList cs) (toStringSymbols syms) = none := by
      rw [← lookupCharSym_eq_lookup]
      cases hlk : lookupCharSym cs syms with
      | none => rfl
      | some off =>
        have hmem : (cs, off) ∈ syms := by
          clear hc hb rest
          induction syms with
          | nil => cases hlk
          | cons hd tl ih =>
            rcases hd with ⟨s, o⟩
            simp only [lookupCharSym] at hlk
            split at hlk
            · rename_i heq
              rw [charListBeq_iff_eq] at heq
              subst heq
              simp only [Option.some.injEq] at hlk
              subst hlk
              exact .head _
            · exact .tail _ (ih hlk)
        have hall := (optPairEq_iff.mp (List.all_eq_true.1 hc.1 (cs, off) hmem))
        rw [hb] at hall
        cases hall
    simp only [List.map_cons, lookupSymInLists, hnone]
    exact lookupSymInLists_none_of_charBucketNone hb (base + 1) rest hc.2

/-- Reflected character-list proof (`0` `String` operations) that `name` is not a block symbol. -/
theorem lookupBlockSym_none_of_chars {name : String} {cs : List Char}
    (hname : name = String.ofList cs) (h : lsNotBlockCharSym cs = true) :
    lookupBlockSym name libsignalSessionLib.blocks = none := by
  subst hname
  have hb : lsCharBucketLookup cs = none := by
    cases h0 : lsCharBucketLookup cs <;> simp [lsNotBlockCharSym, h0] at h ⊢
  have hc : checkListIdx (fun k syms => syms.all (fun p => optPairEq (lsCharBucketLookup p.1) k p.2))
      0 lsBlockCharSymsTree.toList = true :=
    (checkTreeIdx_eq_checkListIdx _ lsBlockCharSymsTree_size 0).symm.trans lsBlockCharSyms_bucket_complete
  exact (lookupBlockSym_eq_lookupSymInLists _ _).trans
    ((congrArg (lookupSymInLists (String.ofList cs) 0) lsBlockCharSymsTree_toList.symm).trans
      (lookupSymInLists_none_of_charBucketNone hb 0 _ hc))

theorem lookupBlockSym_none_of_tree {name : String} (h : lsNotBlockSym name = true) :
    lookupBlockSym name libsignalSessionLib.blocks = none :=
  lookupBlockSym_none_of_chars String.ofList_toList.symm h

private theorem lookupSymInLists_at_of_charBucket {cs : List Char} {i off : Nat}
    {syms : List (List Char × Nat)}
    (hb : lsCharBucketLookup cs = some (i, off)) :
    ∀ (base : Nat) (lists : List (List (List Char × Nat))),
      base ≤ i →
      lists[i - base]? = some syms →
      lookupCharSym cs syms = some off →
      checkListIdx (fun k s => s.all (fun p => optPairEq (lsCharBucketLookup p.1) k p.2))
        base lists = true →
      lookupSymInLists (String.ofList cs) base (lists.map toStringSymbols) = some (i, off)
  | _, [], _, hget, _, _ => by simp at hget
  | base, s0 :: rest, hle, hget, hlk, hc => by
    simp only [checkListIdx, bool_ite_eq_and, Nat.add_eq, Bool.and_eq_true] at hc
    by_cases heq : i = base
    · subst heq
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      have hlkS : lookup (String.ofList cs) (toStringSymbols s0) = some off := by
        rw [← lookupCharSym_eq_lookup]
        exact hlk
      simp only [List.map_cons, lookupSymInLists, hlkS]
    · have hlt : base < i := by omega
      have hsub : i - base = (i - (base + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ] at hget
      have hnone : lookup (String.ofList cs) (toStringSymbols s0) = none := by
        rw [← lookupCharSym_eq_lookup]
        cases hlk0 : lookupCharSym cs s0 with
        | none => rfl
        | some o =>
          have hmem : (cs, o) ∈ s0 := by
            clear hc hb rest hget hlk
            induction s0 with
            | nil => cases hlk0
            | cons hd tl ih =>
              rcases hd with ⟨s, o'⟩
              simp only [lookupCharSym] at hlk0
              split at hlk0
              · rename_i heq'
                rw [charListBeq_iff_eq] at heq'
                subst heq'
                simp only [Option.some.injEq] at hlk0
                subst hlk0
                exact .head _
              · exact .tail _ (ih hlk0)
          have hall := optPairEq_iff.mp (List.all_eq_true.1 hc.1 (cs, o) hmem)
          rw [hb, Option.some.injEq, Prod.mk.injEq] at hall
          omega
      simp only [List.map_cons, lookupSymInLists, hnone]
      exact lookupSymInLists_at_of_charBucket hb (base + 1) rest (by omega) hget hlk hc.2

/-- Reflected character-list proof (`0` `String` operations) that `lookupBlockSym name libsignalSessionLib.blocks = some (i, off)`. -/
theorem lookupBlockSym_some_of_chars {name : String} {cs : List Char} {i off : Nat}
    (hname : name = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, off)) :
    lookupBlockSym name libsignalSessionLib.blocks = some (i, off) := by
  subst hname
  unfold checkBlockCharSymAt at h
  cases hb : lsCharBucketLookup cs with
  | none => simp [hb] at h
  | some p =>
    rcases p with ⟨i', off'⟩
    simp only [hb] at h
    cases hg : lsBlockCharSymsTree.getFast? i' with
    | none => simp [hg] at h
    | some syms =>
      simp only [hg] at h
      cases hlk : lookupCharSym cs syms with
      | none => simp [hlk] at h
      | some o' =>
        simp only [hlk] at h
        split at h
        · rename_i hoeq
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have ho' : o' = off' := Nat.eq_of_beq_eq_true hoeq
          subst ho'
          have hg0 : lsBlockCharSymsTree.get? i' = some syms :=
            (IdxTree.getFast?_eq_get? lsBlockCharSymsTree i').symm.trans hg
          have hget : lsBlockCharSymsTree.toList[i' - 0]? = some syms := by
            rw [Nat.sub_zero]
            exact (IdxTree.get?_eq_toList_getElem? lsBlockCharSymsTree_size i').symm.trans hg0
          have hc : checkListIdx
              (fun k s => s.all (fun p => optPairEq (lsCharBucketLookup p.1) k p.2))
              0 lsBlockCharSymsTree.toList = true :=
            (checkTreeIdx_eq_checkListIdx _ lsBlockCharSymsTree_size 0).symm.trans
              lsBlockCharSyms_bucket_complete
          exact (lookupBlockSym_eq_lookupSymInLists _ _).trans
            ((congrArg (lookupSymInLists (String.ofList cs) 0) lsBlockCharSymsTree_toList.symm).trans
              (lookupSymInLists_at_of_charBucket (syms := syms) hb 0 _ (Nat.zero_le i') hget hlk hc))
        · cases h

theorem lookupBlockSym_of_fast_some {name : String} {i off : Nat}
    (h : fastLookupBlockSym name = some (i, off)) :
    lookupBlockSym name libsignalSessionLib.blocks = some (i, off) :=
  lookupBlockSym_some_of_chars String.ofList_toList.symm h

/-! ## 4. Read-Only `.rodata` and Frozen-Code Helpers -/

/-- Every read-only data object `d` of `libsignalSessionLib` holds its initial (relocated) bytes
    `libsignalSessionLib.patchedData pl d` at `pl.ρ d.sym` in `m`, mapped read-only (`Perm.ro`). -/
def LibsignalRoLoaded (pl : MultiPlacement) (m : Memory) : Prop :=
  ∀ d ∈ libsignalSessionLib.data, d.readOnly = true →
    HoldsBytes m (pl.ρ d.sym) (libsignalSessionLib.patchedData pl d) (fun _ => Perm.ro)

def lookupDataBucket (name : String) : List (String × Nat) → Option Nat
  | [] => none
  | (s, idx) :: rest => if s == name then some idx else lookupDataBucket name rest

/-- Fast $O(1)$ bucket lookup of `sym` in `libsignalSessionLib.data`: finds `idx` in
    `lsDataSymBucketTree` without touching `d.bytes` and fetches `lsDataTree.getFast? idx`
    in 11 tree steps. Kept computable for downstream pure `Bool` helpers. -/
def lsroFind (sym : String) : Option SymDataInfo :=
  match lsDataSymBucketTree.getFast? (lsHashChars1024 sym.toList) with
  | some bkt =>
    match lookupDataBucket sym bkt with
    | some idx =>
      match lsDataTree.getFast? idx with
      | some d => if d.sym == sym then some d else none
      | none => none
    | none => none
  | none => none

theorem lsroFind_spec {sym : String} {d : SymDataInfo} (h : lsroFind sym = some d) :
    d ∈ libsignalSessionLib.data ∧ d.sym = sym := by
  unfold lsroFind at h
  cases hb : lsDataSymBucketTree.getFast? (lsHashChars1024 sym.toList) with
  | none => simp [hb] at h
  | some bkt =>
    simp only [hb] at h
    cases hf : lookupDataBucket sym bkt with
    | none => simp [hf] at h
    | some idx =>
      simp only [hf] at h
      cases hg : lsDataTree.getFast? idx with
      | none => simp [hg] at h
      | some d' =>
        simp only [hg] at h
        split at h
        · rename_i hsym
          simp only [Option.some.injEq] at h
          subst h
          rw [beq_iff_eq] at hsym
          have hg' : lsDataTree.get? idx = some d' :=
            (IdxTree.getFast?_eq_get? lsDataTree idx).symm.trans hg
          exact ⟨Eq.mp (congrArg (d' ∈ ·) lsDataTree_toList) (IdxTree.mem_toList_of_get? hg'), hsym⟩
        · cases h

def lsroBytes (sym : String) : List (BitVec 8) :=
  ((lsroFind sym).map (·.bytes)).getD []

def lsroPlain (sym : String) : Bool :=
  match lsroFind sym with
  | some d => d.readOnly && d.relocs.isEmpty && d.zeroTail == 0
  | none => false

theorem lsro_find {sym : String} (h : lsroPlain sym = true) :
    ∃ d ∈ libsignalSessionLib.data, d.sym = sym ∧ d.readOnly = true ∧ d.relocs = [] ∧
      d.zeroTail = 0 ∧ d.bytes = lsroBytes sym := by
  unfold lsroPlain lsroBytes at *
  cases hfind : lsroFind sym with
  | none => simp [hfind] at h
  | some d =>
    simp only [hfind, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hfind
    exact ⟨d, hmem, hsym, h.1.1, h.1.2, h.2, by simp⟩

theorem lsro_holds {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m) {sym : String}
    (h : lsroPlain sym = true) :
    HoldsBytes m (pl.ρ sym) (lsroBytes sym) (fun _ => Perm.ro) := by
  obtain ⟨d, hmem, hsym, hrd, hrel, hzt, hbytes⟩ := lsro_find h
  have hd := hro d hmem hrd
  rw [hsym, MultiPlacedLib.patchedData, hrel, hzt, List.foldl_nil, List.replicate_zero,
    List.append_nil, hbytes] at hd
  exact hd

theorem lsro_read {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m) {sym : String}
    (h : lsroPlain sym = true) :
    m.RO (pl.ρ sym) (lsroBytes sym).length ∧
      m.readBytes (pl.ρ sym) (lsroBytes sym).length = lsroBytes sym :=
  ProofLib.ObjectLoad.holdsBytes_ro (lsro_holds hro h)

theorem lsro_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m) {sym : String}
    {bs : List (BitVec 8)} (h : lsroPlain sym = true) (hbs : lsroBytes sym = bs)
    (hlen : bs.length ≤ 2 ^ 64 := by decide) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ sym ↦ᵣ bs) ∗ P := by
  obtain ⟨hro', hrd⟩ := lsro_read hro h
  rw [hbs] at hro' hrd
  exact IsBlockRO.intro_of_ro (IsBlockRO.pointsToBytesRO _ _ hlen) hro' hrd hP

def lsroCheck (sym : String) (bs : List (BitVec 8)) : Bool :=
  lsroPlain sym && lsroBytes sym == bs && decide (bs.length ≤ 2 ^ 64)

theorem lsroCheck_spec {sym : String} {bs : List (BitVec 8)} (h : lsroCheck sym bs = true) :
    lsroPlain sym = true ∧ lsroBytes sym = bs ∧ bs.length ≤ 2 ^ 64 := by
  unfold lsroCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lsro_intro_chk {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {bs : List (BitVec 8)} (h : lsroCheck sym bs = true)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ sym ↦ᵣ bs) ∗ P := by
  obtain ⟨hp, hbs, hlen⟩ := lsroCheck_spec h
  exact lsro_intro hro hp hbs hlen hP

theorem lsro_read_chk {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {bs : List (BitVec 8)} (h : lsroCheck sym bs = true) :
    m.RO (pl.ρ sym) bs.length ∧ m.readBytes (pl.ρ sym) bs.length = bs := by
  obtain ⟨hp, hbs, _⟩ := lsroCheck_spec h
  simpa [hbs] using lsro_read hro hp

/-! ## 5. Bytes Outside Relocation Sites -/

private theorem length_splice_eq {bytes mid : List (BitVec 8)} {off w : Nat}
    (hm : mid.length = w) (hin : off + w ≤ bytes.length) :
    (bytes.take off ++ mid ++ bytes.drop (off + w)).length = bytes.length := by
  simp only [List.length_append, List.length_take, List.length_drop, hm]
  omega

private theorem getElem?_splice_of_disjoint {bytes mid : List (BitVec 8)} {off w i : Nat}
    (hm : mid.length = w) (hi : i < off ∨ off + w ≤ i) (hin : off + w ≤ bytes.length) :
    (bytes.take off ++ mid ++ bytes.drop (off + w))[i]? = bytes[i]? := by
  have htake : (bytes.take off).length = off := by simp; omega
  rcases hi with hlt | hge
  · rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hlt]
  · rw [List.getElem?_append_right (by simp [htake, hm]; omega)]
    have hsub : off + w + (i - (off + w)) = i := by omega
    simp only [List.length_append, htake, hm, List.getElem?_drop, hsub]

private theorem length_patchDataReloc {lib : MultiPlacedLib} {pl : MultiPlacement} {addr : BitVec 64}
    {bytes : List (BitVec 8)} {r : RelocEntry}
    (hin : r.off + dataRelocWidth r.kind ≤ bytes.length) :
    (lib.patchDataReloc pl addr bytes r).length = bytes.length := by
  unfold MultiPlacedLib.patchDataReloc
  cases hk : r.kind <;> simp only []
  · exact length_splice_eq (by simp [bytesLE]) (by simpa [hk, dataRelocWidth] using hin)
  · exact length_splice_eq (by simp [bytesLE]) (by simpa [hk, dataRelocWidth] using hin)
  · exact length_splice_eq (by simp [bytesLE]) (by simpa [hk, dataRelocWidth] using hin)
  all_goals rfl

private theorem length_foldl_patchDataReloc_aux {lib : MultiPlacedLib} {pl : MultiPlacement}
    {addr : BitVec 64} :
    ∀ (rs : List RelocEntry) (bs : List (BitVec 8)),
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bs.length) →
      (rs.foldl (lib.patchDataReloc pl addr) bs).length = bs.length
  | [], bs, _ => rfl
  | r :: rs, bs, hin => by
    have h1 : (lib.patchDataReloc pl addr bs r).length = bs.length :=
      length_patchDataReloc (hin r (.head _))
    rw [List.foldl_cons, length_foldl_patchDataReloc_aux rs _ (fun r' hr' => by
      rw [h1]; exact hin r' (.tail _ hr')), h1]

def lsroRO (sym : String) (n : Nat) : Bool :=
  match lsroFind sym with
  | some d => d.readOnly &&
      d.relocs.all (fun r => decide (r.off + dataRelocWidth r.kind ≤ d.bytes.length)) &&
      decide (n ≤ d.bytes.length + d.zeroTail)
  | none => false

theorem lsro_perm {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m) {sym : String}
    {n : Nat} (h : lsroRO sym n = true) : m.RO (pl.ρ sym) n := by
  unfold lsroRO at h
  cases hfind : lsroFind sym with
  | none => simp [hfind] at h
  | some d =>
    simp only [hfind, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hfind
    have hd := hro d hmem h.1.1
    rw [hsym] at hd
    have hlen : (libsignalSessionLib.patchedData pl d).length = d.bytes.length + d.zeroTail := by
      simp only [MultiPlacedLib.patchedData, List.length_append, List.length_replicate]
      rw [length_foldl_patchDataReloc_aux _ _ h.1.2]
    have hfull := (ProofLib.ObjectLoad.holdsBytes_ro hd).1
    intro a ha
    exact hfull a (by unfold InRegion at *; omega)

theorem libsignalRoLoaded_of_keepsFrozen {pl : MultiPlacement} {m m' : Memory}
    (hro : LibsignalRoLoaded pl m) (hk : m.KeepsFrozen m') : LibsignalRoLoaded pl m' :=
  fun d hmem hrd => ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen (hro d hmem hrd) hk

/-- Combined frozen-memory invariant preserving both `libsignal` `.rodata` and multi-block code
    across arbitrary `Steps` transitions (`KeepsFrozen`). -/
def LibsignalFrozen (pl : MultiPlacement) (m : Memory) : Prop :=
  LibsignalRoLoaded pl m ∧ libsignalSessionLib.CodeLoaded pl m

theorem libsignalFrozen_of_keepsFrozen {pl : MultiPlacement} {m m' : Memory}
    (hf : LibsignalFrozen pl m) (hk : m.KeepsFrozen m') : LibsignalFrozen pl m' :=
  ⟨libsignalRoLoaded_of_keepsFrozen hf.1 hk, hf.2.of_keepsFrozen hk⟩

theorem getElem?_patchDataReloc_of_disjoint {lib : MultiPlacedLib} {pl : MultiPlacement}
    {addr : BitVec 64} {bytes : List (BitVec 8)} {r : RelocEntry} {i : Nat}
    (hi : i < r.off ∨ r.off + dataRelocWidth r.kind ≤ i)
    (hin : r.off + dataRelocWidth r.kind ≤ bytes.length) :
    (lib.patchDataReloc pl addr bytes r)[i]? = bytes[i]? := by
  unfold MultiPlacedLib.patchDataReloc
  cases hk : r.kind <;> simp only []
  · exact getElem?_splice_of_disjoint (by simp [bytesLE])
      (by simpa [hk, dataRelocWidth] using hi) (by simpa [hk, dataRelocWidth] using hin)
  · exact getElem?_splice_of_disjoint (by simp [bytesLE])
      (by simpa [hk, dataRelocWidth] using hi) (by simpa [hk, dataRelocWidth] using hin)
  · exact getElem?_splice_of_disjoint (by simp [bytesLE])
      (by simpa [hk, dataRelocWidth] using hi) (by simpa [hk, dataRelocWidth] using hin)
  all_goals rfl

theorem getElem?_patchedData_of_notReloc {lib : MultiPlacedLib} {pl : MultiPlacement}
    {d : SymDataInfo} {i : Nat}
    (hin : ∀ r ∈ d.relocs, r.off + dataRelocWidth r.kind ≤ d.bytes.length)
    (hi : ∀ r ∈ d.relocs, i < r.off ∨ r.off + dataRelocWidth r.kind ≤ i) :
    (lib.patchedData pl d)[i]? =
      (d.bytes ++ List.replicate d.zeroTail 0#8)[i]? := by
  have hfold : ∀ (rs : List RelocEntry) (bs : List (BitVec 8)),
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bs.length) →
      (∀ r ∈ rs, i < r.off ∨ r.off + dataRelocWidth r.kind ≤ i) →
      (rs.foldl (lib.patchDataReloc pl (pl.ρ d.sym)) bs)[i]? = bs[i]? ∧
        (rs.foldl (lib.patchDataReloc pl (pl.ρ d.sym)) bs).length = bs.length := by
    intro rs
    induction rs with
    | nil => intro bs _ _; exact ⟨rfl, rfl⟩
    | cons r rs ih =>
      intro bs h1 h2
      have hlen1 := length_patchDataReloc (lib := lib) (pl := pl)
        (addr := pl.ρ d.sym) (h1 r (.head _))
      have hget1 := getElem?_patchDataReloc_of_disjoint (lib := lib) (pl := pl) (addr := pl.ρ d.sym)
        (h2 r (.head _)) (h1 r (.head _))
      obtain ⟨hget, hlen⟩ := ih (lib.patchDataReloc pl (pl.ρ d.sym) bs r)
        (fun r' hr' => by rw [hlen1]; exact h1 r' (.tail _ hr'))
        (fun r' hr' => h2 r' (.tail _ hr'))
      exact ⟨hget.trans hget1, hlen.trans hlen1⟩
  obtain ⟨hget, hlen⟩ := hfold d.relocs d.bytes hin hi
  unfold MultiPlacedLib.patchedData
  by_cases hlt : i < d.bytes.length
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left hlt, hget]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]

end LibsignalBinary.Proofs.Placed.Bridge

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification
export LibsignalBinary.Proofs.Placed.Bridge (SameSymbolLayout lookupSymInLists lookupBlockSymAux_eq_lookupSymInLists)
export LibsignalBinary.Proofs.Placed.Bridge (lookupBlockSym_eq_lookupSymInLists lookupBlockSym_eq_of_sameSymbolLayout)
export LibsignalBinary.Proofs.Placed.Bridge (resolve_eq_of_sameSymbolLayout fnAddr_eq_of_sameSymbolLayout)
export LibsignalBinary.Proofs.Placed.Bridge (blockPlacement_eq_of_sameSymbolLayout patchDataReloc_eq_of_sameSymbolLayout)
export LibsignalBinary.Proofs.Placed.Bridge (patchedData_eq_of_sameSymbolLayout blockLib_text_eq_of_block_eq)
export LibsignalBinary.Proofs.Placed.Bridge (blockProgram_eq_of_sameSymbolLayout sameSymbolLayout_replaceBlock replaceBlock_getD_ne)
export LibsignalBinary.Proofs.Placed.Bridge (libsignalSessionExterns libsignalMutatedBlocks LibsignalPlacement LibsignalFullPlacement)
export LibsignalBinary.Proofs.Placed.Bridge (lsmpl lsρ LibsignalHooks lsBlkProg libsignalSessionLib_blockProgram_fnAddr)
export LibsignalBinary.Proofs.Placed.Bridge (extract_withCodeLoaded subroutine_ok_withCodeLoaded_of_plain IdxTree lsHashCharsStep)
export LibsignalBinary.Proofs.Placed.Bridge (lsHashChars1024 charListBeq charListBeq_iff_eq lookupCharSym lookupCharSym_eq_lookup)
export LibsignalBinary.Proofs.Placed.Bridge (lookupCharBucket mkIdxTreeExpr evalStrLit lsDataTree lsDataTree_toList lsDataTree_size)
export LibsignalBinary.Proofs.Placed.Bridge (lsDataSymBucketTree lsBlockSymsTree lsBlockSymsTree_toList lsBlockSymsTree_size)
export LibsignalBinary.Proofs.Placed.Bridge (libsignalSessionLib_blocks_length lsBlockCharSymsTree lsBlockCharSymsTree_map_eq)
export LibsignalBinary.Proofs.Placed.Bridge (lsBlockCharSymsTree_toList lsBlockCharSymsTree_size lsBlockSymIdxTree lsCharBucketTree)
export LibsignalBinary.Proofs.Placed.Bridge (lsCharBucketLookup lsNotBlockCharSym checkBlockCharSymAt lsNotBlockSym)
export LibsignalBinary.Proofs.Placed.Bridge (fastLookupBlockSym lookupBlockSym_none_of_chars lookupBlockSym_none_of_tree)
export LibsignalBinary.Proofs.Placed.Bridge (lookupBlockSym_some_of_chars lookupBlockSym_of_fast_some LibsignalRoLoaded)
export LibsignalBinary.Proofs.Placed.Bridge (lookupDataBucket lsroFind lsroFind_spec lsroBytes lsroPlain lsro_find lsro_holds)
export LibsignalBinary.Proofs.Placed.Bridge (lsro_read lsro_intro lsroCheck lsroCheck_spec lsro_intro_chk lsro_read_chk lsroRO)
export LibsignalBinary.Proofs.Placed.Bridge (lsro_perm libsignalRoLoaded_of_keepsFrozen LibsignalFrozen)
export LibsignalBinary.Proofs.Placed.Bridge (libsignalFrozen_of_keepsFrozen getElem?_patchDataReloc_of_disjoint)
export LibsignalBinary.Proofs.Placed.Bridge (getElem?_patchedData_of_notReloc)
end CryptoVerification
namespace CryptoVerification.SameSymbolLayout
export LibsignalBinary.Proofs.Placed.Bridge.SameSymbolLayout (refl symm trans)
end CryptoVerification.SameSymbolLayout
namespace CryptoVerification.IdxTree
export LibsignalBinary.Proofs.Placed.Bridge.IdxTree (empty leaf node get? toList size? all mem_toList_of_get? length_toList_of_size? get?_eq_toList_getElem?)
export LibsignalBinary.Proofs.Placed.Bridge.IdxTree (getFast? getFast?_eq_get? map toList_map get?_map findSome? all_toList getD)
end CryptoVerification.IdxTree
namespace CryptoVerification.LibsignalPlacement
export LibsignalBinary.Proofs.Placed.Bridge.LibsignalPlacement (mk mpl block_placeable externsDistinct)
end CryptoVerification.LibsignalPlacement
namespace CryptoVerification.LibsignalFullPlacement
export LibsignalBinary.Proofs.Placed.Bridge.LibsignalFullPlacement (mk toLibsignalPlacement placeable ofPlaceable)
end CryptoVerification.LibsignalFullPlacement
-- AUTO-BRIDGE END
