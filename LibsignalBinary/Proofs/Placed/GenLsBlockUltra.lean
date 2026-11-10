/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlockFast
public meta import LibsignalBinary.Proofs.Placed.GenLsBlockFast
public meta import LibsignalBinary.Proofs.Placed.GenLsBlock
public meta import LibsignalBinary.Proofs.Placed.PlacedCallSym
public meta import LibsignalBinary.Proofs.Placed.Bridge
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.GenDecodes
public meta import Lean
import ProofLib.Hoare.Hooks
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Tree-Accelerated Per-Block Fetch and Relocation Elaborator

Defines `gen_ls_blk_ultra <idx>`, emitting the same per-block declarations and theorem signatures as
`gen_ls_blk <idx>` using $O(\log N)$ `IdxTree`, `RelocTree`, and `WordTree.getQuad?` proofs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

theorem ls_hook_ok_ultra_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_mem hmem hi hunmut).trans hf) hok

private theorem lsBlocksTree_toList : lsBlocksTree.toList = libsignalSessionLib.blocks := rfl

private theorem lsBlocksTree_size : lsBlocksTree.size? = some 624 := by decide +kernel

theorem blockLib_eq_of_lsBlocksTreeU {lib : PlacedLib} {i : Nat} {blk : CodeBlock}
    (hget : lsBlocksTree.get? i = some blk)
    (hlib : lib = { name := "libsignalSession", text := blk, data := libsignalSessionData,
                    exports := libsignalSessionMultiLib.exports }) :
    lib = libsignalSessionLib.blockLib i := by
  subst hlib
  have h1 : lsBlocksTree.toList[i]? = some blk :=
    (IdxTree.get?_eq_toList_getElem? lsBlocksTree_size i).symm.trans hget
  rw [lsBlocksTree_toList] at h1
  unfold MultiPlacedLib.blockLib
  change PlacedLib.mk "libsignalSession" blk _ _ =
    PlacedLib.mk libsignalSessionLib.name (libsignalSessionLib.blocks.getD i { code := [] })
      libsignalSessionLib.data libsignalSessionLib.exports
  have hgetD : libsignalSessionLib.blocks.getD i { code := [] } = blk := by
    rw [List.getD_eq_getElem?_getD, h1]; rfl
  rw [hgetD]
  rfl

syntax (name := genLsBlkUltraStx) "gen_ls_blk_ultra " num : command

section MetaGenLsBlkUltra

open Lean Meta Elab Term Command

/-- Precompute literal `List (String × Nat × Nat)` and `List String` constants once in
    `GenLsBlockUltra.olean` so downstream modules read raw `.strVal`/`.natVal` syntax directly from
    `ConstantInfo.value!` in `< 1 ms` without `[init]` or `whnf` over `VecTree`. -/
private meta def whnfAllU (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private meta def evalStrLitU (e : Expr) : MetaM String := do
  let r ← whnfAllU e
  match r with
  | .lit (.strVal s) => return s
  | _ =>
    let r2 ← withTransparency .all (reduce e)
    match r2 with
    | .lit (.strVal s) => return s
    | _ => throwError "gen_ls_blk_ultra: expected string literal, got {r2}"

private meta def evalNatExprU? (e : Expr) : MetaM (Option Nat) := do
  if let .lit (.natVal n) := e then return some n
  let r ← whnfAllU e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

private meta partial def lookupIdxTreeExprU (treeE : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let r ← whnfAllU treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return none
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    if idx == 0 then return some (r.getArg! 1) else return none
  else if r.isAppOfArity ``IdxTree.node 4 then
    let some leftSz ← evalNatExprU? (r.getArg! 1)
      | throwError "gen_ls_blk_ultra: invalid leftSz in IdxTree.node"
    if idx < leftSz then
      lookupIdxTreeExprU (r.getArg! 2) idx
    else
      lookupIdxTreeExprU (r.getArg! 3) (idx - leftSz)
  else
    throwError "gen_ls_blk_ultra: unexpected IdxTree expression {r}"

private meta partial def collectSymIdxTreeU (treeE : Expr)
    (acc : Array (String × Nat × Nat))
    (seen : Std.HashSet String)
    (counts : Std.HashMap Nat Nat) :
    MetaM (Array (String × Nat × Nat) × Std.HashSet String × Std.HashMap Nat Nat) := do
  let r ← whnfAllU treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return (acc, seen, counts)
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    let pE ← whnfAllU (r.getArg! 1)
    let s ← evalStrLitU (pE.getArg! 2)
    let some j ← evalNatExprU? (pE.getArg! 3)
      | throwError "gen_ls_blk_ultra: invalid block index in lsBlockSymIdxTree"
    if seen.contains s then
      return (acc, seen, counts)
    else
      let k := counts.getD j 0
      return (acc.push (s, j, k), seen.insert s, counts.insert j (k + 1))
  else if r.isAppOfArity ``IdxTree.node 4 then
    let (acc, seen, counts) ← collectSymIdxTreeU (r.getArg! 2) acc seen counts
    collectSymIdxTreeU (r.getArg! 3) acc seen counts
  else
    throwError "gen_ls_blk_ultra: unexpected lsBlockSymIdxTree expression {r}"

private meta partial def mkBktTreeU (elemTy : Expr) (elems : Array Expr) (lo hi : Nat) : Expr :=
  if hi - lo == 1 then
    mkApp2 (Lean.mkConst ``IdxTree.leaf) elemTy elems[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp4 (Lean.mkConst ``IdxTree.node) elemTy (mkNatLit (mid - lo))
      (mkBktTreeU elemTy elems lo mid) (mkBktTreeU elemTy elems mid hi)

local elab "#init_ls_sym_buckets64" : command => liftTermElabM do
  let currNs ← getCurrNamespace
  let (entries, _, _) ← collectSymIdxTreeU (Lean.mkConst ``lsBlockSymIdxTree) #[] {} {}
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let strNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
  let mut bkts : Array (Array Expr) := Array.replicate 64 #[]
  for (s, j, _) in entries do
    let sjE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natTy (mkStrLit s) (mkNatLit j)
    let bi := s.utf8ByteSize % 64
    bkts := bkts.modify bi (·.push sjE)
  let listPairTy := mkApp (Lean.mkConst ``List [.zero]) strNatTy
  let mut bktListExprs : Array Expr := #[]
  for b in bkts do
    bktListExprs := bktListExprs.push (← mkListLit strNatTy b.toList)
  withExporting <| addDecl (.defnDecl {
    name := currNs ++ `lsSymBuckets64, levelParams := [],
    type := mkApp (Lean.mkConst ``IdxTree) listPairTy,
    value := mkBktTreeU listPairTy bktListExprs 0 64, hints := .regular 0, safety := .safe
  })

set_option maxHeartbeats 0 in
#init_ls_sym_buckets64

noncomputable def lsBucketLookup (name : String) : Option Nat :=
  match lsSymBuckets64.get? (name.utf8ByteSize % 64) with
  | some bkt => lookup name bkt
  | none => none

private def checkTreeIdxU {α : Type} (f : Nat → α → Bool) : Nat → IdxTree α → Bool
  | _, .empty => true
  | base, .leaf v => f base v
  | base, .node leftSz l r => checkTreeIdxU f base l && checkTreeIdxU f (base + leftSz) r

private def checkListIdxU {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | base, x :: xs => f base x && checkListIdxU f (base + 1) xs

private theorem checkListIdxU_append {α : Type} (f : Nat → α → Bool) :
    ∀ (base : Nat) (l1 l2 : List α),
      checkListIdxU f base (l1 ++ l2) =
        (checkListIdxU f base l1 && checkListIdxU f (base + l1.length) l2)
  | base, [], l2 => by simp [checkListIdxU]
  | base, x :: xs, l2 => by
    simp [checkListIdxU, checkListIdxU_append f (base + 1) xs l2, Bool.and_assoc,
      Nat.add_right_comm, Nat.add_assoc]

private theorem checkTreeIdxU_eq_checkListIdxU {α : Type} (f : Nat → α → Bool) :
    ∀ {t : IdxTree α} {n : Nat}, t.size? = some n →
      ∀ (base : Nat), checkTreeIdxU f base t = checkListIdxU f base t.toList
  | .empty, _, _, _ => rfl
  | .leaf v, _, _, base => by simp [checkTreeIdxU, checkListIdxU, IdxTree.toList]
  | .node leftSz l r, _, h, base => by
    simp only [IdxTree.size?] at h
    cases hl : l.size? with
    | none => simp [hl] at h
    | some ls =>
      cases hr : r.size? with
      | some rs =>
        simp only [hl, hr] at h
        split at h
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          have hllen := IdxTree.length_toList_of_size? hl
          simp [checkTreeIdxU, IdxTree.toList, checkListIdxU_append,
            checkTreeIdxU_eq_checkListIdxU f hl base,
            checkTreeIdxU_eq_checkListIdxU f hr (base + leftSz), hllen]
        · cases h
      | none => simp [hl, hr] at h

private theorem lsBlockSyms_bucket_sound :
    checkTreeIdxU (fun i syms => syms.all (fun p => lsBucketLookup p.1 == some i))
      0 lsBlockSymsTree = true := by
  decide +kernel

private theorem lookupSymInLists_none_of_bucketNone {tgt : String} (hb : lsBucketLookup tgt = none) :
    ∀ (base : Nat) (lists : List (List (String × Nat))),
      checkListIdxU (fun i syms => syms.all (fun p => lsBucketLookup p.1 == some i)) base lists = true →
      lookupSymInLists tgt base lists = none
  | _, [], _ => rfl
  | base, syms :: rest, hc => by
    simp only [checkListIdxU, Bool.and_eq_true] at hc
    have hnone : lookup tgt syms = none := by
      apply lookup_none_of_not_mem_fst
      intro hmem
      obtain ⟨⟨s, off⟩, hp, rfl⟩ := List.mem_map.1 hmem
      have hall := List.all_eq_true.1 hc.1 (s, off) hp
      rw [beq_iff_eq] at hall
      rw [hb] at hall
      cases hall
    simp only [lookupSymInLists, hnone]
    exact lookupSymInLists_none_of_bucketNone hb (base + 1) rest hc.2

theorem ls_resolve_data_ultra {pl : MultiPlacement} {tgt : String}
    (h : (lsBucketLookup tgt).isNone = true) :
    libsignalSessionLib.resolve pl tgt = pl.ρ tgt := by
  have hb : lsBucketLookup tgt = none := Option.isNone_iff_eq_none.mp h
  have hc : checkListIdxU (fun i syms => syms.all (fun p => lsBucketLookup p.1 == some i))
      0 lsBlockSymsTree.toList = true := by
    rw [← checkTreeIdxU_eq_checkListIdxU _ lsBlockSymsTree_size 0]
    exact lsBlockSyms_bucket_sound
  have hlk : lookupBlockSym tgt libsignalSessionLib.blocks = none := by
    rw [lookupBlockSym_eq_lookupSymInLists, ← lsBlockSymsTree_toList]
    exact lookupSymInLists_none_of_bucketNone hb 0 _ hc
  simp [MultiPlacedLib.resolve, hlk]

noncomputable def checkBlockSymAtU (i : Nat) (tgt : String) : Bool :=
  (lsBucketLookup tgt == some i) &&
  match lsBlockSymsTree.get? i with
  | some syms => lookup tgt syms == some 0
  | none => false

private theorem lookupSymInLists_at_of_bucket {tgt : String} {i : Nat}
    {syms : List (String × Nat)}
    (hb : lsBucketLookup tgt = some i) :
    ∀ (base : Nat) (lists : List (List (String × Nat))),
      base ≤ i →
      lists[i - base]? = some syms →
      lookup tgt syms = some 0 →
      checkListIdxU (fun k s => s.all (fun p => lsBucketLookup p.1 == some k)) base lists = true →
      lookupSymInLists tgt base lists = some (i, 0)
  | _, [], _, hget, _, _ => by simp at hget
  | base, s0 :: rest, hle, hget, hlk, hc => by
    simp only [checkListIdxU, Bool.and_eq_true] at hc
    by_cases heq : i = base
    · subst heq
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [lookupSymInLists, hlk]
    · have hlt : base < i := by omega
      have hsub : i - base = (i - (base + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ] at hget
      have hnone : lookup tgt s0 = none := by
        apply lookup_none_of_not_mem_fst
        intro hmem
        obtain ⟨⟨s, off⟩, hp, rfl⟩ := List.mem_map.1 hmem
        have hall := List.all_eq_true.1 hc.1 (s, off) hp
        rw [beq_iff_eq, hb, Option.some.injEq] at hall
        omega
      simp only [lookupSymInLists, hnone]
      exact lookupSymInLists_at_of_bucket hb (base + 1) rest (by omega) hget hlk hc.2

theorem lookupBlockSym_of_checkBlockSymAtU {i : Nat} {tgt : String}
    (h : checkBlockSymAtU i tgt = true) :
    lookupBlockSym tgt libsignalSessionLib.blocks = some (i, 0) := by
  unfold checkBlockSymAtU at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases hg : lsBlockSymsTree.get? i with
  | none => simp [hg] at h
  | some syms =>
    simp only [hg, beq_iff_eq] at h
    have hget : lsBlockSymsTree.toList[i]? = some syms := by
      rw [← IdxTree.get?_eq_toList_getElem? lsBlockSymsTree_size i]
      exact hg
    have hc : checkListIdxU (fun k s => s.all (fun p => lsBucketLookup p.1 == some k))
        0 lsBlockSymsTree.toList = true := by
      rw [← checkTreeIdxU_eq_checkListIdxU _ lsBlockSymsTree_size 0]
      exact lsBlockSyms_bucket_sound
    rw [lookupBlockSym_eq_lookupSymInLists, ← lsBlockSymsTree_toList]
    exact lookupSymInLists_at_of_bucket (syms := syms) h.1 0 _ (Nat.zero_le i)
      (by simpa using hget) h.2 hc

theorem ls_resolve_block_ultra {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : checkBlockSymAtU i tgt = true) :
    libsignalSessionLib.resolve pl tgt = pl.base i := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_of_checkBlockSymAtU h]

theorem ls_fnAddr_block_ultra {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : checkBlockSymAtU i tgt = true) :
    libsignalSessionLib.fnAddr pl tgt = pl.base i := by
  simp [MultiPlacedLib.fnAddr, lookupBlockSym_of_checkBlockSymAtU h]

theorem lsProg_fnAddr_of_blockProg_ultra [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H] {tgt : String}
    (h : checkBlockSymAtU i tgt = true) :
    prog.fnAddr tgt = lsmpl.base i := by
  rw [hprog.eq_blockProgram]
  have h' := libsignalSessionLib_blockProgram_fnAddr (pl := lsmpl) (H := H)
    (lookupBlockSym_of_checkBlockSymAtU h)
  exact h'.1.trans h'.2

private meta partial def readLitListU (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``List.cons 3 then
    readLitListU (e.getArg! 2) (acc.push (e.getArg! 1))
  else
    acc

private meta def loadLsSymMetaU : CoreM (Std.HashMap String (Nat × Nat) × Std.HashSet String) := do
  let ci1 ← getConstInfo ``lsSymMetaLits
  let ci2 ← getConstInfo ``lsExtSymsLits
  let mut m : Std.HashMap String (Nat × Nat) := {}
  for tE in readLitListU ci1.value! do
    if let .lit (.strVal s) := tE.getArg! 2 then
      let jkE := tE.getArg! 3
      if let (.lit (.natVal j), .lit (.natVal k)) := (jkE.getArg! 2, jkE.getArg! 3) then
        m := m.insert s (j, k)
  let mut ext : Std.HashSet String := {}
  for sE in readLitListU ci2.value! do
    if let .lit (.strVal s) := sE then
      ext := ext.insert s
  return (m, ext)

private meta def evalIntLitU (e : Expr) : MetaM Int := do
  let r ← withTransparency .all (reduce e)
  if let some n ← evalNatExprU? r then return Int.ofNat n
  if r.isAppOfArity ``Int.ofNat 1 then
    if let some n ← evalNatExprU? (r.getArg! 0) then return Int.ofNat n
  if r.isAppOfArity ``Int.negSucc 1 then
    if let some n ← evalNatExprU? (r.getArg! 0) then return Int.negSucc n
  if r.isAppOfArity ``Neg.neg 3 then
    if let some n ← evalNatExprU? (r.getArg! 2) then return -Int.ofNat n
  throwError "gen_ls_blk_ultra: expected Int literal, got {r}"

private meta def sanitizeSymIdentU (s : String) : String :=
  String.ofList <| (s.toList.take 48).map fun c =>
    if c.isAlphanum then c else '_'

private meta def targetExprForRelocU (plE : Expr) (sym : String) (addend : Int) : Expr :=
  let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
  let base := mkApp2 (Lean.mkConst ``Placement.ρ) plE (mkStrLit sym)
  if addend == 0 then base
  else if addend > 0 then
    mkApp6 (Lean.mkConst ``HAdd.hAdd [.zero, .zero, .zero]) bv64 bv64 bv64
      (mkApp2 (Lean.mkConst ``instHAdd [.zero]) bv64 (mkApp (Lean.mkConst ``BitVec.instAdd) (mkNatLit 64)))
      base (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit addend.toNat))
  else
    mkApp6 (Lean.mkConst ``HSub.hSub [.zero, .zero, .zero]) bv64 bv64 bv64
      (mkApp2 (Lean.mkConst ``instHSub [.zero]) bv64 (mkApp (Lean.mkConst ``BitVec.instSub) (mkNatLit 64)))
      base (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit (-addend).toNat))

private meta partial def buildRelocTreeExprU (relocs : Array (Nat × Expr)) : Expr :=
  let emptyE := Lean.mkConst ``RelocTree.empty
  let leafFn := Lean.mkConst ``RelocTree.leaf
  let nodeFn := Lean.mkConst ``RelocTree.node
  let rec go (loIdx hiIdx : Nat) : Expr × Nat × Nat :=
    let len := hiIdx - loIdx
    if len == 0 then
      (emptyE, 0, 0)
    else if len == 1 then
      let (off, rE) := relocs[loIdx]!
      (mkApp leafFn rE, off, off)
    else
      let mid := loIdx + len / 2
      let (lE, llo, lhi) := go loIdx mid
      let (rE, rlo, rhi) := go mid hiIdx
      let lo := Nat.min llo rlo
      let hi := Nat.max lhi rhi
      (mkApp4 nodeFn (mkRawNatLit lo) (mkRawNatLit hi) lE rE, lo, hi)
  (go 0 relocs.size).1

private meta def wordAtLitProofU (textE treeE nE hcodeE hsizeE treeVal : Expr) (off : Nat) :
    MetaM (Nat × Expr × Expr) := do
  let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
  let w : Nat := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
  let bv8 (k : Nat) := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit k)
  let bv32Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)
  let wE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit w)
  let j := off / 4
  let quadE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[bv8 b0, ← mkAppM ``Prod.mk #[bv8 b1,
    ← mkAppM ``Prod.mk #[bv8 b2, bv8 b3]]]]
  let optQuadTy ← inferType quadE
  let hget := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optQuadTy quadE
  let p1 := mkAppN (Lean.mkConst ``wordAt_of_getQuad?)
    #[textE, treeE, nE, mkNatLit j, bv8 b0, bv8 b1, bv8 b2, bv8 b3, hcodeE, hsizeE, hget]
  let p2 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32Ty wE
  let hw ← mkEqTrans p1 p2
  return (w, wE, hw)

@[command_elab genLsBlkUltraStx]
meta def elabGenLsBlkUltra : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk_ultra $idxStx:num) => do
    elabCommand (← `(command| open ProofLib.ProgramReflection ProofLib.GenPlacedFetches))
    let idx := idxStx.getNat
    let currNs ← getCurrNamespace
    let blkLibId := mkIdent (Name.mkSimple s!"blkLib_{idx}")
    let fullBlkLibName := currNs ++ blkLibId.getId
    if (← getEnv).contains fullBlkLibName then
      return
    let isMutated := idx ∈ ([55, 72, 77, 79, 159, 202, 462, 519] : List Nat)
    let (blkRaw, blkReduced, codeLen, symNames, relocData, blockSymMap, extSymSet) ← liftTermElabM do
      let (blockSymMap, extSymSet) ← loadLsSymMetaU
      let some blkRaw ← lookupIdxTreeExprU (Lean.mkConst ``lsBlocksTree) idx
        | throwErrorAt idxStx "gen_ls_blk_ultra: block index {idx} out of bounds"
      let blkWhnf ← whnfAllU blkRaw
      let codeField := if blkWhnf.isAppOfArity ``CodeBlock.mk 6 then blkWhnf.getArg! 0
        else mkApp (Lean.mkConst ``CodeBlock.code) blkWhnf
      let alignVal ← match ← evalNatExprU? (mkApp (Lean.mkConst ``CodeBlock.align) blkWhnf) with
        | some a => pure a
        | none => throwError "gen_ls_blk_ultra: bad align"
      let codeBytes ← ProofLib.ProgramReflection.listElemsWhnf codeField
      let symElems ← ProofLib.ProgramReflection.listElemsWhnf (mkApp (Lean.mkConst ``CodeBlock.symbols) blkWhnf)
      let strTy := Lean.mkConst ``String
      let natTy := Lean.mkConst ``Nat
      let strNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
      let mut symNames : Array String := #[]
      let mut symLitElems : Array Expr := #[]
      for pE in symElems do
        let pE ← whnfAllU pE
        let s ← evalStrLitU (pE.getArg! 2)
        let some o ← evalNatExprU? (pE.getArg! 3) | throwError "gen_ls_blk_ultra: bad symbol offset"
        symNames := symNames.push s
        symLitElems := symLitElems.push (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natTy (mkStrLit s) (mkNatLit o))
      let symsLitE ← mkListLit strNatTy symLitElems.toList
      let relocElems ← ProofLib.ProgramReflection.listElemsWhnf (mkApp (Lean.mkConst ``CodeBlock.relocs) blkWhnf)
      let mut relocData : Array (Nat × Name × String × Int × Expr) := #[]
      let mut relocLitElems : Array Expr := #[]
      for rE in relocElems do
        let rE ← whnfAllU rE
        let off ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``RelocEntry.off) rE)
        let kE ← whnfAllU (mkApp (Lean.mkConst ``RelocEntry.kind) rE)
        let some kn := kE.constName? | throwError "gen_ls_blk_ultra: bad reloc kind {kE}"
        let sym ← evalStrLitU (mkApp (Lean.mkConst ``RelocEntry.sym) rE)
        let addend ← evalIntLitU (mkApp (Lean.mkConst ``RelocEntry.addend) rE)
        let locB ← whnfAllU (mkApp (Lean.mkConst ``RelocEntry.localSym) rE)
        let locBool := locB.isConstOf ``Bool.true
        let rLit := mkApp5 (Lean.mkConst ``RelocEntry.mk)
          (mkNatLit off) (Lean.mkConst kn) (mkStrLit sym) (toExpr addend) (toExpr locBool)
        relocData := relocData.push (off, kn, sym, addend, rLit)
        relocLitElems := relocLitElems.push rLit
      let relocsLitE ← mkListLit (Lean.mkConst ``RelocEntry) relocLitElems.toList
      let weakRefsField := if blkWhnf.isAppOfArity ``CodeBlock.mk 6 then blkWhnf.getArg! 5
        else mkApp (Lean.mkConst ``CodeBlock.weakRefs) blkWhnf
      let blkReduced := mkApp6 (Lean.mkConst ``CodeBlock.mk)
        codeField (mkNatLit alignVal) symsLitE relocsLitE (Lean.mkConst ``libsignalSessionExterns) weakRefsField
      return (blkRaw, blkReduced, codeBytes.size, symNames, relocData, blockSymMap, extSymSet)

    let nWords := codeLen / 4
    let maxOff := if nWords > 0 then (nWords - 1) * 4 else 0
    let blkLibEqId := mkIdent (Name.mkSimple s!"blkLib_eq_{idx}")
    let blkExternsEqId := mkIdent (Name.mkSimple s!"blkExterns_eq_{idx}")
    let blkPlId := mkIdent (Name.mkSimple s!"blkPl_{idx}")
    let blkPlaceableId := mkIdent (Name.mkSimple s!"blkPlaceable_{idx}")
    let blkPCId := mkIdent (Name.mkSimple s!"blkPC_{idx}")
    let lsProgId := mkIdent (Name.mkSimple s!"lsProg_{idx}")
    let instIsLsId := mkIdent (Name.mkSimple s!"instIsLsBlockProg_{idx}")
    let blkTextProgId := mkIdent (Name.mkSimple s!"blkTextProg_{idx}")
    let blkTreeId := mkIdent (Name.mkSimple s!"blkTree_{idx}")
    let blkCodeEqId := mkIdent (Name.mkSimple s!"blkCodeEq_{idx}")
    let blkTreeSizeId := mkIdent (Name.mkSimple s!"blkTreeSize_{idx}")
    let nWordsLit := Syntax.mkNumLit (toString nWords)
    let maxOffLit := Syntax.mkNumLit (toString maxOff)

    let fullBlkPlName := currNs ++ blkPlId.getId
    let fullBlkPlaceableName := currNs ++ blkPlaceableId.getId
    let fullBlkPCName := currNs ++ blkPCId.getId
    let fullBlkTreeName := currNs ++ blkTreeId.getId
    let fullBlkCodeEqName := currNs ++ blkCodeEqId.getId
    let fullBlkTreeSizeName := currNs ++ blkTreeSizeId.getId

    liftTermElabM do
      let val := mkApp4 (Lean.mkConst ``PlacedLib.mk)
        (mkStrLit "libsignalSession")
        blkReduced
        (Lean.mkConst ``libsignalSessionData)
        (mkApp (Lean.mkConst ``MultiPlacedLib.exports) (Lean.mkConst ``libsignalSessionMultiLib))
      withExporting <| addAndCompile (.defnDecl {
        name := fullBlkLibName, levelParams := [], type := Lean.mkConst ``PlacedLib,
        value := val, hints := .regular 0, safety := .safe
      })
      let libE := Lean.mkConst fullBlkLibName
      let optBlkTy := mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``CodeBlock)
      let someBlkRaw := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``CodeBlock) blkRaw
      let hgetE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optBlkTy someBlkRaw
      let hlibE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``PlacedLib) libE
      let eqPrf := mkAppN (Lean.mkConst ``blockLib_eq_of_lsBlocksTreeU)
        #[libE, mkNatLit idx, blkRaw, hgetE, hlibE]
      let eqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (Lean.mkConst ``PlacedLib)
        libE (mkApp2 (Lean.mkConst ``MultiPlacedLib.blockLib) (Lean.mkConst ``libsignalSessionLib) (mkNatLit idx))
      addDecl (.thmDecl {
        name := currNs ++ blkLibEqId.getId, levelParams := [], type := eqTy, value := eqPrf
      })

    elabCommand (← `(command|
      theorem $blkExternsEqId:ident : ($blkLibId:ident).text.externs = libsignalSessionExterns := rfl
    ))
    let blkPlRhoId := mkIdent (Name.mkSimple s!"blkPl_{idx}_ρ")
    if isMutated then
      elabCommand (← `(command|
        abbrev $blkPlId:ident [LibsignalFullPlacement] : Placement :=
          libsignalSessionLib.blockPlacement lsmpl $idxStx:num
      ))
      elabCommand (← `(command|
        @[simp, arm64_norm, wp_norm]
        theorem $blkPlRhoId:ident [LibsignalFullPlacement] (sym : String) :
            ($blkPlId:ident).ρ sym = libsignalSessionLib.resolve lsmpl sym := rfl
      ))
      elabCommand (← `(command|
        theorem $blkPlaceableId:ident [LibsignalFullPlacement] : ($blkLibId:ident).Placeable $blkPlId:ident :=
          Eq.mp (congrArg (PlacedLib.Placeable · $blkPlId:ident) ($blkLibEqId:ident).symm)
            (full_block_placeable $idxStx:num (by decide))
      ))
      elabCommand (← `(command|
        noncomputable def $blkPCId:ident [LibsignalFullPlacement] : Program :=
          ($blkLibId:ident).program $blkPlId:ident
      ))
      elabCommand (← `(command|
        noncomputable abbrev $lsProgId:ident [LibsignalFullPlacement] (H : LibsignalHooks) : Program :=
          ($blkPCId:ident).rebase ($blkPlId:ident).base H
      ))
      elabCommand (← `(command|
        instance $instIsLsId:ident [LibsignalFullPlacement] (H : LibsignalHooks) :
            IsLsBlockProg (($blkPCId:ident).rebase ($blkPlId:ident).base H) $idxStx:num H where
          eq_blockProgram := prog_eq_blockProgram $blkLibEqId:ident
          externs_eq := Eq.trans (congrArg (fun b : PlacedLib => b.text.externs) ($blkLibEqId:ident).symm) $blkExternsEqId:ident
      ))
    else
      elabCommand (← `(command|
        abbrev $blkPlId:ident [LibsignalPlacement] : Placement :=
          libsignalSessionLib.blockPlacement lsmpl $idxStx:num
      ))
      elabCommand (← `(command|
        @[simp, arm64_norm, wp_norm]
        theorem $blkPlRhoId:ident [LibsignalPlacement] (sym : String) :
            ($blkPlId:ident).ρ sym = libsignalSessionLib.resolve lsmpl sym := rfl
      ))
      elabCommand (← `(command|
        theorem $blkPlaceableId:ident [LibsignalPlacement] : ($blkLibId:ident).Placeable $blkPlId:ident :=
          Eq.mp (congrArg (PlacedLib.Placeable · $blkPlId:ident) ($blkLibEqId:ident).symm)
            (LibsignalPlacement.block_placeable $idxStx:num (by decide) (by decide))
      ))
      elabCommand (← `(command|
        noncomputable def $blkPCId:ident [LibsignalPlacement] : Program :=
          ($blkLibId:ident).program $blkPlId:ident
      ))
      elabCommand (← `(command|
        noncomputable abbrev $lsProgId:ident [LibsignalPlacement] (H : LibsignalHooks) : Program :=
          ($blkPCId:ident).rebase ($blkPlId:ident).base H
      ))
      elabCommand (← `(command|
        instance $instIsLsId:ident [LibsignalPlacement] (H : LibsignalHooks) :
            IsLsBlockProg (($blkPCId:ident).rebase ($blkPlId:ident).base H) $idxStx:num H where
          eq_blockProgram := prog_eq_blockProgram $blkLibEqId:ident
          externs_eq := Eq.trans (congrArg (fun b : PlacedLib => b.text.externs) ($blkLibEqId:ident).symm) $blkExternsEqId:ident
      ))

    -- Pre-emit shared RelocTree so both `gen_placed_fetches` and ADRP/`:lo12:` share $O(\log R)$ lookups
    let shRtNm := fullBlkPCName ++ `_gpf_shared_relocTree
    let shRtEqNm := fullBlkPCName ++ `_gpf_shared_relocTree_eq
    let shRtWfNm := fullBlkPCName ++ `_gpf_shared_relocTree_wf
    liftTermElabM do
      let libE := Lean.mkConst fullBlkLibName
      let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
      let rtVal := buildRelocTreeExprU (relocData.map fun (off, _, _, _, rE) => (off, rE))
      withExporting <| addDecl (.defnDecl {
        name := shRtNm, levelParams := [], type := Lean.mkConst ``RelocTree, value := rtVal,
        hints := .abbrev, safety := .safe
      })
      let shRtE := Lean.mkConst shRtNm
      let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``RelocEntry)
      let lhsEq := mkApp (Lean.mkConst ``CodeBlock.relocs) textE
      let rhsEq := mkApp (Lean.mkConst ``RelocTree.toList) shRtE
      let eqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) listTy lhsEq rhsEq
      let eqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) listTy lhsEq
      addDecl (.thmDecl { name := shRtEqNm, levelParams := [], type := eqTy, value := eqVal })
      let boolTy := Lean.mkConst ``Bool
      let trueE := Lean.mkConst ``Bool.true
      let wfTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) boolTy (mkApp (Lean.mkConst ``RelocTree.wf) shRtE) trueE
      let wfVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy trueE
      addDecl (.thmDecl { name := shRtWfNm, levelParams := [], type := wfTy, value := wfVal })

    let mut symIdx : Nat := 0
    for sym in symNames do
      let suffix := if symIdx == 0 then "" else s!"_{symIdx}"
      symIdx := symIdx + 1
      let fnOffId := mkIdent (Name.mkSimple s!"blkPC_{idx}_fnOff_0x0{suffix}")
      let fullFnOffName := currNs ++ fnOffId.getId
      let symLit := Syntax.mkStrLit sym
      if isMutated then
        elabCommand (← `(command|
          @[simp, arm64_norm]
          theorem $fnOffId:ident [LibsignalFullPlacement] : ($blkPCId:ident).fnOff $symLit:str = 0 := rfl
        ))
      else
        elabCommand (← `(command|
          @[simp, arm64_norm]
          theorem $fnOffId:ident [LibsignalPlacement] : ($blkPCId:ident).fnOff $symLit:str = 0 := rfl
        ))
      modifyEnv fun env => fnEntryExt.addEntry env {
        sym := sym, codeConst := fullBlkPCName, decPrefix := fullBlkPCName,
        fnOffLemma := fullFnOffName, off := 0, sizeBytes := 0, placed := true }

    if nWords > 0 then
      elabCommand (← `(command|
        def $blkTextProgId:ident : Program := { code := ($blkLibId:ident).text.code }
      ))
      elabCommand (← `(command|
        def $blkTreeId:ident : WordTree := word_tree_of% $blkTextProgId:ident
      ))
      elabCommand (← `(command|
        theorem $blkCodeEqId:ident : ($blkLibId:ident).text.code = ($blkTreeId:ident).toBytes := rfl
      ))
      elabCommand (← `(command|
        theorem $blkTreeSizeId:ident : ($blkTreeId:ident).checkSize? = some $nWordsLit:num := by decide +kernel
      ))
      elabCommand (← `(command|
        gen_placed_fetches $blkPCId:ident $blkLibId:ident $blkTreeId:ident $blkCodeEqId:ident $blkTreeSizeId:ident
          via_placement $blkPlId:ident $blkPlaceableId:ident [0 → $maxOffLit:num]
      ))

    let mut relocByOff : Std.HashMap Nat (Name × String × Int × Expr) := {}
    for (o, kn, s, a, rE) in relocData do
      if !relocByOff.contains o then
        relocByOff := relocByOff.insert o (kn, s, a, rE)

    let relaxableAddKind (kn : Name) : Bool :=
      kn == ``RelocKind.addLo12

    let isRelaxableAt (off : Nat) (kn : Name) (sym : String) (addend : Int) : Bool :=
      if kn != ``RelocKind.adrpHi21 then false
      else
        match relocByOff.get? (off + 4) with
        | some (kn2, sym2, add2, _) =>
          relaxableAddKind kn2 && sym == sym2 && addend == add2
        | none => false

    let ldstScale? (kn : Name) : Option Nat :=
      if kn == ``RelocKind.ldst8Lo12 then some 0
      else if kn == ``RelocKind.ldst16Lo12 then some 1
      else if kn == ``RelocKind.ldst32Lo12 then some 2
      else if kn == ``RelocKind.ldst64Lo12 then some 3
      else none

    if nWords > 0 then
      liftTermElabM do
        let paramTy := if isMutated then Lean.mkConst ``LibsignalFullPlacement else Lean.mkConst ``LibsignalPlacement
        let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
        let bv32 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)
        let bv5 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 5)
        let natTy := Lean.mkConst ``Nat
        let boolTy := Lean.mkConst ``Bool
        let optRelTy := mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry)
        let progFn := Lean.mkConst fullBlkPCName
        let plFn := Lean.mkConst fullBlkPlName
        let placeableFn := Lean.mkConst fullBlkPlaceableName
        let libE := Lean.mkConst fullBlkLibName
        let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
        let treeE := Lean.mkConst fullBlkTreeName
        let codeEqE := Lean.mkConst fullBlkCodeEqName
        let sizeEqE := Lean.mkConst fullBlkTreeSizeName
        let rtE := Lean.mkConst shRtNm
        let hrelocsE := Lean.mkConst shRtEqNm
        let hwfE := Lean.mkConst shRtWfNm
        let nWordsE := mkNatLit nWords
        let hprogE := Expr.lam `a paramTy
          (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Program)
            (mkApp progFn (.bvar 0))) .instImplicit

        let mkRelocSomePrf (offE rE : Expr) : Expr :=
          let someRE := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE
          let hlk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optRelTy someRE
          mkAppN (Lean.mkConst ``relocAt?_of_tree) #[textE, rtE, offE, someRE, hrelocsE, hwfE, hlk]

        let mkRelocNonePrf (offE : Expr) : Expr :=
          let noneRE := mkApp (Lean.mkConst ``Option.none [.zero]) (Lean.mkConst ``RelocEntry)
          let hlk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optRelTy noneRE
          mkAppN (Lean.mkConst ``relocAt?_of_tree) #[textE, rtE, offE, noneRE, hrelocsE, hwfE, hlk]

        let treeVal ← ProofLib.GenDecodes.treeValueOf fullBlkTreeName
        for (off, kn, sym, addend, rE) in relocData do
          let offHex := String.ofList (Nat.toDigits 16 off)
          if kn == ``RelocKind.adrpHi21 && !isRelaxableAt off kn sym addend then
            let thmName := currNs ++ Name.mkSimple s!"blkPC_{idx}_pairStep_0x{offHex}"
            let offE := mkNatLit off
            let off4E := mkNatLit (off + 4)
            let (w, wE, hwdE) ← wordAtLitProofU textE treeE nWordsE codeEqE sizeEqE treeVal off
            let rd := w % 32
            let rdE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rd)
            let tLam := Expr.lam `a paramTy (targetExprForRelocU (mkApp plFn (.bvar 0)) sym addend) .instImplicit
            let hltTy := mkApp4 (Lean.mkConst ``LT.lt [.zero]) natTy (Lean.mkConst ``instLTNat)
              offE (mkNatMul (mkNatLit 4) nWordsE)
            let hltE ← mkDecideProof hltTy
            let hrE := mkRelocSomePrf offE rE
            let hkE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``RelocKind)
              (Lean.mkConst ``RelocKind.adrpHi21)
            let hnrelE ← match relocByOff.get? (off + 4) with
              | none =>
                pure <| mkAppN (Lean.mkConst ``relaxableAt_false_of_next_none)
                  #[textE, offE, mkRelocNonePrf off4E]
              | some (kn2, _, _, r2E) =>
                let hr2E := mkRelocSomePrf off4E r2E
                if kn2 != ``RelocKind.addLo12 then
                  let hkFalse := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
                  pure <| mkAppN (Lean.mkConst ``relaxableAt_false_of_next_notAddLo12)
                    #[textE, offE, r2E, hr2E, hkFalse]
                else
                  let (_, w1E, hwd1E) ← wordAtLitProofU textE treeE nWordsE codeEqE sizeEqE treeVal (off + 4)
                  let hfFalse := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
                  pure <| mkAppN (Lean.mkConst ``relaxableAt_false_of_relocs_words)
                    #[textE, offE, rE, r2E, wE, w1E, hrE, hr2E, hwdE, hwd1E, hfFalse]
            let hwE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32
              (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x90000000))
            let hrdE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv5 rdE
            let hrd31Ty := mkApp (Lean.mkConst ``Not)
              (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv5 rdE
                (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit 31)))
            let hrd31E ← mkDecideProof hrd31Ty
            let plTy := Lean.mkConst ``Placement
            let hPlTargetTy := Expr.forallE `pl plTy
              (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
                (mkApp3 (Lean.mkConst ``CodeBlock.target) textE (.bvar 0) rE)
                (targetExprForRelocU (.bvar 0) sym addend)) .default
            let hPlTarget := Expr.lam `pl plTy
              (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                (targetExprForRelocU (.bvar 0) sym addend)) .default
            let hPlTargetChecked ← mkExpectedTypeHint hPlTarget hPlTargetTy
            let hTE := Expr.lam `a paramTy
              (mkApp hPlTargetChecked (mkApp plFn (.bvar 0))) .instImplicit
            let h4E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy off4E
            let prf := mkAppN (Lean.mkConst ``sepWP_rebase_adrpPlain_of_tree [.succ .zero])
              #[paramTy, progFn, plFn, libE, treeE, nWordsE, offE, off4E, rE, rdE, tLam, wE,
                hprogE, placeableFn, codeEqE, sizeEqE, hltE, hrE, hkE, hnrelE, hwdE, hwE, hrdE,
                hrd31E, hTE, h4E]
            let ty ← inferType prf
            ProofLib.GenDecodes.addThm thmName ty prf

          if let some scale := ldstScale? kn then
            let prevRelax :=
              if off < 4 then false
              else
                match relocByOff.get? (off - 4) with
                | some (kn0, s0, a0, _) => isRelaxableAt (off - 4) kn0 s0 a0
                | none => false
            if !prevRelax then
              let thmName := currNs ++ Name.mkSimple s!"blkPC_{idx}_rebase_fetch_0x{offHex}"
              let offE := mkNatLit off
              let scaleE := mkNatLit scale
              let (w, wE, hwdE) ← wordAtLitProofU textE treeE nWordsE codeEqE sizeEqE treeVal off
              let opc := (w >>> 22) % 4
              let rt := w % 32
              let rn := (w >>> 5) % 32
              let opcE := mkNatLit opc
              let rtE := if rt == 31 then Lean.mkConst ``Reg.xzr
                else mkApp (Lean.mkConst ``Reg.gpr) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rt))
              let rnE := if rn == 31 then Lean.mkConst ``Reg.sp
                else mkApp (Lean.mkConst ``Reg.gpr) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rn))
              let tLam := Expr.lam `a paramTy (targetExprForRelocU (mkApp plFn (.bvar 0)) sym addend) .instImplicit
              let instOfT ← withLocalDeclD `t bv64 fun tFVar => do
                let addrT := mkApp2 (Lean.mkConst ``AddrMode.Offset) rnE (mkApp (Lean.mkConst ``lo12Of) tFVar)
                let someInstT ← whnfAllU (mkApp4 (Lean.mkConst ``mkLoadStoreInst) scaleE opcE rtE addrT)
                let instT := someInstT.getArg! 1
                mkLambdaFVars #[tFVar] instT
              let instLam := Expr.lam `a paramTy
                (instOfT.beta #[targetExprForRelocU (mkApp plFn (.bvar 0)) sym addend]) .instImplicit
              let hltTy := mkApp4 (Lean.mkConst ``LT.lt [.zero]) natTy (Lean.mkConst ``instLTNat)
                offE (mkNatMul (mkNatLit 4) nWordsE)
              let hltE ← mkDecideProof hltTy
              let hrE := mkRelocSomePrf offE rE
              let hkE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                (mkApp (Lean.mkConst ``Option [.zero]) natTy)
                (mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy scaleE)
              let hscaleE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy scaleE
              let hw1E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32
                (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x39000000))
              let hw2E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
              let plTy := Lean.mkConst ``Placement
              let hPlTargetTy := Expr.forallE `pl plTy
                (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
                  (mkApp3 (Lean.mkConst ``CodeBlock.target) textE (.bvar 0) rE)
                  (targetExprForRelocU (.bvar 0) sym addend)) .default
              let hPlTarget := Expr.lam `pl plTy
                (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                  (targetExprForRelocU (.bvar 0) sym addend)) .default
              let hPlTargetChecked ← mkExpectedTypeHint hPlTarget hPlTargetTy
              let hTE := Expr.lam `a paramTy
                (mkApp hPlTargetChecked (mkApp plFn (.bvar 0))) .instImplicit
              let hInstOfT ← withLocalDeclD `t bv64 fun tFVar => do
                let instT := instOfT.beta #[tFVar]
                let someInstT := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``Instr) instT
                let lhsT := mkApp4 (Lean.mkConst ``mkLoadStoreInst) scaleE
                  (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 2)
                    (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 22) (mkNatLit 2) wE))
                  (mkApp (Lean.mkConst ``Reg.fromZRBits)
                    (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 0) (mkNatLit 5) wE))
                  (mkApp2 (Lean.mkConst ``AddrMode.Offset)
                    (mkApp (Lean.mkConst ``Reg.fromSPBits)
                      (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 5) (mkNatLit 5) wE))
                    (mkApp (Lean.mkConst ``lo12Of) tFVar))
                let eqTyT := mkApp3 (Lean.mkConst ``Eq [.succ .zero])
                  (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``Instr)) lhsT someInstT
                let eqPrfT := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                  (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``Instr)) someInstT
                let checkedT ← mkExpectedTypeHint eqPrfT eqTyT
                mkLambdaFVars #[tFVar] checkedT
              let hinstE := Expr.lam `a paramTy
                (mkApp hInstOfT (targetExprForRelocU (mkApp plFn (.bvar 0)) sym addend)) .instImplicit
              let prf := mkAppN (Lean.mkConst ``fetch_rebase_ldstLo12_of_tree [.succ .zero])
                #[paramTy, progFn, plFn, libE, treeE, nWordsE, offE, rE, scaleE, tLam, instLam, wE,
                  hprogE, placeableFn, codeEqE, sizeEqE, hltE, hrE, hkE, hwdE, hscaleE, hw1E, hw2E,
                  hTE, hinstE]
              let ty ← inferType prf
              ProofLib.GenDecodes.addThm thmName ty prf
              Term.applyAttributes thmName #[{ name := `simp }, { name := `arm64_norm }]

    let mut ownSymIdx : Nat := 0
    for sym in symNames do
      let suffix := if ownSymIdx == 0 then "" else s!"_{ownSymIdx}"
      ownSymIdx := ownSymIdx + 1
      let resShort := Name.mkSimple s!"ls_resolve_blk_{idx}{suffix}"
      let fnShort := Name.mkSimple s!"ls_fnAddr_blk_{idx}{suffix}"
      let progFnShort := Name.mkSimple s!"ls_blockProgram_fnAddr_blk_{idx}{suffix}"
      let symLit := Syntax.mkStrLit sym
      let env ← getEnv
      if !env.contains (currNs ++ resShort) then
        let resId := mkIdent resShort
        elabCommand (← `(command|
          @[simp, arm64_norm, wp_norm]
          theorem $resId:ident (pl : MultiPlacement) :
              libsignalSessionLib.resolve pl $symLit:str = pl.base $idxStx:num :=
            ls_resolve_block_ultra (by decide +kernel)
        ))
      if !env.contains (currNs ++ fnShort) then
        let fnId := mkIdent fnShort
        elabCommand (← `(command|
          @[simp, arm64_norm, wp_norm]
          theorem $fnId:ident (pl : MultiPlacement) :
              libsignalSessionLib.fnAddr pl $symLit:str = pl.base $idxStx:num :=
            ls_fnAddr_block_ultra (by decide +kernel)
        ))
      if !env.contains (currNs ++ progFnShort) then
        let progFnId := mkIdent progFnShort
        if isMutated then
          elabCommand (← `(command|
            @[simp, arm64_norm, wp_norm]
            theorem $progFnId:ident [LibsignalFullPlacement] (H : LibsignalHooks) :
                (($blkPCId:ident).rebase ($blkPlId:ident).base H).fnAddr $symLit:str = lsmpl.base $idxStx:num :=
              lsProg_fnAddr_of_blockProg_ultra (by decide +kernel)
          ))
        else
          elabCommand (← `(command|
            @[simp, arm64_norm, wp_norm]
            theorem $progFnId:ident [LibsignalPlacement] (H : LibsignalHooks) :
                (($blkPCId:ident).rebase ($blkPlId:ident).base H).fnAddr $symLit:str = lsmpl.base $idxStx:num :=
              lsProg_fnAddr_of_blockProg_ultra (by decide +kernel)
          ))

    let mut seenRelSyms : Std.HashSet String := extSymSet
    seenRelSyms := seenRelSyms.insert "log::MAX_LOG_LEVEL_FILTER"
    seenRelSyms := seenRelSyms.insert "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_STORAGE"
    seenRelSyms := seenRelSyms.insert "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_ONCE"
    seenRelSyms := seenRelSyms.insert "curve25519_dalek::constants::ED25519_BASEPOINT_TABLE"
    for (_, _, rsym, _, _) in relocData do
      if !seenRelSyms.contains rsym then
        seenRelSyms := seenRelSyms.insert rsym
        let symLit := Syntax.mkStrLit rsym
        match blockSymMap.get? rsym with
        | some (j, rSymIdx) =>
          let suffix := if rSymIdx == 0 then "" else s!"_{rSymIdx}"
          let canonRes := Name.mkSimple s!"ls_resolve_blk_{j}{suffix}"
          let canonFn := Name.mkSimple s!"ls_fnAddr_blk_{j}{suffix}"
          let resShort := Name.mkSimple s!"ls_resolve_rel_{idx}_blk_{j}{suffix}"
          let fnShort := Name.mkSimple s!"ls_fnAddr_rel_{idx}_blk_{j}{suffix}"
          let jLit := Syntax.mkNumLit (toString j)
          let env ← getEnv
          if !env.contains (currNs ++ canonRes) && !env.contains (currNs ++ resShort) then
            let resId := mkIdent resShort
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $resId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.resolve pl $symLit:str = pl.base $jLit:num :=
                ls_resolve_block_ultra (by decide +kernel)
            ))
          if !env.contains (currNs ++ canonFn) && !env.contains (currNs ++ fnShort) then
            let fnId := mkIdent fnShort
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $fnId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.fnAddr pl $symLit:str = pl.base $jLit:num :=
                ls_fnAddr_block_ultra (by decide +kernel)
            ))
        | none =>
          let hash := UInt64.toNat (Hashable.hash rsym)
          let resShort := Name.mkSimple s!"ls_resolve_rel_{idx}_dat_{sanitizeSymIdentU rsym}_{hash}"
          let env ← getEnv
          if !env.contains (currNs ++ resShort) then
            let resId := mkIdent resShort
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $resId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.resolve pl $symLit:str = pl.ρ $symLit:str :=
                ls_resolve_data_ultra (by decide +kernel)
            ))

    liftTermElabM do
      setIrreducibleAttribute fullBlkPCName
  | _ => throwUnsupportedSyntax

end MetaGenLsBlkUltra

end CryptoVerification
