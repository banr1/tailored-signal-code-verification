/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public meta import LibsignalBinary.Proofs.Placed.PlacedCallSym -- shake: keep
public meta import ProofLib.GenPlacedFetches -- shake: keep
import LibsignalBinary.Proofs.Placed.BridgeReloc
import ProofLib.GenPlacedFetches
import ProofLib.Placed.Multi
public meta import ProofLib.ProgramReflection -- shake: keep
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.Bridge -- shake: keep
public meta import ProofLib.GenDecodes -- shake: keep

/-!
# Tree-Indexed Per-Block Fetch and Relocation Elaborator

Defines the `gen_ls_blk <idx>`, `gen_ls_blk_shard <tag> <idx>`, and `gen_ls_blk_base <idx>` command
elaborators, emitting per-block `PlacedLib` instances, `RelocTree` and `WordTree` fetch lemmas,
plain `ADRP`/`:lo12:` steppers, and reflected symbol-resolution rules in $O(\log N)$ kernel steps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

abbrev lsLogFilterSym : String := "_RNvCs4Dv7yoBiUx4_3log20MAX_LOG_LEVEL_FILTER"
abbrev lsBlackBoxU8Sym : String := "_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek"

abbrev lsLogFilterAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ lsLogFilterSym

/-- Wrap a spec with `⌜LibsignalCodeLoaded pl ·.mem⌝` in both precondition and postcondition
    so `wp_apply` automatically discharges `LibsignalCodeLoaded` before a cross-block call and
    extracts `LibsignalCodeLoaded pl sf.mem` into the local context after the call. -/
abbrev withLsCl {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝
    post := fun x s0 sf => ⌜LibsignalCodeLoaded pl sf.mem⌝ ∗ spec.post x s0 sf }

theorem ls_subroutine_ok_cl_of_block [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [hbj : LsBlockBound bj]
    (_hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcl0 j (Nat.lt_of_lt_of_le hj hbj.le_blocks) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hclf : LibsignalCodeLoaded lsmpl sf.mem := hcl0.of_keepsFrozen hstepsQ.keepsFrozen
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  refine reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

theorem ls_subroutine_ok_cl_of_plain [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hi hj hj_unmut

/-- Step up to a cross-block call target `mid` while threading `LibsignalCodeLoaded lsmpl ·.mem`
    across any intervening memory stores (`STR`/`STP`). -/
macro "wp_steps_lscl " mid:term : tactic =>
  `(tactic| (
    apply sepWP_seq_lscl ‹_› (mid := $mid)
    wp_steps
    apply SepWP.done
    · first | wp_norm_lhs | rfl
    · wp_norm_lhs
    intro _hcl_call))

-- 624 = libsignalSessionLib.blocks.length (libsignalSessionLib_blocks_length)
theorem full_block_placeable [LibsignalFullPlacement] (i : Nat) (hi : i < 624) :
    (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement lsmpl i) :=
  MultiPlacedLib.placeable_blockLib
    (by rw [libsignalSessionLib_blocks_length]; omega)
    LibsignalFullPlacement.placeable

syntax (name := genLsBlkStx) "gen_ls_blk " num : command

section MetaGenLsBlk

open Lean Meta Elab Term Command Tactic

private meta partial def mkIdxTreeExprGls (ty : Expr) (elems : Array Expr) (lo hi : Nat) : Expr :=
  if _h : lo < hi then
    if hi - lo == 1 then
      mkApp2 (Lean.mkConst ``IdxTree.leaf) ty elems[lo]!
    else
      let mid := (lo + hi) / 2
      let l := mkIdxTreeExprGls ty elems lo mid
      let r := mkIdxTreeExprGls ty elems mid hi
      mkApp4 (Lean.mkConst ``IdxTree.node) ty (mkNatLit (mid - lo)) l r
  else
    mkApp (Lean.mkConst ``IdxTree.empty) ty

elab "blocks_idx_tree_of% " listStx:term:max : term => do
  let listE ← elabTerm listStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  return mkIdxTreeExprGls (Lean.mkConst ``CodeBlock) elems 0 elems.size

set_option maxHeartbeats 0 in
/-- Balanced binary tree of the 624 `CodeBlock` entries of `libsignalSessionBlocks`, precomputed
    once in `GenLsBlock.olean` so `gen_ls_blk <idx>` looks up block `<idx>` in $O(\log 624) = 10$
    tree steps without unfolding the other 622 blocks. -/
noncomputable def lsBlocksTree : IdxTree CodeBlock :=
  blocks_idx_tree_of% libsignalSessionBlocks

private theorem lsBlocksTree_toList : lsBlocksTree.toList = libsignalSessionLib.blocks := by
  rfl_kernel

private theorem lsBlocksTree_size : lsBlocksTree.size? = some 624 := by
  decide +kernel

theorem blockLib_eq_of_lsBlocksTree {lib : PlacedLib} {i : Nat} {blk : CodeBlock}
    (hget : lsBlocksTree.getFast? i = some blk)
    (hlib : lib = { name := "libsignalSession", text := blk, data := libsignalSessionData,
                    exports := libsignalSessionMultiLib.exports }) :
    lib = libsignalSessionLib.blockLib i := by
  subst hlib
  have hg0 : lsBlocksTree.get? i = some blk :=
    (IdxTree.getFast?_eq_get? lsBlocksTree i).symm.trans hget
  have h1 : libsignalSessionLib.blocks[i]? = some blk :=
    (congrArg (·[i]?) lsBlocksTree_toList.symm).trans
      ((IdxTree.get?_eq_toList_getElem? lsBlocksTree_size i).symm.trans hg0)
  unfold MultiPlacedLib.blockLib
  change PlacedLib.mk "libsignalSession" blk _ _ =
    PlacedLib.mk libsignalSessionLib.name (libsignalSessionLib.blocks.getD i { code := [] })
      libsignalSessionLib.data libsignalSessionLib.exports
  have hgetD : libsignalSessionLib.blocks.getD i { code := [] } = blk := by
    rw [List.getD_eq_getElem?_getD, h1]; rfl
  rw [hgetD]
  rfl

theorem relaxableAt_false_of_next_none {blk : CodeBlock} {off : Nat}
    (h2 : blk.relocAt? (off + 4) = none) :
    blk.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt
  rw [h2]
  cases blk.relocAt? off <;> rfl

theorem relaxableAt_false_of_next_notAddLo12 {blk : CodeBlock} {off : Nat} {r2 : RelocEntry}
    (h2 : blk.relocAt? (off + 4) = some r2)
    (hk : (r2.kind == .addLo12) = false) :
    blk.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt
  rw [h2]
  cases blk.relocAt? off with
  | none => rfl
  | some r1 => simp [hk]

theorem relaxableAt_false_of_relocs_words {blk : CodeBlock} {off : Nat} {r1 r2 : RelocEntry}
    {w0 w1 : BitVec 32}
    (h1 : blk.relocAt? off = some r1) (h2 : blk.relocAt? (off + 4) = some r2)
    (hw0 : blk.wordAt off = w0) (hw1 : blk.wordAt (off + 4) = w1)
    (hf : (r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.sym == r2.sym &&
      r1.addend == r2.addend && isAdrpWord w0 && isAddImm64Word w1 &&
      (w0 &&& 0x1f#32) == (w1 &&& 0x1f#32) && ((w1 >>> 5) &&& 0x1f#32) == (w0 &&& 0x1f#32) &&
      (w0 &&& 0x1f#32) != 0x1f#32) = false) :
    blk.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt
  rw [h1, h2, hw0, hw1]
  exact hf

private theorem find?_toStringSymbols_eq_of_lookupCharSym {cs : List Char} {off : Nat} :
    ∀ (charSyms : List (List Char × Nat)),
      lookupCharSym cs charSyms = some off →
      (toStringSymbols charSyms).find? (fun p => p.1 == String.ofList cs) =
        some (String.ofList cs, off)
  | [], h => by cases h
  | (s, o) :: rest, h => by
    simp only [lookupCharSym] at h
    cases hb : charListBeq s cs with
    | true =>
      simp only [hb, ↓reduceIte, Option.some.injEq] at h
      have hs : s = cs := charListBeq_iff_eq.mp hb
      subst hs; subst h
      simp [toStringSymbols]
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      have hne : (String.ofList s == String.ofList cs) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        have hcs : s = cs := by simpa using congrArg String.toList heq
        exact Bool.false_ne_true (hb ▸ charListBeq_iff_eq.mpr hcs)
      simp only [toStringSymbols, List.find?_cons, hne]
      exact find?_toStringSymbols_eq_of_lookupCharSym rest h

theorem placed_fnOff_of_lookupCharSym {α : Sort _} {P : α → Program}
    {charSyms : List (List Char × Nat)}
    (hsyms : ∀ a, (P a).symbols = toStringSymbols charSyms)
    {name : String} {cs : List Char} {off : Nat}
    (hname : name = String.ofList cs)
    (hlk : lookupCharSym cs charSyms = some off)
    (a : α) :
    (P a).fnOff name = off := by
  subst hname
  simp only [Program.fnOff, Program.findSymbol?, hsyms a,
    find?_toStringSymbols_eq_of_lookupCharSym charSyms hlk,
    Option.orElse, Option.map, Option.getD]

private meta def evalStrLitGls (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let r ← whnfAll e
  match r with
  | .lit (.strVal s) => return s
  | _ =>
    let r2 ← withTransparency .all (reduce e)
    match r2 with
    | .lit (.strVal s) => return s
    | _ => throwError "gen_ls_blk: expected string literal, got {r2}"

private meta def evalNatExprGls? (e : Expr) : MetaM (Option Nat) := do
  if let .lit (.natVal n) := e then return some n
  let r ← whnfAll e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

private meta partial def lookupIdxTreeExpr (treeE : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let r ← whnfAll treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return none
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    if idx == 0 then return some (r.getArg! 1) else return none
  else if r.isAppOfArity ``IdxTree.node 4 then
    let some leftSz ← evalNatExprGls? (r.getArg! 1)
      | throwError "gen_ls_blk: invalid leftSz in IdxTree.node"
    if idx < leftSz then
      lookupIdxTreeExpr (r.getArg! 2) idx
    else
      lookupIdxTreeExpr (r.getArg! 3) (idx - leftSz)
  else
    throwError "gen_ls_blk: unexpected IdxTree expression {r}"

private meta partial def collectSymIdxTreeEntries (treeE : Expr)
    (acc : Array (String × Nat × Nat))
    (seen : Std.HashSet String)
    (counts : Std.HashMap Nat Nat) :
    MetaM (Array (String × Nat × Nat) × Std.HashSet String × Std.HashMap Nat Nat) := do
  let r ← whnfAll treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return (acc, seen, counts)
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    let pE ← whnfAll (r.getArg! 1)
    let s ← evalStrLitGls (pE.getArg! 2)
    let some j ← evalNatExprGls? (pE.getArg! 3)
      | throwError "gen_ls_blk: invalid block index in lsBlockSymIdxTree"
    if seen.contains s then
      return (acc, seen, counts)
    else
      let k := counts.getD j 0
      return (acc.push (s, j, k), seen.insert s, counts.insert j (k + 1))
  else if r.isAppOfArity ``IdxTree.node 4 then
    let (acc, seen, counts) ← collectSymIdxTreeEntries (r.getArg! 2) acc seen counts
    collectSymIdxTreeEntries (r.getArg! 3) acc seen counts
  else
    throwError "gen_ls_blk: unexpected lsBlockSymIdxTree expression {r}"

private meta def buildListExpr0 (elemTy : Expr) (elems : Array Expr) : Expr := Id.run do
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [.zero]) elemTy
  let mut acc := nilE
  for i in [0 : elems.size] do
    acc := mkApp2 consFn elems[elems.size - 1 - i]! acc
  return acc

local elab "#init_ls_sym_meta_lits" : command => liftTermElabM <| withExporting do
  let currNs ← getCurrNamespace
  let (entries, _, _) ← collectSymIdxTreeEntries (Lean.mkConst ``lsBlockSymIdxTree) #[] {} {}
  let extElems ← ProofLib.ProgramReflection.listElemsWhnf (Lean.mkConst ``libsignalSessionExterns)
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let natNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy
  let tripleTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natNatTy
  let mut tripleElems : Array Expr := #[]
  for (s, j, k) in entries do
    let jkE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy (mkRawNatLit j) (mkRawNatLit k)
    let tE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natNatTy (mkStrLit s) jkE
    tripleElems := tripleElems.push tE
  addDecl (.defnDecl {
    name := currNs ++ `lsSymMetaLits, levelParams := [],
    type := mkApp (Lean.mkConst ``List [.zero]) tripleTy,
    value := buildListExpr0 tripleTy tripleElems, hints := .abbrev, safety := .safe
  })
  let mut extLitElems : Array Expr := #[]
  for eE in extElems do
    let s ← evalStrLitGls eE
    extLitElems := extLitElems.push (mkStrLit s)
  addDecl (.defnDecl {
    name := currNs ++ `lsExtSymsLits, levelParams := [],
    type := mkApp (Lean.mkConst ``List [.zero]) strTy,
    value := buildListExpr0 strTy extLitElems, hints := .abbrev, safety := .safe
  })

set_option maxHeartbeats 0 in
#init_ls_sym_meta_lits

private meta partial def readLitList (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``List.cons 3 then
    readLitList (e.getArg! 2) (acc.push (e.getArg! 1))
  else
    acc

private meta initialize lsBlockMetaCache :
    IO.Ref (Option (Std.HashMap String (Nat × Nat) × Std.HashSet String × Std.HashMap String Nat)) ←
  IO.mkRef none

private meta def loadLsSymMeta :
    CoreM (Std.HashMap String (Nat × Nat) × Std.HashSet String × Std.HashMap String Nat) := do
  if let some cached ← lsBlockMetaCache.get then
    return cached
  let ci1 ← getConstInfo ``lsSymMetaLits
  let ci2 ← getConstInfo ``lsExtSymsLits
  let mut m : Std.HashMap String (Nat × Nat) := {}
  for tE in readLitList ci1.value! do
    if let .lit (.strVal s) := tE.getArg! 2 then
      let jkE := tE.getArg! 3
      if let (.lit (.natVal j), .lit (.natVal k)) := (jkE.getArg! 2, jkE.getArg! 3) then
        m := m.insert s (j, k)
  let mut ext : Std.HashSet String := {}
  let mut extIdx : Std.HashMap String Nat := {}
  let extArr := readLitList ci2.value!
  for i in [0 : extArr.size] do
    if let .lit (.strVal s) := extArr[i]! then
      ext := ext.insert s
      if !extIdx.contains s then
        extIdx := extIdx.insert s i
  let res := (m, ext, extIdx)
  lsBlockMetaCache.set (some res)
  return res

/-- Fast reflection tactic for `(hmem : sym ∈ libsignalSessionExterns)`: looks up `k` in the
    precomputed literal index table and closes `libsignalSessionExterns[k]? = some sym` by
    `rfl_kernel` (`0` `String.decEq` calls), falling back to `decide` on non-literal goals. -/
elab "ls_extern_mem_tac" : tactic => do
  try
    let tgt ← instantiateMVars (← getMainTarget)
    let args := tgt.getAppArgs
    let mut kFound? : Option Nat := none
    let (_, _, extIdx) ← loadLsSymMeta
    for a in args do
      let aTy ← inferType a
      if aTy.isConstOf ``String then
        let s ← evalStrLitGls a
        if let some k := extIdx.get? s then
          kFound? := some k
          break
    match kFound? with
    | some k =>
      let kLit := Syntax.mkNumLit (toString k)
      evalTactic (← `(tactic| exact List.mem_of_getElem? (i := $kLit:num) (by rfl_kernel)))
    | none =>
      evalTactic (← `(tactic| decide))
  catch _ =>
    evalTactic (← `(tactic| decide))

theorem ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by ls_extern_mem_tac)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

private meta def evalIntLitGls (e : Expr) : MetaM Int := do
  let r ← withTransparency .all (reduce e)
  if let some n ← evalNatExprGls? r then return Int.ofNat n
  if r.isAppOfArity ``Int.ofNat 1 then
    if let some n ← evalNatExprGls? (r.getArg! 0) then return Int.ofNat n
  if r.isAppOfArity ``Int.negSucc 1 then
    if let some n ← evalNatExprGls? (r.getArg! 0) then return Int.negSucc n
  if r.isAppOfArity ``Neg.neg 3 then
    if let some n ← evalNatExprGls? (r.getArg! 2) then return -Int.ofNat n
  throwError "gen_ls_blk: expected Int literal, got {r}"

private meta partial def buildRelocTreeExpr (relocs : Array (Nat × Expr)) : Expr :=
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

private meta partial def buildWordTreeExpr (elems : Array Expr) (lo hi : Nat) : Expr :=
  let len := hi - lo
  if len == 0 then
    Lean.mkConst ``WordTree.empty
  else if len == 1 then
    let baseIdx := 4 * lo
    mkApp4 (Lean.mkConst ``WordTree.leaf)
      elems[baseIdx]! elems[baseIdx + 1]! elems[baseIdx + 2]! elems[baseIdx + 3]!
  else
    let half := len / 2
    let mid := lo + half
    mkApp3 (Lean.mkConst ``WordTree.node) (mkRawNatLit half)
      (buildWordTreeExpr elems lo mid) (buildWordTreeExpr elems mid hi)

private meta def wordAtLitProof (textE treeE nE hcodeE hsizeE treeVal : Expr) (off : Nat) :
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

/-- Shared implementation for `gen_ls_blk` / `gen_ls_blk_shard` (`emitFetches := true`)
    and `gen_ls_blk_base` (`emitFetches := false`). When `relocTag` is non-empty,
    cross-block relocation symbol lemmas are namespaced under `relocTag` so parallel
    sibling shards in the same namespace can be merged cleanly. -/
meta def elabGenLsBlkImpl (idxStx : TSyntax `num) (emitFetches : Bool)
    (relocTag : String := "") : CommandElabM Unit := do
  elabCommand (← `(command| open ProofLib.ProgramReflection ProofLib.GenPlacedFetches))
  let idx := idxStx.getNat
  let currNs ← getCurrNamespace
  let blkLibId := mkIdent (Name.mkSimple s!"blkLib_{idx}")
  let fullBlkLibName := currNs ++ blkLibId.getId
  if (← getEnv).contains fullBlkLibName then
    return
  let isMutated := idx ∈ ([55, 72, 77, 79, 159, 202, 462, 519] : List Nat)
  let (blkRaw, blkReduced, codeField, codeBytes, symEntries, relocData, blockSymMap, extSymSet) ←
      liftTermElabM do
    let (blockSymMap, extSymSet, _) ← loadLsSymMeta
    let some blkRaw ← lookupIdxTreeExpr (Lean.mkConst ``lsBlocksTree) idx
      | throwErrorAt idxStx "gen_ls_blk: block index {idx} out of bounds"
    let blkWhnf ← whnfAll blkRaw
    let codeField := if blkWhnf.isAppOfArity ``CodeBlock.mk 6 then blkWhnf.getArg! 0
      else mkApp (Lean.mkConst ``CodeBlock.code) blkWhnf
    let alignVal ← match ← evalNatExprGls? (mkApp (Lean.mkConst ``CodeBlock.align) blkWhnf) with
      | some a => pure a
      | none => throwError "gen_ls_blk: bad align"
    let codeBytes ← ProofLib.ProgramReflection.listElemsWhnf codeField
    let symElems ← ProofLib.ProgramReflection.listElemsWhnf
      (mkApp (Lean.mkConst ``CodeBlock.symbols) blkWhnf)
    let strTy := Lean.mkConst ``String
    let natTy := Lean.mkConst ``Nat
    let strNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
    let mut symEntries : Array (String × Nat) := #[]
    let mut symLitElems : Array Expr := #[]
    for pE in symElems do
      let pE ← whnfAll pE
      let s ← evalStrLitGls (pE.getArg! 2)
      let some o ← evalNatExprGls? (pE.getArg! 3) | throwError "gen_ls_blk: bad symbol offset"
      symEntries := symEntries.push (s, o)
      symLitElems := symLitElems.push
        (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natTy (mkStrLit s) (mkNatLit o))
    let symsLitE := buildListExpr0 strNatTy symLitElems
    let relocElems ← ProofLib.ProgramReflection.listElemsWhnf
      (mkApp (Lean.mkConst ``CodeBlock.relocs) blkWhnf)
    let mut relocData : Array (Nat × Name × String × Int × Expr) := #[]
    let mut relocLitElems : Array Expr := #[]
    for rE in relocElems do
      let rE ← whnfAll rE
      let off ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``RelocEntry.off) rE)
      let kE ← whnfAll (mkApp (Lean.mkConst ``RelocEntry.kind) rE)
      let some kn := kE.constName? | throwError "gen_ls_blk: bad reloc kind {kE}"
      let sym ← evalStrLitGls (mkApp (Lean.mkConst ``RelocEntry.sym) rE)
      let addend ← evalIntLitGls (mkApp (Lean.mkConst ``RelocEntry.addend) rE)
      let locB ← whnfAll (mkApp (Lean.mkConst ``RelocEntry.localSym) rE)
      let locBool := locB.isConstOf ``Bool.true
      let rLit := mkApp5 (Lean.mkConst ``RelocEntry.mk)
        (mkNatLit off) (Lean.mkConst kn) (mkStrLit sym) (toExpr addend) (toExpr locBool)
      relocData := relocData.push (off, kn, sym, addend, rLit)
      relocLitElems := relocLitElems.push rLit
    let relocsLitE := buildListExpr0 (Lean.mkConst ``RelocEntry) relocLitElems
    let weakRefsField := if blkWhnf.isAppOfArity ``CodeBlock.mk 6 then blkWhnf.getArg! 5
      else mkApp (Lean.mkConst ``CodeBlock.weakRefs) blkWhnf
    let blkReduced := mkApp6 (Lean.mkConst ``CodeBlock.mk)
      codeField (mkNatLit alignVal) symsLitE relocsLitE (Lean.mkConst ``libsignalSessionExterns) weakRefsField
    return (blkRaw, blkReduced, codeField, codeBytes, symEntries, relocData, blockSymMap, extSymSet)

  let codeLen := codeBytes.size
  let nWords := codeLen / 4
  let maxOff := if nWords > 0 then (nWords - 1) * 4 else 0
  let blkLibEqId := mkIdent (Name.mkSimple s!"blkLib_eq_{idx}")
  let blkExternsEqId := mkIdent (Name.mkSimple s!"blkExterns_eq_{idx}")
  let blkPlId := mkIdent (Name.mkSimple s!"blkPl_{idx}")
  let blkPlaceableId := mkIdent (Name.mkSimple s!"blkPlaceable_{idx}")
  let blkPCId := mkIdent (Name.mkSimple s!"blkPC_{idx}")
  let lsProgId := mkIdent (Name.mkSimple s!"lsProg_{idx}")
  let instIsLsId := mkIdent (Name.mkSimple s!"instIsLsBlockProg_{idx}")
  let blkTreeId := mkIdent (Name.mkSimple s!"blkTree_{idx}")
  let blkCodeEqId := mkIdent (Name.mkSimple s!"blkCodeEq_{idx}")
  let blkTreeSizeId := mkIdent (Name.mkSimple s!"blkTreeSize_{idx}")
  let maxOffLit := Syntax.mkNumLit (toString maxOff)

  let fullBlkPlName := currNs ++ blkPlId.getId
  let fullBlkPlaceableName := currNs ++ blkPlaceableId.getId
  let fullBlkPCName := currNs ++ blkPCId.getId
  let fullInstIsLsName := currNs ++ instIsLsId.getId
  let fullBlkTreeName := currNs ++ blkTreeId.getId
  let fullBlkCodeEqName := currNs ++ blkCodeEqId.getId
  let fullBlkTreeSizeName := currNs ++ blkTreeSizeId.getId

  -- Emit `blkLib_<idx>`, `blkLib_eq_<idx>`, and `blkExterns_eq_<idx>` via kernel trees.
  liftTermElabM <| withExporting do
    let val := mkApp4 (Lean.mkConst ``PlacedLib.mk)
      (mkStrLit "libsignalSession")
      blkReduced
      (Lean.mkConst ``libsignalSessionData)
      (mkApp (Lean.mkConst ``MultiPlacedLib.exports) (Lean.mkConst ``libsignalSessionMultiLib))
    addDecl (.defnDecl {
      name := fullBlkLibName, levelParams := [], type := Lean.mkConst ``PlacedLib,
      value := val, hints := .regular 0, safety := .safe
    })
    let libE := Lean.mkConst fullBlkLibName
    let optBlkTy := mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``CodeBlock)
    let someBlkRaw := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``CodeBlock) blkRaw
    let hgetE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optBlkTy someBlkRaw
    let hlibE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``PlacedLib) libE
    let eqPrf := mkAppN (Lean.mkConst ``blockLib_eq_of_lsBlocksTree)
      #[libE, mkNatLit idx, blkRaw, hgetE, hlibE]
    let eqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (Lean.mkConst ``PlacedLib)
      libE (mkApp2 (Lean.mkConst ``MultiPlacedLib.blockLib) (Lean.mkConst ``libsignalSessionLib) (mkNatLit idx))
    addDecl (.thmDecl {
      name := currNs ++ blkLibEqId.getId, levelParams := [], type := eqTy, value := eqPrf
    })
    let listStrTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``String)
    let extRhs := Lean.mkConst ``libsignalSessionExterns
    let extEqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) listStrTy
      (mkApp (Lean.mkConst ``CodeBlock.externs) (mkApp (Lean.mkConst ``PlacedLib.text) libE)) extRhs
    let extEqPrf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) listStrTy extRhs
    addDecl (.thmDecl {
      name := currNs ++ blkExternsEqId.getId, levelParams := [], type := extEqTy, value := extEqPrf
    })

  -- Emit `blkPl_<idx>`, `blkPlaceable_<idx>`, `blkPC_<idx>`, `lsProg_<idx>`, and `IsLsBlockProg`.
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

  -- Pre-emit shared `RelocTree`, shared `SymEnc`, and `blkPC_<idx>_fnOff_0x0*`.
  let shRtNm := fullBlkPCName ++ `_gpf_shared_relocTree
  let shRtEqNm := fullBlkPCName ++ `_gpf_shared_relocTree_eq
  let shRtWfNm := fullBlkPCName ++ `_gpf_shared_relocTree_wf
  let shXsNm := fullBlkPCName ++ `_gpf_shared_symChars
  let shEncNm := fullBlkPCName ++ `_gpf_shared_symEnc
  let shHtblNm := fullBlkPCName ++ `_gpf_shared_symChars_eq
  let shHeqNm := fullBlkPCName ++ `_gpf_shared_symEnc_eq
  liftTermElabM <| withExporting do
    let paramTy := if isMutated then Lean.mkConst ``LibsignalFullPlacement else Lean.mkConst ``LibsignalPlacement
    let paramLvl ← getLevel paramTy
    let libE := Lean.mkConst fullBlkLibName
    let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
    let natTy := Lean.mkConst ``Nat
    let strTy := Lean.mkConst ``String
    let boolTy := Lean.mkConst ``Bool
    let optNatTy := mkApp (Lean.mkConst ``Option [.zero]) natTy

    let rtVal := buildRelocTreeExpr (relocData.map fun (off, _, _, _, rE) => (off, rE))
    addDecl (.defnDecl {
      name := shRtNm, levelParams := [], type := Lean.mkConst ``RelocTree, value := rtVal,
      hints := .abbrev, safety := .safe
    })
    let shRtE := Lean.mkConst shRtNm
    let relListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``RelocEntry)
    let lhsRtEq := mkApp (Lean.mkConst ``CodeBlock.relocs) textE
    let rtEqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) relListTy lhsRtEq
      (mkApp (Lean.mkConst ``RelocTree.toList) shRtE)
    let rtEqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) relListTy lhsRtEq
    addDecl (.thmDecl { name := shRtEqNm, levelParams := [], type := rtEqTy, value := rtEqVal })
    let trueE := Lean.mkConst ``Bool.true
    let wfTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) boolTy (mkApp (Lean.mkConst ``RelocTree.wf) shRtE) trueE
    let wfVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy trueE
    addDecl (.thmDecl { name := shRtWfNm, levelParams := [], type := wfTy, value := wfVal })

    let charListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
    let charPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) charListTy natTy
    let charPairMk := mkApp2 (Lean.mkConst ``Prod.mk [.zero, .zero]) charListTy natTy
    let xsTy := mkApp (Lean.mkConst ``List [.zero]) charPairTy
    let natListTy := mkApp (Lean.mkConst ``List [.zero]) natTy
    let encKeyTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natListTy
    let encEntryTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) encKeyTy natTy
    let encEntryMk := mkApp2 (Lean.mkConst ``Prod.mk [.zero, .zero]) encKeyTy natTy
    let encTy := mkApp (Lean.mkConst ``ProofLib.ObjectLoad.EncSymTable) natTy
    let xsElems := symEntries.map fun (s, off) =>
      mkApp2 charPairMk (mkStrCharsExpr s) (mkNatLit off)
    let encElems := symEntries.map fun (s, off) =>
      let cs := s.toList
      let ekE := toExpr (cs.length, cs.map (fun ch => ch.val.toNat))
      mkApp2 encEntryMk ekE (mkNatLit off)
    addDecl (.defnDecl {
      name := shXsNm, levelParams := [], type := xsTy, value := buildListExpr0 charPairTy xsElems,
      hints := .abbrev, safety := .safe
    })
    addDecl (.defnDecl {
      name := shEncNm, levelParams := [], type := encTy, value := buildListExpr0 encEntryTy encElems,
      hints := .abbrev, safety := .safe
    })
    let shXsE := Lean.mkConst shXsNm
    let shEncE := Lean.mkConst shEncNm
    let strPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
    let strListTy := mkApp (Lean.mkConst ``List [.zero]) strPairTy
    let symsLhs := mkApp (Lean.mkConst ``CodeBlock.symbols) textE
    let symsRhs := mkApp (Lean.mkConst ``toStringSymbols) shXsE
    let htblTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) strListTy symsLhs symsRhs
    let htblVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strListTy symsLhs
    addDecl (.thmDecl { name := shHtblNm, levelParams := [], type := htblTy, value := htblVal })
    let prepLhs := mkApp2 (Lean.mkConst ``ProofLib.ObjectLoad.prepareCharAssocVal) natTy shXsE
    let heqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) encTy prepLhs shEncE
    let heqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) encTy shEncE
    addDecl (.thmDecl { name := shHeqNm, levelParams := [], type := heqTy, value := heqVal })

    let shHtblE := Lean.mkConst shHtblNm
    let hsymsFn := Expr.lam `a paramTy shHtblE .default
    let progFn := Lean.mkConst fullBlkPCName
    let mut symIdx : Nat := 0
    for (sym, off) in symEntries do
      let suffix := if symIdx == 0 then "" else s!"_{symIdx}"
      symIdx := symIdx + 1
      let fullFnOffName := currNs ++ Name.mkSimple s!"blkPC_{idx}_fnOff_0x0{suffix}"
      let symE := mkStrLit sym
      let csE := mkStrCharsExpr sym
      let offE := mkNatLit off
      let someOffE := mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy offE
      let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symE
      let hlk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optNatTy someOffE
      let corePrf := mkAppN (Lean.mkConst ``placed_fnOff_of_lookupCharSym [paramLvl])
        #[paramTy, progFn, shXsE, hsymsFn, symE, csE, offE, hname, hlk]
      let prf := Expr.lam `a paramTy (mkApp corePrf (.bvar 0)) .instImplicit
      let eqBody := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) natTy
        (mkApp2 (Lean.mkConst ``Program.fnOff) (mkApp progFn (.bvar 0)) symE) offE
      let ty := Expr.forallE `a paramTy eqBody .instImplicit
      addDecl (.thmDecl { name := fullFnOffName, levelParams := [], type := ty, value := prf })
      Term.applyAttributes fullFnOffName #[{ name := `simp }, { name := `arm64_norm }]
      modifyEnv fun env => fnEntryExt.addEntry env {
        sym := sym, codeConst := fullBlkPCName, decPrefix := fullBlkPCName,
        fnOffLemma := fullFnOffName, off := off, sizeBytes := 0, placed := true }

  -- Build `blkTree_<idx>` from `codeBytes` and run `gen_placed_fetches` when requested.
  if nWords > 0 then
    liftTermElabM <| withExporting do
      let libE := Lean.mkConst fullBlkLibName
      let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
      let natTy := Lean.mkConst ``Nat
      let optNatTy := mkApp (Lean.mkConst ``Option [.zero]) natTy
      let byteListTy := mkApp (Lean.mkConst ``List [.zero])
        (mkApp (Lean.mkConst ``BitVec) (mkNatLit 8))
      let treeValExpr := buildWordTreeExpr codeBytes 0 nWords
      addDecl (.defnDecl {
        name := fullBlkTreeName, levelParams := [], type := Lean.mkConst ``WordTree,
        value := treeValExpr, hints := .regular 0, safety := .safe
      })
      let treeE := Lean.mkConst fullBlkTreeName
      let codeLhs := mkApp (Lean.mkConst ``CodeBlock.code) textE
      let codeRhs := mkApp (Lean.mkConst ``WordTree.toBytes) treeE
      let codeEqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) byteListTy codeLhs codeRhs
      let codeEqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) byteListTy codeField
      addDecl (.thmDecl {
        name := fullBlkCodeEqName, levelParams := [], type := codeEqTy, value := codeEqVal
      })
      let nWordsE := mkNatLit nWords
      let someNWordsE := mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy nWordsE
      let sizeTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) optNatTy
        (mkApp (Lean.mkConst ``WordTree.checkSize?) treeE) someNWordsE
      let sizeVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optNatTy someNWordsE
      addDecl (.thmDecl {
        name := fullBlkTreeSizeName, levelParams := [], type := sizeTy, value := sizeVal
      })
    if emitFetches then
      elabCommand (← `(command|
        gen_placed_fetches $blkPCId:ident $blkLibId:ident $blkTreeId:ident $blkCodeEqId:ident $blkTreeSizeId:ident
          via_placement $blkPlId:ident $blkPlaceableId:ident [0 → $maxOffLit:num]
      ))

  -- Emit plain `ADRP` `pairStep`s and `:lo12:` load/store fetches via tree lookups.
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
    liftTermElabM <| withExporting do
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
          let (w, wE, hwdE) ← wordAtLitProof textE treeE nWordsE codeEqE sizeEqE treeVal off
          let rd := w % 32
          let rdE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rd)
          let tLam := Expr.lam `a paramTy (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend) .instImplicit
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
                let (_, w1E, hwd1E) ← wordAtLitProof textE treeE nWordsE codeEqE sizeEqE treeVal (off + 4)
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
              (targetExprForReloc (.bvar 0) sym addend)) .default
          let hPlTarget := Expr.lam `pl plTy
            (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
              (targetExprForReloc (.bvar 0) sym addend)) .default
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
            let (w, wE, hwdE) ← wordAtLitProof textE treeE nWordsE codeEqE sizeEqE treeVal off
            let opc := (w >>> 22) % 4
            let rt := w % 32
            let rn := (w >>> 5) % 32
            let opcE := mkNatLit opc
            let rtE := if rt == 31 then Lean.mkConst ``Reg.xzr
              else mkApp (Lean.mkConst ``Reg.gpr) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rt))
            let rnE := if rn == 31 then Lean.mkConst ``Reg.sp
              else mkApp (Lean.mkConst ``Reg.gpr) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rn))
            let tLam := Expr.lam `a paramTy (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend) .instImplicit
            let instOfT ← withLocalDeclD `t bv64 fun tFVar => do
              let addrT := mkApp2 (Lean.mkConst ``AddrMode.Offset) rnE (mkApp (Lean.mkConst ``lo12Of) tFVar)
              let someInstT ← whnfAll (mkApp4 (Lean.mkConst ``mkLoadStoreInst) scaleE opcE rtE addrT)
              let instT := someInstT.getArg! 1
              mkLambdaFVars #[tFVar] instT
            let instLam := Expr.lam `a paramTy
              (instOfT.beta #[targetExprForReloc (mkApp plFn (.bvar 0)) sym addend]) .instImplicit
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
                (targetExprForReloc (.bvar 0) sym addend)) .default
            let hPlTarget := Expr.lam `pl plTy
              (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                (targetExprForReloc (.bvar 0) sym addend)) .default
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
              (mkApp hInstOfT (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend)) .instImplicit
            let prf := mkAppN (Lean.mkConst ``fetch_rebase_ldstLo12_of_tree [.succ .zero])
              #[paramTy, progFn, plFn, libE, treeE, nWordsE, offE, rE, scaleE, tLam, instLam, wE,
                hprogE, placeableFn, codeEqE, sizeEqE, hltE, hrE, hkE, hwdE, hscaleE, hw1E, hw2E,
                hTE, hinstE]
            let ty ← inferType prf
            ProofLib.GenDecodes.addThm thmName ty prf
            Term.applyAttributes thmName #[{ name := `simp }, { name := `arm64_norm }]

  -- Emit `@[simp, arm64_norm, wp_norm]` resolution and `fnAddr` lemmas via `List Char` reflection.
  liftTermElabM <| withExporting do
    let mplTy := Lean.mkConst ``MultiPlacement
    let paramTy := if isMutated then Lean.mkConst ``LibsignalFullPlacement else Lean.mkConst ``LibsignalPlacement
    let hooksTy := Lean.mkConst ``LibsignalHooks
    let strTy := Lean.mkConst ``String
    let natTy := Lean.mkConst ``Nat
    let boolTy := Lean.mkConst ``Bool
    let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
    let natPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy
    let optPairTy := mkApp (Lean.mkConst ``Option [.zero]) natPairTy
    let lsLibE := Lean.mkConst ``libsignalSessionLib
    let normAttrs : Array Attribute := #[{ name := `simp }, { name := `arm64_norm }, { name := `wp_norm }]

    let addResolveBlk (shortNm : Name) (sym : String) (j : Nat) : TermElabM Unit := do
      let fullNm := currNs ++ shortNm
      if !(← getEnv).contains fullNm then
        let symE := mkStrLit sym
        let csE := mkStrCharsExpr sym
        let jE := mkNatLit j
        let someP := mkApp2 (Lean.mkConst ``Option.some [.zero]) natPairTy
          (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy jE (mkNatLit 0))
        let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symE
        let hchk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optPairTy someP
        let bodyTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
          (mkApp3 (Lean.mkConst ``MultiPlacedLib.resolve) lsLibE (.bvar 0) symE)
          (mkApp2 (Lean.mkConst ``MultiPlacement.base) (.bvar 0) jE)
        let ty := Expr.forallE `pl mplTy bodyTy .default
        let prf := Expr.lam `pl mplTy
          (mkAppN (Lean.mkConst ``ls_resolve_block_chars) #[.bvar 0, symE, csE, jE, hname, hchk]) .default
        addDecl (.thmDecl { name := fullNm, levelParams := [], type := ty, value := prf })
        Term.applyAttributes fullNm normAttrs

    let addFnAddrBlk (shortNm : Name) (sym : String) (j : Nat) : TermElabM Unit := do
      let fullNm := currNs ++ shortNm
      if !(← getEnv).contains fullNm then
        let symE := mkStrLit sym
        let csE := mkStrCharsExpr sym
        let jE := mkNatLit j
        let someP := mkApp2 (Lean.mkConst ``Option.some [.zero]) natPairTy
          (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy jE (mkNatLit 0))
        let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symE
        let hchk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optPairTy someP
        let bodyTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
          (mkApp3 (Lean.mkConst ``MultiPlacedLib.fnAddr) lsLibE (.bvar 0) symE)
          (mkApp2 (Lean.mkConst ``MultiPlacement.base) (.bvar 0) jE)
        let ty := Expr.forallE `pl mplTy bodyTy .default
        let prf := Expr.lam `pl mplTy
          (mkAppN (Lean.mkConst ``ls_fnAddr_block_chars) #[.bvar 0, symE, csE, jE, hname, hchk]) .default
        addDecl (.thmDecl { name := fullNm, levelParams := [], type := ty, value := prf })
        Term.applyAttributes fullNm normAttrs

    let addProgFnAddrBlk (shortNm : Name) (sym : String) : TermElabM Unit := do
      let fullNm := currNs ++ shortNm
      if !(← getEnv).contains fullNm then
        let symE := mkStrLit sym
        let csE := mkStrCharsExpr sym
        let idxE := mkNatLit idx
        let someP := mkApp2 (Lean.mkConst ``Option.some [.zero]) natPairTy
          (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy idxE (mkNatLit 0))
        let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symE
        let hchk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optPairTy someP
        -- Under binders `[a : paramTy] (H : LibsignalHooks)`, `a` is `.bvar 1` and `H` is `.bvar 0`.
        let aRef := Expr.bvar 1
        let hRef := Expr.bvar 0
        let instLsPl := if isMutated then
          mkApp (Lean.mkConst ``LibsignalFullPlacement.toLibsignalPlacement) aRef
        else aRef
        let progFn := Lean.mkConst fullBlkPCName
        let plFn := Lean.mkConst fullBlkPlName
        let noneOvr := Expr.lam `x strTy
          (mkApp (Lean.mkConst ``Option.none [.zero])
            (Expr.forallE `s (Lean.mkConst ``Arm64.State) (Lean.mkConst ``Arm64.State) .default)) .default
        let rebProg := mkApp4 (Lean.mkConst ``Program.rebase)
          (mkApp progFn aRef)
          (mkApp (Lean.mkConst ``Placement.base) (mkApp plFn aRef))
          hRef noneOvr
        let lsmplE := mkApp (Lean.mkConst ``lsmpl) instLsPl
        let bodyTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
          (mkApp2 (Lean.mkConst ``Program.fnAddr) rebProg symE)
          (mkApp2 (Lean.mkConst ``MultiPlacement.base) lsmplE idxE)
        let ty := Expr.forallE `inst paramTy (Expr.forallE `H hooksTy bodyTy .default) .instImplicit
        let hprogInst := mkApp2 (Lean.mkConst fullInstIsLsName) aRef hRef
        let bodyPrf := mkAppN (Lean.mkConst ``lsProg_fnAddr_of_blockProg_chars)
          #[instLsPl, rebProg, idxE, hRef, hprogInst, symE, csE, hname, hchk]
        let prf := Expr.lam `inst paramTy (Expr.lam `H hooksTy bodyPrf .default) .instImplicit
        addDecl (.thmDecl { name := fullNm, levelParams := [], type := ty, value := prf })
        Term.applyAttributes fullNm normAttrs

    let addResolveDat (shortNm : Name) (sym : String) : TermElabM Unit := do
      let fullNm := currNs ++ shortNm
      if !(← getEnv).contains fullNm then
        let symE := mkStrLit sym
        let csE := mkStrCharsExpr sym
        let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symE
        let hchk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.true)
        let bodyTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
          (mkApp3 (Lean.mkConst ``MultiPlacedLib.resolve) lsLibE (.bvar 0) symE)
          (mkApp2 (Lean.mkConst ``MultiPlacement.ρ) (.bvar 0) symE)
        let ty := Expr.forallE `pl mplTy bodyTy .default
        let prf := Expr.lam `pl mplTy
          (mkAppN (Lean.mkConst ``ls_resolve_data_chars) #[.bvar 0, symE, csE, hname, hchk]) .default
        addDecl (.thmDecl { name := fullNm, levelParams := [], type := ty, value := prf })
        Term.applyAttributes fullNm normAttrs

    let mut ownSymIdx : Nat := 0
    for (sym, _) in symEntries do
      let suffix := if ownSymIdx == 0 then "" else s!"_{ownSymIdx}"
      ownSymIdx := ownSymIdx + 1
      addResolveBlk (Name.mkSimple s!"ls_resolve_blk_{idx}{suffix}") sym idx
      addFnAddrBlk (Name.mkSimple s!"ls_fnAddr_blk_{idx}{suffix}") sym idx
      addProgFnAddrBlk (Name.mkSimple s!"ls_blockProgram_fnAddr_blk_{idx}{suffix}") sym

    let mut seenRelSyms : Std.HashSet String := extSymSet
    seenRelSyms := seenRelSyms.insert "log::MAX_LOG_LEVEL_FILTER"
    seenRelSyms := seenRelSyms.insert "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_STORAGE"
    seenRelSyms := seenRelSyms.insert "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_ONCE"
    seenRelSyms := seenRelSyms.insert "curve25519_dalek::constants::ED25519_BASEPOINT_TABLE"
    let relocPrefix := if relocTag.isEmpty then "" else s!"{relocTag}_"
    for (_, _, rsym, _, _) in relocData do
      if !seenRelSyms.contains rsym then
        seenRelSyms := seenRelSyms.insert rsym
        match blockSymMap.get? rsym with
        | some (j, rSymIdx) =>
          let suffix := if rSymIdx == 0 then "" else s!"_{rSymIdx}"
          let stdRes := Name.mkSimple s!"ls_resolve_blk_{j}{suffix}"
          if relocTag.isEmpty || !(← getEnv).contains (currNs ++ stdRes) then
            addResolveBlk (Name.mkSimple s!"ls_resolve_{relocPrefix}blk_{j}{suffix}") rsym j
          let stdFn := Name.mkSimple s!"ls_fnAddr_blk_{j}{suffix}"
          if relocTag.isEmpty || !(← getEnv).contains (currNs ++ stdFn) then
            addFnAddrBlk (Name.mkSimple s!"ls_fnAddr_{relocPrefix}blk_{j}{suffix}") rsym j
        | none =>
          let hash := UInt64.toNat (Hashable.hash rsym)
          let stdDat := Name.mkSimple s!"ls_resolve_dat_{sanitizeSymIdent rsym}_{hash}"
          if relocTag.isEmpty || !(← getEnv).contains (currNs ++ stdDat) then
            addResolveDat (Name.mkSimple s!"ls_resolve_{relocPrefix}dat_{sanitizeSymIdent rsym}_{hash}") rsym

  -- Mark `blkPC_<idx>` `[irreducible]` when emitting full fetches so `wp_steps` does not unfold `stubs`.
  if emitFetches then
    liftTermElabM <| withExporting do
      setIrreducibleAttribute fullBlkPCName

@[command_elab genLsBlkStx]
meta def elabGenLsBlk : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk $idxStx:num) =>
    elabGenLsBlkImpl idxStx true
  | _ => throwUnsupportedSyntax

syntax (name := genLsBlkShardStx) "gen_ls_blk_shard " ident num : command

@[command_elab genLsBlkShardStx]
meta def elabGenLsBlkShard : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk_shard $tag:ident $idxStx:num) =>
    elabGenLsBlkImpl idxStx true tag.getId.toString
  | _ => throwUnsupportedSyntax

/-- Emit the base block program, trees, relocation lemmas, and cross-block symbol resolution
    lemmas for block `<idx>` without per-instruction `gen_placed_fetches`, so fetch shards
    can be split across separate files. -/
syntax (name := genLsBlkBaseStx) "gen_ls_blk_base " num : command

@[command_elab genLsBlkBaseStx]
meta def elabGenLsBlkBase : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk_base $idxStx:num) =>
    elabGenLsBlkImpl idxStx false
  | _ => throwUnsupportedSyntax

end MetaGenLsBlk

end CryptoVerification
