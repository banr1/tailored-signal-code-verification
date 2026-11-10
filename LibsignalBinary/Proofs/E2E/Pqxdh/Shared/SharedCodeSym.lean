/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.GenPlacedFetches
import ProofLib.Hoare.Hooks
import ProofLib.SepLogic.WPFrozen
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches and Cross-Block Transfers for `Shared`

Generates per-block `PlacedLib`, `WordTree`, `gen_placed_fetches`, `ADRP` `pairStep`s, `:lo12:`
load/store fetches, and symbol resolution lemmas for Blocks `55` (`append_elements`), `588`
(`try_allocate_in`), `202` (`is_canonical`), and `204` (`verify_signature_for_multipart_message`),
together with uniform hook-lookup and cross-block `subroutine_ok` transfer lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open Lean Meta Elab Command Term

private meta def whnfAllShared (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private meta def evalStrLitShared (e : Expr) : MetaM String := do
  let r ← whnfAllShared e
  match r with
  | .lit (.strVal s) => return s
  | _ =>
    let r2 ← withTransparency .all (reduce e)
    match r2 with
    | .lit (.strVal s) => return s
    | _ => throwError "gen_ls_blk: expected string literal, got {r2}"

private meta def evalNatExprShared? (e : Expr) : MetaM (Option Nat) := do
  let r ← whnfAllShared e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

private meta partial def lookupIdxTreeExprShared (treeE : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let r ← whnfAllShared treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return none
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    if idx == 0 then return some (r.getArg! 1) else return none
  else if r.isAppOfArity ``IdxTree.node 4 then
    let some leftSz ← evalNatExprShared? (r.getArg! 1)
      | throwError "gen_ls_blk: invalid leftSz in IdxTree.node"
    if idx < leftSz then
      lookupIdxTreeExprShared (r.getArg! 2) idx
    else
      lookupIdxTreeExprShared (r.getArg! 3) (idx - leftSz)
  else
    throwError "gen_ls_blk: unexpected IdxTree expression {r}"

private meta partial def collectSymIdxTreeShared (treeE : Expr)
    (acc : Std.HashMap String (Nat × Nat))
    (counts : Std.HashMap Nat Nat) :
    MetaM (Std.HashMap String (Nat × Nat) × Std.HashMap Nat Nat) := do
  let r ← whnfAllShared treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return (acc, counts)
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    let pE ← whnfAllShared (r.getArg! 1)
    let s ← evalStrLitShared (pE.getArg! 2)
    let some j ← evalNatExprShared? (pE.getArg! 3)
      | throwError "gen_ls_blk: invalid block index in lsBlockSymIdxTree"
    if acc.contains s then
      return (acc, counts)
    else
      let k := counts.getD j 0
      return (acc.insert s (j, k), counts.insert j (k + 1))
  else if r.isAppOfArity ``IdxTree.node 4 then
    let (acc, counts) ← collectSymIdxTreeShared (r.getArg! 2) acc counts
    collectSymIdxTreeShared (r.getArg! 3) acc counts
  else
    throwError "gen_ls_blk: unexpected lsBlockSymIdxTree expression {r}"

private meta def evalIntLitShared (e : Expr) : MetaM Int := do
  let r ← withTransparency .all (reduce e)
  if let some n ← evalNatExprShared? r then return Int.ofNat n
  if r.isAppOfArity ``Int.ofNat 1 then
    if let some n ← evalNatExprShared? (r.getArg! 0) then return Int.ofNat n
  if r.isAppOfArity ``Int.negSucc 1 then
    if let some n ← evalNatExprShared? (r.getArg! 0) then return Int.negSucc n
  if r.isAppOfArity ``Neg.neg 3 then
    if let some n ← evalNatExprShared? (r.getArg! 2) then return -Int.ofNat n
  throwError "gen_ls_blk: expected Int literal, got {r}"

private meta def sanitizeSymIdentShared (s : String) : String :=
  String.ofList <| (s.toList.take 48).map fun c =>
    if c.isAlphanum then c else '_'

private meta def targetExprForRelocShared (plE : Expr) (sym : String) (addend : Int) : Expr :=
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

/-- Local override of `gen_ls_blk` supporting full-block fetches and relocations for both
    unmutated blocks (`[LibsignalPlacement]`) and blocks in `libsignalMutatedBlocks`
    (`55`, `202` under `[LibsignalFullPlacement]`). -/
@[local command_elab genLsBlkStx]
private meta def elabGenLsBlkShared : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk $idxStx:num) => do
    elabCommand (← `(command| open ProofLib.ProgramReflection ProofLib.GenPlacedFetches))
    let idx := idxStx.getNat
    let blkLibId := mkIdent (Name.mkSimple s!"blkLib_{idx}")
    let currNs ← getCurrNamespace
    let fullBlkLibName := currNs ++ blkLibId.getId
    if (← getEnv).contains fullBlkLibName then
      return
    let isMutated := idx ∈ ([55, 72, 77, 79, 159, 202, 462, 519] : List Nat)
    let (blkE, codeLen, symNames, relocData, blockSymMap, extSymSet) ← liftTermElabM do
      let (blockSymMap, _) ← collectSymIdxTreeShared (Lean.mkConst ``lsBlockSymIdxTree) {} {}
      let extsE := Lean.mkConst ``libsignalSessionExterns
      let extElems ← ProofLib.ProgramReflection.listElemsWhnf extsE
      let mut extSymSet : Std.HashSet String := {}
      for eE in extElems do
        let s ← evalStrLitShared eE
        extSymSet := extSymSet.insert s
      let some blkRaw ← lookupIdxTreeExprShared (Lean.mkConst ``lsBlocksTree) idx
        | throwErrorAt idxStx "gen_ls_blk: block index {idx} out of bounds"
      let blkE ← whnfAllShared blkRaw
      let codeE := mkApp (Lean.mkConst ``CodeBlock.code) blkE
      let codeBytes ← ProofLib.ProgramReflection.listElemsWhnf codeE
      let symsE := mkApp (Lean.mkConst ``CodeBlock.symbols) blkE
      let symElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
      let mut symNames : Array String := #[]
      for pE in symElems do
        let pE ← whnfAllShared pE
        let s ← evalStrLitShared (pE.getArg! 2)
        symNames := symNames.push s
      let relocsE := mkApp (Lean.mkConst ``CodeBlock.relocs) blkE
      let relocElems ← ProofLib.ProgramReflection.listElemsWhnf relocsE
      let mut relocData : Array (Nat × Name × String × Int × Expr) := #[]
      for rE in relocElems do
        let rE ← whnfAllShared rE
        let off ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``RelocEntry.off) rE)
        let kE ← whnfAllShared (mkApp (Lean.mkConst ``RelocEntry.kind) rE)
        let some kn := kE.constName? | throwError "gen_ls_blk: bad reloc kind {kE}"
        let sym ← evalStrLitShared (mkApp (Lean.mkConst ``RelocEntry.sym) rE)
        let addend ← evalIntLitShared (mkApp (Lean.mkConst ``RelocEntry.addend) rE)
        relocData := relocData.push (off, kn, sym, addend, rE)
      return (blkE, codeBytes.size, symNames, relocData, blockSymMap, extSymSet)

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
        blkE
        (Lean.mkConst ``libsignalSessionData)
        (mkApp (Lean.mkConst ``MultiPlacedLib.exports) (Lean.mkConst ``libsignalSessionMultiLib))
      let decl := Declaration.defnDecl {
        name := fullBlkLibName
        levelParams := []
        type := Lean.mkConst ``PlacedLib
        value := val
        hints := .regular 0
        safety := .safe
      }
      withExporting <| addAndCompile decl

    elabCommand (← `(command|
      theorem $blkLibEqId:ident : $blkLibId:ident = libsignalSessionLib.blockLib $idxStx:num := rfl
    ))
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

    let relaxableAddKind (kn : Name) : Bool :=
      kn == ``RelocKind.addLo12

    let isRelaxableAt (off : Nat) (kn : Name) (sym : String) (addend : Int) : Bool :=
      if kn != ``RelocKind.adrpHi21 then false
      else
        match relocData.find? (fun (o, _, _, _, _) => o == off + 4) with
        | some (_, kn2, sym2, add2, _) =>
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
        let progFn := Lean.mkConst fullBlkPCName
        let plFn := Lean.mkConst fullBlkPlName
        let placeableFn := Lean.mkConst fullBlkPlaceableName
        let libE := Lean.mkConst fullBlkLibName
        let treeE := Lean.mkConst fullBlkTreeName
        let codeEqE := Lean.mkConst fullBlkCodeEqName
        let sizeEqE := Lean.mkConst fullBlkTreeSizeName
        let nWordsE := mkNatLit nWords
        let hprogE := Expr.lam `a paramTy
          (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Program)
            (mkApp progFn (.bvar 0))) .instImplicit

        let treeVal ← ProofLib.GenDecodes.treeValueOf fullBlkTreeName
        for (off, kn, sym, addend, rE) in relocData do
          let offHex := String.ofList (Nat.toDigits 16 off)
          if kn == ``RelocKind.adrpHi21 && !isRelaxableAt off kn sym addend then
            let thmName := currNs ++ Name.mkSimple s!"blkPC_{idx}_pairStep_0x{offHex}"
            let offE := mkNatLit off
            let off4E := mkNatLit (off + 4)
            let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
            let w : Nat := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
            let wE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit w)
            let rd := w % 32
            let rdE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rd)
            let tLam := Expr.lam `a paramTy (targetExprForRelocShared (mkApp plFn (.bvar 0)) sym addend) .instImplicit
            let hltTy := mkApp4 (Lean.mkConst ``LT.lt [.zero]) natTy (Lean.mkConst ``instLTNat)
              offE (mkNatMul (mkNatLit 4) nWordsE)
            let hltE ← mkDecideProof hltTy
            let hrE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
              (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry))
              (mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE)
            let hkE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``RelocKind)
              (Lean.mkConst ``RelocKind.adrpHi21)
            let hnrelE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
            let hwdE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32 wE
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
                (mkApp3 (Lean.mkConst ``CodeBlock.target) (mkApp (Lean.mkConst ``PlacedLib.text) libE) (.bvar 0) rE)
                (targetExprForRelocShared (.bvar 0) sym addend)) .default
            let hPlTarget := Expr.lam `pl plTy
              (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                (targetExprForRelocShared (.bvar 0) sym addend)) .default
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
                match relocData.find? (fun (o, _, _, _, _) => o == off - 4) with
                | some (o, kn0, s0, a0, _) => isRelaxableAt o kn0 s0 a0
                | none => false
            if !prevRelax then
              let thmName := currNs ++ Name.mkSimple s!"blkPC_{idx}_rebase_fetch_0x{offHex}"
              let offE := mkNatLit off
              let scaleE := mkNatLit scale
              let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
              let w : Nat := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
              let wE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit w)
              let opc := (w >>> 22) % 4
              let rt := w % 32
              let rn := (w >>> 5) % 32
              let opcE := mkNatLit opc
              let rtE := if rt == 31 then Lean.mkConst ``Reg.xzr
                else mkApp (Lean.mkConst ``Reg.gpr) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rt))
              let rnE := if rn == 31 then Lean.mkConst ``Reg.sp
                else mkApp (Lean.mkConst ``Reg.gpr) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rn))
              let tLam := Expr.lam `a paramTy (targetExprForRelocShared (mkApp plFn (.bvar 0)) sym addend) .instImplicit
              let instOfT ← withLocalDeclD `t bv64 fun tFVar => do
                let addrT := mkApp2 (Lean.mkConst ``AddrMode.Offset) rnE (mkApp (Lean.mkConst ``lo12Of) tFVar)
                let someInstT ← whnfAllShared (mkApp4 (Lean.mkConst ``mkLoadStoreInst) scaleE opcE rtE addrT)
                let instT := someInstT.getArg! 1
                mkLambdaFVars #[tFVar] instT
              let instLam := Expr.lam `a paramTy
                (instOfT.beta #[targetExprForRelocShared (mkApp plFn (.bvar 0)) sym addend]) .instImplicit
              let hltTy := mkApp4 (Lean.mkConst ``LT.lt [.zero]) natTy (Lean.mkConst ``instLTNat)
                offE (mkNatMul (mkNatLit 4) nWordsE)
              let hltE ← mkDecideProof hltTy
              let hrE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry))
                (mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE)
              let hkE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                (mkApp (Lean.mkConst ``Option [.zero]) natTy)
                (mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy scaleE)
              let hwdE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32 wE
              let hscaleE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy scaleE
              let hw1E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32
                (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x39000000))
              let hw2E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
              let plTy := Lean.mkConst ``Placement
              let hPlTargetTy := Expr.forallE `pl plTy
                (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv64
                  (mkApp3 (Lean.mkConst ``CodeBlock.target) (mkApp (Lean.mkConst ``PlacedLib.text) libE) (.bvar 0) rE)
                  (targetExprForRelocShared (.bvar 0) sym addend)) .default
              let hPlTarget := Expr.lam `pl plTy
                (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                  (targetExprForRelocShared (.bvar 0) sym addend)) .default
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
                (mkApp hInstOfT (targetExprForRelocShared (mkApp plFn (.bvar 0)) sym addend)) .instImplicit
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
            ls_resolve_block (by decide +kernel)
        ))
      if !env.contains (currNs ++ fnShort) then
        let fnId := mkIdent fnShort
        elabCommand (← `(command|
          @[simp, arm64_norm, wp_norm]
          theorem $fnId:ident (pl : MultiPlacement) :
              libsignalSessionLib.fnAddr pl $symLit:str = pl.base $idxStx:num :=
            ls_fnAddr_block (by decide +kernel)
        ))
      if !env.contains (currNs ++ progFnShort) then
        let progFnId := mkIdent progFnShort
        if isMutated then
          elabCommand (← `(command|
            @[simp, arm64_norm, wp_norm]
            theorem $progFnId:ident [LibsignalFullPlacement] (H : LibsignalHooks) :
                (($blkPCId:ident).rebase ($blkPlId:ident).base H).fnAddr $symLit:str = lsmpl.base $idxStx:num :=
              lsProg_fnAddr_of_blockProg (by decide +kernel)
          ))
        else
          elabCommand (← `(command|
            @[simp, arm64_norm, wp_norm]
            theorem $progFnId:ident [LibsignalPlacement] (H : LibsignalHooks) :
                (($blkPCId:ident).rebase ($blkPlId:ident).base H).fnAddr $symLit:str = lsmpl.base $idxStx:num :=
              lsProg_fnAddr_of_blockProg (by decide +kernel)
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
          let resShort := Name.mkSimple s!"ls_resolve_blk_{j}{suffix}"
          let fnShort := Name.mkSimple s!"ls_fnAddr_blk_{j}{suffix}"
          let jLit := Syntax.mkNumLit (toString j)
          let env ← getEnv
          if !env.contains (currNs ++ resShort) then
            let resId := mkIdent resShort
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $resId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.resolve pl $symLit:str = pl.base $jLit:num :=
                ls_resolve_block (by decide +kernel)
            ))
          if !env.contains (currNs ++ fnShort) then
            let fnId := mkIdent fnShort
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $fnId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.fnAddr pl $symLit:str = pl.base $jLit:num :=
                ls_fnAddr_block (by decide +kernel)
            ))
        | none =>
          let hash := UInt64.toNat (Hashable.hash rsym)
          let resShort := Name.mkSimple s!"ls_resolve_dat_{sanitizeSymIdentShared rsym}_{hash}"
          let env ← getEnv
          if !env.contains (currNs ++ resShort) then
            let resId := mkIdent resShort
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $resId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.resolve pl $symLit:str = pl.ρ $symLit:str :=
                ls_resolve_data (by decide +kernel)
            ))

    liftTermElabM do
      setIrreducibleAttribute fullBlkPCName
  | _ => throwUnsupportedSyntax

-- Block 0 (used to discharge `externAt?` uniformly for mutated & unmutated blocks):
private theorem blk0_externs_eq : (libsignalSessionLib.blockLib 0).text.externs = libsignalSessionExterns := rfl

private instance instIsLsBlockProg_blk0_shared [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 0 H) 0 H where
  eq_blockProgram := rfl
  externs_eq := blk0_externs_eq

/-- Look up the external hook at `lsρ sym` in any block `i`'s program `prog` (including mutated blocks). -/
theorem ls_externAt?_any [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  have heq : prog.externAt? = (libsignalSessionLib.blockProgram lsmpl 0 H).externAt? := by
    rw [hprog.eq_blockProgram]
    exact ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
      (hprog.externs_eq.trans blk0_externs_eq.symm)
  rw [heq]
  exact ls_externAt?_of_mem (prog := libsignalSessionLib.blockProgram lsmpl 0 H) (i := 0) hmem
    (by decide) (by decide)

/-- Prove `subroutine_ok prog (lsρ sym) spec` for an external hook `sym` in any block `i`'s
    program `prog` (including mutated blocks). -/
theorem ls_hook_ok_any [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_any hmem).trans hf) hok

/-- Prove `subroutine_ok prog (lsρ sym) spec` when `prog` uses `Rust.withPanics hooks` and `sym`
    is a non-panic external hook (including on mutated blocks). -/
theorem ls_hook_ok_panics_any [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {hooks : LibsignalHooks} [hprog : IsLsBlockProg prog i (Rust.withPanics hooks)]
    {sym : String} {spec : Spec α} (hsat : HookSat hooks sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hnp : Rust.isPanicSymbol sym = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  refine ls_hook_ok_any ⟨f, ?_, hok⟩ hmem
  simp [Rust.withPanics, hnp, hf]

/-- Transfer `subroutine_ok calleeProg entry (libsignalSessionLib.withCodeLoaded lsmpl spec)` from
    any block `j < 619` (including mutated blocks) to block `i`'s `callerProg`. -/
theorem full_ls_subroutine_ok_of_block [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (libsignalSessionLib.withCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide) :
    subroutine_ok callerProg entry (libsignalSessionLib.withCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withCodeLoaded hpre
  have hblk0 := hcl0 j (by rw [libsignalSessionLib_blocks_length]; omega)
  have hQL : calleeProg.CodeLoaded s0.mem := by
    rw [hcallee_prog.eq_blockProgram]
    rwa [Program.codeLoaded_iff] at hblk0 ⊢
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Transfer `subroutine_ok calleeProg entry spec` from any block `j < 619` (including mutated
    blocks) to block `i`'s `callerProg` wrapped in `libsignalSessionLib.withCodeLoaded lsmpl spec`. -/
theorem full_ls_subroutine_ok_of_plain [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hj : j < 619 := by decide) :
    subroutine_ok callerProg entry (libsignalSessionLib.withCodeLoaded lsmpl spec) :=
  full_ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withCodeLoaded_of_plain hcallee) hj

-- Block 55: `<alloc::vec::Vec<u8>>::append_elements` (mutated -> `[LibsignalFullPlacement]`)
gen_ls_blk 55

-- Block 588: `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (unmutated -> `[LibsignalPlacement]`)
gen_ls_blk 588

-- Block 202: `<libsignal_core::curve::PublicKey>::is_canonical` (mutated -> `[LibsignalFullPlacement]`)
gen_ls_blk 202

-- Block 204: `<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message` (unmutated -> `[LibsignalPlacement]`)
gen_ls_blk 204

end CryptoVerification
