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
public meta import Lean -- shake: keep

/-!
# Relocatable Per-Block Symbol Bindings for `TripleRatchet/Record`

Per-block symbol bindings and instruction-fetch aliases for the `try_decrypt_from_record` region
(`+0x1a8..+0x2648`) of `libsignal_session::session_message_decrypt_signal` (block 197).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches Lean Elab Command Term Meta
open CryptoVerification

private meta def whnfAllRec (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private meta def evalStrLitRec (e : Expr) : MetaM String := do
  let r ← whnfAllRec e
  match r with
  | .lit (.strVal s) => return s
  | _ =>
    let r2 ← withTransparency .all (reduce e)
    match r2 with
    | .lit (.strVal s) => return s
    | _ => throwError "gen_ls_blk: expected string literal, got {r2}"

private meta def evalNatExprRec? (e : Expr) : MetaM (Option Nat) := do
  let r ← whnfAllRec e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

private meta partial def lookupIdxTreeExprRec (treeE : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let r ← whnfAllRec treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return none
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    if idx == 0 then return some (r.getArg! 1) else return none
  else if r.isAppOfArity ``IdxTree.node 4 then
    let some leftSz ← evalNatExprRec? (r.getArg! 1)
      | throwError "gen_ls_blk: invalid leftSz in IdxTree.node"
    if idx < leftSz then
      lookupIdxTreeExprRec (r.getArg! 2) idx
    else
      lookupIdxTreeExprRec (r.getArg! 3) (idx - leftSz)
  else
    throwError "gen_ls_blk: unexpected IdxTree expression {r}"

private meta partial def collectSymIdxTreeRec (treeE : Expr)
    (acc : Std.HashMap String Nat) : MetaM (Std.HashMap String Nat) := do
  let r ← whnfAllRec treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return acc
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    let pE ← whnfAllRec (r.getArg! 1)
    let s ← evalStrLitRec (pE.getArg! 2)
    let some j ← evalNatExprRec? (pE.getArg! 3)
      | throwError "gen_ls_blk: invalid block index in lsBlockSymIdxTree"
    return if acc.contains s then acc else acc.insert s j
  else if r.isAppOfArity ``IdxTree.node 4 then
    let acc ← collectSymIdxTreeRec (r.getArg! 2) acc
    collectSymIdxTreeRec (r.getArg! 3) acc
  else
    throwError "gen_ls_blk: unexpected lsBlockSymIdxTree expression {r}"

private meta def evalIntLitRec (e : Expr) : MetaM Int := do
  let r ← withTransparency .all (reduce e)
  if let some n ← evalNatExprRec? r then return Int.ofNat n
  if r.isAppOfArity ``Int.ofNat 1 then
    if let some n ← evalNatExprRec? (r.getArg! 0) then return Int.ofNat n
  if r.isAppOfArity ``Int.negSucc 1 then
    if let some n ← evalNatExprRec? (r.getArg! 0) then return Int.negSucc n
  if r.isAppOfArity ``Neg.neg 3 then
    if let some n ← evalNatExprRec? (r.getArg! 2) then return -Int.ofNat n
  throwError "gen_ls_blk: expected Int literal, got {r}"

private meta def targetExprForRelocRec (plE : Expr) (sym : String) (addend : Int) : Expr :=
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

private meta def inRecordRanges (off : Nat) : Bool :=
  (424 ≤ off && off ≤ 1188) ||
  (1272 ≤ off && off ≤ 1688) ||
  (1692 ≤ off && off ≤ 1752) ||
  (1984 ≤ off && off ≤ 2152) ||
  (5860 ≤ off && off ≤ 5872) ||
  (5948 ≤ off && off ≤ 6100) ||
  (6388 ≤ off && off ≤ 6452) ||
  (6836 ≤ off && off ≤ 6864) ||
  (7408 ≤ off && off ≤ 7412) ||
  (7636 ≤ off && off ≤ 7720) ||
  (7812 ≤ off && off ≤ 7924) ||
  (7988 ≤ off && off ≤ 8012) ||
  (9720 ≤ off && off ≤ 9800)

/-- Local override of `gen_ls_blk` for Block `197` restricted to the `Record` instruction ranges. -/
elab "gen_ls_blk_rec " idxStx:num : command => do
    elabCommand (← `(command| open ProofLib.ProgramReflection ProofLib.GenPlacedFetches))
    let idx := idxStx.getNat
    let blkLibId := mkIdent (Name.mkSimple s!"blkLib_{idx}")
    let currNs ← getCurrNamespace
    let fullBlkLibName := currNs ++ blkLibId.getId
    if (← getEnv).contains fullBlkLibName then
      return
    let (blkE, codeLen, symNames, relocData, blockSymMap, extSymSet) ← liftTermElabM do
      let blockSymMap ← collectSymIdxTreeRec (Lean.mkConst ``lsBlockSymIdxTree) {}
      let extsE := Lean.mkConst ``libsignalSessionExterns
      let extElems ← ProofLib.ProgramReflection.listElemsWhnf extsE
      let mut extSymSet : Std.HashSet String := {}
      for eE in extElems do
        let s ← evalStrLitRec eE
        extSymSet := extSymSet.insert s
      let some blkRaw ← lookupIdxTreeExprRec (Lean.mkConst ``lsBlocksTree) idx
        | throwErrorAt idxStx "gen_ls_blk: block index {idx} out of bounds"
      let blkE ← whnfAllRec blkRaw
      let codeE := mkApp (Lean.mkConst ``CodeBlock.code) blkE
      let codeBytes ← ProofLib.ProgramReflection.listElemsWhnf codeE
      let symsE := mkApp (Lean.mkConst ``CodeBlock.symbols) blkE
      let symElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
      let mut symNames : Array String := #[]
      for pE in symElems do
        let pE ← whnfAllRec pE
        let s ← evalStrLitRec (pE.getArg! 2)
        symNames := symNames.push s
      let relocsE := mkApp (Lean.mkConst ``CodeBlock.relocs) blkE
      let relocElems ← ProofLib.ProgramReflection.listElemsWhnf relocsE
      let mut relocData : Array (Nat × Name × String × Int × Expr) := #[]
      for rE in relocElems do
        let rE ← whnfAllRec rE
        let off ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``RelocEntry.off) rE)
        let kE ← whnfAllRec (mkApp (Lean.mkConst ``RelocEntry.kind) rE)
        let some kn := kE.constName? | throwError "gen_ls_blk: bad reloc kind {kE}"
        let sym ← evalStrLitRec (mkApp (Lean.mkConst ``RelocEntry.sym) rE)
        let addend ← evalIntLitRec (mkApp (Lean.mkConst ``RelocEntry.addend) rE)
        relocData := relocData.push (off, kn, sym, addend, rE)
      return (blkE, codeBytes.size, symNames, relocData, blockSymMap, extSymSet)

    let nWords := codeLen / 4
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
          via_placement $blkPlId:ident $blkPlaceableId:ident
          [424 → 1188, 1272 → 1688, 1692 → 1752, 1984 → 2152,
           5860 → 5872, 5948 → 6100, 6388 → 6452, 6836 → 6864,
           7408 → 7412, 7636 → 7720, 7812 → 7924, 7988 → 8012, 9720 → 9800]
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
        let paramTy := Lean.mkConst ``LibsignalPlacement
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
          if inRecordRanges off then
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
              let tLam := Expr.lam `a paramTy (targetExprForRelocRec (mkApp plFn (.bvar 0)) sym addend) .instImplicit
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
                  (targetExprForRelocRec (.bvar 0) sym addend)) .default
              let hPlTarget := Expr.lam `pl plTy
                (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                  (targetExprForRelocRec (.bvar 0) sym addend)) .default
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
                let tLam := Expr.lam `a paramTy (targetExprForRelocRec (mkApp plFn (.bvar 0)) sym addend) .instImplicit
                let instOfT ← withLocalDeclD `t bv64 fun tFVar => do
                  let addrT := mkApp2 (Lean.mkConst ``AddrMode.Offset) rnE (mkApp (Lean.mkConst ``lo12Of) tFVar)
                  let someInstT ← whnfAllRec (mkApp4 (Lean.mkConst ``mkLoadStoreInst) scaleE opcE rtE addrT)
                  let instT := someInstT.getArg! 1
                  mkLambdaFVars #[tFVar] instT
                let instLam := Expr.lam `a paramTy
                  (instOfT.beta #[targetExprForRelocRec (mkApp plFn (.bvar 0)) sym addend]) .instImplicit
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
                    (targetExprForRelocRec (.bvar 0) sym addend)) .default
                let hPlTarget := Expr.lam `pl plTy
                  (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                    (targetExprForRelocRec (.bvar 0) sym addend)) .default
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
                  (mkApp hInstOfT (targetExprForRelocRec (mkApp plFn (.bvar 0)) sym addend)) .instImplicit
                let prf := mkAppN (Lean.mkConst ``fetch_rebase_ldstLo12_of_tree [.succ .zero])
                  #[paramTy, progFn, plFn, libE, treeE, nWordsE, offE, rE, scaleE, tLam, instLam, wE,
                    hprogE, placeableFn, codeEqE, sizeEqE, hltE, hrE, hkE, hwdE, hscaleE, hw1E, hw2E,
                    hTE, hinstE]
                let ty ← inferType prf
                ProofLib.GenDecodes.addThm thmName ty prf
                Term.applyAttributes thmName #[{ name := `simp }, { name := `arm64_norm }]

    let mut symIdx2 : Nat := 0
    for sym in symNames do
      let suffix := if symIdx2 == 0 then "" else s!"_{symIdx2}"
      symIdx2 := symIdx2 + 1
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
    for (off, _, rsym, _, _) in relocData do
      if inRecordRanges off && !seenRelSyms.contains rsym then
        seenRelSyms := seenRelSyms.insert rsym
        let symLit := Syntax.mkStrLit rsym
        match blockSymMap.get? rsym with
        | some j =>
          let resShort := Name.mkSimple s!"ls_resolve_blk_{j}"
          let fnShort := Name.mkSimple s!"ls_fnAddr_blk_{j}"
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
        | none => pure ()

    liftTermElabM do
      setIrreducibleAttribute fullBlkPCName

set_option maxHeartbeats 16000000 in
gen_ls_blk_rec 197

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_rodata_decrypt_signal (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "libsignal_session:.rodata.session_message_decrypt_signal" =
      pl.ρ "libsignal_session:.rodata.session_message_decrypt_signal" :=
  ls_resolve_data (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_rodata_lanon42 (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "libsignal_session:.rodata..Lanon.43" =
      pl.ρ "libsignal_session:.rodata..Lanon.43" :=
  ls_resolve_data (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_rodata_lanon39 (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "libsignal_session:.rodata..Lanon.40" =
      pl.ρ "libsignal_session:.rodata..Lanon.40" :=
  ls_resolve_data (by decide +kernel)

end CryptoVerification.LibsignalTripleRatchet.Record
