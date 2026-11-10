/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64
public meta import ProofLib.Placed.Multi
public meta import ProofLib.ProgramReflection
public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenPlacement
public import Arm64
public import GeneratedLean.LibsignalSessionPlacedObj
public import ProofLib.Placed.Multi

/-!
# Mutant Interned `MultiLib` Elaborator

Defines `gen_mutant_ls_interned`, which reflects `CryptoVerification.libsignalSessionMultiLib` into
`lsSharedExterns` and `lsInternedMultiLib` while reusing `lsNames` so `lsInternedMultiLib.names` is
definitionally equal to `lsNames`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenInterned

open Lean Meta Elab Term Command ProofLib.ProgramReflection
open Arm64 Arm64.Obj Arm64.Obj.Interned
open Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenPlacement
  (collectSortedLsNames evalStrLitMut mkListExprMut whnfAllMut)

meta def addNoncompDefMut (nm : Name) (ty val : Expr) : TermElabM Unit := do
  Lean.withExporting (isExporting := true) do
    let env ← getEnv
    addDecl <| Declaration.defnDecl {
      name := nm
      levelParams := []
      type := ty
      value := val
      hints := .regular (getMaxHeight env val + 1)
      safety := .safe
    }
    modifyEnv (addNoncomputable · nm)

syntax "gen_mutant_ls_interned " ident : command

elab_rules : command
  | `(command| gen_mutant_ls_interned $lsNamesId:ident) => liftTermElabM do
    let currNs ← getCurrNamespace
    let lsNamesDeclName ← realizeGlobalConstNoOverloadWithInfo lsNamesId
    let natTy := Lean.mkConst ``Nat

    let sortedNames := collectSortedLsNames
    let mut symMap : Std.HashMap String Nat := {}
    for idx in [:sortedNames.size] do
      symMap := symMap.insert sortedNames[idx]! idx

    let lookupSymIdx (strE : Expr) : MetaM Expr := do
      let s ← evalStrLitMut strE
      let some idx := symMap[s]?
        | throwError "gen_mutant_ls_interned: symbol missing in symMap: {s}"
      return mkNatLit idx

    let internRelocs (relocsListE : Expr) : MetaM Expr := do
      let rElems ← listElemsWhnf relocsListE
      let relocTy := Lean.mkConst ``Arm64.Obj.Interned.Reloc
      let relocMk := Lean.mkConst ``Arm64.Obj.Interned.Reloc.mk
      let mut out : Array Expr := #[]
      for rRaw in rElems do
        let rE ← whnfAllMut rRaw
        let symIdxE ← lookupSymIdx (rE.getArg! 2)
        out := out.push (mkApp5 relocMk (rE.getArg! 0) (rE.getArg! 1) symIdxE (rE.getArg! 3) (rE.getArg! 4))
      return mkListExprMut relocTy out

    let libE ← whnfAllMut (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
    let libNameE := libE.getArg! 0
    let blocksRaw ← listElemsWhnf (libE.getArg! 1)
    let dataRaw ← listElemsWhnf (libE.getArg! 2)
    let exportsRaw ← listElemsWhnf (libE.getArg! 3)
    let exportSymsRaw ← listElemsWhnf (libE.getArg! 4)

    let b0E ← whnfAllMut blocksRaw[0]!
    let extsRaw ← listElemsWhnf (b0E.getArg! 4)
    let mut sharedExtsArr : Array Expr := #[]
    for extStrE in extsRaw do
      sharedExtsArr := sharedExtsArr.push (← lookupSymIdx extStrE)
    let lsSharedExternsNm := currNs ++ `lsSharedExterns
    addNoncompDefMut lsSharedExternsNm (mkApp (Lean.mkConst ``List [Level.zero]) natTy)
      (mkListExprMut natTy sharedExtsArr)
    let sharedExtsConst := Lean.mkConst lsSharedExternsNm

    let prodNatNatTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natTy
    let prodNatNatMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) natTy natTy
    let blkTy := Lean.mkConst ``Arm64.Obj.Interned.Block
    let blkMk := Lean.mkConst ``Arm64.Obj.Interned.Block.mk
    let mut blksArr : Array Expr := #[]
    for bRaw in blocksRaw do
      let bE ← whnfAllMut bRaw
      let codeE := bE.getArg! 0
      let alignE := bE.getArg! 1
      let symsRaw ← listElemsWhnf (bE.getArg! 2)
      let mut symsArr : Array Expr := #[]
      for sRaw in symsRaw do
        let sE ← whnfAllMut sRaw
        let symIdxE ← lookupSymIdx (sE.getArg! 2)
        symsArr := symsArr.push (mkApp2 prodNatNatMk symIdxE (sE.getArg! 3))
      let symsInternedE := mkListExprMut prodNatNatTy symsArr
      let relocsInternedE ← internRelocs (bE.getArg! 3)
      let weakRefsRaw ← listElemsWhnf (bE.getArg! 5)
      let mut weakRefsArr : Array Expr := #[]
      for wStrE in weakRefsRaw do
        weakRefsArr := weakRefsArr.push (← lookupSymIdx wStrE)
      let weakRefsInternedE := mkListExprMut natTy weakRefsArr
      blksArr := blksArr.push
        (mkApp6 blkMk codeE alignE symsInternedE relocsInternedE sharedExtsConst weakRefsInternedE)

    let dataTy := Lean.mkConst ``Arm64.Obj.Interned.Data
    let dataMk := Lean.mkConst ``Arm64.Obj.Interned.Data.mk
    let mut dataArr : Array Expr := #[]
    for dRaw in dataRaw do
      let dE ← whnfAllMut dRaw
      let symIdxE ← lookupSymIdx (dE.getArg! 0)
      let alignE := dE.getArg! 1
      let roE := dE.getArg! 2
      let bytesE := dE.getArg! 3
      let ztE := dE.getArg! 4
      let relocsInternedE ← internRelocs (dE.getArg! 5)
      dataArr := dataArr.push (mkApp6 dataMk symIdxE alignE roE bytesE ztE relocsInternedE)

    let mut exportsArr : Array Expr := #[]
    for expStrE in exportsRaw do
      exportsArr := exportsArr.push (← lookupSymIdx expStrE)

    let mut exportSymsArr : Array Expr := #[]
    for esRaw in exportSymsRaw do
      let esE ← whnfAllMut esRaw
      let kIdxE ← lookupSymIdx (esE.getArg! 2)
      let vIdxE ← lookupSymIdx (esE.getArg! 3)
      exportSymsArr := exportSymsArr.push (mkApp2 prodNatNatMk kIdxE vIdxE)

    let multiLibVal := mkApp6 (Lean.mkConst ``Arm64.Obj.Interned.MultiLib.mk)
      libNameE
      (Lean.mkConst lsNamesDeclName)
      (mkListExprMut blkTy blksArr)
      (mkListExprMut dataTy dataArr)
      (mkListExprMut natTy exportsArr)
      (mkListExprMut prodNatNatTy exportSymsArr)
    addNoncompDefMut (currNs ++ `lsInternedMultiLib) (Lean.mkConst ``Arm64.Obj.Interned.MultiLib)
      multiLibVal

end Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenInterned
