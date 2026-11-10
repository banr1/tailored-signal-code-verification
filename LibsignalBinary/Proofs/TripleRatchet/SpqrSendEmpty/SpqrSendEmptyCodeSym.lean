/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.GenPlacedFetches

/-!
# Relocatable Per-Block Symbol Bindings for `TripleRatchet/SpqrSendEmpty`

Per-block symbol bindings and instruction-fetch ranges on the empty-state path for
`spqr::send::<libsignal_session::HookRng>` (block 124) and `spqr::decode_state` (block 325).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open Lean Elab Command Term Meta
open CryptoVerification

private meta def whnfAllSE (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private meta def evalNatExprSE? (e : Expr) : MetaM (Option Nat) := do
  let r ← whnfAllSE e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

private meta partial def lookupIdxTreeExprSE (treeE : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let r ← whnfAllSE treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return none
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    if idx == 0 then return some (r.getArg! 1) else return none
  else if r.isAppOfArity ``IdxTree.node 4 then
    let some leftSz ← evalNatExprSE? (r.getArg! 1)
      | throwError "def_ls_blk_se: invalid leftSz in IdxTree.node"
    if idx < leftSz then
      lookupIdxTreeExprSE (r.getArg! 2) idx
    else
      lookupIdxTreeExprSE (r.getArg! 3) (idx - leftSz)
  else
    throwError "def_ls_blk_se: unexpected IdxTree expression {r}"

elab "def_ls_blk_se " idxStx:num : command => do
  let idx := idxStx.getNat
  let blkLibId := mkIdent (Name.mkSimple s!"blkLib_{idx}")
  let currNs ← getCurrNamespace
  let fullBlkLibName := currNs ++ blkLibId.getId
  let (blkE, codeLen) ← liftTermElabM do
    let some blkRaw ← lookupIdxTreeExprSE (Lean.mkConst ``lsBlocksTree) idx
      | throwErrorAt idxStx "def_ls_blk_se: block index {idx} out of bounds"
    let blkE ← whnfAllSE blkRaw
    let codeE := mkApp (Lean.mkConst ``CodeBlock.code) blkE
    let codeBytes ← ProofLib.ProgramReflection.listElemsWhnf codeE
    return (blkE, codeBytes.size)
  let nWords := codeLen / 4
  let blkLibEqId := mkIdent (Name.mkSimple s!"blkLib_eq_{idx}")
  let blkExternsEqId := mkIdent (Name.mkSimple s!"blkExterns_eq_{idx}")
  let blkPlId := mkIdent (Name.mkSimple s!"blkPl_{idx}")
  let blkPlRhoId := mkIdent (Name.mkSimple s!"blkPl_{idx}_ρ")
  let blkPlaceableId := mkIdent (Name.mkSimple s!"blkPlaceable_{idx}")
  let blkPCId := mkIdent (Name.mkSimple s!"blkPC_{idx}")
  let lsProgId := mkIdent (Name.mkSimple s!"lsProg_{idx}")
  let instIsLsId := mkIdent (Name.mkSimple s!"instIsLsBlockProg_{idx}")
  let blkTextProgId := mkIdent (Name.mkSimple s!"blkTextProg_{idx}")
  let blkTreeId := mkIdent (Name.mkSimple s!"blkTree_{idx}")
  let blkCodeEqId := mkIdent (Name.mkSimple s!"blkCodeEq_{idx}")
  let blkTreeSizeId := mkIdent (Name.mkSimple s!"blkTreeSize_{idx}")
  let nWordsLit := Syntax.mkNumLit (toString nWords)
  liftTermElabM do
    let val := mkApp4 (Lean.mkConst ``PlacedLib.mk)
      (mkStrLit "libsignalSession")
      blkE
      (Lean.mkConst ``libsignalSessionData)
      (mkApp (Lean.mkConst ``MultiPlacedLib.exports) (Lean.mkConst ``libsignalSessionMultiLib))
    withExporting <| addAndCompile (.defnDecl {
      name := fullBlkLibName, levelParams := [], type := Lean.mkConst ``PlacedLib,
      value := val, hints := .regular 0, safety := .safe })
  elabCommand (← `(command|
    theorem $blkLibEqId:ident : $blkLibId:ident = libsignalSessionLib.blockLib $idxStx:num := rfl))
  elabCommand (← `(command|
    theorem $blkExternsEqId:ident : ($blkLibId:ident).text.externs = libsignalSessionExterns := rfl))
  elabCommand (← `(command|
    abbrev $blkPlId:ident [LibsignalPlacement] : Placement :=
      libsignalSessionLib.blockPlacement lsmpl $idxStx:num))
  elabCommand (← `(command|
    @[simp, arm64_norm, wp_norm]
    theorem $blkPlRhoId:ident [LibsignalPlacement] (sym : String) :
        ($blkPlId:ident).ρ sym = libsignalSessionLib.resolve lsmpl sym := rfl))
  elabCommand (← `(command|
    theorem $blkPlaceableId:ident [LibsignalPlacement] : ($blkLibId:ident).Placeable $blkPlId:ident :=
      Eq.mp (congrArg (PlacedLib.Placeable · $blkPlId:ident) ($blkLibEqId:ident).symm)
        (LibsignalPlacement.block_placeable $idxStx:num (by decide) (by decide))))
  elabCommand (← `(command|
    noncomputable def $blkPCId:ident [LibsignalPlacement] : Program :=
      ($blkLibId:ident).program $blkPlId:ident))
  elabCommand (← `(command|
    noncomputable abbrev $lsProgId:ident [LibsignalPlacement] (H : LibsignalHooks) : Program :=
      ($blkPCId:ident).rebase ($blkPlId:ident).base H))
  elabCommand (← `(command|
    instance $instIsLsId:ident [LibsignalPlacement] (H : LibsignalHooks) :
        IsLsBlockProg (($blkPCId:ident).rebase ($blkPlId:ident).base H) $idxStx:num H where
      eq_blockProgram := prog_eq_blockProgram $blkLibEqId:ident
      externs_eq := Eq.trans (congrArg (fun b : PlacedLib => b.text.externs) ($blkLibEqId:ident).symm) $blkExternsEqId:ident))
  elabCommand (← `(command|
    def $blkTextProgId:ident : Program := { code := ($blkLibId:ident).text.code }))
  elabCommand (← `(command|
    def $blkTreeId:ident : WordTree := word_tree_of% $blkTextProgId:ident))
  elabCommand (← `(command|
    theorem $blkCodeEqId:ident : ($blkLibId:ident).text.code = ($blkTreeId:ident).toBytes := rfl))
  elabCommand (← `(command|
    theorem $blkTreeSizeId:ident : ($blkTreeId:ident).checkSize? = some $nWordsLit:num := by decide +kernel))

def_ls_blk_se 124
gen_placed_fetches blkPC_124 blkLib_124 blkTree_124 blkCodeEq_124 blkTreeSize_124
  via_placement blkPl_124 blkPlaceable_124
  [0 → 104, 136 → 220, 4608 → 4616, 4632 → 4664]

attribute [irreducible] blkPC_124

def_ls_blk_se 325
gen_placed_fetches blkPC_325 blkLib_325 blkTree_325 blkCodeEq_325 blkTreeSize_325
  via_placement blkPl_325 blkPlaceable_325
  [0 → 44, 1604 → 1624, 2500 → 2528]

attribute [irreducible] blkPC_325

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_325 (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "spqr::decode_state" = pl.base 325 :=
  ls_resolve_block (by decide +kernel)

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
