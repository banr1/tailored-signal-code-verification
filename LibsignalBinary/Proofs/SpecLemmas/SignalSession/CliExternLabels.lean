/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import ProofLib.Placed.LabelsInterned
public import ProofLib.ProgramReflection
public meta import Lean
public meta import Arm64
public meta import ProofLib.ProgramReflection
public meta import ProofLib.Placed.LabelsInterned
public meta import GeneratedLean.LibsignalSessionExtractedObj
public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import LibsignalBinary.Specifications.SignalSession.CliLabels

@[expose] public section

set_option autoImplicit false

/-!
# Undefined Extern Label Certificate (`CliExternLabelsUndefined`)

**Checked by Lean.** Proves `cliExternLabelsUndefined : CliExternLabelsUndefined` across
`cliLinkObjs` and `libsignalSessionLib`: for every `b ∈ libsignalSessionLib.blocks` and
`x ∈ b.externs`, `x` occurs in `cliLinkObjs` as an undefined non-local symbol with `.strtab` name
`x`, every non-local symbol in `cliLinkObjs` with `sy.rawName = x` has `sy.sec = .undef`, and no
symbol with `sy.rawName = x` has `sy.kind = .tls`.

Symbol names are interned into a sorted `IdxTree` via `String.ofList` so kernel checking avoids
UTF-8 string comparisons across `.o` symbol tables and code blocks.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternLabels

open Arm64
open ProofLib.ProgramReflection (IdxTree)
open CryptoVerification.SignalSession (CliExternLabelsUndefined cliLinkObjs libsignalSessionLib)

section MetaGenP2a

open Lean Elab Command Meta

private meta def p2aWhnfCtor (ctor : Name) (arity : Nat) (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ctor arity then return e'
  let eAll ← withTransparency .all (whnf e)
  if eAll.isAppOfArity ctor arity then return eAll
  throwError "p2aWhnfCtor: expected {ctor}/{arity}, got {eAll}"

private meta partial def p2aListElems (e : Expr) : MetaM (Array Expr) := do
  let mut cur := e
  let mut out : Array Expr := #[]
  while true do
    let c ← whnf cur
    if c.isAppOfArity ``List.nil 1 then return out
    if c.isAppOfArity ``List.cons 3 then
      out := out.push (c.getArg! 1)
      cur := c.getArg! 2
    else
      let cAll ← withTransparency .all (whnf cur)
      if cAll.isAppOfArity ``List.nil 1 then return out
      if cAll.isAppOfArity ``List.cons 3 then
        out := out.push (cAll.getArg! 1)
        cur := cAll.getArg! 2
      else
        throwError "p2aListElems: expected List, got {cAll}"
  return out

private meta def p2aStrVal (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let e' ← withTransparency .all (whnf e)
  if let .lit (.strVal s) := e' then return s
  throwError "p2aStrVal: expected string literal, got {e'}"

private meta def p2aCharCodeLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then true
    else if b.toNat < a.toNat then false
    else p2aCharCodeLt as bs

private meta def p2aMkList (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) ty)

elab "gen_p2a_interned" : command => do
  let currNs ← getCurrNamespace
  let (numNames, numBlocks) ← liftTermElabM do
    let objEs ← p2aListElems (Lean.mkConst ``CryptoVerification.libsignalSessionExtractedObjs)
    let libC ← p2aWhnfCtor ``Obj.MultiPlacedLib.mk 5
      (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
    let blkEs ← p2aListElems (libC.getArg! 1)
    let b0C ← p2aWhnfCtor ``Obj.CodeBlock.mk 6 blkEs[0]!
    let extEs ← p2aListElems (b0C.getArg! 4)
    let extStrs ← (extEs.mapM p2aStrVal : MetaM (Array String))

    let mut nameSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 8192
    nameSet := nameSet.insert ""
    for s in extStrs do
      nameSet := nameSet.insert s

    let mut rawObjSymEs : Array (Array (String × String × Expr)) := #[]
    for oE in objEs do
      let oC ← p2aWhnfCtor ``Obj.ExtractedObj.mk 4 oE
      let symEs ← p2aListElems (oC.getArg! 2)
      let mut arr : Array (String × String × Expr) := Array.mkEmpty symEs.size
      for syE in symEs do
        let syC ← p2aWhnfCtor ``Obj.RawSym.mk 7 syE
        let rn ← p2aStrVal (syC.getArg! 0)
        let dn ← p2aStrVal (syC.getArg! 1)
        nameSet := nameSet.insert rn
        nameSet := nameSet.insert dn
        arr := arr.push (rn, dn, syC)
      rawObjSymEs := rawObjSymEs.push arr

    let sortedNames := nameSet.toArray.qsort (fun a b => p2aCharCodeLt a.toList b.toList)
    let N := sortedNames.size
    let mut idMap : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity (N * 2)
    for idx in [:N] do
      idMap := idMap.insert sortedNames[idx]! idx
    let idOf (s : String) : Nat := idMap.getD s 0

    let strTy := Lean.mkConst ``String
    let charListTy := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
    let natTy := Lean.mkConst ``Nat
    let iSymTy := Lean.mkConst ``Obj.LabelsInterned.ISym
    let mkTreeTy (t : Expr) := mkApp (Lean.mkConst ``IdxTree [Level.zero]) t

    let namesTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero strTy
      (sortedNames.map mkStrLit)
    let charsTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero charListTy
      (sortedNames.map ProofLib.ProgramReflection.mkStrCharsExpr)

    let mut extIdSet : Std.HashSet Nat := Std.HashSet.emptyWithCapacity (extStrs.size * 2)
    for s in extStrs do
      extIdSet := extIdSet.insert (idOf s)

    let boolTy := Lean.mkConst ``Bool
    let trueE := Lean.mkConst ``Bool.true
    let falseE := Lean.mkConst ``Bool.false
    let mut isExternArr : Array Expr := Array.mkEmpty N
    for idx in [:N] do
      isExternArr := isExternArr.push (if extIdSet.contains idx then trueE else falseE)
    let isExternTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero boolTy isExternArr

    let iSymTreeTy := mkTreeTy iSymTy
    let mut objSymTrees : Array Expr := Array.mkEmpty rawObjSymEs.size
    let mut firstUndefWit : Std.HashMap Nat (Nat × Nat) := Std.HashMap.emptyWithCapacity (extStrs.size * 2)
    let zeroLit := mkRawNatLit 0
    for oi in [:rawObjSymEs.size] do
      let syms := rawObjSymEs[oi]!
      let mut isyms : Array Expr := Array.mkEmpty syms.size
      for si in [:syms.size] do
        let (rn, dn, syC) := syms[si]!
        let rid := idOf rn
        if extIdSet.contains rid && !firstUndefWit.contains rid then
          let secE ← withTransparency .all (whnf (syC.getArg! 2))
          let bindE ← withTransparency .all (whnf (syC.getArg! 6))
          if secE.isConstOf ``Obj.SymSec.undef && !bindE.isConstOf ``Obj.SymBind.local then
            firstUndefWit := firstUndefWit.insert rid (oi, si)
        let isyE := mkAppN (Lean.mkConst ``Obj.LabelsInterned.ISym.mk) #[
          mkRawNatLit rid,
          mkRawNatLit (idOf dn),
          zeroLit,
          syC.getArg! 6,
          syC.getArg! 5,
          syC.getArg! 2,
          syC.getArg! 3,
          syC.getArg! 4
        ]
        isyms := isyms.push isyE
      objSymTrees := objSymTrees.push
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy isyms)
    let objSymsTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTreeTy objSymTrees

    let natPairTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natTy
    let witTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natPairTy
    let mut witExprs : Array Expr := Array.mkEmpty extStrs.size
    for s in extStrs do
      let rid := idOf s
      let some (oi, si) := firstUndefWit[rid]?
        | throwError "gen_p2a_interned: missing undef non-local witness for extern {s}"
      let pair2 := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
        natTy natTy (mkRawNatLit oi) (mkRawNatLit si)
      let triple := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
        natTy natPairTy (mkRawNatLit rid) pair2
      witExprs := witExprs.push triple
    let witsVal := p2aMkList witTy witExprs

    let addD (nm : Name) (ty val : Expr) : MetaM Unit := do
      let env ← getEnv
      addDecl (.defnDecl {
        name := currNs ++ nm
        levelParams := []
        type := ty
        value := val
        hints := .regular (getMaxHeight env val + 1)
        safety := .safe
      })
      modifyEnv (addNoncomputable · (currNs ++ nm))

    addD `p2aNumNames natTy (mkRawNatLit N)
    addD `p2aNumBlocks natTy (mkRawNatLit blkEs.size)
    addD `p2aNamesTree (mkTreeTy strTy) namesTreeVal
    addD `p2aCharsTree (mkTreeTy charListTy) charsTreeVal
    addD `p2aIsExternTree (mkTreeTy boolTy) isExternTreeVal
    addD `p2aObjSymsTree (mkTreeTy iSymTreeTy) objSymsTreeVal
    addD `p2aExternWits (mkApp (Lean.mkConst ``List [Level.zero]) witTy) witsVal
    return (N, blkEs.size)
  let _ := (numNames, numBlocks)

gen_p2a_interned

end MetaGenP2a

private theorem p2a_names_sz : p2aNamesTree.size? = some p2aNumNames := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2a_names_eq :
    p2aNamesTree.toList = p2aCharsTree.toList.map String.ofList := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2a_names_nodup :
    Obj.Interned.namesNodup p2aCharsTree.toList = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2a_objs_syms_eq :
    cliLinkObjs.map Obj.ExtractedObj.symbols =
      p2aObjSymsTree.toList.map
        (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2aNamesTree)) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2a_blocks_externs_eq :
    libsignalSessionLib.blocks.map Obj.CodeBlock.externs =
      List.replicate p2aNumBlocks
        (p2aExternWits.map (fun w => Obj.LabelsInterned.symAt p2aNamesTree w.1)) := by
  open ProofLib.ProgramReflection in rfl_kernel

private noncomputable def p2aWitOk (w : Nat × Nat × Nat) : Bool :=
  Nat.blt w.1 p2aNumNames &&
  (p2aIsExternTree.get? w.1 == some true) &&
  match p2aObjSymsTree.get? w.2.1 with
  | none => false
  | some t =>
    match t.get? w.2.2 with
    | none => false
    | some isy =>
      Nat.beq isy.rawId w.1 && (isy.sec == .undef) && (isy.bind != .local)

private noncomputable def p2aSymOk (isy : Obj.LabelsInterned.ISym) : Bool :=
  Nat.blt isy.rawId p2aNumNames &&
  match p2aIsExternTree.get? isy.rawId with
  | some true =>
    (if isy.bind != .local then isy.sec == .undef else true) && (isy.kind != .tls)
  | _ => true

private noncomputable def p2aCheckB : Bool :=
  p2aExternWits.all p2aWitOk &&
  p2aObjSymsTree.all (fun t => t.all p2aSymOk)

private theorem p2aCheckB_ok : p2aCheckB = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2a_sym_props_of_mem
    (hnd : p2aNamesTree.toList.Nodup)
    (hall_objs : ∀ t ∈ p2aObjSymsTree.toList, t.all p2aSymOk = true)
    {extId : Nat} (hext_lt : extId < p2aNumNames)
    (hext_tree : p2aIsExternTree.get? extId = some true)
    {o : Obj.ExtractedObj} (ho : o ∈ cliLinkObjs)
    {sy : Obj.RawSym} (hsy : sy ∈ o.symbols)
    (hraw : sy.rawName = Obj.LabelsInterned.symAt p2aNamesTree extId) :
    (sy.bind ≠ .local → sy.sec = .undef) ∧ sy.kind ≠ .tls := by
  have ho_map :
      o.symbols ∈
        p2aObjSymsTree.toList.map
          (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2aNamesTree)) := by
    rw [← p2a_objs_syms_eq]
    exact List.mem_map_of_mem ho
  obtain ⟨t, ht_mem, ht_eq⟩ := List.mem_map.mp ho_map
  rw [← ht_eq] at hsy
  obtain ⟨isy, hisy_mem, rfl⟩ := List.mem_map.mp hsy
  have ht_ok := hall_objs t ht_mem
  rw [IdxTree.all_eq_toList_all] at ht_ok
  have hisy_ok : p2aSymOk isy = true := List.all_eq_true.mp ht_ok isy hisy_mem
  unfold p2aSymOk at hisy_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hisy_ok with ⟨hisy_lt_b, hisy_ext⟩
  have hisy_lt : isy.rawId < p2aNumNames := Obj.Interned.blt_iff.mp hisy_lt_b
  have hid_eq : isy.rawId = extId :=
    Obj.LabelsInterned.symAt_inj p2a_names_sz hnd hisy_lt hext_lt hraw
  rw [hid_eq, hext_tree] at hisy_ext
  dsimp only at hisy_ext
  rcases Eq.mp (Bool.and_eq_true _ _) hisy_ext with ⟨hsec_chk, hkind_chk⟩
  refine ⟨fun hbind => ?_, bne_iff_ne.mp hkind_chk⟩
  have hbn : (isy.bind != .local) = true := bne_iff_ne.mpr hbind
  rw [hbn] at hsec_chk
  simp only [↓reduceIte] at hsec_chk
  exact beq_iff_eq.mp hsec_chk

/-- Every extern of `libsignalSessionLib` is referenced in `cliLinkObjs` as an undefined non-local
symbol with that `.strtab` name, is never defined non-locally in `cliLinkObjs`, and has no `STT_TLS`
symbol of that name in `cliLinkObjs`. -/
theorem cliExternLabelsUndefined : CliExternLabelsUndefined := by
  have hnd : p2aNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2a_names_eq p2a_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2aCheckB_ok with ⟨hwits_b, htree_b⟩
  have hwits : ∀ w ∈ p2aExternWits, p2aWitOk w = true := List.all_eq_true.mp hwits_b
  rw [IdxTree.all_eq_toList_all] at htree_b
  have hall_objs : ∀ t ∈ p2aObjSymsTree.toList, t.all p2aSymOk = true :=
    List.all_eq_true.mp htree_b
  intro b hb x hx
  have hb_mem : b.externs ∈ libsignalSessionLib.blocks.map Obj.CodeBlock.externs :=
    List.mem_map_of_mem hb
  rw [p2a_blocks_externs_eq] at hb_mem
  rw [List.eq_of_mem_replicate hb_mem, List.mem_map] at hx
  obtain ⟨w, hw_mem, rfl⟩ := hx
  have hw := hwits w hw_mem
  unfold p2aWitOk at hw
  rcases Eq.mp (Bool.and_eq_true _ _) hw with ⟨hw12, hw3⟩
  rcases Eq.mp (Bool.and_eq_true _ _) hw12 with ⟨hext_lt_b, hext_tree_b⟩
  have hext_lt : w.1 < p2aNumNames := Obj.Interned.blt_iff.mp hext_lt_b
  have hext_tree : p2aIsExternTree.get? w.1 = some true := beq_iff_eq.mp hext_tree_b
  cases hget_o : p2aObjSymsTree.get? w.2.1 with
  | none => rw [hget_o] at hw3; cases hw3
  | some t0 =>
    rw [hget_o] at hw3
    dsimp only at hw3
    cases hget_s : t0.get? w.2.2 with
    | none => rw [hget_s] at hw3; cases hw3
    | some isy0 =>
      rw [hget_s] at hw3
      dsimp only at hw3
      rcases Eq.mp (Bool.and_eq_true _ _) hw3 with ⟨hw3a, hbind0_b⟩
      rcases Eq.mp (Bool.and_eq_true _ _) hw3a with ⟨hraw0_b, hsec0_b⟩
      have hraw0 : isy0.rawId = w.1 := Nat.eq_of_beq_eq_true hraw0_b
      have hsec0 : isy0.sec = .undef := beq_iff_eq.mp hsec0_b
      have hbind0 : isy0.bind ≠ .local := bne_iff_ne.mp hbind0_b
      have ht0_mem : t0 ∈ p2aObjSymsTree.toList := IdxTree.mem_toList_of_get? hget_o
      have hisy0_mem : isy0 ∈ t0.toList := IdxTree.mem_toList_of_get? hget_s
      have hmap0 :
          t0.toList.map (Obj.LabelsInterned.ISym.toRawSym p2aNamesTree) ∈
            cliLinkObjs.map Obj.ExtractedObj.symbols := by
        rw [p2a_objs_syms_eq]
        exact List.mem_map_of_mem ht0_mem
      obtain ⟨o0, ho0, ho0_syms⟩ := List.mem_map.mp hmap0
      have hsy0_mem : isy0.toRawSym p2aNamesTree ∈ o0.symbols := by
        rw [ho0_syms]
        exact List.mem_map_of_mem hisy0_mem
      refine ⟨⟨o0, ho0, isy0.toRawSym p2aNamesTree, hsy0_mem,
        congrArg (Obj.LabelsInterned.symAt p2aNamesTree) hraw0, hsec0, hbind0⟩,
        fun o ho sy hsy hraw hbind =>
          (p2a_sym_props_of_mem hnd hall_objs hext_lt hext_tree ho hsy hraw).1 hbind,
        fun o ho sy hsy hraw =>
          (p2a_sym_props_of_mem hnd hall_objs hext_lt hext_tree ho hsy hraw).2⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternLabels
