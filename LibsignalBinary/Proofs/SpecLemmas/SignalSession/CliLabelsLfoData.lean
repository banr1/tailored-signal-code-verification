/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import ProofLib.Placed.LabelsInterned
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection.IdxTree
meta import ProofLib.Placed.LabelsInterned
meta import Lean

@[expose] public section

set_option autoImplicit false

/-!
# Data-Slice Byte, Metadata, and Relocation Certificate Checks

**Checked by Lean.** Proves `cliLabelsLfo_dbytes_ok`, `cliLabelsLfo_dmeta_ok`, and
`cliLabelsLfo_drelocs_ok` over `libsignalSessionLib.data` against the interned `IdxTree`
certificate in `CliLabelsLfoCert`, pre-indexing `.object` symbol `(si, value, size)` triples per
object via `collectObjTriples`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoData

open Arm64.Obj Arm64.Obj.LabelsInterned
open ProofLib.ProgramReflection
open Lean Elab Command
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_N cliLabelsLfo_objsTree cliLabelsLfo_iLib cliLabelsLfo_bOTree
   cliLabelsLfo_dOTree cliLabelsLfo_symRole cliLabelsLfo_rawSummary cliLabelsLfo_rawClaimed
   cliLabelsLfo_dataGroups)

private def collectObjTriples : IdxTree ISym → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | .empty, acc => acc
  | .leaf sy, acc =>
    match sy.sec with
    | .sec si =>
      if (sy.kind == .object) && (sy.rawId != 0) then
        (si, sy.value, sy.size) :: acc
      else acc
    | _ => acc
  | .node _ l r, acc => collectObjTriples l (collectObjTriples r acc)

private def noCoveringTriple (si start len : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (s, v, z) :: rest =>
    !((s == si) && (v == start) && (z == len)) && noCoveringTriple si start len rest

private theorem symSec_sec_beq (s si : Nat) :
    (SymSec.sec s == SymSec.sec si) = (s == si) := by
  cases h : (s == si) <;> simp_all

private theorem noCoveringTriple_collectObjTriples (si start len : Nat) :
    ∀ (t : IdxTree ISym) (acc : List (Nat × Nat × Nat)),
      noCoveringTriple si start len (collectObjTriples t acc) =
        ((t.all fun sy =>
          !((sy.kind == .object) && (sy.sec == .sec si) &&
            (sy.value == start) && (sy.size == len) && (sy.rawId != 0))) &&
         noCoveringTriple si start len acc)
  | .empty, acc => by simp [collectObjTriples, IdxTree.all]
  | .leaf sy, acc => by
    simp only [collectObjTriples, IdxTree.all]
    cases sy.sec <;> cases sy.kind <;> cases (sy.rawId != 0) <;>
      simp [noCoveringTriple, symSec_sec_beq]
  | .node _ l r, acc => by
    simp [collectObjTriples, IdxTree.all,
      noCoveringTriple_collectObjTriples si start len l,
      noCoveringTriple_collectObjTriples si start len r, Bool.and_assoc]

private def checkDataSlicesMetaFastB (N : Nat) (objsTree : IdxTree IObj)
    (triplesTree : IdxTree (List (Nat × Nat × Nat))) (dataTree : IdxTree IData)
    (dOTree : IdxTree SliceOrigin) (rawClaimed : IdxTree Bool) : Bool :=
  IdxTree.allIdx (fun di d =>
    match dOTree.get? di with
    | none => false
    | some o =>
      match objsTree.get? o.oi, triplesTree.get? o.oi with
      | some io, some triples =>
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
            noCoveringTriple o.si o.start o.len triples
      | _, _ => false) 0 dataTree

private theorem allIdx_congr {α : Type} {p q : Nat → α → Bool}
    (hpq : ∀ i x, p i x = q i x) :
    ∀ (t : IdxTree α) (base : Nat), t.allIdx p base = t.allIdx q base
  | .empty, _ => rfl
  | .leaf x, base => hpq base x
  | .node sz l r, base => by
    simp [IdxTree.allIdx, allIdx_congr hpq l base, allIdx_congr hpq r (base + sz)]

private theorem checkDataSlicesMetaB_eq_fast (N : Nat) (objsTree : IdxTree IObj)
    (dataTree : IdxTree IData) (dOTree : IdxTree SliceOrigin) (rawClaimed : IdxTree Bool) :
    checkDataSlicesMetaB N objsTree dataTree dOTree rawClaimed =
      checkDataSlicesMetaFastB N objsTree
        (objsTree.map fun io => collectObjTriples io.symbols [])
        dataTree dOTree rawClaimed := by
  unfold checkDataSlicesMetaB checkDataSlicesMetaFastB
  apply allIdx_congr
  intro di d
  cases dOTree.get? di with
  | none => rfl
  | some o =>
    dsimp only
    rw [IdxTree.get?_map]
    cases objsTree.get? o.oi with
    | none => rfl
    | some io =>
      dsimp only [Option.map]
      cases io.sections.get? o.si with
      | none => rfl
      | some _ =>
        dsimp only
        cases d.covWit with
        | some _ => rfl
        | none =>
          dsimp only
          have hcov := noCoveringTriple_collectObjTriples o.si o.start o.len io.symbols []
          simp only [noCoveringTriple, Bool.and_true] at hcov
          rw [hcov]

private meta partial def extractIdxTreeLeaves (e : Expr) : Array Expr :=
  let c := e.consumeMData
  if c.isAppOfArity ``IdxTree.empty 1 then #[]
  else if c.isAppOfArity ``IdxTree.leaf 2 then #[c.getArg! 1]
  else if c.isAppOfArity ``IdxTree.node 4 then
    extractIdxTreeLeaves (c.getArg! 2) ++ extractIdxTreeLeaves (c.getArg! 3)
  else #[]

local syntax (name := genCliLabelsLfoObjTriples) "gen_cli_labels_lfo_obj_triples" : command

@[local command_elab genCliLabelsLfoObjTriples]
private meta def elabGenCliLabelsLfoObjTriples : CommandElab := fun _ => do
  let currNs ← getCurrNamespace
  liftTermElabM do
    let env ← getEnv
    let srcName := `LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert.cliLabelsLfo_objsTree
    let some cinfo := (env.setExporting false).find? srcName
      | throwError "gen_cli_labels_lfo_obj_triples: missing {srcName}"
    let some objsVal := cinfo.value?
      | throwError "gen_cli_labels_lfo_obj_triples: missing value for {srcName}"
    let natTy := Lean.mkConst ``Nat
    let natNatTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natTy
    let tripleTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natNatTy
    let listTripleTy := mkApp (Lean.mkConst ``List [0]) tripleTy
    let treeTy := mkApp (Lean.mkConst ``IdxTree [0]) listTripleTy
    let mkPair (t1 t2 a b : Expr) := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) t1 t2 a b
    let objLeaves := extractIdxTreeLeaves objsVal
    let mut objTripleLists : Array Expr := Array.mkEmpty objLeaves.size
    for ioE in objLeaves do
      let symLeaves := extractIdxTreeLeaves (ioE.getArg! 3)
      let mut triples : Array Expr := #[]
      for syE in symLeaves do
        let rawId := (syE.getArg! 0).rawNatLit?.getD 0
        let kindE := syE.getArg! 4
        let secE := syE.getArg! 5
        if rawId != 0 && kindE.isConstOf ``SymKind.object &&
           secE.isAppOfArity ``SymSec.sec 1 then
          let siE := secE.getArg! 0
          let valE := syE.getArg! 6
          let szE := syE.getArg! 7
          triples := triples.push (mkPair natTy natNatTy siE (mkPair natTy natTy valE szE))
      let listE := triples.foldr
        (fun x acc => mkApp3 (Lean.mkConst ``List.cons [0]) tripleTy x acc)
        (mkApp (Lean.mkConst ``List.nil [0]) tripleTy)
      objTripleLists := objTripleLists.push listE
    let val := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero listTripleTy objTripleLists
    let declName := currNs ++ `cliLabelsLfo_objTriples
    let wasExp := env.isExporting
    modifyEnv (·.setExporting false)
    try
      addDecl (.defnDecl {
        name := declName
        levelParams := []
        type := treeTy
        value := val
        hints := .regular (getMaxHeight env val + 1)
        safety := .safe
      })
      modifyEnv (addNoncomputable · declName)
    finally
      modifyEnv (·.setExporting wasExp)

gen_cli_labels_lfo_obj_triples

private theorem cliLabelsLfo_objTriples_eq :
    cliLabelsLfo_objTriples =
      cliLabelsLfo_objsTree.map (fun io => collectObjTriples io.symbols []) := by
  rfl_kernel

private theorem cliLabelsLfo_dmeta_fast_ok :
    checkDataSlicesMetaFastB cliLabelsLfo_N cliLabelsLfo_objsTree cliLabelsLfo_objTriples
      cliLabelsLfo_iLib.data cliLabelsLfo_dOTree cliLabelsLfo_rawClaimed = true := by
  rfl_kernel

theorem cliLabelsLfo_dbytes_ok :
    Arm64.Obj.LabelsInterned.checkDataGroupsBytesB cliLabelsLfo_objsTree
      cliLabelsLfo_iLib.data cliLabelsLfo_dOTree cliLabelsLfo_dataGroups = true := by
  rfl_kernel

theorem cliLabelsLfo_dmeta_ok :
    Arm64.Obj.LabelsInterned.checkDataSlicesMetaB cliLabelsLfo_N cliLabelsLfo_objsTree
      cliLabelsLfo_iLib.data cliLabelsLfo_dOTree cliLabelsLfo_rawClaimed = true := by
  rw [checkDataSlicesMetaB_eq_fast, ← cliLabelsLfo_objTriples_eq]
  exact cliLabelsLfo_dmeta_fast_ok

theorem cliLabelsLfo_drelocs_ok :
    Arm64.Obj.LabelsInterned.checkAllDataRelocsB cliLabelsLfo_N cliLabelsLfo_objsTree
      cliLabelsLfo_iLib cliLabelsLfo_bOTree cliLabelsLfo_dOTree cliLabelsLfo_symRole
      cliLabelsLfo_rawSummary = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoData
