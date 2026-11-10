/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.AdrpLdst
public meta import Lean
public meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# Plain `ADRP` and `:lo12:` Load/Store Lemmas for Placed Libraries

Provides `gen_placed_odd_sites` and its supporting rules for relocated sites that
`gen_placed_fetches` skips: standalone `ADRP Xd, sym+k` instructions (`adrpHi21` not starting a
relaxable `ADRP`+`ADD` pair) and scaled GPR `:lo12:` loads/stores (`ldst{8,16,32,64}Lo12`).

Given `gen_placed_odd_sites <P> <lib> <tree> <hcode> <hsize> via_placement <plOf> <hPOf> [ranges]`
with `P a = lib.program (plOf a)` and `hPOf a : lib.Placeable (plOf a)`, each offset in `ranges`
elaborates either:
- `P_pairStep_0x<off>` at a plain `ADRP` site (`Xd ≠ X31`), stepping `Xd` to `pageOf T` for the
  pair-step hook (`ProofLib.SepLogic.WP.PairStep`); or
- `@[simp, arm64_norm] P_rebase_fetch_0x<off>` at a scaled GPR `:lo12:` load/store, fetching an
  instruction addressing `[Xn, #lo12Of T]` for every base `b`, so `pageOf_add_lo12Of` folds
  `pageOf T + lo12Of T` back to `T`.
-/

namespace ProofLib.GenPlacedFetches

open Arm64 Arm64.Obj ProofLib.ProgramReflection

@[expose] public section

/-- An `ADRP` site whose next word has no relocation does not start a relaxable pair. -/
theorem relaxableAt_false_of_next_none {blk : CodeBlock} {off : Nat}
    (h : blk.relocAt? (off + 4) = none) : blk.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt
  rw [h]
  cases blk.relocAt? off <;> rfl

/-- `relaxableAt off = false` from the two relocations and the two words, when the pair check
    fails (the words can come from `wordAt_of_getQuad?`). -/
theorem relaxableAt_false_of_words {blk : CodeBlock} {off : Nat} {r1 r2 : RelocEntry}
    {w0 w1 : BitVec 32} (h1 : blk.relocAt? off = some r1) (h2 : blk.relocAt? (off + 4) = some r2)
    (hw0 : blk.wordAt off = w0) (hw1 : blk.wordAt (off + 4) = w1)
    (hchk : (r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.sym == r2.sym &&
      r1.addend == r2.addend && isAdrpWord w0 && isAddImm64Word w1 &&
      (w0 &&& 0x1f#32) == (w1 &&& 0x1f#32) && ((w1 >>> 5) &&& 0x1f#32) == (w0 &&& 0x1f#32) &&
      (w0 &&& 0x1f#32) != 0x1f#32) = false) :
    blk.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt
  rw [h1, h2, hw0, hw1]
  exact hchk

/-- `PlacedLib.sepWP_rebase_adrpPlain` for `prog.rebase b X` with `prog = lib.program pl`, in the
    argument order of a generated `P_pairStep_0x<off>` lemma: the site facts (decided from the
    library), then `hb : b = pl.base`, then the facts the pair-step hook discharges. `hT` may use
    `hb` (a block-symbol target is written `b + symOff`). -/
theorem sepWP_rebase_adrpPlain_site {lib : PlacedLib} {prog : Program} {pl : Placement}
    {b : BitVec 64} {X : String → Option (State → State)} {off off4 : Nat} {r : RelocEntry}
    {w : BitVec 32} {rd : BitVec 5} {T : BitVec 64}
    (hprog : prog = lib.program pl) (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .adrpHi21)
    (hnrel : lib.text.relaxableAt off = false) (hwd : lib.text.wordAt off = w)
    (hw : w &&& 0x9f000000#32 = 0x90000000#32) (hrd : w.extractLsb' 0 5 = rd)
    (hrd31 : rd ≠ 31#5) (h4 : off + 4 = off4)
    (hh0 : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hT : b = pl.base → lib.text.target pl r = T)
    (hb : b = pl.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP (prog.rebase b X) tgt
      ((s.writeReg64 (.gpr rd) (pageOf T)).setPC (b + BitVec.ofNat 64 off4)) P post oom) :
    SepWP (prog.rebase b X) tgt s P post oom := by
  subst hprog
  exact PlacedLib.sepWP_rebase_adrpPlain hP hb hr hk hnrel hwd hw hrd hrd31 (hT hb) h4 hh0 hpc
    hrun hnext

-- Intentional literal `.Offset` in the conclusion: this is the generated-lemma shape.
set_option linter.literalFetch false in
/-- `PlacedLib.fetch_rebase_ldstLo12_of_placeable` for `prog.rebase b X` with
    `prog = lib.program pl`, for every base `b`, with the instruction written
    `mkInst (.Offset rn (lo12Of T))`: the shape of a generated `P_rebase_fetch_0x<off>` lemma at a
    scaled `:lo12:` load/store site. -/
theorem fetch_rebase_ldstLo12_site {lib : PlacedLib} {prog : Program} {pl : Placement}
    {b : BitVec 64} {X : String → Option (State → State)} {off scale : Nat} {r : RelocEntry}
    {w : BitVec 32} {rn : Reg} {mkInst : AddrMode → Instr} {T : BitVec 64}
    (hprog : prog = lib.program pl) (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : ldstLo12Scale r.kind = some scale)
    (hh : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hwd : lib.text.wordAt off = w) (hscale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hrn : Reg.fromSPBits (w.extractLsb' 5 5) = rn)
    (hinst : ∀ am : AddrMode,
      mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5)) am =
        some (mkInst am))
    (hT : lib.text.target pl r = T) :
    (prog.rebase b X).fetch (b + BitVec.ofNat 64 off) = some (mkInst (.Offset rn (lo12Of T))) := by
  subst hprog
  exact PlacedLib.fetch_rebase_ldstLo12_of_placeable hP hr hk hh hwd hscale hw1 hw2 hT
    (by rw [hrn]; exact hinst _)

end

syntax (name := genPlacedOddSitesStx)
  "gen_placed_odd_sites " ident ident ident ident ident " via_placement " ident ident
    " [" decodeRange,* "]" : command

public meta section

open Lean Meta Elab Term Command

private def osRefl (ty v : Expr) : Expr := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) ty v

private def osBv (w k : Nat) : Expr := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit k)

private def osBvTy (w : Nat) : Expr := mkApp (Lean.mkConst ``BitVec) (mkNatLit w)

private def osLdstScale? (kn : Name) : Option Nat :=
  if kn == ``RelocKind.ldst8Lo12 then some 0
  else if kn == ``RelocKind.ldst16Lo12 then some 1
  else if kn == ``RelocKind.ldst32Lo12 then some 2
  else if kn == ``RelocKind.ldst64Lo12 then some 3
  else none

private def osLdstInst? (scale opc rt : Nat) : Option Expr :=
  let rtE := if rt == 31 then Lean.mkConst ``Reg.xzr
    else mkApp (Lean.mkConst ``Reg.gpr) (osBv 5 rt)
  let szE := Lean.mkConst <| match scale with
    | 0 => ``MemWidth.B8 | 1 => ``MemWidth.H16 | 2 => ``MemWidth.W32 | _ => ``MemWidth.X64
  let ldr (rw : Name) (signed : Bool) : Option Expr :=
    some (mkApp4 (Lean.mkConst ``Instr.ldr) (Lean.mkConst rw) szE
      (Lean.mkConst (if signed then ``Bool.true else ``Bool.false)) rtE)
  match scale, opc with
  | _, 0 => some (mkApp2 (Lean.mkConst ``Instr.str) szE rtE)
  | 3, 1 => ldr ``RegWidth.W64 false
  | 3, _ => none
  | _, 1 => ldr ``RegWidth.W32 false
  | 2, 2 => ldr ``RegWidth.W64 true
  | 2, _ => none
  | _, 2 => ldr ``RegWidth.W64 true
  | _, _ => ldr ``RegWidth.W32 true

private def osTargetOk (c : Ctx) (sym : String) (addend : Int) : Bool :=
  addend ≥ 0 && (addend == 0 || !c.symMap.contains sym)

private def osTarget (c : Ctx) (pl rE : Expr) (sym : String) (addend : Int) (bE hbE : Expr) :
    MetaM (Expr × Expr) := do
  let symLit := mkStrLit sym
  let intTy := Lean.mkConst ``Int
  let hsymE := osRefl (Lean.mkConst ``String) symLit
  match c.symMap.get? sym with
  | some symOff =>
    let hsym ← lookupSymProof c sym symLit (← mkAppM ``Option.some #[mkNatLit symOff])
    let T ← mkAppM ``HAdd.hAdd #[bE, osBv 64 symOff]
    let haddend := osRefl intTy (toExpr (0 : Int))
    return (T, mkAppN (Lean.mkConst ``target_of_blockSym)
      #[c.textE, pl, rE, mkNatLit symOff, bE, hsym, haddend, hbE])
  | none =>
    let hsym ← lookupSymProof c sym symLit (← mkAppOptM ``Option.none #[Lean.mkConst ``Nat])
    let rho := mkApp2 (Lean.mkConst ``Placement.ρ) pl symLit
    if addend == 0 then
      let haddend := osRefl intTy (toExpr (0 : Int))
      return (rho, mkAppN (Lean.mkConst ``target_of_extern_zero)
        #[c.textE, pl, rE, symLit, hsymE, hsym, haddend])
    else
      let k := addend.toNat
      let T ← mkAppM ``HAdd.hAdd #[rho, osBv 64 k]
      let haddend := osRefl intTy (toExpr addend)
      let hk0 := osRefl (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.false)
      return (T, mkAppN (Lean.mkConst ``target_of_extern_pos)
        #[c.textE, pl, rE, symLit, mkNatLit k, hsymE, hsym, haddend, hk0])

private def osAdrpLemma? (c : Ctx) (off : Nat) : MetaM (Option (Expr × Expr)) := do
  let some (_, _, symE, rE) := c.relocMap.get? off | return none
  let sym ← symStringOf symE
  let addend ← addendOf rE
  let w0 ← wordOfTreeVal c.treeVal off
  let rd := w0 % 32
  unless w0 &&& 0x9f000000 == 0x90000000 && rd != 31 do
    logInfo m!"gen_placed_odd_sites: skipping ADRP site {off}: unsupported word {w0}"
    return none
  unless osTargetOk c sym addend do
    logInfo m!"gen_placed_odd_sites: skipping ADRP site {off}: unsupported target {sym} + {addend}"
    return none
  let offE := mkNatLit off
  let off4E := mkNatLit (off + 4)
  let (w0E, hw0) ← wordAtProof c off
  let hr ← relocAtSomeProof c offE rE
  let hnrel? ← match c.relocMap.get? (off + 4) with
    | none =>
      let hnr ← relocAtNoneProof c off4E
      pure (some (mkAppN (Lean.mkConst ``relaxableAt_false_of_next_none) #[c.textE, offE, hnr]))
    | some (_, k2, sym2E, r2E) =>
      let w1 ← wordOfTreeVal c.treeVal (off + 4)
      let sym2 ← symStringOf sym2E
      let addend2 ← addendOf r2E
      let relax := k2 == ``RelocKind.addLo12 && sym2 == sym && addend2 == addend &&
        w1 &&& 0xffc00000 == 0x91000000 && w1 % 32 == rd && (w1 >>> 5) % 32 == rd
      if relax then pure none
      else
        let hr4 ← relocAtSomeProof c off4E r2E
        let (w1E, hw1) ← wordAtProof c (off + 4)
        let hchk := osRefl (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.false)
        pure (some (mkAppN (Lean.mkConst ``relaxableAt_false_of_words)
          #[c.textE, offE, rE, r2E, w0E, w1E, hr, hr4, hw0, hw1, hchk]))
  let some hnrel := hnrel? | return none
  let rdE := osBv 5 rd
  let hk := osRefl (Lean.mkConst ``RelocKind) (Lean.mkConst ``RelocKind.adrpHi21)
  let hw := osRefl (osBvTy 32) (osBv 32 0x90000000)
  let hrd := osRefl (osBvTy 5) rdE
  let hrd31 ← mkDecideProof (mkNot (← mkEq rdE (osBv 5 31)))
  let h4 := osRefl (Lean.mkConst ``Nat) off4E
  let hprogFn ← getHProg c
  let r ← withParams c fun a pl hP? b X => do
    let some hP := hP? | throwError "gen_placed_odd_sites: needs a placeability witness"
    let progE := mkApp (Lean.mkConst c.progName) a
    let hh0 ← hnhOf c pl hP? b X off
    let hbTy ← mkEq b (mkApp (Lean.mkConst ``Placement.base) pl)
    let (T, hT) ← withLocalDeclD `hb' hbTy fun hb' => do
      let (T, prf) ← osTarget c pl rE sym addend b hb'
      return (T, ← mkLambdaFVars #[hb'] prf)
    withLocalDeclD `hb hbTy fun hb => do
      let p := mkAppN (Lean.mkConst ``sepWP_rebase_adrpPlain_site)
        #[c.libE, progE, pl, b, X, offE, off4E, rE, w0E, rdE, T,
          mkApp hprogFn a, hP, hr, hk, hnrel, hw0, hw, hrd, hrd31, h4, hh0, hT, hb]
      return (#[], ← mkForallFVars #[hb] (← inferType p), ← mkLambdaFVars #[hb] p)
  return some r

private def osLdstLemma? (c : Ctx) (off scale : Nat) : MetaM (Option (Expr × Expr)) := do
  let some (_, _, symE, rE) := c.relocMap.get? off | return none
  let sym ← symStringOf symE
  let addend ← addendOf rE
  let w0 ← wordOfTreeVal c.treeVal off
  let opc := (w0 >>> 22) % 4
  let rt := w0 % 32
  let rn := (w0 >>> 5) % 32
  let inst? := osLdstInst? scale opc rt
  unless w0 &&& 0x3f000000 == 0x39000000 && (w0 >>> 30) % 4 == scale &&
      w0 &&& 0xffc00000 != 0xf9800000 && inst?.isSome do
    logInfo m!"gen_placed_odd_sites: skipping load/store site {off}: unsupported word {w0}"
    return none
  let some mkInstE := inst? | return none
  unless osTargetOk c sym addend do
    logInfo m!"gen_placed_odd_sites: skipping load/store site {off}: unsupported target {sym} + {addend}"
    return none
  let offE := mkNatLit off
  let scaleE := mkNatLit scale
  let (w0E, hw0) ← wordAtProof c off
  let hr ← relocAtSomeProof c offE rE
  let natTy := Lean.mkConst ``Nat
  let hk := osRefl (mkApp (Lean.mkConst ``Option [.zero]) natTy)
    (mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy scaleE)
  let hscale := osRefl natTy scaleE
  let hw1 := osRefl (osBvTy 32) (osBv 32 0x39000000)
  let hw2 := osRefl (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.false)
  let rnE := if rn == 31 then Lean.mkConst ``Reg.sp else mkApp (Lean.mkConst ``Reg.gpr) (osBv 5 rn)
  let hrn := osRefl (Lean.mkConst ``Reg) rnE
  let hinst := Lean.mkLambda `am .default (Lean.mkConst ``AddrMode)
    (osRefl ProofLib.GenDecodes.optInstr
      (mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``Instr) (mkApp mkInstE (.bvar 0))))
  let hprogFn ← getHProg c
  let r ← withParams c fun a pl hP? b X => do
    let some hP := hP? | throwError "gen_placed_odd_sites: needs a placeability witness"
    let progE := mkApp (Lean.mkConst c.progName) a
    let hh ← hnhOf c pl hP? b X off
    let baseE := mkApp (Lean.mkConst ``Placement.base) pl
    let (T, hT) ← osTarget c pl rE sym addend baseE (← mkEqRefl baseE)
    let p := mkAppN (Lean.mkConst ``fetch_rebase_ldstLo12_site)
      #[c.libE, progE, pl, b, X, offE, scaleE, rE, w0E, rnE, mkInstE, T,
        mkApp hprogFn a, hP, hr, hk, hh, hw0, hscale, hw1, hw2, hrn, hinst, hT]
    return (#[], ← inferType p, p)
  return some r

private def osMkCtx (prog lib tree hcode hsize plOf hPOf : Ident) : TermElabM Ctx := do
  let progName ← realizeGlobalConstNoOverloadWithInfo prog
  let libName ← realizeGlobalConstNoOverloadWithInfo lib
  let treeName ← realizeGlobalConstNoOverloadWithInfo tree
  let hcodeName ← realizeGlobalConstNoOverloadWithInfo hcode
  let hsizeName ← realizeGlobalConstNoOverloadWithInfo hsize
  let viaPl := some (Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo plOf),
    Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo hPOf))
  let libE := Lean.mkConst libName
  let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
  let hsizeTy ← inferType (Lean.mkConst hsizeName)
  let some (_, _, someN) := hsizeTy.eq? | throwError "gen_placed_odd_sites: bad {hsizeName}"
  let nE := someN.appArg!
  let n ← ProofLib.GenDecodes.natOf nE
  let progTy ← inferType (Lean.mkConst progName)
  let .forallE _ paramTy _ paramBi := progTy
    | throwError "gen_placed_odd_sites: {progName} must take one parameter"
  let env0 ← getEnv
  let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
  let (shRtNm, shRtEqNm, shRtWfNm) := sharedRelocTreeNames progName
  let sharedRtVal? : Option Expr :=
    match env0.find? shRtNm, env0.find? shRtEqNm with
    | some rtCi, some eqCi =>
      if rtCi.hasValue && env0.contains shRtWfNm &&
          eqCi.type.eq?.any (fun (_, lhs, _) =>
            lhs == mkApp (Lean.mkConst ``CodeBlock.relocs) textE) then
        rtCi.value?
      else none
    | _, _ => none
  let relocs ← match sharedRtVal? with
    | some rtV => collectRelocsFromTree rtV #[]
    | none => relocEntries libE
  let mut relocMap : Std.HashMap Nat (Nat × Name × Expr × Expr) := {}
  for entry in relocs do
    if !relocMap.contains entry.1 then
      relocMap := relocMap.insert entry.1 entry
  let (shXsNm, shEncNm, shHtblNm, shHeqNm) := sharedSymEncNames progName
  let sharedSymMap? : Option (Std.HashMap String Nat) :=
    match env0.find? shXsNm, env0.find? shEncNm, env0.find? shHtblNm with
    | some xsCi, some encCi, some htblCi =>
      if xsCi.hasValue && encCi.hasValue && env0.contains shHeqNm &&
          htblCi.type.eq?.any (fun (_, lhs, _) =>
            lhs == mkApp (Lean.mkConst ``CodeBlock.symbols) textE) then
        encCi.value?.bind extractSymMapFromEnc?
      else none
    | _, _, _ => none
  let (syms, symMap) ← match sharedSymMap? with
    | some sm => pure (#[], sm)
    | none =>
      let ss ← symbolOffsets libE
      let mut sm : Std.HashMap String Nat := {}
      for (s, o, _) in ss do
        if !sm.contains s then
          sm := sm.insert s o
      pure (ss, sm)
  return { progName := progName, libName := libName, libE := libE
           textE := textE
           treeE := Lean.mkConst treeName, treeVal := treeVal, nE := nE, n := n
           hcodeE := Lean.mkConst hcodeName, hsizeE := Lean.mkConst hsizeName
           relocs := relocs, relocMap := relocMap, syms := syms, symMap := symMap
           viaPl := viaPl, paramTy := paramTy, paramBi := paramBi
           hprogRef := ← IO.mkRef none, hextRef := ← IO.mkRef none
           rtRef := ← IO.mkRef none, symEncRef := ← IO.mkRef none
           symProofCache := ← IO.mkRef {} }

@[command_elab genPlacedOddSitesStx] def elabGenPlacedOddSites : CommandElab := fun stx => do
  match stx with
  | `(gen_placed_odd_sites $prog:ident $lib:ident $tree:ident $hcode:ident $hsize:ident
        via_placement $plOf:ident $hPOf:ident [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let attrStx ← `(Lean.Parser.Term.attrInstance| simp)
    let attrStx2 ← `(Lean.Parser.Term.attrInstance| arm64_norm)
    liftTermElabM do
      let attrs ← elabAttrs #[attrStx, attrStx2]
      let c ← osMkCtx prog lib tree hcode hsize plOf hPOf
      for off in offs do
        if off + 4 > 4 * c.n then
          throwError "gen_placed_odd_sites: offset {off} is out of bounds"
      let pfxStr := c.progName.getString!
      let progNs := c.progName.getPrefix
      for off in offs do
        let some (_, kn, _, _) := c.relocMap.get? off | continue
        if kn == ``RelocKind.adrpHi21 then
          let nm := progNs ++ hexName pfxStr "pairStep" off
          if (← getEnv).contains nm then continue
          if let some (ty, prf) ← osAdrpLemma? c off then
            ProofLib.GenDecodes.addThm nm ty prf
        else if let some scale := osLdstScale? kn then
          let nm := progNs ++ hexName pfxStr "rebase_fetch" off
          if (← getEnv).contains nm then continue
          if let some (ty, prf) ← osLdstLemma? c off scale then
            ProofLib.GenDecodes.addThm nm ty prf
            for a in attrs do Term.applyAttributes nm #[a]
  | _ => throwUnsupportedSyntax

end

end ProofLib.GenPlacedFetches
