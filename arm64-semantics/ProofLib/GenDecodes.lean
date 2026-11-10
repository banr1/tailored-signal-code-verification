/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.Meta.ToExpr
public import ProofLib.ProgramReflection
public import ProofLib.LiteralFetchLint
public meta import Lean
public meta import ProofLib.Meta.ToExpr
public meta import ProofLib.LiteralFetchLint
public meta import Arm64.Trusted.ISA.Syntax
public meta import Arm64.Trusted.ISA.Decode
public meta import ProofLib.VCGen
import Arm64.Trusted.Spec.SepLogic

/-!
# Decode and Fetch Lemma Generation

Command elaborators generating per-instruction decode and fetch theorems from a `WordTree` code
definition: `gen_decodes` emits `WordTree.fetchDecodeAt` equations proved by `Eq.refl`,
`gen_fetches` adds `@[simp, arm64_norm]` concrete and rebased `Program.fetch` theorems, and
`gen_concrete_fetches` emits concrete-base fetch theorems in $O(\log N)$ per instruction.
-/

namespace ProofLib.GenDecodes

open Lean Meta Elab Term Command Arm64 ProofLib.ProgramReflection

@[expose] public section

/-- Rewrite `prog.fetch (b + 0#64) = some inst` to `prog.fetch b = some inst` for the offset-0
    base-fetch corollary `<prefix>_rebase_fetch_base`. -/
theorem fetch_rebase_base_of_zero {prog : Program} {b : BitVec 64} {inst : Instr}
    (h : prog.fetch (b + 0#64) = some inst) :
    prog.fetch b = some inst := by
  simpa using h

end

public meta section

private def markGeneratedFetchDecode (declName : Name) : MetaM Unit :=
  modifyEnv fun env => ProofLib.LiteralFetchLint.generatedFetchDecodeExt.addEntry env declName

private partial def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? (e.getArg! 1) else none

private def whnfAll (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

partial def natOf (e : Expr) : MetaM Nat := do
  if let some n := natLit? e then return n
  let e' ← whnfAll e
  if let some n := natLit? e' then return n
  let r ← withTransparency .all (reduce e)
  match natLit? r with
  | some n => return n
  | none => throwError "gen_decodes: expected a numeral, got {e}"

partial def byteOf (e : Expr) : MetaM Nat := do
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some n := natLit? (e.getArg! 1) then return n % 256
  let e' ← whnfAll e
  if e'.isAppOfArity ``BitVec.ofNat 2 then
    return (← natOf (e'.getArg! 1)) % 256
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    let fin ← whnfAll (e'.getArg! 1)
    if fin.isAppOfArity ``Fin.mk 3 then return (← natOf (fin.getArg! 1)) % 256
  throwError "gen_decodes: expected a byte, got {e}"

partial def quadAt (t : Expr) (j : Nat) : MetaM (Nat × Nat × Nat × Nat) := do
  let t ← if t.isAppOfArity ``WordTree.node 3 || t.isAppOfArity ``WordTree.leaf 4 then pure t
    else whnfAll t
  if t.isAppOfArity ``WordTree.node 3 then
    let lw ← natOf (t.getArg! 0)
    if j < lw then quadAt (t.getArg! 1) j else quadAt (t.getArg! 2) (j - lw)
  else if t.isAppOfArity ``WordTree.leaf 4 then
    unless j == 0 do throwError "gen_decodes: word index out of range"
    return (← byteOf (t.getArg! 0), ← byteOf (t.getArg! 1), ← byteOf (t.getArg! 2),
      ← byteOf (t.getArg! 3))
  else throwError "gen_decodes: word index out of range (or not a `WordTree` literal)"

def treeValueOf (tree : Name) : MetaM Expr := do
  let some ci := (← getEnv).find? tree | throwError "gen_decodes: unknown constant `{tree}`"
  let some v := ci.value? (allowOpaque := true)
    | throwError "gen_decodes: `{tree}` has no definition"
  return v

def quadOfTreeVal (treeVal : Expr) (off : Nat) : MetaM (Nat × Nat × Nat × Nat) := do
  unless off % 4 == 0 do throwError "gen_decodes: offset {off} is not 4-byte aligned"
  quadAt treeVal (off / 4)


def decodeAtTreeVal? (treeVal : Expr) (off : Nat) : MetaM (BitVec 32 × Option Instr) := do
  let (b0, b1, b2, b3) ← quadOfTreeVal treeVal off
  let w : BitVec 32 :=
    BitVec.ofNat 8 b3 ++ BitVec.ofNat 8 b2 ++ BitVec.ofNat 8 b1 ++ BitVec.ofNat 8 b0
  return (w, Arm64.decode w)

def normalizeLits (e : Expr) : Expr :=
  e.replace fun s =>
    if s.isAppOfArity ``BitVec.ofNat 2 then
      match s.getArg! 1 with
      | .lit (.natVal n) => some (mkApp2 (mkConst ``BitVec.ofNat) (s.getArg! 0) (mkNatLit n))
      | _ => none
    else none

def foldRegs (e : Expr) : Expr := e

private def binderDoms : Expr → List Expr
  | .forallE _ d b _ => d :: binderDoms b
  | _ => []

partial def foldAliases (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let alias? (dom : Expr) (a : Expr) : Option Expr :=
    match dom, a with
    | .const ab _, .const ac@(.str _ s) us =>
      let cand := Name.str ab s
      if cand != ac && ((env.find? cand).bind (·.value?)).any (·.isConstOf ac) then
        some (mkConst cand us)
      else none
    | _, _ => none
  let rec go (e : Expr) : Expr :=
    if !e.isApp then e else
    let fn := e.getAppFn
    let args := e.getAppArgs.map go
    let doms := match fn with
      | .const c _ => match env.find? c with
        | some (.ctorInfo ci) => binderDoms ci.type
        | _ => []
      | _ => []
    mkAppN fn (args.mapIdx fun i a => (doms[i]?.bind (alias? · a)).getD a)
  return go e

def formatInstrRhs (i : Instr) (raw : Bool := false) : MetaM Expr := do
  let rhs ← if raw then pure (normalizeLits (toExpr (some i)))
    else mkAppM ``Option.some #[← ProofLib.cleanReducedExpr (toExpr i)]
  foldAliases (foldRegs rhs)


/-- Return `(word, some rhs)` when the word at `off` decodes, or `(word, none)` otherwise. -/
def instrRhs? (treeVal : Expr) (off : Nat) (raw : Bool := false) :
    MetaM (BitVec 32 × Option Expr) := do
  let (w, i?) ← decodeAtTreeVal? treeVal off
  match i? with
  | some i => return (w, some (← formatInstrRhs i raw))
  | none => return (w, none)

def optInstr : Expr := mkApp (mkConst ``Option [.zero]) (mkConst ``Instr)

def decodeStmtOf (tree : Name) (off : Nat) (rhs : Expr) : Expr :=
  let lhs := mkApp2 (mkConst ``WordTree.fetchDecodeAt) (mkConst tree) (mkNatLit off)
  mkApp3 (mkConst ``Eq [.succ .zero]) optInstr lhs rhs

def addThm (n : Name) (ty val : Expr) : MetaM Unit := do
  addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := val })
  markGeneratedFetchDecode n

private def hex8 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  let pad := List.replicate (8 - digits.length) '0'
  String.ofList (pad ++ digits)

end

declare_syntax_cat decodeRange (behavior := both)
syntax num : decodeRange
syntax num " → " num : decodeRange
syntax &"raw " num : decodeRange

syntax (name := genDecodesStx)
  declModifiers "gen_decodes " ident ident " [" decodeRange,* "]" : command

/-- `gen_fetches <code> <prefix> [<textEnd>] [<root>] [ranges]`. -/
syntax (name := genFetchesStx)
  "gen_fetches " ident ident (num)? (ident)? " [" decodeRange,* "]" : command

/-- `gen_concrete_fetches <prefix> <tree> <fetchAddrThm> <base> [(loOff, hiOff), ...]`:
    emit `@[simp 2000, arm64_norm 2000]` `<prefix>_fetch_0x<addr>` theorems at canonical concrete
    addresses `<base> + off` for every 4-byte offset in each `(loOff, hiOff)` range (inclusive),
    checked in $O(\log N)$ via `<tree>` and `<fetchAddrThm>`. -/
syntax (name := genConcreteFetchesStx) (priority := low)
  "gen_concrete_fetches " ident ident ident num " [" term,* "]" : command

public meta section

private def rangeOffsets (r : TSyntax `decodeRange) : CommandElabM (Array (Nat × Bool)) := do
  match r with
  | `(decodeRange| $a:num) => return #[(a.getNat, false)]
  | `(decodeRange| raw $a:num) => return #[(a.getNat, true)]
  | `(decodeRange| $a:num → $b:num) =>
    let (a, b) := (a.getNat, b.getNat)
    unless a ≤ b && (b - a) % 4 == 0 do
      throwErrorAt r "gen_decodes: bad range {a} → {b}"
    return (List.range ((b - a) / 4 + 1)).toArray.map (a + 4 * ·, false)
  | _ => throwUnsupportedSyntax

private def hexName (pfx : String) (kind : String) (off : Nat) : Name :=
  Name.mkSimple s!"{pfx}_{kind}_0x{String.ofList (Nat.toDigits 16 off)}"

@[command_elab genDecodesStx] def elabGenDecodes : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers gen_decodes $tree:ident $pfx:ident [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let modifiers ← elabModifiers mods
    let scope ← getScope
    let pfxStr := pfx.getId.eraseMacroScopes.toString
    liftTermElabM do
      let treeName ← realizeGlobalConstNoOverloadWithInfo tree
      let treeVal ← treeValueOf treeName
      let ns ← getCurrNamespace
      let env0 ← getEnv
      let isPriv : Bool := (modifiers.visibility matches .private) ||
        (env0.header.isModule && !scope.isPublic && !(modifiers.visibility matches .public))
      for (off, raw) in offs do
        let base := ns ++ hexName pfxStr "decode" off
        let env ← getEnv
        let declName := if isPriv then mkPrivateName env base else base
        let (w, rhs?) ← instrRhs? treeVal off raw
        let some rhs := rhs?
          | throwError "gen_decodes: the word {w} at offset {off} does not decode ({Arm64.describeUnsupportedAt (BitVec.ofNat 64 off) w})"
        let ty := decodeStmtOf treeName off rhs
        addThm declName ty (mkApp2 (mkConst ``Eq.refl [.succ .zero]) optInstr ty.appFn!.appArg!)
        applyAttributesAt declName modifiers.attrs .afterTypeChecking
        applyAttributesAt declName modifiers.attrs .afterCompilation
  | _ => throwUnsupportedSyntax

@[command_elab genFetchesStx] def elabGenFetches : CommandElab := fun stx => do
  match stx with
  | `(gen_fetches $code:ident $pfx:ident $[$te?:num]? $[$root?:ident]? [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let withRoot : Bool := match root? with
      | some r => r.getId == `true
      | none => Bool.true
    let pfxStr := pfx.getId.eraseMacroScopes.toString
    let attrStx ← `(Lean.Parser.Term.attrInstance| simp)
    let attrStx2 ← `(Lean.Parser.Term.attrInstance| arm64_norm)
    liftTermElabM do
      let attrs ← elabAttrs #[attrStx, attrStx2]
      let codeName ← realizeGlobalConstNoOverloadWithInfo code
      let treeName := codeName.appendAfter "_tree"
      let treeVal ← treeValueOf treeName
      let fetchAt := codeName.appendAfter "_fetch_at"
      let fetchRebaseText := codeName.appendAfter "_fetch_rebase_text"
      let textEnd ← match te? with
        | some te => pure te.getNat
        | none =>
          let teName := codeName.appendAfter "TextEnd"
          natOf (mkConst teName)
      let codeNs := codeName.getPrefix
      let codeStr := codeName.getString!
      let ns ← getCurrNamespace
      let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
      let hookTy ← mkArrow (mkConst ``String)
        (mkApp (mkConst ``Option [.zero]) (← mkArrow (mkConst ``Arm64.State) (mkConst ``Arm64.State)))
      let twoPow64 ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]
      let textEndE := mkNatLit textEnd
      for (off, raw) in offs do
        let (w, rhs?) ← instrRhs? treeVal off raw
        let some rhs := rhs? | continue
        let dName := ns ++ hexName pfxStr "decode" off
        let dTy := decodeStmtOf treeName off rhs
        addThm dName dTy (mkApp2 (mkConst ``Eq.refl [.succ .zero]) optInstr dTy.appFn!.appArg!)
        let inst := rhs.appArg!
        let offE := mkNatLit off
        let hoffTy ← mkAppM ``LT.lt #[offE, twoPow64]
        let hoff ← mkDecideProof hoffTy
        let fPrf := mkAppN (mkConst fetchAt) #[offE, inst, mkConst dName, hoff]
        let fTy ← inferType fPrf
        let fName := ns ++ hexName pfxStr "fetch" off
        addThm fName fTy fPrf
        addDocStringCore fName s!"`0x{hex8 w.toNat}`"
        for a in attrs do Term.applyAttributes fName #[a]
        let mut rName? := none
        let mut rBase? := none
        if off < textEnd then
          let htextTy ← mkAppM ``LT.lt #[offE, textEndE]
          let htext ← mkDecideProof htextTy
          let (rTy, rPrf) ← withLocalDeclD `b bv64 fun b => withLocalDeclD `X hookTy fun X => do
            let p := mkAppN (mkConst fetchRebaseText) #[b, X, offE, inst, mkConst dName, htext, hoff]
            let t ← inferType p
            return (← mkForallFVars #[b, X] t, ← mkLambdaFVars #[b, X] p)
          let rName := ns ++ hexName pfxStr "rebase_fetch" off
          addThm rName rTy rPrf
          for a in attrs do Term.applyAttributes rName #[a]
          rName? := some (rName, rTy)
          if off == 0 then
            let (rBaseTy, rBasePrf) ←
              withLocalDeclD `b bv64 fun b => withLocalDeclD `X hookTy fun X => do
                let pBase ← mkAppM ``fetch_rebase_base_of_zero #[mkApp2 (mkConst rName) b X]
                let tBase ← inferType pBase
                return (← mkForallFVars #[b, X] tBase, ← mkLambdaFVars #[b, X] pBase)
            let rBaseName := ns ++ Name.mkSimple s!"{pfxStr}_rebase_fetch_base"
            addThm rBaseName rBaseTy rBasePrf
            for a in attrs do Term.applyAttributes rBaseName #[a]
            rBase? := some (rBaseName, rBaseTy)
        if withRoot then
          addThm (codeNs ++ hexName codeStr "fetch" off) fTy (mkConst fName)
          if let some (rName, rTy) := rName? then
            addThm (codeNs ++ hexName codeStr "rebase_fetch" off) rTy (mkConst rName)
          if let some (rBaseName, rBaseTy) := rBase? then
            addThm (codeNs ++ Name.mkSimple s!"{codeStr}_rebase_fetch_base")
              rBaseTy (mkConst rBaseName)
  | _ => throwUnsupportedSyntax

/-- Elaborate `@[simp 2000, arm64_norm 2000]` concrete-base fetch theorems for one or more
    `(prefix, fetchAddrThm)` targets at `baseNat + off` across `pairs` of `(loOff, hiOff)` ranges. -/
def elabConcreteFetches (tree : Ident) (targets : Array (String × Ident)) (baseNat : Nat)
    (pairs : Array (TSyntax `term)) : CommandElabM Unit := do
  let attr1 ← `(Lean.Parser.Term.attrInstance| simp 2000)
  let attr2 ← `(Lean.Parser.Term.attrInstance| arm64_norm 2000)
  liftTermElabM do
    let attrs ← elabAttrs #[attr1, attr2]
    let treeName ← realizeGlobalConstNoOverloadWithInfo tree
    let resolvedTargets ← targets.mapM fun (pfxStr, thmIdent) => do
      return (pfxStr, ← realizeGlobalConstNoOverloadWithInfo thmIdent)
    let treeVal ← treeValueOf treeName
    let ns ← getCurrNamespace
    let natTy := Lean.mkConst ``Nat
    let n64 ← mkNumeral natTy 64
    let bv64 := mkApp (Lean.mkConst ``BitVec) n64
    for pStx in pairs do
      let pWhnf ← whnf (← Term.elabTerm pStx
        (some (mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy)))
      let a ← natOf (pWhnf.getArg! 2)
      let b ← natOf (pWhnf.getArg! 3)
      unless a ≤ b && (b - a) % 4 == 0 do
        throwErrorAt pStx "gen_concrete_fetches: bad range ({a}, {b})"
      for i in [:(b - a) / 4 + 1] do
        let off := a + 4 * i
        let (_, some rhs) ← instrRhs? treeVal off false
          | throwErrorAt pStx "gen_concrete_fetches: decode failed at offset {off}"
        let hex := String.ofList (Nat.toDigits 16 (baseNat + off))
        let offE := toExpr off
        let addrE := ProofLib.mkCanonBitVecLit 64 (baseNat + off)
        let hPrf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optInstr rhs
        let haddrPrf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64 addrE
        let hbPrf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
          (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
        for (pfxStr, fetchAddrName) in resolvedTargets do
          let fPrf := mkAppN (Lean.mkConst fetchAddrName)
            #[offE, addrE, rhs.appArg!, hPrf, haddrPrf, hbPrf]
          let fName := ns ++ Name.mkSimple s!"{pfxStr}_fetch_0x{hex}"
          addThm fName (← inferType fPrf) fPrf
          for at_ in attrs do Term.applyAttributes fName #[at_]

@[command_elab genConcreteFetchesStx] def elabGenConcreteFetches : CommandElab := fun stx => do
  match stx with
  | `(gen_concrete_fetches $pfx:ident $tree:ident $fetchAddrThm:ident $baseLit:num [$pairs:term,*]) =>
    let pfxStr := pfx.getId.eraseMacroScopes.toString
    elabConcreteFetches tree #[(pfxStr, fetchAddrThm)] baseLit.getNat pairs.getElems
  | _ => throwUnsupportedSyntax

end

end ProofLib.GenDecodes
