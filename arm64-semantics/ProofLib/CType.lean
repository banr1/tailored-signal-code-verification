/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.Surface.CType
public import Arm64
public import ProofLib.Abi
public import ProofLib.CType.Attr
import Arm64.Trusted.Spec.SepLogic
import Arm64.Trusted.Spec.Hoare

/-!
# Typed C Specification Simp Lemmas and Caveat Reports

Provides `@[ctype_simp]` unfolding lemmas for built-in `SemType` combinators (`scalarTy`,
`StatusCode`, `SliceLen`, `Bytes`, `CStr`, `OptOwn`, `outPtrPost`, `OutPtrOnOk`, `OptOutPtr`,
`CondOwn`, `InteriorPtr`, and scalar cells) together with the `#c_type_report` command for
summarizing `c_type_spec` parameter types and caveats under a namespace.
-/

namespace Arm64.CType

@[expose] public section

open Arm64 ProofLib

/-! ## Unfolding lemmas for built-in semantic types -/

@[simp, ctype_simp] theorem scalarTy_interp (w : Nat) (n : String) (v : BitVec 64) (m : BitVec w) :
    (scalarTy w n).interp v m = emp := rfl
@[simp, ctype_simp] theorem scalarTy_pureWf (w : Nat) (n : String) (v : BitVec 64) (m : BitVec w) :
    (scalarTy w n).pureWf v m = True := rfl
@[simp, ctype_simp] theorem scalarTy_valWf (w : Nat) (n : String) (m : BitVec w) :
    (scalarTy w n).valWf m = True := rfl

@[simp, ctype_simp] theorem StatusCode_valWf {w : Nat} (cs : List (BitVec w)) (r : BitVec w) :
    (StatusCode cs).valWf r = (r ∈ cs) := rfl
@[simp, ctype_simp] theorem StatusCode_interp {w : Nat} (cs : List (BitVec w)) (v : BitVec 64)
    (r : BitVec w) : (StatusCode cs).interp v r = emp := rfl
@[simp, ctype_simp] theorem SliceLen_valWf {w : Nat} (bs : List (BitVec 8)) (n : BitVec w) :
    (SliceLen bs).valWf n = (n.toNat = bs.length) := rfl
@[simp, ctype_simp] theorem SliceLen_interp {w : Nat} (bs : List (BitVec 8)) (v : BitVec 64)
    (n : BitVec w) : (SliceLen bs).interp v n = emp := rfl

@[simp, ctype_simp] theorem Bytes_interp (p : BitVec 64) (bs : List (BitVec 8)) :
    Bytes.interp p bs = (p ↦ₛ bs) := rfl
@[simp, ctype_simp] theorem Bytes_pureWf (p : BitVec 64) (bs : List (BitVec 8)) :
    Bytes.pureWf p bs = True := rfl
@[simp, ctype_simp] theorem CStr_interp (p : BitVec 64) (bs : List (BitVec 8)) :
    CStr.interp p bs = (p ↦ₛ (bs ++ [0#8])) := rfl
@[simp, ctype_simp] theorem CStr_pureWf (p : BitVec 64) (bs : List (BitVec 8)) :
    CStr.pureWf p bs = (0#8 ∉ bs) := rfl

@[simp, ctype_simp] theorem OptOwn_interp_none {M : Type} (T : SemType M) (p : BitVec 64) :
    (OptOwn T).interp p none = ⌜p = 0#64⌝ := rfl
@[simp, ctype_simp] theorem OptOwn_interp_some {M : Type} (T : SemType M) (p : BitVec 64) (m : M) :
    (OptOwn T).interp p (some m) = T.interp p m := rfl
@[simp, ctype_simp] theorem OptOwn_pureWf_none {M : Type} (T : SemType M) (p : BitVec 64) :
    (OptOwn T).pureWf p none = True := rfl
@[simp, ctype_simp] theorem OptOwn_pureWf_some {M : Type} (T : SemType M) (p : BitVec 64) (m : M) :
    (OptOwn T).pureWf p (some m) = (p ≠ 0#64 ∧ T.pureWf p m) := rfl

@[ctype_simp] theorem outPtrPost_def {M : Type} (T : SemType M) (p : BitVec 64) (m : M) :
    outPtrPost T p m = ∃∗ v : BitVec 64, ⌜T.pureWf v m⌝ ∗ (p ↦₆₄ v) ∗ T.interp v m := rfl

@[simp, ctype_simp] theorem OutPtrOnOk_interp {M : Type} (T : SemType M) (ok : Prop) [Decidable ok]
    (v : BitVec 64) (m : M) :
    (OutPtrOnOk T ok).interp v m = (if ok then T.interp v m else emp) := rfl
@[simp, ctype_simp] theorem OutPtrOnOk_pureWf {M : Type} (T : SemType M) (ok : Prop) [Decidable ok]
    (v : BitVec 64) (m : M) :
    (OutPtrOnOk T ok).pureWf v m = (if ok then T.pureWf v m else True) := rfl

@[simp, ctype_simp] theorem OptOutPtr_interp_none {M : Type} (T : SemType M) (p : BitVec 64) :
    (OptOutPtr T).interp p none = memRegion p 8 := rfl
@[simp, ctype_simp] theorem OptOutPtr_interp_some {M : Type} (T : SemType M) (p : BitVec 64)
    (m : M) : (OptOutPtr T).interp p (some m) = outPtrPost T p m := rfl
@[simp, ctype_simp] theorem OptOutPtr_pureWf {M : Type} (T : SemType M) (p : BitVec 64)
    (om : Option M) : (OptOutPtr T).pureWf p om = True := rfl

@[simp, ctype_simp] theorem CondOwn_interp_none {M : Type} (T : SemType M) (p : BitVec 64) :
    (CondOwn T).interp p none = emp := rfl
@[simp, ctype_simp] theorem CondOwn_interp_some {M : Type} (T : SemType M) (p : BitVec 64)
    (m : M) : (CondOwn T).interp p (some m) = T.interp p m := rfl
@[simp, ctype_simp] theorem CondOwn_pureWf_none {M : Type} (T : SemType M) (p : BitVec 64) :
    (CondOwn T).pureWf p none = True := rfl
@[simp, ctype_simp] theorem CondOwn_pureWf_some {M : Type} (T : SemType M) (p : BitVec 64)
    (m : M) : (CondOwn T).pureWf p (some m) = T.pureWf p m := rfl

@[simp, ctype_simp] theorem InteriorPtr_interp (tyName : String) (p target : BitVec 64) :
    (InteriorPtr tyName).interp p target = emp := rfl
@[simp, ctype_simp] theorem InteriorPtr_pureWf (tyName : String) (p target : BitVec 64) :
    (InteriorPtr tyName).pureWf p target = (p = target) := rfl

@[simp, ctype_simp] theorem U8Cell_interp (p : BitVec 64) (v : BitVec 8) :
    U8Cell.interp p v = (p ↦₈ v) := rfl
@[simp, ctype_simp] theorem U8Cell_pureWf (p : BitVec 64) (v : BitVec 8) :
    U8Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem I8Cell_interp (p : BitVec 64) (v : BitVec 8) :
    I8Cell.interp p v = (p ↦₈ v) := rfl
@[simp, ctype_simp] theorem I8Cell_pureWf (p : BitVec 64) (v : BitVec 8) :
    I8Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem U16Cell_interp (p : BitVec 64) (v : BitVec 16) :
    U16Cell.interp p v = (p ↦₁₆ v) := rfl
@[simp, ctype_simp] theorem U16Cell_pureWf (p : BitVec 64) (v : BitVec 16) :
    U16Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem I16Cell_interp (p : BitVec 64) (v : BitVec 16) :
    I16Cell.interp p v = (p ↦₁₆ v) := rfl
@[simp, ctype_simp] theorem I16Cell_pureWf (p : BitVec 64) (v : BitVec 16) :
    I16Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem U32Cell_interp (p : BitVec 64) (v : BitVec 32) :
    U32Cell.interp p v = (p ↦₃₂ v) := rfl
@[simp, ctype_simp] theorem U32Cell_pureWf (p : BitVec 64) (v : BitVec 32) :
    U32Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem I32Cell_interp (p : BitVec 64) (v : BitVec 32) :
    I32Cell.interp p v = (p ↦₃₂ v) := rfl
@[simp, ctype_simp] theorem I32Cell_pureWf (p : BitVec 64) (v : BitVec 32) :
    I32Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem U64Cell_interp (p : BitVec 64) (v : BitVec 64) :
    U64Cell.interp p v = (p ↦₆₄ v) := rfl
@[simp, ctype_simp] theorem U64Cell_pureWf (p : BitVec 64) (v : BitVec 64) :
    U64Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem I64Cell_interp (p : BitVec 64) (v : BitVec 64) :
    I64Cell.interp p v = (p ↦₆₄ v) := rfl
@[simp, ctype_simp] theorem I64Cell_pureWf (p : BitVec 64) (v : BitVec 64) :
    I64Cell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem SizeTCell_interp (p : BitVec 64) (v : BitVec 64) :
    SizeTCell.interp p v = (p ↦₆₄ v) := rfl
@[simp, ctype_simp] theorem SizeTCell_pureWf (p : BitVec 64) (v : BitVec 64) :
    SizeTCell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem SSizeTCell_interp (p : BitVec 64) (v : BitVec 64) :
    SSizeTCell.interp p v = (p ↦₆₄ v) := rfl
@[simp, ctype_simp] theorem SSizeTCell_pureWf (p : BitVec 64) (v : BitVec 64) :
    SSizeTCell.pureWf p v = True := rfl
@[simp, ctype_simp] theorem PtrdiffTCell_interp (p : BitVec 64) (v : BitVec 64) :
    PtrdiffTCell.interp p v = (p ↦₆₄ v) := rfl
@[simp, ctype_simp] theorem PtrdiffTCell_pureWf (p : BitVec 64) (v : BitVec 64) :
    PtrdiffTCell.pureWf p v = True := rfl

end

/-! ## `#c_type_report` command -/

public meta section Report

open Lean Elab Command Meta

-- Syntactically decode a `CTypeSpecInfo.mk` constant emitted by `c_type_spec`.
private partial def decList (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, h, t]) => (h :: ·) <$> decList t
  | _ => none

private def decStr (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

private def decStrs (e : Expr) : Option (List String) := do
  (← decList e).mapM decStr

private def decParam (e : Expr) : Option CParamInfo :=
  match e.getAppFnArgs with
  | (``CParamInfo.mk, #[n, m, t]) => return ⟨← decStr n, ← decStr m, ← decStr t⟩
  | _ => none

private def decKind (e : Expr) : Option CaveatKind :=
  if e.isConstOf ``CaveatKind.apiRestriction then some .apiRestriction
  else if e.isConstOf ``CaveatKind.callerTypestate then some .callerTypestate
  else if e.isConstOf ``CaveatKind.cArithBound then some .cArithBound
  else if e.isConstOf ``CaveatKind.partialSpec then some .partialSpec
  else none

private def decCaveat (e : Expr) : Option CaveatClause :=
  match e.getAppFnArgs with
  | (``CaveatClause.mk, #[k, d, p]) => return ⟨← decKind k, ← decStr d, ← decStr p⟩
  | _ => none

private def decInfo (e : Expr) : Option CTypeSpecInfo :=
  match e.getAppFnArgs with
  | (``CTypeSpecInfo.mk, #[s, ps, r, cs, en, un]) => do
    let ret ← match r.getAppFnArgs with
      | (``Option.none, _) => some none
      | (``Option.some, #[_, p]) => some <$> decParam p
      | _ => none
    return ⟨← decStr s, ← (← decList ps).mapM decParam, ret, ← (← decList cs).mapM decCaveat,
      ← decStrs en, ← decStrs un⟩
  | _ => none

private def escapeCell (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

/-- Render the caveat table for a list of `(constName, info)` pairs. -/
def renderCTypeReport (infos : List (Name × CTypeSpecInfo)) : String := Id.run do
  let mut out := "| Spec | Typed parameters | Return | Caveats |\n| :--- | :--- | :--- | :--- |\n"
  let mut counts : List (String × Nat) :=
    [("API_RESTRICTION", 0), ("CALLER_TYPESTATE", 0), ("C_ARITH_BOUND", 0), ("PARTIAL_SPEC", 0)]
  for (_, i) in infos do
    let ps := ", ".intercalate (i.params.map fun p => s!"`{p.name} : {p.mode} {p.ty}`")
    let r := match i.ret with
      | some p => s!"`{p.mode} {p.ty}`"
      | none => "—"
    let cav := if i.caveats.isEmpty then "none"
      else "<br>".intercalate (i.caveats.map fun c => s!"[{c.kind.tag}] {c.desc} (`{c.prop}`)")
    let extra := (i.env.map (s!"<br>env `{·}`")) ++ (i.untypedRequires.map (s!"<br>UNTYPED `{·}`"))
    out := out ++ s!"| `{i.spec}` | {escapeCell ps} | {escapeCell r} | {escapeCell (cav ++ String.join extra)} |\n"
    for c in i.caveats do
      counts := counts.map fun (t, k) => if t == c.kind.tag then (t, k + 1) else (t, k)
  let summary := ", ".intercalate (counts.map fun (t, k) => s!"{t}: {k}")
  return s!"{infos.length} c_type_spec(s); caveats — {summary}\n\n" ++ out

/-- `#c_type_report Ns` prints a Markdown caveat table of all `*.cTypeInfo` constants under `Ns`. -/
elab "#c_type_report " ns:ident : command => do
  let env ← getEnv
  let pre := ns.getId
  let mut found : Array (Name × CTypeSpecInfo) := #[]
  for (n, ci) in env.constants.toList do
    let isInfo := match n with
      | .str _ "cTypeInfo" => true
      | _ => false
    if isInfo && pre.isPrefixOf n then
      if ci.type.isConstOf ``CTypeSpecInfo then
        match ci.value? >>= decInfo with
        | some i => found := found.push (n, i)
        | none => throwError "#c_type_report: {n} is not a literal `CTypeSpecInfo.mk ...` term"
  let sorted := found.qsort (fun a b => a.1.toString < b.1.toString)
  if sorted.isEmpty then
    logWarning m!"#c_type_report: no c_type_spec metadata found under {pre}"
  else
    logInfo (renderCTypeReport sorted.toList)

end Report

end Arm64.CType
