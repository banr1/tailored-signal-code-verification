/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import Arm64
public import ProofLib.ProgramReflection
public import ProofLib.ObjectLoad
public import ProofLib.SepLogic
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.SepLogic

/-!
# Symbol-Keyed Function Entry Tactics

Provides `wp_entry` (alias `wp_init_fn`) and `wpp_entry` for initializing `SepWP` and
`SepWPp` function proofs from `fnEntryExt` symbol metadata. For linked-image entries,
`wp_entry` unfolds `subroutineOk` wrappers, normalizes caller and callee offsets relative
to `prog.fnAddr sym`, emits `code_fetches`, runs `wp_init`, and generalizes `entry`;
for placed-library entries (`gen_placed_fnOffs`), it rewrites entry and callee addresses to
`b + off#64` and delegates fetches to the global `P_rebase_fetch_0x<off>` lemmas.
-/

namespace ProofLib

open Arm64 ProofLib.ProgramReflection

@[expose] public section

/-- Both `subroutine_ok` and `safe_until_pc` hold for a single entry point `name`.
    Marked `protected` so `open ProofLib` does not shadow a client-side `EntrySafe`. -/
protected abbrev EntrySafe {α : Type} (prog : Program) (name : String) (spec : Spec α) : Prop :=
  subroutine_ok prog (prog.fnAddr name) spec ∧
    ∀ (x : α) (R : SepProp) (s0 : State),
      AapcsEntry s0 (prog.fnAddr name) →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      safe_until_pc prog (s0.readReg64 Reg.lr) s0 (fun _ => True)
        (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)

/-- Both `subroutine_ok` and `safe_until_pc` hold for every entry point in `names`.
    Marked `protected` so `open ProofLib` does not shadow a client-side `EntryListSafe`. -/
protected abbrev EntryListSafe {α : Type} (prog : Program) (names : List String) (spec : Spec α) : Prop :=
  ∀ name ∈ names, ProofLib.EntrySafe prog name spec

/-- Lift `subroutine_ok` for `name` to `EntrySafe prog name spec`. -/
theorem entrySafe_of_subroutine_ok {α : Type} {prog : Program} {name : String} {spec : Spec α}
    (_hno : false = false := rfl)
    (hok : subroutine_ok prog (prog.fnAddr name) spec)
    (h_no_panic : ∀ x s, spec.onPanic x s = (fun _ => ⌜False⌝) := by intros; rfl)
    (h_no_exit : ∀ x code s, spec.onExit x code s = (fun _ => ⌜False⌝) := by intros; rfl) :
    ProofLib.EntrySafe prog name spec :=
  ⟨hok, fun x R _ hentry hpre =>
    subroutine_ok.safe hok x R hentry hpre
      (fun _ _ hp => by rw [h_no_panic] at hp; exact not_satisfies_false_sepConj hp)
      (fun _ _ _ he => by rw [h_no_exit] at he; exact not_satisfies_false_sepConj he)⟩

/-- Lift `subroutine_ok` for `n1` to `EntryListSafe prog [n1] spec`. -/
theorem entryListSafe_singleton {α : Type} {prog : Program} {n1 : String} {spec : Spec α}
    (_hno : false = false := rfl)
    (h1 : subroutine_ok prog (prog.fnAddr n1) spec)
    (h_no_panic : ∀ x s, spec.onPanic x s = (fun _ => ⌜False⌝) := by intros; rfl)
    (h_no_exit : ∀ x code s, spec.onExit x code s = (fun _ => ⌜False⌝) := by intros; rfl) :
    ProofLib.EntryListSafe prog [n1] spec := by
  intro name hname
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
  subst hname
  exact entrySafe_of_subroutine_ok _hno h1 h_no_panic h_no_exit

/-- Rewrite a rebased program's `fnAddr` to `b + BitVec.ofNat 64 off` given `P.fnOff name = off`. -/
theorem fnAddr_rebase_eq_add_of_fnOff {P : Program} {b : BitVec 64}
    {X O : String → Option (Arm64.State → Arm64.State)} {name : String} {off : Nat}
    (hfn : P.fnOff name = off) :
    (P.rebase b X O).fnAddr name = b + BitVec.ofNat 64 off := by
  rw [Program.fnAddr_rebase, hfn]

/-- Rewrite a rebased program's `fnAddr` at offset `0` to `b` given `P.fnOff name = 0`. -/
theorem fnAddr_rebase_eq_base_of_fnOff_zero {P : Program} {b : BitVec 64}
    {X O : String → Option (Arm64.State → Arm64.State)} {name : String}
    (hfn : P.fnOff name = 0) :
    (P.rebase b X O).fnAddr name = b := by
  rw [Program.fnAddr_rebase, hfn]
  simp

/-- Express a callee's `fnAddr` relative to the caller's `fnAddr` on the same rebased program. -/
theorem fnAddr_callee_of_fnOff {P : Program} {b : BitVec 64}
    {X O : String → Option (Arm64.State → Arm64.State)} {caller callee : String}
    {callerOff calleeOff k : Nat}
    (hcaller : P.fnOff caller = callerOff)
    (hcallee : P.fnOff callee = calleeOff)
    (hk : (BitVec.ofNat 64 callerOff + BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff) :
    (P.rebase b X O).fnAddr callee =
      (P.rebase b X O).fnAddr caller + BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hcaller, hcallee, BitVec.add_assoc, hk]

/-- Express a raw `b + BitVec.ofNat 64 calleeOff` address relative to the caller's `fnAddr`. -/
theorem base_add_callee_of_fnOff {P : Program} {b : BitVec 64}
    {X O : String → Option (Arm64.State → Arm64.State)} {caller : String}
    {callerOff calleeOff k : Nat}
    (hcaller : P.fnOff caller = callerOff)
    (hk : (BitVec.ofNat 64 callerOff + BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff) :
    b + BitVec.ofNat 64 calleeOff =
      (P.rebase b X O).fnAddr caller + BitVec.ofNat 64 k := by
  rw [Program.fnAddr_rebase, hcaller, BitVec.add_assoc, hk]

/-- Re-express `subroutine_ok` for `callee` at `(P.rebase b X O).fnAddr caller + BitVec.ofNat 64 k`
    so `wp_entry caller` keeps it entry-relative. -/
theorem callee_ok_at_of_fnOff {α : Type} {P : Program} {b : BitVec 64}
    {X O : String → Option (Arm64.State → Arm64.State)} {caller callee : String}
    {callerOff calleeOff k : Nat} {spec : Spec α}
    (hcaller : P.fnOff caller = callerOff)
    (hcallee : P.fnOff callee = calleeOff)
    (hk : (BitVec.ofNat 64 callerOff + BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 calleeOff)
    (h : subroutine_ok (P.rebase b X O) ((P.rebase b X O).fnAddr callee) spec) :
    subroutine_ok (P.rebase b X O)
      ((P.rebase b X O).fnAddr caller + BitVec.ofNat 64 k) spec := by
  rwa [fnAddr_callee_of_fnOff hcaller hcallee hk] at h

/-- Lift `subroutine_ok` from `tgt` to a 1-instruction `b t` trampoline `src` on the same
    rebased program `P.rebase b X O`. -/
theorem subroutine_ok_of_trampoline {α : Type} {P : Program} {b : BitVec 64}
    {X O : String → Option (Arm64.State → Arm64.State)} {src tgt : String}
    {srcOff tgtOff : Nat} {t : BitVec 64} {spec : Spec α}
    (hsrc : P.fnOff src = srcOff)
    (htgt : P.fnOff tgt = tgtOff)
    (hfetch : (P.rebase b X O).fetch ((P.rebase b X O).fnAddr src) = some (.b t))
    (h : subroutine_ok (P.rebase b X O) ((P.rebase b X O).fnAddr tgt) spec)
    (ht : (BitVec.ofNat 64 srcOff + t : BitVec 64) = BitVec.ofNat 64 tgtOff := by decide)
    (hpre : ∀ x s pc, spec.pre x (s.setPC pc) = spec.pre x s := by intros; rfl)
    (hpost : ∀ x s pc sf, spec.post x (s.setPC pc) sf = spec.post x s sf := by intros; rfl)
    (hpan : ∀ x s pc sf, spec.onPanic x (s.setPC pc) sf = spec.onPanic x s sf := by intros; rfl)
    (hexit : ∀ x code s pc sf, spec.onExit x code (s.setPC pc) sf = spec.onExit x code s sf := by intros; rfl)
    (hoom : ∀ x s pc sf, spec.onOom x (s.setPC pc) sf = spec.onOom x s sf := by intros; rfl) :
    subroutine_ok (P.rebase b X O) ((P.rebase b X O).fnAddr src) spec := by
  have heq : (P.rebase b X O).fnAddr src + t = (P.rebase b X O).fnAddr tgt := by
    rw [fnAddr_rebase_eq_add_of_fnOff hsrc, fnAddr_rebase_eq_add_of_fnOff htgt,
        BitVec.add_assoc, ht]
  exact subroutine_ok_of_b hfetch heq rfl hpre h hpost hpan hexit hoom

/-- `fn_rebase% <code> "sym"`: rewrite `(<code>.rebase b X O).fnAddr "sym"` to
    `b + BitVec.ofNat 64 off` via the symbol's `fnOff` lemma. -/
macro "fn_rebase% " code:ident s:str : term =>
  `(fnAddr_rebase_eq_add_of_fnOff (code_lemma% $code fnOff $s))

/-- `wp_code_init <code> <decPrefix> "sym" b hooks x s0`: emit instruction-fetch hypotheses for
    `"sym"`, rewrite its rebased `fnAddr` to `b + BitVec.ofNat 64 off` in context and goal, and
    initialize `SepWP` with `wp_init x s0`. -/
macro "wp_code_init " code:ident dec:ident s:str b:ident hooks:ident x:ident s0:ident : tactic =>
  `(tactic| (code_fetches_fn $code $dec $b $hooks $s
             simp only [fn_rebase% $code $s, BitVec.add_assoc, BitVec.reduceAdd] at *
             wp_init $x $s0))

/-- `callee_call% <code> "caller" "callee" h`: re-express `h` at `fnAddr "caller" + k` for a
    callee placed after `"caller"` in `<code>` (`k` resolved by symbol). -/
macro "callee_call% " code:ident f:str t:str h:term:max : term =>
  `(callee_ok_at_of_fnOff (code_lemma% $code fnOff $f)
      (code_lemma% $code fnOff $t)
      (k := (code_rel% $code $f $t : Nat)) (by decide) $h)

/-- `callee_call_back% <code> "caller" "callee" h`: as `callee_call%`, for a callee placed before
    `"caller"` in `<code>` (`k = 2^64 - (fnOff caller - fnOff callee)`, resolved by symbol). -/
macro "callee_call_back% " code:ident f:str t:str h:term:max : term =>
  `(callee_ok_at_of_fnOff (code_lemma% $code fnOff $f)
      (code_lemma% $code fnOff $t)
      (k := 2 ^ 64 - (code_rel% $code $t $f : Nat)) (by decide) $h)

/-- `hook_call% <code> b "caller" "stub" h`: `subroutine_ok` for extern `"stub"` at its call site
    `fnAddr "caller" + k` in `<code>.rebase b hooks`. -/
macro "hook_call% " code:ident b:term:max f:str t:str h:term:max : term =>
  `(hook_ok_at_raw (b := $b) (code_lemma% $code fnOff $f)
      (k := (code_rel% $code $f $t : Nat)) rfl (by decide)
      (code_lemma% $code hookAtOff $t) $h)

end

public meta section

open Lean Meta Elab Tactic

private def isSubroutineOkApp (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOf ``Arm64.subroutine_ok ||
  e.isAppOf ``Program.subroutineOk ||
  e.isAppOf ``Arm64.fn_subroutine_ok ||
  e.isAppOf ``Program.relocSubroutineOk ||
  e.isAppOf ``Program.alignedSubroutineOk ||
  e.isAppOf ``Obj.LinkedImage.subroutineOk

private def isQuantifiedSubroutineOk (e : Expr) : Bool :=
  let e := e.consumeMData
  if isSubroutineOkApp e then true
  else match e with
  | .forallE _ dom body _ =>
    let dom := dom.consumeMData
    let body := body.consumeMData
    if dom.isConstOf ``Arm64.Obj.Image || dom.isAppOfArity ``BitVec 1 then
      if isSubroutineOkApp body then true
      else match body with
      | .forallE _ _ body2 _ => isSubroutineOkApp body2
      | _ => false
    else false
  | _ => false

/-- Unfold a top-level statement definition (`*Stmt`) or base-quantified `subroutineOk` wrapper
    and introduce any universally quantified load base `b : BitVec 64` (or `img : Obj.Image` and
    `himg : Obj.Loads li img`), rewriting `Program.ofImage img` to `<code>.rebase img.base`. -/
def prepareBaseQuantifiedGoal : TacticM Unit := do
  let gInit ← getMainGoal
  let needsPrep ← gInit.withContext do
    let tgt := (← instantiateMVars (← gInit.getType)).consumeMData
    let hasLoads := (← getLCtx).any fun d =>
      !d.isImplementationDetail && !d.isAuxDecl &&
      d.type.consumeMData.isAppOfArity ``Arm64.Obj.Loads 2
    if tgt.isAppOf ``Arm64.subroutine_ok &&
       !tgt.isAppOf ``Program.subroutineOk &&
       !tgt.isAppOf ``Arm64.fn_subroutine_ok &&
       (tgt.find? (·.isAppOf ``ToBaseSpec.toSpec)).isNone &&
       !hasLoads then
      return false
    if !isQuantifiedSubroutineOk tgt then
      if let some c := tgt.getAppFn.constName? then
        if let some tgtUnf ← unfoldDefinition? tgt then
          if isQuantifiedSubroutineOk tgtUnf then
            let _ ← tryTactic (evalTactic (← `(tactic| unfold $(mkIdent c))))
    return true
  if !needsPrep then
    return
  let _ ← tryTactic (evalTactic (← `(tactic|
    dsimp only [Program.relocSubroutineOk, Program.alignedSubroutineOk,
      Obj.LinkedImage.subroutineOk, Program.subroutineOk, fn_subroutine_ok,
      ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard])))
  let g1 ← getMainGoal
  g1.withContext do
    let tgt := (← instantiateMVars (← g1.getType)).consumeMData
    if let .forallE _ dom _ _ := tgt then
      let dom := dom.consumeMData
      if dom.isConstOf ``Arm64.Obj.Image then
        let imgId := mkIdent `img
        let himgId := mkIdent `himg
        evalTactic (← `(tactic| intro $imgId:ident $himgId:ident))
      else if dom.isAppOfArity ``BitVec 1 then
        let bId := mkIdent `b
        evalTactic (← `(tactic| intro $bId:ident))
        let g2 ← getMainGoal
        g2.withContext do
          let tgt2 := (← instantiateMVars (← g2.getType)).consumeMData
          if let .forallE _ dom2 _ _ := tgt2 then
            if dom2.consumeMData.isAppOf ``Eq then
              let hbId := mkIdent `hb
              evalTactic (← `(tactic| intro $hbId:ident))
  let g3 ← getMainGoal
  g3.withContext do
    let env ← getEnv
    let lctx ← getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty := (← instantiateMVars decl.type).consumeMData
        if ty.isAppOfArity ``Arm64.Obj.Loads 2 then
          let liExpr := (ty.getArg! 0).consumeMData
          let imgExpr := (ty.getArg! 1).consumeMData
          let himgId := mkIdent decl.userName
          let hasHb := lctx.any fun d =>
            !d.isImplementationDetail && !d.isAuxDecl && d.userName == `hb
          if !hasHb then
            let imgStx ← Term.exprToSyntax (← instantiateMVars imgExpr)
            let hbId := mkIdent `hb
            let _ ← tryTactic (evalTactic (← `(tactic|
              have $hbId:ident : ($imgStx : Arm64.Obj.Image).base &&& 0xfff#64 = 0#64 :=
                ProofLib.ObjectLoad.base_aligned_of_loads $himgId:ident)))
            (← getGoals).forM instantiateMVarDeclMVars
          if let some liName := liExpr.getAppFn.constName? then
            let liStr := liName.getString!
            let pfx := if liStr.endsWith "Image" then (liStr.dropEnd 5).toString else liStr
            let ofImageName := Name.str liName.getPrefix (pfx ++ "Code_ofImage")
            if env.contains ofImageName then
              let _ ← tryTactic (evalTactic (← `(tactic|
                rw [$(mkIdent ofImageName) $himgId:ident])))
          break
  let _ ← tryTactic (evalTactic (← `(tactic|
    dsimp only [Program.subroutineOk, fn_subroutine_ok,
      ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard])))

private def unreducedEntryHead? (e : Expr) : Option Name :=
  let isLookupConst (nm : Name) : Bool :=
    nm == ``Arm64.Obj.PlacedLib.fnAddr ||
    nm == ``Arm64.Obj.MultiPlacedLib.fnAddr ||
    nm == ``Arm64.Obj.LinkedImage.fnAddr ||
    nm == ``Arm64.Obj.MultiPlacedLib.resolve ||
    nm == ``Arm64.Obj.CodeBlock.resolve ||
    nm == ``Arm64.Obj.LinkedImage.resolveSym ||
    nm == ``Arm64.Obj.LinkedImage.resolveObjSym ||
    nm == ``Arm64.Obj.Image.symtab ||
    nm == ``Arm64.Obj.lookup ||
    nm == ``Arm64.Obj.lookupUnique ||
    nm == ``Arm64.Obj.lookupBlockSym ||
    nm == ``Arm64.Obj.lookupBlockSymAux ||
    nm == `Arm64.Obj.lookupSymInLists ||
    nm == `Arm64.Obj.MultiPlacedLib.SymIndex.lookupBlockCharSym ||
    nm == `Arm64.Obj.MultiPlacedLib.SymIndex.lookupBlockSym ||
    nm == `Arm64.Obj.MultiPlacedLib.SymIndex.findDataSym ||
    nm == `Arm64.Obj.MultiPlacedLib.SymIndex.fnAddr ||
    nm == `Arm64.Obj.MultiPlacedLib.SymIndex.resolve ||
    nm == `Arm64.Obj.RelocFnIndex.lookupIdxChars ||
    nm == `Arm64.Obj.RelocFnIndex.lookupIdx ||
    nm == `Arm64.Obj.RelocFnIndex.findFn? ||
    nm == ``Arm64.Program.fnOff ||
    nm == ``Arm64.Program.findSymbol?
  (e.find? fun sub =>
    match sub.constName? with
    | some nm => isLookupConst nm
    | none => false).bind (·.constName?)

private def hasTableLookupConst (e : Expr) : Bool :=
  (unreducedEntryHead? e).isSome ||
    (e.find? fun sub =>
      match sub.constName? with
      | some nm =>
        nm.getPrefix == `Arm64.Obj.Interned ||
        nm.getPrefix == `Arm64.Obj.MultiPlacedLib.SymIndex ||
        nm.getPrefix == `Arm64.Obj.RelocFnIndex ||
        nm == ``List.idxOf || nm == ``List.find? || nm == ``List.filter
      | none => false).isSome

private def resolveRegisteredFnOffApp? (env : Environment) (sub : Expr) :
    MetaM (Option FnEntryInfo) := do
  unless sub.isAppOfArity ``Arm64.Program.fnOff 2 do
    return none
  let progArg := (sub.getArg! 0).consumeMData
  let symArg := (sub.getArg! 1).consumeMData
  let sym? ← match symArg with
    | .lit (.strVal s) => pure (some s)
    | _ =>
      match ← Arm64.Program.reduceToStringLit? symArg with
      | some (.lit (.strVal s)) => pure (some s)
      | _ => pure none
  let some sym := sym? | return none
  if let some pConst := progArg.getAppFn.constName? then
    if let some info := lookupFnEntry? env sym (some pConst) then
      return some info
  if let some (pConst, _, _, _) ← extractRebase? progArg then
    return lookupFnEntry? env sym (some pConst)
  return none

private def findRegisteredFnOff? (env : Environment) (e : Expr) : MetaM (Option FnEntryInfo) := do
  let e ← instantiateMVars e
  let some sub := e.find? (·.isAppOfArity ``Arm64.Program.fnOff 2) | return none
  resolveRegisteredFnOffApp? env sub

private partial def substRegisteredFnOffs (env : Environment) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if (e.find? (·.isAppOfArity ``Arm64.Program.fnOff 2)).isNone then
    return e
  Meta.transform e (pre := fun sub => do
    if let some info ← resolveRegisteredFnOffApp? env sub then
      return .done (toExpr info.off)
    return .continue)

private def sepEntryAddrBaseOff (e : Expr) : MetaM (Expr × Nat) := do
  let e ← substRegisteredFnOffs (← getEnv) e
  if hasTableLookupConst e then
    return sepAddrBaseOffPure e
  MonadRuntimeException.tryCatchRuntimeEx
    (sepAddrBaseOff e)
    (fun _ => return sepAddrBaseOffPure e)

private def entryProgramHint (tacName : String) (progExpr : Expr) : MessageData :=
  if (progExpr.find? fun s =>
      s.isConstOf ``Arm64.Obj.PlacedLib.program ||
      s.isConstOf ``Arm64.Obj.MultiPlacedLib.blockProgram).isSome then
    m!"\nhint: program uses unrewritten `PlacedLib.program` / `MultiPlacedLib.blockProgram`; rewrite the program to its `(<progPC> pl).rebase b H` wrapper (registered via `gen_placed_fnOffs`) and pre-fold the entry address to `b + 0x...#64` before calling `{tacName}`"
  else if (progExpr.find? fun s =>
      s.isConstOf ``Arm64.Program.ofImage ||
      s.isConstOf ``Arm64.Program.ofImageWithSvc).isSome then
    m!"\nhint: program uses unrewritten `Program.ofImage`; rewrite it with `<prefix>Code_ofImage himg` (or `Program.ofImage_eq_rebase`) to `<codeConst>.rebase img.base hooks` before calling `{tacName}`"
  else
    m!""

private def collectTableOrLookupHeads (g : MVarId) : MetaM (Array Name) := do
  let ref ← IO.mkRef (#[] : Array Name)
  let isInteresting (nm : Name) : Bool :=
    let pfx := nm.getPrefix
    pfx == `Arm64.Obj.Image || pfx == `Arm64.Obj.LinkedImage ||
    pfx == `Arm64.Obj.CodeBlock || pfx == `Arm64.Obj.PlacedLib ||
    pfx == `Arm64.Obj.MultiPlacedLib || pfx == `Arm64.Obj.MultiPlacedLib.SymIndex ||
    pfx == `Arm64.Obj.RelocFnIndex || pfx == `Arm64.Obj.Interned ||
    pfx == `Arm64.Process.ElfImage ||
    nm == ``Arm64.Obj.lookup || nm == ``Arm64.Obj.lookupUnique ||
    nm == ``Arm64.Obj.lookupBlockSym || nm == `Arm64.Obj.lookupSymInLists ||
    nm == ``Arm64.Program.fnOff
  let scan (e : Expr) : MetaM Unit := do
    e.forEach fun sub => do
      if (← ref.get).size < 4 then
        if let some nm := sub.constName? then
          if isInteresting nm && !nm.getString!.endsWith "mk" then
            let cur ← ref.get
            if !cur.contains nm then
              ref.set (cur.push nm)
  scan (← instantiateMVars (← g.getType))
  for decl in ← getLCtx do
    if (← ref.get).size >= 4 then break
    if !decl.isImplementationDetail && !decl.isAuxDecl then
      scan (← instantiateMVars decl.type)
  ref.get

private def bridgeLocalCallees (info : FnEntryInfo) (bExpr : Expr)
    (placedFnOff? : Option (FnEntryInfo → TacticM Term) := none) : TacticM Unit := do
  let env ← getEnv
  let declNames ← withMainContext do
    let mut out : Array Name := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !out.contains decl.userName then
        out := out.push decl.userName
    pure out
  let refreshTy? (uName : Name) : TacticM (Option Expr) := withMainContext do
    let some d := (← getLCtx).findFromUserName? uName | return none
    pure (some (← instantiateMVars d.type).consumeMData)
  let currentBaseExpr : TacticM Expr := withMainContext do
    let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
    if tgt.isAppOfArity ``Arm64.subroutine_ok 4 then
      if let some (_, bNow, _, _) ← extractRebase? (tgt.getArg! 1).consumeMData then
        return bNow
    return bExpr
  for uName in declNames do
    let hypId := mkIdent uName
    let _ ← tryTactic do
      let some ty0 ← refreshTy? uName | return
      let mut ty := ty0
      if !isQuantifiedSubroutineOk ty then
        let unfoldConst? ← withMainContext do
          if let some c := ty.getAppFn.constName? then
            if let some tyUnf ← unfoldDefinition? ty then
              if isQuantifiedSubroutineOk tyUnf then
                return some c
          return none
        if let some c := unfoldConst? then
          let _ ← tryTactic (evalTactic (← `(tactic| unfold $(mkIdent c) at $hypId:ident)))
          let some ty' ← refreshTy? uName | return
          ty := ty'
      unless isQuantifiedSubroutineOk ty do
        return
      if !ty.isAppOf ``Arm64.subroutine_ok ||
         ty.isAppOf ``Program.subroutineOk ||
         ty.isAppOf ``Arm64.fn_subroutine_ok ||
         (ty.find? (·.isAppOf ``ToBaseSpec.toSpec)).isSome then
        let _ ← tryTactic (evalTactic (← `(tactic|
          dsimp only [Program.relocSubroutineOk, Program.alignedSubroutineOk,
            Obj.LinkedImage.subroutineOk, Program.subroutineOk, fn_subroutine_ok,
            ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard] at $hypId:ident)))
        let some ty' ← refreshTy? uName | return
        ty := ty'
      if let .forallE _ dom _ _ := ty then
        let dom := dom.consumeMData
        if dom.isConstOf ``Arm64.Obj.Image then
          let loadsHyp? ← withMainContext do
            let mut res : Option (Ident × Term × Option Name) := none
            for d in (← getLCtx) do
              if !d.isImplementationDetail && !d.isAuxDecl then
                let dty := (← instantiateMVars d.type).consumeMData
                if dty.isAppOfArity ``Arm64.Obj.Loads 2 then
                  let liExpr := (dty.getArg! 0).consumeMData
                  let imgExpr := (dty.getArg! 1).consumeMData
                  let imgStx ← Term.exprToSyntax (← instantiateMVars imgExpr)
                  let ofImageName? := liExpr.getAppFn.constName?.bind fun liName =>
                    let liStr := liName.getString!
                    let pfx := if liStr.endsWith "Image" then (liStr.dropEnd 5).toString else liStr
                    let n := Name.str liName.getPrefix (pfx ++ "Code_ofImage")
                    if env.contains n then some n else none
                  res := some (mkIdent d.userName, imgStx, ofImageName?)
            pure res
          if let some (himgId, imgStx, ofImageName?) := loadsHyp? then
            evalTactic (← `(tactic| replace $hypId:ident := $hypId:ident $imgStx $himgId:ident))
            (← getGoals).forM instantiateMVarDeclMVars
            if let some ofImageName := ofImageName? then
              let _ ← tryTactic (evalTactic (← `(tactic|
                rw [$(mkIdent ofImageName) $himgId:ident] at $hypId:ident)))
            let _ ← tryTactic (evalTactic (← `(tactic|
              dsimp only [Program.subroutineOk, fn_subroutine_ok,
                ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard] at $hypId:ident)))
            let some ty' ← refreshTy? uName | return
            ty := ty'
        else if dom.isAppOfArity ``BitVec 1 then
          let bNow ← currentBaseExpr
          let bStx ← withMainContext do Term.exprToSyntax (← instantiateMVars bNow)
          evalTactic (← `(tactic| replace $hypId:ident := $hypId:ident $bStx))
          (← getGoals).forM instantiateMVarDeclMVars
          let some ty1 ← refreshTy? uName | return
          ty := ty1
          if let .forallE _ dom2 _ _ := ty then
            if dom2.consumeMData.isAppOf ``Eq then
              let hbId := mkIdent `hb
              let _ ← tryTactic (evalTactic (← `(tactic| replace $hypId:ident := $hypId:ident $hbId:ident)))
          let _ ← tryTactic (evalTactic (← `(tactic|
            dsimp only [Program.subroutineOk, fn_subroutine_ok,
              ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard] at $hypId:ident)))
          let some ty2 ← refreshTy? uName | return
          ty := ty2
      unless ty.isAppOfArity ``Arm64.subroutine_ok 4 do
        return
      let bNow ← currentBaseExpr
      let progArg := (ty.getArg! 1).consumeMData
      let mut entryArg := (ty.getArg! 2).consumeMData
      let some (cConst, bArg, hArg, oArg) ← withMainContext (extractRebase? progArg) | return
      let sameBase ← withMainContext do
        pure (bArg == bNow || (← withReducible (isDefEq bArg bNow)))
      unless cConst == info.codeConst && sameBase do
        return
      if let some placedFnOff := placedFnOff? then
        if let some s ← withMainContext (extractFnAddrSym? entryArg) then
          if let some calleeInfo := lookupFnEntry? env s (some info.codeConst) then
            let fnOffStx ← placedFnOff calleeInfo
            evalTactic (← `(tactic|
              rw [fnAddr_rebase_eq_add_of_fnOff $fnOffStx:term] at $hypId:ident))
        else if let some calleeInfo ← withMainContext (findRegisteredFnOff? env entryArg) then
          if calleeInfo.codeConst == info.codeConst then
            let fnOffStx ← placedFnOff calleeInfo
            let _ ← tryTactic (evalTactic (← `(tactic| rw [Program.fnOff_rebase] at $hypId:ident)))
            let _ ← tryTactic (evalTactic (← `(tactic| rw [$fnOffStx:term] at $hypId:ident)))
        return
      if let some s ← withMainContext (extractFnAddrSym? entryArg) then
        if s == info.sym then
          return
        if let some calleeInfo := lookupFnEntry? env s (some info.codeConst) then
          let k := (2 ^ 64 + calleeInfo.off - info.off) % (2 ^ 64)
          let callerFnOffId := mkIdent info.fnOffLemma
          let calleeFnOffId := mkIdent calleeInfo.fnOffLemma
          let kLit := Syntax.mkNumLit (toString k)
          evalTactic (← `(tactic|
            rw [fnAddr_callee_of_fnOff $callerFnOffId:ident $calleeFnOffId:ident (k := $kLit) (by decide)] at $hypId:ident))
          return
      -- Fold registered `Program.fnOff` via `fnOffLemma` to avoid unfolding `Program` constants.
      if let some calleeInfo ← withMainContext (findRegisteredFnOff? env entryArg) then
        if calleeInfo.codeConst == info.codeConst then
          let calleeFnOffId := mkIdent calleeInfo.fnOffLemma
          let _ ← tryTactic (evalTactic (← `(tactic| rw [Program.fnOff_rebase] at $hypId:ident)))
          let _ ← tryTactic (evalTactic (← `(tactic| rw [$calleeFnOffId:ident] at $hypId:ident)))
          let some ty' ← refreshTy? uName | return
          ty := ty'
          if ty.isAppOfArity ``Arm64.subroutine_ok 4 then
            entryArg := (ty.getArg! 2).consumeMData
      let bNow2 ← currentBaseExpr
      let (basePart, calleeOff) ← withMainContext (sepEntryAddrBaseOff entryArg)
      let sameBase2 ← withMainContext do
        pure (basePart == bNow2 || (← withReducible (isDefEq basePart bNow2)))
      if sameBase2 then
        if calleeOff != info.off then
          let k := (2 ^ 64 + calleeOff - info.off) % (2 ^ 64)
          let callerFnOffId := mkIdent info.fnOffLemma
          let calleeOffLit := Syntax.mkNumLit (toString calleeOff)
          let kLit := Syntax.mkNumLit (toString k)
          -- Pass `X` and `O` explicitly since `b + calleeOff#64` does not mention the program's hooks.
          let (hStx, oStx) ← withMainContext do
            let progNow := (ty.getArg! 1).consumeMData
            let (hNow, oNow) ← match ← extractRebase? progNow with
              | some (_, _, h', o') => pure (h', o')
              | none => pure (hArg, oArg)
            pure (← Term.exprToSyntax (← instantiateMVars hNow),
                  ← Term.exprToSyntax (← instantiateMVars oNow))
          let _ ← tryTactic (evalTactic (← `(tactic|
            change Arm64.subroutine_ok _ (_ + BitVec.ofNat 64 $calleeOffLit) _ at $hypId:ident)))
          evalTactic (← `(tactic|
            rw [base_add_callee_of_fnOff (X := $hStx) (O := $oStx) $callerFnOffId:ident
              (calleeOff := $calleeOffLit) (k := $kLit) (by decide)] at $hypId:ident))
          (← getGoals).forM instantiateMVarDeclMVars

private partial def rebaseCodeArgs? (e : Expr) (fuel : Nat := 8) : MetaM (Option (Array Expr)) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Program.rebase 4 then
    return some (e.getArg! 0).consumeMData.getAppArgs
  match fuel with
  | 0 => return none
  | fuel' + 1 =>
    if let .const nm _ := e.getAppFn.consumeMData then
      if ← isBlockedEntryUnfoldHead (← getEnv) nm then
        return none
    if let some e' ← unfoldDefinition? e then
      return ← rebaseCodeArgs? e' fuel'
    return none

private def wpInitCore (isPanic : Bool) (a? s0? : Option Ident) (pInit? : Option Term) :
    TacticM Unit := do
  if isPanic then
    let aId ← match a? with
      | some id => pure id
      | none => freshIdent `x
    let s0Id ← match s0? with
      | some id => pure id
      | none => freshIdent `s0
    evalTactic (← `(tactic| wpp_init $aId:ident $s0Id:ident))
  else
    match a?, s0?, pInit? with
    | some aId, some s0Id, some pInit =>
      evalTactic (← `(tactic| wp_init $aId:ident $s0Id:ident $pInit:term))
    | some aId, some s0Id, none =>
      evalTactic (← `(tactic| wp_init $aId:ident $s0Id:ident))
    | none, none, some pInit =>
      evalTactic (← `(tactic| wp_init $pInit:term))
    | _, _, _ =>
      evalTactic (← `(tactic| wp_init))

private def wpEntryPlacedTail (isPanic : Bool) (a? s0? : Option Ident) (pInit? : Option Term)
    (info : FnEntryInfo) (bExpr : Expr) (entryIsAddr : Bool) (hasRegFnOff : Bool) : TacticM Unit := do
  let fnOffTerm (e : FnEntryInfo) : TacticM Term := withMainContext do
    let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
    let some args ← rebaseCodeArgs? (tgt.getArg! 1)
      | throwError "wp_entry: could not extract the code arguments of the placed program"
    let c ← mkConstWithFreshMVarLevels e.fnOffLemma
    Term.exprToSyntax (mkAppN c args)
  if !entryIsAddr then
    let t ← fnOffTerm info
    if info.off == 0 then
      evalTactic (← `(tactic| rw [fnAddr_rebase_eq_base_of_fnOff_zero $t:term]))
    else
      evalTactic (← `(tactic| rw [fnAddr_rebase_eq_add_of_fnOff $t:term]))
  else if hasRegFnOff then
    let t ← fnOffTerm info
    let _ ← tryTactic (evalTactic (← `(tactic| rw [Program.fnOff_rebase])))
    let _ ← tryTactic (evalTactic (← `(tactic| rw [$t:term])))
  bridgeLocalCallees info bExpr (some fnOffTerm)
  wpInitCore isPanic a? s0? pInit?

private def wpEntryCoreBody (tacName : String) (isPanic : Bool) (sym? : Option String)
    (a? s0? : Option Ident) (pInit? : Option Term) : TacticM Unit := do
  prepareBaseQuantifiedGoal
  let g0 ← getMainGoal
  let (info, bExpr, hExpr, oExpr, needsEntryRw, isZeroOffBase, hasRegFnOff) ← g0.withContext do
    let tgt := (← instantiateMVars (← g0.getType)).consumeMData
    unless tgt.isAppOfArity ``Arm64.subroutine_ok 4 do
      throwError "{tacName}: goal must be `subroutine_ok`, `Program.subroutineOk`, `Program.relocSubroutineOk`, or `Obj.LinkedImage.subroutineOk`, got{indentExpr tgt}"
    let progExpr := (tgt.getArg! 1).consumeMData
    let entryExpr := (tgt.getArg! 2).consumeMData
    let some (codeConst, bExpr, hExpr, oExpr) ← extractRebase? progExpr
      | throwError "{tacName}: could not extract `<codeConst>.rebase b H` from program{indentExpr progExpr}{entryProgramHint tacName progExpr}"
    let env ← getEnv
    let goalFnSym? ← extractFnAddrSym? entryExpr
    let entryNorm ← substRegisteredFnOffs env entryExpr
    let hasRegFnOff := (← findRegisteredFnOff? env entryExpr).isSome
    if goalFnSym?.isNone then
      if let some badHead := unreducedEntryHead? entryNorm then
        throwError "{tacName}: unreduced symbol/address lookup (`{badHead}`) in entry expression{indentExpr entryExpr}\nhint: pre-fold the entry address before calling `{tacName}` (for example, `have hentry : <entry> = b + 0x...#64 := ...; rw [hentry]`, or rewrite the entry to `((<progPC> pl).rebase b H).fnAddr \"sym\"`)"
    let info? ← match sym? with
      | some sym =>
        pure ((lookupFnEntry? env sym (some codeConst)).orElse fun _ => lookupFnEntry? env sym none)
      | none =>
        match goalFnSym? with
        | some sym =>
          pure ((lookupFnEntry? env sym (some codeConst)).orElse fun _ => lookupFnEntry? env sym none)
        | none =>
          let (basePart, offNat) ← sepEntryAddrBaseOff entryExpr
          if basePart == bExpr || (← withReducible (isDefEq basePart bExpr)) then
            pure (lookupFnEntryByOff? env codeConst offNat)
          else
            let (bBase, bOff) ← sepEntryAddrBaseOff bExpr
            if bOff > 0 && offNat ≥ bOff &&
                (basePart == bBase || (← withReducible (isDefEq basePart bBase))) then
              pure (lookupFnEntryByOff? env codeConst (offNat - bOff))
            else
              pure none
    let some info := info?
      | throwError "{tacName}: no registered function entry found (symbol: {sym?.orElse (fun _ => goalFnSym?)}); make sure the generated `*Fns.lean` or `*Fetch.lean` module is imported"
    let hasFnAddr := goalFnSym? == some info.sym
    let isZeroBase := !hasFnAddr && info.off == 0 &&
      (entryExpr == bExpr || (← withReducible (isDefEq entryExpr bExpr)))
    pure (info, bExpr, hExpr, oExpr, !hasFnAddr, isZeroBase, hasRegFnOff)

  if info.placed then
    return ← wpEntryPlacedTail isPanic a? s0? pInit? info bExpr needsEntryRw hasRegFnOff

  if needsEntryRw then
    let (hStx, oStx) ← g0.withContext do
      pure (← Term.exprToSyntax (← instantiateMVars hExpr),
            ← Term.exprToSyntax (← instantiateMVars oExpr))
    let fnOffId := mkIdent info.fnOffLemma
    if hasRegFnOff then
      let _ ← tryTactic (evalTactic (← `(tactic| rw [Program.fnOff_rebase])))
      let _ ← tryTactic (evalTactic (← `(tactic| rw [$fnOffId:ident])))
    if isZeroOffBase then
      let _ ← tryTactic (evalTactic (← `(tactic|
        rw [← fnAddr_rebase_eq_base_of_fnOff_zero (X := $hStx) (O := $oStx) $fnOffId:ident])))
    else
      let offLit := Syntax.mkNumLit (toString info.off)
      let _ ← tryTactic (evalTactic (← `(tactic| (
        change Arm64.subroutine_ok _ (_ + BitVec.ofNat 64 $offLit) _
        rw [← fnAddr_rebase_eq_add_of_fnOff (X := $hStx) (O := $oStx) $fnOffId:ident]))))
    (← getGoals).forM instantiateMVarDeclMVars

  bridgeLocalCallees info bExpr

  let (bStx, hStx) ← withMainContext do
    let tgtNow := (← instantiateMVars (← getMainTarget)).consumeMData
    let (bNow, hNow) ← do
      if tgtNow.isAppOfArity ``Arm64.subroutine_ok 4 then
        if let some (_, b', h', _) ← extractRebase? (tgtNow.getArg! 1).consumeMData then
          pure (b', h')
        else pure (bExpr, hExpr)
      else pure (bExpr, hExpr)
    pure (← Term.exprToSyntax (← instantiateMVars bNow),
          ← Term.exprToSyntax (← instantiateMVars hNow))
  let codeId := mkIdent info.codeConst
  let decId := mkIdent info.decPrefix
  let fnOffId := mkIdent info.fnOffLemma
  let offLit := Syntax.mkNumLit (toString info.off)
  let szLit := Syntax.mkNumLit (toString info.sizeBytes)
  evalTactic (← `(tactic|
    code_fetches $codeId:ident $decId:ident $bStx:term $hStx:term $fnOffId:ident $offLit:num $szLit:num))
  (← getGoals).forM instantiateMVarDeclMVars

  -- Hide hypotheses mentioning `Program.fnAddr` during `wp_init` so `wpSplitAndNormHyps` does not
  -- unfold `fnAddr` to `b + off#64` before `examples_generalize_entry` runs.
  let isProtectedFnAddrHyp (ty : Expr) : Bool :=
    (ty.find? (·.isAppOfArity ``Program.fnAddr 2)).isSome &&
      (ty.isForall ||
        !(ty.isAppOf ``And || isSubroutineOkApp ty ||
          match ty.eq? with
          | some (_, lhs, _) => lhs.isAppOf ``Program.fetch
          | none => false))
  let protectedHyps ← do
    let g ← getMainGoal
    g.withContext do
      let env ← getEnv
      let mut out : Array (Name × Array Name) := #[]
      for decl in (← getLCtx) do
        if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
          let ty := (← instantiateMVars decl.type).consumeMData
          if isProtectedFnAddrHyp ty then
            let ref ← IO.mkRef (#[] : Array Name)
            ty.forEach fun sub => do
              if sub.isConst then
                let nm := sub.constName!
                if nm != ``Arm64.Program.mk && nm != ``Arm64.Program.rebase &&
                   nm != ``Arm64.Program.ofImage && nm != ``Arm64.Program.ofWords &&
                   nm != ``Arm64.Obj.LinkedImage.toProgram then
                  if !(← isReducible nm) then
                    if let some cinfo := env.find? nm then
                      if let some val := cinfo.value? then
                        if val.getLambdaBody.getAppFn.isConstOf ``Arm64.Program.rebase then
                          let cur ← ref.get
                          if !cur.contains nm then
                            ref.set (cur.push nm)
            out := out.push (decl.userName, ← ref.get)
      pure out
  for (uName, abbrs) in protectedHyps do
    let hypId := mkIdent uName
    for nm in abbrs do
      let nmId := mkIdent nm
      let _ ← tryTactic (evalTactic (← `(tactic| delta $nmId:ident at $hypId:ident)))
  let protectedFVars ← do
    if protectedHyps.isEmpty then
      pure #[]
    else
      let g ← getMainGoal
      g.withContext do
        let mut lctx ← getLCtx
        let mut fids : Array FVarId := #[]
        for decl in lctx do
          if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
            let ty := (← instantiateMVars decl.type).consumeMData
            if isProtectedFnAddrHyp ty then
              fids := fids.push decl.fvarId
              lctx := lctx.setKind decl.fvarId .implDetail
        if !fids.isEmpty then
          let g' ← mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType) .syntheticOpaque (← g.getTag)
          g.assign g'
          replaceMainGoal [g'.mvarId!]
        pure fids

  wpInitCore isPanic a? s0? pInit?

  if !protectedFVars.isEmpty then
    let g ← getMainGoal
    g.withContext do
      let mut lctx ← getLCtx
      for fid in protectedFVars do
        if lctx.contains fid then
          lctx := lctx.setKind fid .default
      let g' ← mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType) .syntheticOpaque (← g.getTag)
      g.assign g'
      replaceMainGoal [g'.mvarId!]

  evalTactic (← `(tactic| examples_generalize_entry))
  evalTactic (← `(tactic| examples_hide_fetches))

/-- Core implementation of `wp_entry` / `wp_init_fn` / `wpp_entry`. Catches `maxRecDepth`
    exhaustion and attaches an actionable hint explaining how to pre-fold concrete image,
    placement, or symbol-table projections before calling `wp_entry`. -/
def wpEntryCore (isPanic : Bool) (sym? : Option String) (a? s0? : Option Ident)
    (pInit? : Option Term) : TacticM Unit := do
  let tacName := if isPanic then "wpp_entry" else "wp_entry"
  let savedInit ← saveState
  MonadRuntimeException.tryCatchRuntimeEx
    (wpEntryCoreBody tacName isPanic sym? a? s0? pInit?)
    fun ex => do
      if ex.isMaxRecDepth || ex.toMessageData.hasTag (· == `nested.runtime.maxRecDepth) then
        restoreState savedInit
        withTheReader Core.Context (fun ctx => { ctx with currRecDepth := 0, maxRecDepth := 0 }) do
          let heads ← match (← getGoals) with
            | g :: _ => g.withContext (collectTableOrLookupHeads g)
            | [] => pure #[]
          let foundNote : MessageData :=
            if heads.isEmpty then m!""
            else
              let listStr := String.intercalate ", " (heads.toList.map (s!"`{·}`"))
              m!" (saw {listStr} in goal/context)"
          throwError "{tacName}: maximum recursion depth (`maxRecDepth`) reached during entry setup{foundNote}\nhint: pre-fold concrete `Obj.Image` / `Obj.LinkedImage` / `Obj.Interned` / `PlacedLib` / symbol-table or address projections before calling `{tacName}` (for example, `have hentry : <addr> = b + 0x...#64 := ...; rw [hentry]`, or bind large table expressions behind an opaque local `have`/`generalize` hypothesis)"
      throw ex

/-- Symbol-keyed function entry tactic for `SepWP`:
    looks up the function's offset, size, and decode prefix in `fnEntryExt` (by `"sym"` or
    inferred from the goal's `fnAddr` / `b + 0x...#64` entry address), emits `code_fetches`,
    runs `wp_init`, generalizes the entry address (`examples_generalize_entry`), and hides
    the fetch hypotheses (`examples_hide_fetches`). For a placed library entry (registered by
    `gen_placed_fnOffs`) on `(P a).rebase b H`, it instead rewrites the entry and local callee
    hypotheses to `b + off#64` and runs `wp_init` only (fetches come from the global
    `P_rebase_fetch_0x<off>` lemmas). -/
syntax "wp_entry" (ppSpace colGt str)? (atomic(ppSpace colGt ident ppSpace colGt ident))?
  (ppSpace colGt term)? : tactic

/-- Alias for `wp_entry`. -/
syntax "wp_init_fn" (ppSpace colGt str)? (atomic(ppSpace colGt ident ppSpace colGt ident))?
  (ppSpace colGt term)? : tactic

/-- Panic-aware symbol-keyed function entry tactic for `SepWPp` (`wpp_init`). -/
syntax "wpp_entry" (ppSpace colGt str)? (atomic(ppSpace colGt ident ppSpace colGt ident))? : tactic

elab_rules : tactic
  | `(tactic| wp_entry $[$sym?:str]? $[$a?:ident $s0?:ident]? $[$pInit?:term]?) =>
    wpEntryCore false (sym?.map (·.getString)) a? s0? pInit?
  | `(tactic| wp_init_fn $[$sym?:str]? $[$a?:ident $s0?:ident]? $[$pInit?:term]?) =>
    wpEntryCore false (sym?.map (·.getString)) a? s0? pInit?
  | `(tactic| wpp_entry $[$sym?:str]? $[$a?:ident $s0?:ident]?) =>
    wpEntryCore true (sym?.map (·.getString)) a? s0? none

end

end ProofLib
