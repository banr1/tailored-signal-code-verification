/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.CallInv

/-!
# `InImageKit`: Explicit-Invariant `wp_call` for `.inImage` Callees

Provides `SepWP` and `SepWPp` call lemmas (`call_imgInv`, `call_inImage`) and the tactics
`wp_call_inImage` / `wp_call_frozen` that thread `ImgCallInv img s`
(`img.FrozenLoaded s ∧ s.symtab = img.symtab`) as an explicit term across `bl` calls without
exposing `Obj.Image.FrozenLoaded` to `simp`.

## Usage Rules
- Never run `simp`, `simp_all`, or `simp … at *` on goals or hypotheses containing
  `Obj.Image.FrozenLoaded` (unassigned ghost metavariables under `FrozenLoaded` cause multi-GB
  blowups).
- `wp_call_inImage hcall hinv (x)?` (alias `wp_call_frozen`) discharges the callee's `.inImage`
  invariant from `hinv` via `mem`/`symtab` equalities, clears invariant hypotheses before running
  the spatial precondition discharger, and supplies `hinv_sf : ImgCallInv img sf` to the
  continuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib

/-! ## Call Lemmas -/

/-- `ImgCallInv` depends only on `mem` and `symtab`. -/
theorem imgCallInv_of_mem_eq {img : Obj.Image} {s s' : State} (h : ImgCallInv img s)
    (hmem : s'.mem = s.mem) (hsym : s'.symtab = s.symtab) : ImgCallInv img s' :=
  ⟨frozenLoaded_of_mem_eq hmem h.1, hsym.trans h.2⟩

/-- The `.inImage` precondition from the invariant term and the plain precondition. -/
theorem satisfies_inImage_pre {α : Type} {spec : Spec α} {img : Obj.Image} {x : α} {s : State}
    {R : SepProp} (hinv : ImgCallInv img s) (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
  show s.mem ⊨ (⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗ spec.pre x s) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hinv, hpre⟩

/-- Framed `bl` to a plain-`spec` callee in `SepWP`. The continuation also gets
    `ImgCallInv img sf`, carried over from `hinv`. -/
theorem SepWP.call_imgInv {α : Type} {prog : Program} {img : Obj.Image}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := ret_pc) hinv
    (ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp hlr hpre h_no_panic h_no_exit
      (fun sf hpcf hrunf hspf hcsf =>
        ProofLib.SepWP.done hpcf hrunf (hnext sf hpcf hrunf hspf hcsf))
      (fun R' sf ho h => (not_satisfies_false_sepConj (h_no_oom (F ∗ R') sf ho h)).elim))

/-- `SepWP.call_imgInv` for a `spec.inImage img` callee: the invariant conjunct of the callee's
    precondition is discharged by `hinv`; `hpre` only concerns the plain `spec.pre`. -/
theorem SepWP.call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  SepWP.call_imgInv (spec := spec.inImage img) (x := x) hcall hinv hpc hrun hsp hlr
    (fun R hm => satisfies_inImage_pre hinv (hpre R hm)) h_no_panic h_no_exit hnext h_no_oom

/-- Framed `bl` to a plain-`spec` (possibly panicking) callee in `SepWPp`. The continuation also
    gets `ImgCallInv img sf`, carried over from `hinv`. -/
theorem SepWPp.call_imgInv {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hfz_sf hsym_sf =>
      hnext sf hpc_sf hrun_sf hsp_sf hcs_sf ⟨hfz_sf, hsym_sf⟩)
    (fun sf R' hoom hpost => (not_satisfies_false_sepConj (h_no_oom (F ∗ R') sf hoom hpost)).elim)

/-- `SepWPp.call_imgInv` for a `spec.inImage img` callee: the invariant conjunct of the callee's
    precondition is discharged by `hinv`; `hpre` only concerns the plain `spec.pre`. -/
theorem SepWPp.call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_imgInv (spec := spec.inImage img) (x := x) hcall hinv hpc hrun hsp hlr
    (fun R hm => satisfies_inImage_pre hinv (hpre R hm)) hexit hpanic hnext h_no_oom

/-! ## Explicit-Invariant Usage Examples -/

example {img : Obj.Image} {s s' : State} (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hmem : s'.mem = s.mem) (hsym' : s'.symtab = s.symtab) : ImgCallInv img s' :=
  imgCallInv_of_mem_eq ⟨hF, hsym⟩ hmem hsym'

example {α : Type} {spec : Spec α} {img : Obj.Image} {x : α} {s : State} {R : SepProp}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (spec.inImage img).pre x s ∗ R :=
  satisfies_inImage_pre ⟨hF, hsym⟩ hpre

example {α : Type} {prog : Program} {img : Obj.Image} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom : ∀ R' sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s sf ∗ R')) :
    SepWP prog target_pc s P post :=
  SepWP.call_imgInv hcall ⟨hF, hsym⟩ hpc hrun hsp hlr hpre h_no_panic h_no_exit
    (h_no_oom := fun R' sf ho h => (hoom R' sf ho h).elim)
    fun sf h1 h2 h3 h4 ⟨hF_sf, hsym_sf⟩ => hnext sf h1 h2 h3 h4 hF_sf hsym_sf

example {α : Type} {prog : Program} {img : Obj.Image} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom : ∀ R' sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s sf ∗ R')) :
    SepWP prog target_pc s P post :=
  SepWP.call_inImage hcall ⟨hF, hsym⟩ hpc hrun hsp hlr hpre h_no_panic h_no_exit
    (h_no_oom := fun R' sf ho h => (hoom R' sf ho h).elim)
    fun sf h1 h2 h3 h4 ⟨hF_sf, hsym_sf⟩ => hnext sf h1 h2 h3 h4 hF_sf hsym_sf

example {α : Type} {prog : Program} {img : Obj.Image} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ R' sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s sf ∗ R')) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_imgInv hcall ⟨hF, hsym⟩ hpc hrun hsp hlr hpre hexit hpanic
    (h_no_oom := fun R' sf ho h => (hoom R' sf ho h).elim)
    fun sf h1 h2 h3 h4 ⟨hF_sf, hsym_sf⟩ => hnext sf h1 h2 h3 h4 hF_sf hsym_sf

example {α : Type} {prog : Program} {img : Obj.Image} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ R' sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s sf ∗ R')) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_inImage hcall ⟨hF, hsym⟩ hpc hrun hsp hlr hpre hexit hpanic
    (h_no_oom := fun R' sf ho h => (hoom R' sf ho h).elim)
    fun sf h1 h2 h3 h4 ⟨hF_sf, hsym_sf⟩ => hnext sf h1 h2 h3 h4 hF_sf hsym_sf

/-! ## `wp_call_inImage` and `wp_call_frozen` Tactics -/

open Lean Elab Tactic Meta

/-- Last string component of a constant name. -/
meta def inImageKitLastStr : Name → String
  | .str _ s => s
  | .num p _ => inImageKitLastStr p
  | .anonymous => ""

/-- Does `e` mention `Obj.Image.FrozenLoaded`, `ImgCallInv` or `FrozenInv`? -/
meta def inImageKitMentionsInv (e : Expr) : Bool :=
  (e.find? fun t => t.isConst &&
    (t.constName! == ``Arm64.Obj.Image.FrozenLoaded ||
      ["ImgCallInv", "FrozenInv"].contains (inImageKitLastStr t.constName!))).isSome

/-- The image `img` of an invariant type `img.FrozenLoaded s` / `ImgCallInv img s` /
    `FrozenInv img s`, or of the first such conjunct of an `And`. -/
meta partial def inImageKitFindImg? (ty : Expr) : Option Expr :=
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Arm64.Obj.Image.FrozenLoaded 2 then some (ty.getArg! 0)
  else if ty.getAppNumArgs == 2 && ty.getAppFn.isConst &&
      ["ImgCallInv", "FrozenInv"].contains (inImageKitLastStr ty.getAppFn.constName!) then
    some (ty.getArg! 0)
  else if ty.isAppOfArity ``And 2 then
    (inImageKitFindImg? (ty.getArg! 0)).orElse fun _ => inImageKitFindImg? (ty.getArg! 1)
  else none

/-- Clear (where possible) every hypothesis of the main goal whose type mentions the image
    invariant, so that `wpDischargeCallSubgoalsCore`'s `simp … [*] at *` never sees it. Hypotheses
    of type `subroutine_ok …` are kept. -/
meta def inImageKitClearInvHyps : TacticM Unit := do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut acc : Array FVarId := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOf ``Arm64.subroutine_ok then continue
      if inImageKitMentionsInv ty then acc := acc.push decl.fvarId
    return acc
  let g' ← g.tryClearMany fvs
  replaceMainGoal [g']

/-- Clear the hypothesis with user name `n` from the main goal, if present. -/
meta def inImageKitClearByName (n : Name) : TacticM Unit := do
  let g ← getMainGoal
  let some decl := (← g.getDecl).lctx.findFromUserName? n | return
  replaceMainGoal [← g.tryClear decl.fvarId]

/-- Copy of the engine's private `destructureSatHyps`. -/
meta def inImageKitDestructureSat : TacticM Unit := do
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let lctx ← g.withContext getLCtx
    let mut progress := false
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
        let ty ← g.withContext (instantiateMVars decl.type)
        if (ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2) &&
           (ty.find? (·.isConstOf ``SepProp.Satisfies)).isSome then
          let id := mkIdent decl.userName
          let vId ← freshIdent `v_stk
          if ← tryTacticCatchRuntimeBool
              (evalTactic (← `(tactic| rcases $id:ident with ⟨$vId:ident, $id:ident⟩))) then
            progress := true
            break
    if !progress then break

/-- Copy of the engine's private `closeCallAddrEqSubgoal`. -/
meta def inImageKitCloseAddrEq (g : MVarId) (preferGoal : Bool) : TacticM Bool := do
  setGoals [g]
  let (closedFastMeta, distinctFastMeta) ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | return (false, false)
    if rhs.hasMVar then return (false, false)
    let (lhsAddr, hPc?) ← do
      if lhs.isAppOfArity ``State.pc 1 then
        let s := lhs.getArg! 0
        if let some (pc, prf) ← provePcEq? s then
          Pure.pure (pc, some prf)
        else if s.isFVar then
          let mut found : Option (Expr × Expr) := none
          for decl in (← getLCtx) do
            if !decl.isImplementationDetail && !decl.isAuxDecl then
              let dty ← instantiateMVars decl.type
              if let some (_, l, r) := dty.eq? then
                if l.isAppOfArity ``State.pc 1 && l.getArg! 0 == s then
                  found := some (r, decl.toExpr)
                  break
          match found with
          | some (pc, prf) => Pure.pure (pc, some prf)
          | none => Pure.pure (lhs, none)
        else
          Pure.pure (lhs, none)
      else
        Pure.pure (lhs, none)
    if let some hAddr ← proveSepAddrEqMeta? lhsAddr rhs then
      let prf ← match hPc? with
        | some hp => mkEqTrans hp hAddr
        | none => Pure.pure hAddr
      g.assign (← mkExpectedTypeHint prf ty)
      return (true, false)
    let (lhsNorm0, _) ← SepSolver.normAddrMeta lhsAddr
    let (rhsNorm0, _) ← SepSolver.normAddrMeta rhs
    let (b1, o1) ← sepAddrBaseOff lhsNorm0
    let (b2, o2) ← sepAddrBaseOff rhsNorm0
    if o1 != o2 && (b1 == b2 || (← withReducible (isDefEq b1 b2))) then
      return (false, true)
    return (false, false)
  if closedFastMeta then
    replaceMainGoal []
    return true
  if distinctFastMeta then
    return false
  let saved ← saveState
  let closer ← if preferGoal then
      `(tactic| wp_focus_close (first | wp_norm_goal | wp_norm_lhs))
    else
      `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  if ← tryTacticCatchRuntimeBool (evalTactic closer) then
    return true
  saved.restore
  setGoals [g]
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_norm_goal)))
  if (← getGoals).isEmpty then
    return true
  let g1 ← getMainGoal
  let closedAfterNorm ← g1.withContext do
    let ty ← instantiateMVars (← g1.getType)
    let some (_, lhs, rhs) := ty.eq? | return false
    if !rhs.hasMVar then
      if let some prf ← proveSepAddrEqMeta? lhs rhs then
        g1.assign (← mkExpectedTypeHint prf ty)
        return true
    let (lhsNorm, hLhs?) ← SepSolver.normAddrMeta lhs
    let (rhsNorm, hRhs?) ← SepSolver.normAddrMeta rhs
    if !rhs.hasMVar &&
        (lhsNorm == rhsNorm || (← withReducibleAndInstances (isDefEq lhsNorm rhsNorm))) then
      let hLhs ← match hLhs? with | some p => Pure.pure p | none => mkEqRefl lhs
      let hRhs ← match hRhs? with | some p => Pure.pure p | none => mkEqRefl rhs
      let prf ← mkEqTrans hLhs (← mkEqSymm hRhs)
      g1.assign (← mkExpectedTypeHint prf ty)
      return true
    return false
  if closedAfterNorm then
    replaceMainGoal []
    return true
  saved.restore
  setGoals [g]
  return false

/-- Close the 4 call-site goals (`pc`, `status`, `spAligned`, `lr`); copy of the engine's private
    `closeCallSiteSetupSubgoals` with plain error messages. -/
meta def inImageKitCloseSetup (tacName : String) : TacticM Unit := do
  let gs ← getGoals
  let gPc :: gRun :: gSp :: gLr :: rest := gs
    | throwError "{tacName}: unexpected subgoals after applying the call lemma"
  if !(← inImageKitCloseAddrEq gPc (preferGoal := true)) then
    throwError "{tacName}: call target address does not match callee entry:{indentD (MessageData.ofGoal gPc)}"
  setGoals [gRun]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_norm_lhs)))) then
    throwError "{tacName}: failed to prove machine status is `.Running`:{indentD (MessageData.ofGoal gRun)}"
  setGoals [gSp]
  if !(← tryTacticCatchRuntimeBool
      (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
    throwError "{tacName}: failed to prove `s.spAligned = true`:{indentD (MessageData.ofGoal gSp)}"
  if !(← inImageKitCloseAddrEq gLr (preferGoal := false)) then
    throwError "{tacName}: failed to resolve link register (`s.readReg64 .lr = ret_pc`):{indentD (MessageData.ofGoal gLr)}"
  setGoals (← rest.filterM fun m => not <$> m.isAssigned)

/-- `SepWPp` analogue of the engine's `wpElimSpatialContext`. -/
meta def inImageKitElimSpatialWPp (hEq : Ident) : TacticM Unit := do
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``SepWPp 7 do return
    let P := (ty.getArg! 3).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      evalTactic (← `(tactic| (apply ProofLib.SepWPp.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 &&
        (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      evalTactic (← `(tactic| (apply ProofLib.SepWPp.pure_elim; intro $hId:ident)))
      wpNormAndSplitHyp hId
    else
      return

/-- Core of `wp_call_inImage` / `wp_call_frozen`. -/
meta def inImageKitCall (tacName : String) (hcall hinv : Term) (arg? : Option Term) :
    TacticM Unit := do
  let g0 ← getMainGoal
  let gty ← g0.withContext do instantiateMVars (← g0.getType)
  let gty := gty.consumeMData
  let isWPp ← if gty.isAppOfArity ``SepWPp 7 then pure true
    else if gty.isAppOfArity ``SepWP 6 then pure false
    else throwError "{tacName}: goal is not `SepWP …` / `SepWPp …`"
  let sGoal := gty.getArg! 2
  -- Is the callee contract `.inImage`? Also find `img`. It must be explicit in the `have` type
  -- below: a `_` there is not solved before the `by` block runs, so the `have` fails.
  let (inImg, imgE) ← g0.withContext <| withoutModifyingState do
    let e ← Tactic.elabTerm hcall none
    let ty ← whnfR (← instantiateMVars (← inferType e))
    if !ty.isAppOfArity ``Arm64.subroutine_ok 4 then
      throwError "{tacName}: `{hcall}` is not a `subroutine_ok` hypothesis:{indentExpr ty}"
    let specE := (ty.getArg! 3).consumeMData
    if specE.isAppOfArity ``Arm64.Spec.inImage 3 then
      return (true, ← instantiateMVars (specE.getArg! 2))
    let hty ← instantiateMVars (← inferType (← Tactic.elabTerm hinv none))
    let some img := inImageKitFindImg? hty
      | throwError "{tacName}: cannot read the image `img` off `{hinv} : {hty}`"
    return (false, ← instantiateMVars img)
  let hinvId ← freshIdent `hinv_call
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hinvSfId ← freshIdent `hinv_sf
  -- 1. The invariant at the call state, as a term. No `simp` on anything mentioning `FrozenLoaded`:
  --    only `exact`, or `imgCallInv_of_mem_eq` with `simp only` on `mem` / `symtab` equalities.
  let sStx ← g0.withContext (Term.exprToSyntax sGoal)
  let imgStx ← g0.withContext (Term.exprToSyntax imgE)
  let haveStx ← `(tactic|
    have $hinvId:ident : CryptoVerification.LibsignalTripleRatchet.ImgCallInv $imgStx $sStx := by
      first
        | with_reducible exact $hinv
        | exact ⟨($hinv).1, ($hinv).2⟩
        | exact ⟨$hinv, by assumption⟩
        | exact CryptoVerification.LibsignalTripleRatchet.imgCallInv_of_mem_eq $hinv
            (by simp only [arm64_norm, wp_norm]; done) (by simp only [arm64_norm, wp_norm]; done)
        | exact CryptoVerification.LibsignalTripleRatchet.imgCallInv_of_mem_eq
            ⟨($hinv).1, ($hinv).2⟩
            (by simp only [arm64_norm, wp_norm]; done) (by simp only [arm64_norm, wp_norm]; done)
        | exact CryptoVerification.LibsignalTripleRatchet.imgCallInv_of_mem_eq
            ⟨$hinv, by assumption⟩
            (by simp only [arm64_norm, wp_norm]; done) (by simp only [arm64_norm, wp_norm]; done))
  if !(← tryTacticCatchRuntimeBool (evalTactic haveStx)) then
    throwError "{tacName}: could not establish `ImgCallInv img s` at the call state from `{hinv}`. \
      Pass `ImgCallInv img s` / `FrozenInv img s` / `img.FrozenLoaded s` (with a `symtab` \
      hypothesis) for a state `s` with the same `mem` and `symtab` as the call state, or cut \
      with `SepWP.seq_inImage` / `SepWPp.of_sepWP_inImage` before the stores."
  -- 2. Apply the call lemma.
  let lemmaName : Name := match isWPp, inImg with
    | false, true => ``CryptoVerification.LibsignalTripleRatchet.SepWP.call_inImage
    | false, false => ``CryptoVerification.LibsignalTripleRatchet.SepWP.call_imgInv
    | true, true => ``CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    | true, false => ``CryptoVerification.LibsignalTripleRatchet.SepWPp.call_imgInv
  let lem := mkCIdent lemmaName
  let applyStx ← match arg? with
    | some a => `(tactic| apply ($lem $hcall $hinvId (x := $a)))
    | none => `(tactic| apply ($lem $hcall $hinvId))
  evalTactic applyStx
  inImageKitCloseSetup tacName
  let gs ← getGoals
  let gPre :: gA :: gB :: gCont :: rest := gs
    | throwError "{tacName}: unexpected subgoals after the call-site setup"
  -- 3. Framed precondition (plain `spec.pre`; image-invariant hypotheses cleared first).
  setGoals [gPre]
  inImageKitClearInvHyps
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  inImageKitDestructureSat
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  let preLeft ← getGoals
  -- 4. Callee exit / panic goals. `SepWP`: `h_no_panic`, `h_no_exit`. `SepWPp`: `hexit`, `hpanic`.
  let mut side : List MVarId := []
  if isWPp then
    setGoals [gA]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hinvId.getId
    let gB' ← getMainGoal
    gB'.setTag `panic
    side := side ++ [gB']
  else
    setGoals [gA]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
  -- 5. Continuation: `sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf`. `hinv_sf` is never simplified.
  setGoals [gCont]
  inImageKitClearByName hinvId.getId
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hinvSfId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  if isWPp then inImageKitElimSpatialWPp hspId else wpElimSpatialContext hspId
  let contGoals ← getGoals
  -- 6. `h_no_oom` (engine v0.23 OOM outcome): `apply` leaves the `autoParam` as a goal; run the
  --    engine's `wp_close_oom_default` on it, keep it open if that fails (abstract `onOom`).
  let mut restOpen : List MVarId := []
  for m in rest do
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    if ty.consumeMData.isAppOfArity ``autoParam 2 then
      let m' ← m.replaceTargetDefEq (ty.consumeMData.getArg! 0)
      let saved ← saveState
      setGoals [m']
      if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_close_oom_default))) then
        if (← getGoals).isEmpty then continue
      saved.restore
      restOpen := restOpen ++ [m']
    else
      restOpen := restOpen ++ [m]
  let preOpen ← preLeft.filterM fun m => not <$> m.isAssigned
  let sideOpen ← side.filterM fun m => not <$> m.isAssigned
  setGoals (contGoals ++ preOpen ++ sideOpen ++ restOpen)

/-- `wp_call_inImage hcall hinv (x)?`: `wp_call` for a callee contract `hcall` (`.inImage img` or
    plain) with the image invariant `hinv` passed as a term. See the module docstring. -/
syntax (name := wpCallInImage) "wp_call_inImage" ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max)? : tactic

/-- Alias for `wp_call_inImage`. -/
syntax (name := wpCallFrozen) "wp_call_frozen" ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_call_inImage $hcall $hinv) => inImageKitCall "wp_call_inImage" hcall hinv none
  | `(tactic| wp_call_inImage $hcall $hinv $arg) =>
    inImageKitCall "wp_call_inImage" hcall hinv (some arg)

elab_rules : tactic
  | `(tactic| wp_call_frozen $hcall $hinv) => inImageKitCall "wp_call_frozen" hcall hinv none
  | `(tactic| wp_call_frozen $hcall $hinv $arg) =>
    inImageKitCall "wp_call_frozen" hcall hinv (some arg)

end CryptoVerification.LibsignalTripleRatchet
