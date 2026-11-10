/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import ProofLib
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Proofs.Common.CallInv
public meta import Lean
public meta import ProofLib

/-!
# Shared Proof Combinators and Guarded `sep_ac_rfl`

Provides `CryptoGames`-free separation-logic and state-invariant helpers shared across
`LibsignalBinary`, `Symbolic`, and `Computational`:
- `sep_ac_rfl`: $O(n \log n)$ separation-logic AC reflexivity via `ProofLib.SepSolver.synReifyPermTbl?`
  with polymorphic atom abstraction, falling back to `ac_rfl` / `sep_frame`.
- `ProofLib.SepWP.weaken_pre_sat`: semantic `SatEntails` precondition weakening for `SepWP`.
- Shared `FrozenLoaded`, `symtab`, `LayoutOk`, `seq_clean_inImage*`, `sepWPp_pure_mid`, and
  `allocFailedIn` lemmas (no global `@[simp]` or `@[wp_norm]` attributes).
-/

@[expose] public section

set_option autoImplicit false

public meta section

partial def denoteSepTreeExpr (xs : Array Lean.Expr) (t : Lean.Expr) : Lean.Expr :=
  if t.isAppOfArity ``ProofLib.SepTree.sep 2 then
    Lean.mkApp2 (Lean.mkConst ``Arm64.SepProp.sepConj)
      (denoteSepTreeExpr xs (t.getArg! 0))
      (denoteSepTreeExpr xs (t.getArg! 1))
  else if t.isAppOfArity ``ProofLib.SepTree.atom 1 then
    match (t.getArg! 0).rawNatLit? with
    | some i => xs[i]!
    | none => Lean.mkConst ``Arm64.SepProp.emp
  else
    Lean.mkConst ``Arm64.SepProp.emp

def eqACOfTblPoly (lhs rhs : Lean.Expr) (tbl : Array Lean.Expr) (tA tB : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  let sepPropTy := Lean.mkConst ``Arm64.SepProp
  let decls : Array (Lean.Name × Lean.Expr) :=
    tbl.mapIdx fun i _ => (Lean.Name.mkSimple s!"a_{i}", sepPropTy)
  let (polyPrf, polyTy) ← Lean.Meta.withLocalDeclsDND decls fun xs => do
    let f := Lean.mkApp (Lean.mkConst ``ProofLib.SepAtomTree.get) (ProofLib.SepSolver.mkSepAtomTree xs)
    let lhsX := denoteSepTreeExpr xs tA
    let rhsX := denoteSepTreeExpr xs tB
    let eqX ← Lean.Meta.mkEq lhsX rhsX
    let body ← Lean.Meta.mkExpectedTypeHint
      (Lean.mkAppN (Lean.mkConst ``ProofLib.SepTree.eq_of_sortIdx) #[f, tA, tB, ProofLib.SepSolver.rflTrue])
      eqX
    return (← Lean.Meta.mkLambdaFVars xs body, ← Lean.Meta.mkForallFVars xs eqX)
  let polyChecked ← Lean.Meta.mkExpectedTypeHint polyPrf polyTy
  Lean.Meta.mkExpectedTypeHint (Lean.mkAppN polyChecked tbl) (← Lean.Meta.mkEq lhs rhs)

open Lean Meta Elab Tactic in
/-- $O(n \log n)$ separation-logic AC reflexivity via `ProofLib.SepSolver.synReifyPermTbl?`
    with polymorphic atom abstraction (preventing kernel delta-unfolding of leaf `SepProp` defs),
    falling back to `ac_rfl` / `sep_frame` on non-`SepProp` or residual AC goals. -/
elab "sep_ac_rfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if let some (_, lhs, rhs) := ty.eq? then
      if lhs == rhs then
        g.assign (← mkEqRefl lhs)
        replaceMainGoal []
      else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
        g.assign (← eqACOfTblPoly lhs rhs tbl tA tB)
        replaceMainGoal []
      else
        evalTactic (← `(tactic| first | ac_rfl | sep_frame))
    else
      evalTactic (← `(tactic| ac_rfl))

end

/-- Semantic frame-preserving entailment weakens the spatial precondition of `SepWP`. -/
theorem _root_.ProofLib.SepWP.weaken_pre_sat {prog : Arm64.Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P P' : Arm64.SepProp} {post : Arm64.State → Arm64.SepProp → Prop}
    {oom : Arm64.State → Arm64.SepProp}
    (himp : ∀ (m : Arm64.Memory) (R : Arm64.SepProp), (m ⊨ P ∗ R) → (m ⊨ P' ∗ R))
    (h : ProofLib.SepWP prog target_pc s P' post oom) :
    ProofLib.SepWP prog target_pc s P post oom :=
  ProofLib.SepWP.weaken_pre_frame (himp s.mem) h

namespace LibsignalBinary.Proofs.Common.SharedHelpers

open Arm64 ProofLib
open CryptoVerification.RustHeap (LayoutOk allocFailedEvent allocFailedIn)

/-! ## `FrozenLoaded`, `symtab`, and `SepWP` Helpers -/

theorem frozenLoaded_setPC (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.FrozenLoaded (s.setPC pc) ↔ img.FrozenLoaded s :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem symtab_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by simp

theorem frozenLoaded_writeReg64 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg64 r v) ↔ img.FrozenLoaded s :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem symtab_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by simp

theorem frozenLoaded_setPState (img : Obj.Image) (s : State) (ps : PState) :
    img.FrozenLoaded (s.setPState ps) ↔ img.FrozenLoaded s :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by simp

theorem frozenLoaded_setPC_setMem (img : Obj.Image) (s : State) (pc : BitVec 64) (m : Memory) :
    img.FrozenLoaded ((s.setPC pc).setMem m) ↔ img.FrozenLoaded (s.setMem m) :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem frozenLoaded_setPState_setMem (img : Obj.Image) (s : State) (ps : PState) (m : Memory) :
    img.FrozenLoaded ((s.setPState ps).setMem m) ↔ img.FrozenLoaded (s.setMem m) :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem frozenLoaded_writeReg64_setMem (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64)
    (m : Memory) :
    img.FrozenLoaded ((s.writeReg64 r v).setMem m) ↔ img.FrozenLoaded (s.setMem m) :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem frozenLoaded_writeVReg128 (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 128) :
    img.FrozenLoaded (s.writeVReg128 idx v) ↔ img.FrozenLoaded s :=
  ⟨CryptoVerification.frozenLoaded_of_mem_eq (by simp),
   CryptoVerification.frozenLoaded_of_mem_eq (by simp)⟩

theorem symtab_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).symtab = s.symtab := by simp

theorem symtab_setMem (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by simp

theorem exists_two_pow_zero : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨0, rfl⟩⟩

theorem exists_two_pow_one : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨0, rfl⟩⟩

theorem exists_two_pow_two : (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨1, rfl⟩⟩

theorem exists_two_pow_four : (∃ k : Nat, 4 = 2 ^ k) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨2, rfl⟩⟩

theorem exists_two_pow_eight : (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨3, rfl⟩⟩

theorem layoutOk_of_beq_zero_false {cap : BitVec 64}
    (hcap : ¬(cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) : LayoutOk cap.toNat 1 := by
  have hne : cap ≠ 0#64 := by
    intro h
    exact hcap (by subst h; rfl)
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
    hne (BitVec.eq_of_toNat_eq (by simpa using h0))
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

def SatEntails (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

theorem seq_clean_inImage {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) oom)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q sm →
      SepWP prog target_pc sm P_mid post oom) :
    SepWP prog target_pc s P post oom :=
  ProofLib.SepWP.of_sepWP_frozen hfrozen hsym <|
    SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hQ⟩ hfz hsym_m =>
      SepWP.weaken_pre hent (h2 sm hpc hrun hfz hsym_m hQ)

theorem seq_clean_inImage_fl_first {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    {img : Obj.Image} (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) oom)
    (h2 : ∀ sm, img.FrozenLoaded sm → sm.symtab = img.symtab →
      sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target_pc sm P_mid post oom) :
    SepWP prog target_pc s P post oom :=
  seq_clean_inImage hfl hsym h1 fun sm hpc hrun hfz hsym_m hQ =>
    h2 sm hfz hsym_m hpc hrun hQ

theorem seq_clean_inImage_inv {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) oom)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      (img.FrozenLoaded sm ∧ sm.symtab = img.symtab) → Q sm →
      SepWP prog target_pc sm P_mid post oom) :
    SepWP prog target_pc s P post oom :=
  seq_clean_inImage hinv.1 hinv.2 h1 fun sm hpc hrun hfz hsym_m hQ =>
    h2 sm hpc hrun ⟨hfz, hsym_m⟩ hQ

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp oom) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp oom := by
  have heq : A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ (A ∗ B ∗ C) := by sep_ac_rfl
  exact SepWPp.congr_pre heq (SepWPp.pure_left h)

theorem sepWPp_rw_pre {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post panic_post : State → SepProp → Prop} {oom : State → SepProp}
    (heq : P = P') (h : SepWPp prog pc s P' post panic_post oom) :
    SepWPp prog pc s P post panic_post oom :=
  heq ▸ h

theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢
  rwa [← htr]

theorem allocFailedIn_of_trace_append_singleton {s0 sf : State}
    (ht : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf := by
  simp [allocFailedIn, ht]

theorem allocFailedIn_and_prefix_of_trace_append_singleton {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace :=
  ⟨allocFailedIn_of_trace_append_singleton h, ⟨[allocFailedEvent], h.symm⟩⟩
def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s =>
      .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

end LibsignalBinary.Proofs.Common.SharedHelpers
