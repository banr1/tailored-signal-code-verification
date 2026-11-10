/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.AdrpLdst
public meta import LibsignalBinary.Proofs.Placed.Bridge -- shake: keep
public import LibsignalBinary.Proofs.Placed.Bridge
public import ProofLib.GenDecodes
import LibsignalBinary.Proofs.Placed.BridgeReloc
import ProofLib.GenPlacedFetches
import ProofLib.Hoare.Hooks
import ProofLib.Placed.Multi
public meta import ProofLib.ProgramReflection -- shake: keep
public meta import Lean -- shake: keep

/-!
# Relocatable Cross-Block Calls, External Hooks, and Block Fetch Generator

Provides `IsLsBlockProg`, `LibsignalCodeLoaded`, cross-block call and tail-jump transfer lemmas
(`ls_subroutine_ok_of_block`, `lscall_blk_cl`, `lscall_blk`, `lsjump_blk`), external hook lookup
lemmas (`ls_hook_ok`, `ls_hook_ok_panics`), and the `gen_ls_block <idx>` command elaborator.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Placed.PlacedCallSym

open _root_.Arm64 _root_.Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification (libsignalSessionBlocks libsignalSessionData libsignalSessionLib libsignalSessionMultiLib)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalHooks LibsignalPlacement checkBlockCharSymAt evalStrLit extract_withCodeLoaded fastLookupBlockSym libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib_blockProgram_fnAddr libsignalSessionLib_blocks_length lookupBlockSym_of_fast_some lookupBlockSym_some_of_chars lsNotBlockCharSym lsmpl lsρ)
open LibsignalBinary.Proofs.Placed.BridgeReloc (ls_fnAddr_text_chars ls_resolve_data_chars ls_resolve_text_chars)

/-! ## 1. `IsLsBlockProg` Typeclass -/

theorem prog_eq_blockProgram {lib : PlacedLib} {i : Nat} {pl : MultiPlacement}
    {H : LibsignalHooks} (h : lib = libsignalSessionLib.blockLib i) :
    (lib.program (libsignalSessionLib.blockPlacement pl i)).rebase
      (libsignalSessionLib.blockPlacement pl i).base H =
      libsignalSessionLib.blockProgram pl i H := by
  rw [h]
  rfl

/-- Typeclass associating a rebased block program `prog` (`blkPC_<i>.rebase blkPl_<i>.base H`)
    with its block index `i` and hook map `H` in $O(1)$ synthesis time. -/
class IsLsBlockProg [LibsignalPlacement] (prog : Program) (i : outParam Nat)
    (H : outParam LibsignalHooks) : Prop where
  eq_blockProgram : prog = libsignalSessionLib.blockProgram lsmpl i H
  externs_eq : (libsignalSessionLib.blockLib i).text.externs = libsignalSessionExterns

/-! ## 2. Cross-Block `externAt?` Equality -/

private theorem findSome?_const_none {α β : Type} (l : List α) :
    l.findSome? (fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ rest ih => exact ih

theorem ls_externAt?_blockProgram_eq_of_externs_eq
    (lib : MultiPlacedLib) (pl : MultiPlacement)
    (X : String → Option (State → State)) (svc : State → State) {i j : Nat}
    (hext : (lib.blockLib i).text.externs = (lib.blockLib j).text.externs) :
    (lib.blockProgram pl i X (fun _ => none) svc).externAt? =
      (lib.blockProgram pl j X (fun _ => none) svc).externAt? := by
  funext a
  dsimp only [Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram,
    MultiPlacedLib.blockPlacement, PlacedLib.program]
  simp only [ite_self, findSome?_const_none, Option.or_none]
  have hfind :
      ∀ (es : List String) (b1 b2 : BitVec 64),
        (es.map (fun e => (e, (lib.resolve pl e - b1).toNat))).findSome?
          (fun p => if (p.2 == (a - b1).toNat) = true then X p.1 else none) =
        (es.map (fun e => (e, (lib.resolve pl e - b2).toNat))).findSome?
          (fun p => if (p.2 == (a - b2).toNat) = true then X p.1 else none) := by
    intro es b1 b2
    induction es with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.map_cons, List.findSome?_cons]
      have hcond :
          ((lib.resolve pl e - b1).toNat == (a - b1).toNat) =
          ((lib.resolve pl e - b2).toNat == (a - b2).toNat) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, BitVec.toNat_inj]
        constructor <;> intro h <;> bv_omega
      rw [hcond, ih]
  rw [hext]
  exact hfind (lib.blockLib j).text.externs (pl.base i) (pl.base j)

/-! ## 3. `LibsignalCodeLoaded`, `withLsCodeLoaded`, and `withMemEq` -/

/-- Every unmutated block `i ∉ libsignalMutatedBlocks` of `libsignalSessionLib` has its relocated
code loaded in `m` (`624 = libsignalSessionLib.blocks.length`), satisfied by both stock and
mutated binaries. -/
def LibsignalCodeLoaded (pl : MultiPlacement) (m : Memory) : Prop :=
  ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
    ∀ (X O : String → Option (State → State)) (svc : State → State),
      (libsignalSessionLib.blockProgram pl i X O svc).CodeLoaded m

/-- Upper bound `n ≤ 624` (`libsignalSessionLib.blocks.length`) on a block index argument,
    defaulting to `624` (`@[default_instance]`) while remaining backward-compatible with callers
    passing `(hi : i < 619)`. -/
class LsBlockBound (n : Nat) : Prop where
  le_blocks : n ≤ 624

@[default_instance] instance : LsBlockBound 624 := ⟨Nat.le_refl 624⟩
instance : LsBlockBound 623 := ⟨by decide⟩
instance : LsBlockBound 619 := ⟨by decide⟩

theorem LibsignalCodeLoaded.of_keepsFrozen {pl : MultiPlacement} {m m' : Memory}
    (hcl : LibsignalCodeLoaded pl m) (hk : m.KeepsFrozen m') : LibsignalCodeLoaded pl m' :=
  fun i hi hunmut X O svc => (hcl i hi hunmut X O svc).of_keepsFrozen hk

theorem LibsignalCodeLoaded.of_codeLoaded {pl : MultiPlacement} {m : Memory}
    (hcl : libsignalSessionLib.CodeLoaded pl m) : LibsignalCodeLoaded pl m := by
  intro i hi _ _ _ _
  have h := hcl i (by rw [libsignalSessionLib_blocks_length]; omega)
  rwa [Program.codeLoaded_iff] at h ⊢

abbrev withLsCodeLoaded {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝ }

/-- Add `⌜s0.mem = m⌝` to `spec`'s precondition (used by `lscall_blk_cl` / `lscall_blk` so `wp_call`
    at state `s` discharges `⌜s.mem = s.mem⌝` by `rfl`). -/
abbrev withMemEq {α : Type} (m : Memory) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜s0.mem = m⌝ }

theorem extract_withLsCodeLoaded {α : Type} {pl : MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R) :
    LibsignalCodeLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsCodeLoaded] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem extract_withMemEq {α : Type} {m : Memory}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withMemEq m spec).pre x s0 ∗ R) :
    s0.mem = m ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withMemEq] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem subroutine_ok_withLsCodeLoaded_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withLsCodeLoaded hp).2) (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withCodeLoaded_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (libsignalSessionLib.withCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hcl, hpre⟩ := extract_withCodeLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨LibsignalCodeLoaded.of_codeLoaded hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Sequence two `SepWP` segments while threading `LibsignalCodeLoaded pl ·.mem` across the cut. -/
theorem sepWP_seq_lscl {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

/-- Strengthen a `SepWP` postcondition using `LibsignalCodeLoaded pl sf.mem` at the exit state. -/
theorem sepWP_mono_lscl {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {post1 post2 : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog tgt s P post1 oom)
    (himp : ∀ sf Pf, sf.pc = tgt → sf.status = .Running →
      LibsignalCodeLoaded pl sf.mem → post1 sf Pf → post2 sf Pf) :
    SepWP prog tgt s P post2 oom :=
  SepWP.mono_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h himp

/-! ## 4. External Hooks and Cross-Block Call / Jump Transfer -/

section ExternReflection
open Lean Meta Elab Term

local elab "char_strings_of% " listStx:term:max : term => do
  let listE ← elabTerm listStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  let lcTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
  let mut csEs : Array Expr := #[]
  for e in elems do
    let r ← withTransparency .all (whnf e)
    match r with
    | .lit (.strVal s) => csEs := csEs.push (mkStrCharsExpr s)
    | _ =>
      let r2 ← withTransparency .all (reduce e)
      match r2 with
      | .lit (.strVal s) => csEs := csEs.push (mkStrCharsExpr s)
      | _ => throwError "char_strings_of%: expected string literal"
  mkListLit lcTy csEs.toList

private noncomputable def lsExternCharSyms : List (List Char) :=
  char_strings_of% libsignalSessionExterns

private theorem lsExternCharSyms_map_eq :
    lsExternCharSyms.map String.ofList = libsignalSessionExterns := by
  rfl_kernel

private theorem lsExternCharSyms_notBlockSym :
    lsExternCharSyms.all lsNotBlockCharSym = true := by
  decide +kernel

theorem ls_extern_resolve_eq {pl : MultiPlacement} {sym : String}
    (hmem : sym ∈ libsignalSessionExterns) :
    libsignalSessionLib.resolve pl sym = pl.ρ sym := by
  rw [← lsExternCharSyms_map_eq, List.mem_map] at hmem
  obtain ⟨cs, hcs, rfl⟩ := hmem
  exact ls_resolve_data_chars rfl (List.all_eq_true.1 lsExternCharSyms_notBlockSym cs hcs)

end ExternReflection

theorem ls_extern_resolve_of_getElem? {pl : MultiPlacement} {sym : String} {k : Nat}
    (hk : libsignalSessionExterns[k]? = some sym) :
    libsignalSessionLib.resolve pl sym = pl.ρ sym :=
  ls_extern_resolve_eq (List.mem_of_getElem? hk)

theorem ls_blockPlacement_ρ_extern {pl : MultiPlacement} {i : Nat} {sym : String}
    (hmem : sym ∈ libsignalSessionExterns) :
    (libsignalSessionLib.blockPlacement pl i).ρ sym = pl.ρ sym :=
  ls_extern_resolve_eq hmem

private theorem nodup_map_of_nodup_map {α β γ : Type} {l : List α} {f : α → β} {g : α → γ}
    (h : (l.map g).Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → g x = g y) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact .nil
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    refine ⟨?_, ih h.2 (fun x hx y hy => hinj x (.tail _ hx) y (.tail _ hy))⟩
    rintro ⟨b, hb, hfb⟩
    exact h.1 ⟨b, hb, hinj b (.tail _ hb) a (.head _) hfb⟩

theorem lsExterns_offs_nodup_at [LibsignalPlacement] {i : Nat}
    (hext : (libsignalSessionLib.blockLib i).text.externs = libsignalSessionExterns) :
    (((libsignalSessionLib.blockLib i).text.externs.map fun e =>
      ((libsignalSessionLib.blockPlacement lsmpl i).ρ e -
        (libsignalSessionLib.blockPlacement lsmpl i).base).toNat)).Nodup := by
  rw [hext]
  apply nodup_map_of_nodup_map LibsignalPlacement.externsDistinct
  intro x hx y hy hxy
  have hrx : (libsignalSessionLib.blockPlacement lsmpl i).ρ x = lsmpl.ρ x :=
    ls_blockPlacement_ρ_extern hx
  have hry : (libsignalSessionLib.blockPlacement lsmpl i).ρ y = lsmpl.ρ y :=
    ls_blockPlacement_ρ_extern hy
  have hbveq : (libsignalSessionLib.blockPlacement lsmpl i).ρ x -
      (libsignalSessionLib.blockPlacement lsmpl i).base =
      (libsignalSessionLib.blockPlacement lsmpl i).ρ y -
      (libsignalSessionLib.blockPlacement lsmpl i).base :=
    BitVec.eq_of_toNat_eq hxy
  have hρeq : (libsignalSessionLib.blockPlacement lsmpl i).ρ x =
      (libsignalSessionLib.blockPlacement lsmpl i).ρ y := by
    bv_omega
  exact hrx.symm.trans (hρeq.trans hry)

private theorem findSome?_map_off_eq_none {es : List String} {f : String → Nat}
    {H : String → Option (State → State)} {v : Nat}
    (hnotmem : ∀ b ∈ es, f b ≠ v) :
    (es.map (fun e => (e, f e))).findSome?
      (fun p => if (p.2 == v) = true then H p.1 else none) = none := by
  induction es with
  | nil => rfl
  | cons a rest ih =>
    have hne : (f a == v) = false := beq_eq_false_iff_ne.mpr (hnotmem a (.head _))
    simp only [List.map_cons, List.findSome?_cons, hne, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun b hb => hnotmem b (.tail _ hb))

private theorem findSome?_map_off_eq_some {es : List String} {f : String → Nat}
    {H : String → Option (State → State)} {k : Nat} {sym : String}
    (hnodup : (es.map f).Nodup) (hk : es[k]? = some sym) :
    (es.map (fun e => (e, f e))).findSome?
      (fun p => if (p.2 == f sym) = true then H p.1 else none) = H sym := by
  induction es generalizing k with
  | nil => simp at hk
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      have hrest : (rest.map (fun e => (e, f e))).findSome?
          (fun p => if (p.2 == f a) = true then H p.1 else none) = none :=
        findSome?_map_off_eq_none (fun b hb heq => hnodup.1 ⟨b, hb, heq⟩)
      simp only [List.map_cons, List.findSome?_cons, beq_self_eq_true, ↓reduceIte, hrest]
      cases H a <;> rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hk
      have hmem : sym ∈ rest := List.mem_of_getElem? hk
      have hne : (f a == f sym) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hnodup.1 ⟨sym, hmem, heq.symm⟩
      simp only [List.map_cons, List.findSome?_cons, hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hnodup.2 hk

/-- Look up the external hook at `lsρ sym` in any block `i`'s program `prog`. -/
theorem ls_externAt?_of_blockProg [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {k : Nat} (hk : libsignalSessionExterns[k]? = some sym)
    {bi : Nat} [LsBlockBound bi]
    (_hi : i < bi := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  rw [hprog.eq_blockProgram]
  have hext := hprog.externs_eq
  have hmem : sym ∈ libsignalSessionExterns := List.mem_of_getElem? hk
  have hρ : (libsignalSessionLib.blockPlacement lsmpl i).ρ sym = lsρ sym :=
    ls_blockPlacement_ρ_extern hmem
  have hnodup := lsExterns_offs_nodup_at hext
  rw [hext] at hnodup
  dsimp only [Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram, PlacedLib.program]
  simp only [hext, ← hρ, ite_self, findSome?_const_none, Option.or_none]
  exact findSome?_map_off_eq_some hnodup hk

/-- Prove `subroutine_ok prog (lsρ sym) spec` for an external hook `sym` in `libsignalSessionExterns`
    from `HookSat H sym spec`. -/
theorem ls_hook_ok [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} {k : Nat} (hk : libsignalSessionExterns[k]? = some sym)
    (hsat : HookSat H sym spec)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_blockProg hk hi hunmut).trans hf) hok

/-- Prove `subroutine_ok prog (lsρ sym) spec` when `prog` uses `Rust.withPanics hooks` and `sym`
    is a non-panic external hook. -/
theorem ls_hook_ok_panics [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {hooks : LibsignalHooks} [hprog : IsLsBlockProg prog i (Rust.withPanics hooks)]
    {sym : String} {spec : Spec α} {k : Nat} (hk : libsignalSessionExterns[k]? = some sym)
    (hsat : HookSat hooks sym spec)
    (hnp : Rust.isPanicSymbol sym = false := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  refine ls_hook_ok hk ⟨f, ?_, hok⟩ hi hunmut
  simp [Rust.withPanics, hnp, hf]

/-- Resolve `prog.externAt? (lsρ sym) = some Rust.panicked` when `sym` is a Rust panic symbol. -/
theorem ls_externAt?_panicSymbol [LibsignalPlacement] {prog : Program} {i : Nat}
    {hooks : LibsignalHooks} [hprog : IsLsBlockProg prog i (Rust.withPanics hooks)]
    {sym : String} {k : Nat} (hk : libsignalSessionExterns[k]? = some sym)
    (hp : Rust.isPanicSymbol sym = true := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = some Rust.panicked := by
  rw [ls_externAt?_of_blockProg hk hi hunmut]
  simp [Rust.withPanics, hp]

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec)` from block `j` to
    block `i`'s program `callerProg`. -/
theorem ls_subroutine_ok_of_block [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [hbj : LsBlockBound bj]
    (_hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcl0 j (Nat.lt_of_lt_of_le hj hbj.le_blocks) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Transfer a cross-block `subroutine_ok` (whose spec takes `withLsCodeLoaded`) from block `j` to
    block `i`'s program `callerProg` using `hcl : LibsignalCodeLoaded lsmpl m` at the call site
    (wrapping in `withMemEq m spec` so `wp_call` closes `⌜s.mem = s.mem⌝` by `rfl`). -/
theorem lscall_blk_cl [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {m : Memory}
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base j) (withMemEq m spec) := by
  have h1 := ls_subroutine_ok_of_block (callerProg := callerProg) hcallee hi hj hj_unmut
  exact subroutine_ok_mono h1
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm ▸ hcl
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Transfer a cross-block `subroutine_ok` (with a plain `spec`) from block `j` to block `i`'s
    program `callerProg` (wrapping in `withMemEq m spec`) for `wp_call`. -/
theorem lscall_blk [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {m : Memory}
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base j) (withMemEq m spec) :=
  lscall_blk_cl (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hcl hi hj hj_unmut

/-- Transfer a tail-jump (`B callee`) `SepWP` goal in block `i`'s program `callerProg` to block `j`'s
    program `calleeProg`. -/
theorem lsjump_blk [LibsignalPlacement] {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {bi bj : Nat} [LsBlockBound bi] [hbj : LsBlockBound bj]
    (_hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide)
    (hwp : SepWP calleeProg tgt s P post oom) :
    SepWP callerProg tgt s P post oom := by
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hQL : calleeProg.CodeLoaded s.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcl j (Nat.lt_of_lt_of_le hj hbj.le_blocks) hj_unmut H (fun _ => none) Syscall.standard
  exact ProofLib.SepWP.of_sameHooks hext hsvc hQL hwp

/-! ## 5. Address and Symbol Resolution Lemmas -/

@[simp, arm64_norm, wp_norm]
theorem ls_blockPlacement_ρ (mpl : MultiPlacement) (i : Nat) (sym : String) :
    (libsignalSessionLib.blockPlacement mpl i).ρ sym = libsignalSessionLib.resolve mpl sym := rfl

theorem ls_blockPlacement_base (mpl : MultiPlacement) (i : Nat) :
    (libsignalSessionLib.blockPlacement mpl i).base = mpl.base i := rfl

@[simp, arm64_norm, wp_norm]
theorem add_off_add_sub_sub_cancel (b off tgt : BitVec 64) :
    b + off + (tgt - b - off) = tgt := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_add_sub_cancel_bv (b off tgt : BitVec 64) :
    b + off + (tgt - (b + off)) = tgt := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_sub_cancel_left_bv (b tgt : BitVec 64) :
    b + (tgt - b) = tgt := by
  bv_omega

theorem ls_resolve_block_chars {pl : MultiPlacement} {tgt : String} {cs : List Char} {i : Nat}
    (hname : tgt = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, 0)) :
    libsignalSessionLib.resolve pl tgt = pl.base i :=
  ls_resolve_text_chars hname h

theorem ls_fnAddr_block_chars {pl : MultiPlacement} {tgt : String} {cs : List Char} {i : Nat}
    (hname : tgt = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, 0)) :
    libsignalSessionLib.fnAddr pl tgt = pl.base i :=
  ls_fnAddr_text_chars hname h

theorem ls_blockProgram_fnAddr_chars {pl : MultiPlacement} {H : LibsignalHooks} {i : Nat}
    {tgt : String} {cs : List Char}
    (hname : tgt = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, 0)) :
    (libsignalSessionLib.blockProgram pl i H).fnAddr tgt = pl.base i := by
  have h' := libsignalSessionLib_blockProgram_fnAddr (pl := pl) (H := H)
    (lookupBlockSym_some_of_chars hname h)
  exact h'.1.trans h'.2

theorem lsProg_fnAddr_of_blockProg_chars [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H] {tgt : String} {cs : List Char}
    (hname : tgt = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, 0)) :
    prog.fnAddr tgt = lsmpl.base i := by
  rw [hprog.eq_blockProgram]
  exact ls_blockProgram_fnAddr_chars hname h

theorem ls_resolve_block {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : fastLookupBlockSym tgt = some (i, 0)) :
    libsignalSessionLib.resolve pl tgt = pl.base i := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_of_fast_some h]

theorem ls_fnAddr_block {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : fastLookupBlockSym tgt = some (i, 0)) :
    libsignalSessionLib.fnAddr pl tgt = pl.base i := by
  simp [MultiPlacedLib.fnAddr, lookupBlockSym_of_fast_some h]

theorem ls_blockProgram_fnAddr {pl : MultiPlacement} {H : LibsignalHooks} {i : Nat} {tgt : String}
    (h : fastLookupBlockSym tgt = some (i, 0)) :
    (libsignalSessionLib.blockProgram pl i H).fnAddr tgt = pl.base i := by
  have h' := libsignalSessionLib_blockProgram_fnAddr (pl := pl) (H := H) (lookupBlockSym_of_fast_some h)
  exact h'.1.trans h'.2

theorem lsProg_fnAddr_of_blockProg [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H] {tgt : String}
    (h : fastLookupBlockSym tgt = some (i, 0)) :
    prog.fnAddr tgt = lsmpl.base i := by
  rw [hprog.eq_blockProgram]
  exact ls_blockProgram_fnAddr h

-- Resolution lemmas for global data symbols
@[simp, arm64_norm, wp_norm]
theorem ls_resolve_logFilter (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "log::MAX_LOG_LEVEL_FILTER" =
      pl.ρ "log::MAX_LOG_LEVEL_FILTER" :=
  ls_resolve_data_chars (cs := str_chars% "log::MAX_LOG_LEVEL_FILTER")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_tokenStorage (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl
      "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_STORAGE" =
      pl.ρ "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_STORAGE" :=
  ls_resolve_data_chars
    (cs := str_chars% "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_STORAGE")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_tokenOnce (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl
      "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_ONCE" =
      pl.ρ "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_ONCE" :=
  ls_resolve_data_chars
    (cs := str_chars% "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_ONCE")
    (by rfl_kernel) (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_basepointTable (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "curve25519_dalek::constants::ED25519_BASEPOINT_TABLE" =
      pl.ρ "curve25519_dalek::constants::ED25519_BASEPOINT_TABLE" :=
  ls_resolve_data_chars (cs := str_chars% "curve25519_dalek::constants::ED25519_BASEPOINT_TABLE")
    (by rfl_kernel) (by decide +kernel)

/-! ## 6. Plain `ADRP` and `:lo12:` Load/Store Wrappers -/

theorem sepWP_rebase_adrpPlain_of_tree {α : Sort _} {P : α → Program} {plOf : α → Placement}
    {lib : PlacedLib} {t : WordTree} {n off off4 : Nat}
    {r : RelocEntry} {rd : BitVec 5} {T : α → BitVec 64} {w : BitVec 32}
    (hprog : ∀ a, P a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hlt : off < 4 * n)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .adrpHi21)
    (hnrel : lib.text.relaxableAt off = false) (hwd : lib.text.wordAt off = w)
    (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    (hrd : w.extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hT : ∀ a, lib.text.target (plOf a) r = T a) (h4 : off + 4 = off4)
    (a : α) (b : BitVec 64) (X : String → Option (State → State))
    {tgt : BitVec 64} {s : State} {Q : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : b = (plOf a).base)
    (hpc : s.pc = b + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP ((P a).rebase b X) tgt
      ((s.writeReg64 (.gpr rd) (pageOf (T a))).setPC (b + BitVec.ofNat 64 off4)) Q post oom) :
    SepWP ((P a).rebase b X) tgt s Q post oom := by
  rw [hprog a] at hnext ⊢
  exact PlacedLib.sepWP_rebase_adrpPlain (hPOf a) hb hr hk hnrel hwd hw hrd hrd31 (hT a) h4
    (hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) hlt) hpc hrun hnext

theorem fetch_rebase_ldstLo12_of_tree {α : Sort _} {P : α → Program} {plOf : α → Placement}
    {lib : PlacedLib} {t : WordTree} {n off : Nat}
    {r : RelocEntry} {scale : Nat} {T : α → BitVec 64} {inst : α → Instr} {w : BitVec 32}
    (hprog : ∀ a, P a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hlt : off < 4 * n)
    (hr : lib.text.relocAt? off = some r) (hk : ldstLo12Scale r.kind = some scale)
    (hwd : lib.text.wordAt off = w)
    (hscale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hT : ∀ a, lib.text.target (plOf a) r = T a)
    (hinst : ∀ a, mkLoadStoreInst scale (w.extractLsb' 22 2).toNat
      (Reg.fromZRBits (w.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of (T a))) = some (inst a))
    (a : α) (b : BitVec 64) (X : String → Option (State → State)) :
    ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) = some (inst a) := by
  rw [hprog a]
  exact PlacedLib.fetch_rebase_ldstLo12_of_placeable (hPOf a) hr hk
    (hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) hlt) hwd hscale hw1 hw2 (hT a) (hinst a)

/-! ## 7. `gen_ls_extern_resolves` and `gen_ls_block` Elaborators -/

syntax (name := genLsExternResolvesStx) "gen_ls_extern_resolves" : command
syntax (name := genLsBlockStx) "gen_ls_block " num : command

section MetaGenLsBlock

open Lean Meta Elab Term Command

meta def whnfAll (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

meta def evalNatExpr? (e : Expr) : MetaM (Option Nat) := do
  let r ← whnfAll e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

meta def evalIntLit (e : Expr) : MetaM Int := do
  let r ← withTransparency .all (reduce e)
  if let some n ← evalNatExpr? r then return Int.ofNat n
  if r.isAppOfArity ``Int.ofNat 1 then
    if let some n ← evalNatExpr? (r.getArg! 0) then return Int.ofNat n
  if r.isAppOfArity ``Int.negSucc 1 then
    if let some n ← evalNatExpr? (r.getArg! 0) then return Int.negSucc n
  if r.isAppOfArity ``Neg.neg 3 then
    if let some n ← evalNatExpr? (r.getArg! 2) then return -Int.ofNat n
  throwError "gen_ls_block: expected Int literal, got {r}"

meta def sanitizeSymIdent (s : String) : String :=
  String.ofList <| (s.toList.take 48).map fun c =>
    if c.isAlphanum then c else '_'

meta def targetExprForReloc (plE : Expr) (sym : String) (addend : Int) : Expr :=
  let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
  let base := mkApp2 (Lean.mkConst ``Placement.ρ) plE (mkStrLit sym)
  if addend == 0 then base
  else if addend > 0 then
    mkApp6 (Lean.mkConst ``HAdd.hAdd [.zero, .zero, .zero]) bv64 bv64 bv64
      (mkApp2 (Lean.mkConst ``instHAdd [.zero]) bv64 (mkApp (Lean.mkConst ``BitVec.instAdd) (mkNatLit 64)))
      base (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit addend.toNat))
  else
    mkApp6 (Lean.mkConst ``HSub.hSub [.zero, .zero, .zero]) bv64 bv64 bv64
      (mkApp2 (Lean.mkConst ``instHSub [.zero]) bv64 (mkApp (Lean.mkConst ``BitVec.instSub) (mkNatLit 64)))
      base (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit (-addend).toNat))

@[command_elab genLsExternResolvesStx]
meta def elabGenLsExternResolves : CommandElab := fun _ => do
  let syms ← liftTermElabM do
    let extsE := Lean.mkConst ``libsignalSessionExterns
    let elems ← ProofLib.ProgramReflection.listElemsWhnf extsE
    liftM (elems.mapM evalStrLit)
  for idx in [0:syms.size] do
    let sym := syms[idx]!
    let thmId := mkIdent (Name.mkSimple s!"ls_resolve_ext_{idx}")
    let symLit := Syntax.mkStrLit sym
    let idxLit := Syntax.mkNumLit (toString idx)
    elabCommand (← `(command|
      @[simp, arm64_norm, wp_norm]
      theorem $thmId:ident (pl : MultiPlacement) :
          libsignalSessionLib.resolve pl $symLit:str = pl.ρ $symLit:str :=
        ls_extern_resolve_of_getElem? (k := $idxLit:num) rfl
    ))

@[command_elab genLsBlockStx]
meta def elabGenLsBlock : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_block $idxStx:num) => do
    let idx := idxStx.getNat
    let (blkE, codeLen, symNames, relocData) ← liftTermElabM do
      let blocksE := Lean.mkConst ``libsignalSessionBlocks
      let elems ← ProofLib.ProgramReflection.listElemsWhnf blocksE
      unless idx < elems.size do
        throwErrorAt idxStx "gen_ls_block: block index {idx} out of bounds ({elems.size})"
      let blkE ← whnfAll elems[idx]!
      let codeE := mkApp (Lean.mkConst ``CodeBlock.code) blkE
      let codeBytes ← ProofLib.ProgramReflection.listElemsWhnf codeE
      let symsE := mkApp (Lean.mkConst ``CodeBlock.symbols) blkE
      let symElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
      let mut symNames : Array String := #[]
      for pE in symElems do
        let pE ← whnfAll pE
        let s ← evalStrLit (pE.getArg! 2)
        symNames := symNames.push s
      let relocsE := mkApp (Lean.mkConst ``CodeBlock.relocs) blkE
      let relocElems ← ProofLib.ProgramReflection.listElemsWhnf relocsE
      let mut relocData : Array (Nat × Name × String × Int × Expr) := #[]
      for rE in relocElems do
        let rE ← whnfAll rE
        let off ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``RelocEntry.off) rE)
        let kE ← whnfAll (mkApp (Lean.mkConst ``RelocEntry.kind) rE)
        let some kn := kE.constName? | throwError "gen_ls_block: bad reloc kind {kE}"
        let sym ← evalStrLit (mkApp (Lean.mkConst ``RelocEntry.sym) rE)
        let addend ← evalIntLit (mkApp (Lean.mkConst ``RelocEntry.addend) rE)
        relocData := relocData.push (off, kn, sym, addend, rE)
      return (blkE, codeBytes.size, symNames, relocData)

    let nWords := codeLen / 4
    let maxOff := if nWords > 0 then (nWords - 1) * 4 else 0
    let blkLibId := mkIdent (Name.mkSimple s!"blkLib_{idx}")
    let blkLibEqId := mkIdent (Name.mkSimple s!"blkLib_eq_{idx}")
    let blkExternsEqId := mkIdent (Name.mkSimple s!"blkExterns_eq_{idx}")
    let blkPlId := mkIdent (Name.mkSimple s!"blkPl_{idx}")
    let blkPlaceableId := mkIdent (Name.mkSimple s!"blkPlaceable_{idx}")
    let blkPCId := mkIdent (Name.mkSimple s!"blkPC_{idx}")
    let lsProgId := mkIdent (Name.mkSimple s!"lsProg_{idx}")
    let instIsLsId := mkIdent (Name.mkSimple s!"instIsLsBlockProg_{idx}")
    let blkSymProgId := mkIdent (Name.mkSimple s!"blkSymProg_{idx}")
    let blkSymCharsId := mkIdent (Name.mkSimple s!"blkSymChars_{idx}")
    let blkSymsEqId := mkIdent (Name.mkSimple s!"blkSymsEq_{idx}")
    let blkSymsFreshId := mkIdent (Name.mkSimple s!"blkSymsFresh_{idx}")
    let blkTextProgId := mkIdent (Name.mkSimple s!"blkTextProg_{idx}")
    let blkTreeId := mkIdent (Name.mkSimple s!"blkTree_{idx}")
    let blkCodeEqId := mkIdent (Name.mkSimple s!"blkCodeEq_{idx}")
    let blkTreeSizeId := mkIdent (Name.mkSimple s!"blkTreeSize_{idx}")
    let nWordsLit := Syntax.mkNumLit (toString nWords)
    let maxOffLit := Syntax.mkNumLit (toString maxOff)

    -- Define `blkLib_<idx>` directly from `blkE` without unfolding `libsignalSessionBlocks`.
    liftTermElabM do
      let val := mkApp4 (Lean.mkConst ``PlacedLib.mk)
        (mkStrLit "libsignalSession")
        blkE
        (Lean.mkConst ``libsignalSessionData)
        (mkApp (Lean.mkConst ``MultiPlacedLib.exports) (Lean.mkConst ``libsignalSessionMultiLib))
      let decl := Declaration.defnDecl {
        name := blkLibId.getId
        levelParams := []
        type := Lean.mkConst ``PlacedLib
        value := val
        hints := .regular 0
        safety := .safe
      }
      withExporting <| addAndCompile decl

    -- Emit `blkLib_eq_<idx>`, `blkExterns_eq_<idx>`, `blkPl_<idx>`, `blkPlaceable_<idx>`, `blkPC_<idx>`, `lsProg_<idx>`, and `IsLsBlockProg`.
    elabCommand (← `(command|
      theorem $blkLibEqId:ident : $blkLibId:ident = libsignalSessionLib.blockLib $idxStx:num := rfl
    ))
    elabCommand (← `(command|
      theorem $blkExternsEqId:ident : ($blkLibId:ident).text.externs = libsignalSessionExterns := rfl
    ))
    elabCommand (← `(command|
      abbrev $blkPlId:ident [LibsignalPlacement] : Placement :=
        libsignalSessionLib.blockPlacement lsmpl $idxStx:num
    ))
    elabCommand (← `(command|
      theorem $blkPlaceableId:ident [LibsignalPlacement] : ($blkLibId:ident).Placeable $blkPlId:ident :=
        $blkLibEqId:ident ▸ LibsignalPlacement.block_placeable $idxStx:num (by decide) (by decide)
    ))
    elabCommand (← `(command|
      noncomputable def $blkPCId:ident [LibsignalPlacement] : Program :=
        ($blkLibId:ident).program $blkPlId:ident
    ))
    elabCommand (← `(command|
      noncomputable abbrev $lsProgId:ident [LibsignalPlacement] (H : LibsignalHooks) : Program :=
        ($blkPCId:ident).rebase ($blkPlId:ident).base H
    ))
    elabCommand (← `(command|
      instance $instIsLsId:ident [LibsignalPlacement] (H : LibsignalHooks) :
          IsLsBlockProg (($blkPCId:ident).rebase ($blkPlId:ident).base H) $idxStx:num H where
        eq_blockProgram := prog_eq_blockProgram $blkLibEqId:ident
        externs_eq := $blkLibEqId:ident ▸ $blkExternsEqId:ident
    ))

    elabCommand (← `(command|
      private def $blkSymProgId:ident : Program := { symbols := ($blkLibId:ident).text.symbols }
    ))
    elabCommand (← `(command|
      private def $blkSymCharsId:ident : List (List Char × Nat) := char_symbols_of% $blkSymProgId:ident
    ))
    elabCommand (← `(command|
      private theorem $blkSymsEqId:ident [LibsignalPlacement] :
          ($blkPCId:ident).symbols = toStringSymbols $blkSymCharsId:ident := rfl
    ))
    elabCommand (← `(command|
      private theorem $blkSymsFreshId:ident : allFreshCharSymbols $blkSymCharsId:ident = true := by
        decide +kernel
    ))
    elabCommand (← `(command|
      gen_placed_fnOffs $blkPCId:ident $blkLibId:ident $blkSymCharsId:ident $blkSymsEqId:ident $blkSymsFreshId:ident
    ))
    if nWords > 0 then
      elabCommand (← `(command|
        private def $blkTextProgId:ident : Program := { code := ($blkLibId:ident).text.code }
      ))
      elabCommand (← `(command|
        def $blkTreeId:ident : WordTree := word_tree_of% $blkTextProgId:ident
      ))
      elabCommand (← `(command|
        theorem $blkCodeEqId:ident : ($blkLibId:ident).text.code = ($blkTreeId:ident).toBytes := rfl
      ))
      elabCommand (← `(command|
        theorem $blkTreeSizeId:ident : ($blkTreeId:ident).checkSize? = some $nWordsLit:num := by decide +kernel
      ))
      elabCommand (← `(command|
        gen_placed_fetches $blkPCId:ident $blkLibId:ident $blkTreeId:ident $blkCodeEqId:ident $blkTreeSizeId:ident
          via_placement $blkPlId:ident $blkPlaceableId:ident [0 → $maxOffLit:num]
      ))

    let relaxableAddKind (kn : Name) : Bool :=
      kn == ``RelocKind.addLo12

    let isRelaxableAt (off : Nat) (kn : Name) (sym : String) (addend : Int) : Bool :=
      if kn != ``RelocKind.adrpHi21 then false
      else
        match relocData.find? (fun (o, _, _, _, _) => o == off + 4) with
        | some (_, kn2, sym2, add2, _) =>
          relaxableAddKind kn2 && sym == sym2 && addend == add2
        | none => false

    let ldstScale? (kn : Name) : Option Nat :=
      if kn == ``RelocKind.ldst8Lo12 then some 0
      else if kn == ``RelocKind.ldst16Lo12 then some 1
      else if kn == ``RelocKind.ldst32Lo12 then some 2
      else if kn == ``RelocKind.ldst64Lo12 then some 3
      else none

    if nWords > 0 then
      liftTermElabM do
        let paramTy := Lean.mkConst ``LibsignalPlacement
        let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
        let bv32 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)
        let bv5 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 5)
        let natTy := Lean.mkConst ``Nat
        let boolTy := Lean.mkConst ``Bool
        let progFn := Lean.mkConst blkPCId.getId
        let plFn := Lean.mkConst blkPlId.getId
        let placeableFn := Lean.mkConst blkPlaceableId.getId
        let libE := Lean.mkConst blkLibId.getId
        let treeE := Lean.mkConst blkTreeId.getId
        let codeEqE := Lean.mkConst blkCodeEqId.getId
        let sizeEqE := Lean.mkConst blkTreeSizeId.getId
        let nWordsE := mkNatLit nWords
        let hprogE := Expr.lam `a paramTy
          (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Program)
            (mkApp progFn (.bvar 0))) .instImplicit

        for (off, kn, sym, addend, rE) in relocData do
          let offHex := String.ofList (Nat.toDigits 16 off)
          if kn == ``RelocKind.adrpHi21 && !isRelaxableAt off kn sym addend then
            -- Plain ADRP: emit `blkPC_<idx>_pairStep_0x<off>`
            let thmName := Name.mkSimple s!"blkPC_{idx}_pairStep_0x{offHex}"
            let offE := mkNatLit off
            let off4E := mkNatLit (off + 4)
            let wE ← whnfAll (mkApp2 (Lean.mkConst ``CodeBlock.wordAt) (mkApp (Lean.mkConst ``PlacedLib.text) libE) offE)
            let rdE ← whnfAll (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 0) (mkNatLit 5) wE)
            let tLam := Expr.lam `a paramTy (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend) .instImplicit
            let hltTy := mkApp4 (Lean.mkConst ``LT.lt [.zero]) natTy (Lean.mkConst ``instLTNat)
              offE (mkNatMul (mkNatLit 4) nWordsE)
            let hltE ← mkDecideProof hltTy
            let hrE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
              (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry))
              (mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE)
            let hkE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``RelocKind)
              (Lean.mkConst ``RelocKind.adrpHi21)
            let hnrelE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
            let hwdE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32 wE
            let hwE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32
              (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x90000000))
            let hrdE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv5 rdE
            let hrd31Ty := mkApp (Lean.mkConst ``Not)
              (mkApp3 (Lean.mkConst ``Eq [.succ .zero]) bv5 rdE
                (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit 31)))
            let hrd31E ← mkDecideProof hrd31Ty
            let hTE := Expr.lam `a paramTy
              (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend)) .instImplicit
            let h4E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy off4E
            let prf := mkAppN (Lean.mkConst ``sepWP_rebase_adrpPlain_of_tree [.zero])
              #[paramTy, progFn, plFn, libE, treeE, nWordsE, offE, off4E, rE, rdE, tLam, wE,
                hprogE, placeableFn, codeEqE, sizeEqE, hltE, hrE, hkE, hnrelE, hwdE, hwE, hrdE,
                hrd31E, hTE, h4E]
            let ty ← inferType prf
            ProofLib.GenDecodes.addThm thmName ty prf

          if let some scale := ldstScale? kn then
            let prevRelax :=
              if off < 4 then false
              else
                match relocData.find? (fun (o, _, _, _, _) => o == off - 4) with
                | some (o, kn0, s0, a0, _) => isRelaxableAt o kn0 s0 a0
                | none => false
            if !prevRelax then
              -- Plain `:lo12:` load/store: emit `@[simp, arm64_norm] blkPC_<idx>_rebase_fetch_0x<off>`
              let thmName := Name.mkSimple s!"blkPC_{idx}_rebase_fetch_0x{offHex}"
              let offE := mkNatLit off
              let scaleE := mkNatLit scale
              let wE ← whnfAll (mkApp2 (Lean.mkConst ``CodeBlock.wordAt) (mkApp (Lean.mkConst ``PlacedLib.text) libE) offE)
              let opcE ← whnfAll (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 2)
                (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 22) (mkNatLit 2) wE))
              let rtE ← whnfAll (mkApp (Lean.mkConst ``Reg.fromZRBits)
                (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 0) (mkNatLit 5) wE))
              let rnE ← whnfAll (mkApp (Lean.mkConst ``Reg.fromSPBits)
                (mkApp4 (Lean.mkConst ``BitVec.extractLsb') (mkNatLit 32) (mkNatLit 5) (mkNatLit 5) wE))
              let tLam := Expr.lam `a paramTy (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend) .instImplicit
              let instLam ← withLocalDecl `a .instImplicit paramTy fun aFVar => do
                let tA := targetExprForReloc (mkApp plFn aFVar) sym addend
                let addrA := mkApp2 (Lean.mkConst ``AddrMode.Offset) rnE (mkApp (Lean.mkConst ``lo12Of) tA)
                let someInstA ← whnfAll (mkApp4 (Lean.mkConst ``mkLoadStoreInst) scaleE opcE rtE addrA)
                let instA := someInstA.getArg! 1
                mkLambdaFVars #[aFVar] instA
              let hltTy := mkApp4 (Lean.mkConst ``LT.lt [.zero]) natTy (Lean.mkConst ``instLTNat)
                offE (mkNatMul (mkNatLit 4) nWordsE)
              let hltE ← mkDecideProof hltTy
              let hrE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry))
                (mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE)
              let hkE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                (mkApp (Lean.mkConst ``Option [.zero]) natTy)
                (mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy scaleE)
              let hwdE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32 wE
              let hscaleE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy scaleE
              let hw1E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32
                (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x39000000))
              let hw2E := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
              let hTE := Expr.lam `a paramTy
                (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv64
                  (targetExprForReloc (mkApp plFn (.bvar 0)) sym addend)) .instImplicit
              let hinstE ← withLocalDecl `a .instImplicit paramTy fun aFVar => do
                let instA := instLam.beta #[aFVar]
                let someInstA := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``Instr) instA
                let eqPrf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
                  (mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``Instr)) someInstA
                mkLambdaFVars #[aFVar] eqPrf
              let prf := mkAppN (Lean.mkConst ``fetch_rebase_ldstLo12_of_tree [.zero])
                #[paramTy, progFn, plFn, libE, treeE, nWordsE, offE, rE, scaleE, tLam, instLam, wE,
                  hprogE, placeableFn, codeEqE, sizeEqE, hltE, hrE, hkE, hwdE, hscaleE, hw1E, hw2E,
                  hTE, hinstE]
              let ty ← inferType prf
              ProofLib.GenDecodes.addThm thmName ty prf
              Term.applyAttributes thmName #[{ name := `simp }, { name := `arm64_norm }]

    -- Emit resolution and `fnAddr` lemmas for block `<idx>` and its relocation targets.
    for sym in symNames do
      let resName := Name.mkSimple s!"ls_resolve_blk_{idx}"
      let fnName := Name.mkSimple s!"ls_fnAddr_blk_{idx}"
      let progFnName := Name.mkSimple s!"ls_blockProgram_fnAddr_blk_{idx}"
      let symLit := Syntax.mkStrLit sym
      let env ← getEnv
      if !env.contains resName then
        let resId := mkIdent resName
        elabCommand (← `(command|
          @[simp, arm64_norm, wp_norm]
          theorem $resId:ident (pl : MultiPlacement) :
              libsignalSessionLib.resolve pl $symLit:str = pl.base $idxStx:num :=
            ls_resolve_block_chars (cs := str_chars% $symLit:str) (by rfl_kernel) (by decide +kernel)
        ))
      if !env.contains fnName then
        let fnId := mkIdent fnName
        elabCommand (← `(command|
          @[simp, arm64_norm, wp_norm]
          theorem $fnId:ident (pl : MultiPlacement) :
              libsignalSessionLib.fnAddr pl $symLit:str = pl.base $idxStx:num :=
            ls_fnAddr_block_chars (cs := str_chars% $symLit:str) (by rfl_kernel) (by decide +kernel)
        ))
      if !env.contains progFnName then
        let progFnId := mkIdent progFnName
        elabCommand (← `(command|
          @[simp, arm64_norm, wp_norm]
          theorem $progFnId:ident [LibsignalPlacement] (H : LibsignalHooks) :
              (($blkPCId:ident).rebase ($blkPlId:ident).base H).fnAddr $symLit:str = lsmpl.base $idxStx:num :=
            lsProg_fnAddr_of_blockProg_chars (cs := str_chars% $symLit:str) (by rfl_kernel) (by decide +kernel)
        ))

    let extSyms ← liftTermElabM do
      let extsE := Lean.mkConst ``libsignalSessionExterns
      let elems ← ProofLib.ProgramReflection.listElemsWhnf extsE
      liftM (elems.mapM evalStrLit)
    let mut seenRelSyms : Std.HashSet String := {}
    for s in extSyms do
      seenRelSyms := seenRelSyms.insert s
    seenRelSyms := seenRelSyms.insert "log::MAX_LOG_LEVEL_FILTER"
    seenRelSyms := seenRelSyms.insert "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_STORAGE"
    seenRelSyms := seenRelSyms.insert "getrandom::backends::linux_android_with_fallback::sanitize_or_get_GETRANDOM_SYSCALL::TOKEN_ONCE"
    seenRelSyms := seenRelSyms.insert "curve25519_dalek::constants::ED25519_BASEPOINT_TABLE"
    for (_, _, rsym, _, _) in relocData do
      if !seenRelSyms.contains rsym then
        seenRelSyms := seenRelSyms.insert rsym
        let symLit := Syntax.mkStrLit rsym
        -- Check whether `rsym` is a block symbol in `checkBlockCharSymAt` or a data/extern symbol.
        let targetBlk? ← liftTermElabM do
          let app := mkApp (Lean.mkConst ``checkBlockCharSymAt) (mkStrCharsExpr rsym)
          let r ← withTransparency .all (reduce app)
          if r.isAppOfArity ``Option.some 2 then
            let pair := r.getArg! 1
            if pair.isAppOfArity ``Prod.mk 4 then
              return (← evalNatExpr? (pair.getArg! 2))
          return none
        match targetBlk? with
        | some j =>
          let resName := Name.mkSimple s!"ls_resolve_blk_{j}"
          let fnName := Name.mkSimple s!"ls_fnAddr_blk_{j}"
          let jLit := Syntax.mkNumLit (toString j)
          let env ← getEnv
          if !env.contains resName then
            let resId := mkIdent resName
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $resId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.resolve pl $symLit:str = pl.base $jLit:num :=
                ls_resolve_block_chars (cs := str_chars% $symLit:str) (by rfl_kernel) (by decide +kernel)
            ))
          if !env.contains fnName then
            let fnId := mkIdent fnName
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $fnId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.fnAddr pl $symLit:str = pl.base $jLit:num :=
                ls_fnAddr_block_chars (cs := str_chars% $symLit:str) (by rfl_kernel) (by decide +kernel)
            ))
        | none =>
          -- Non-block `.rodata` data symbol:
          let hash := UInt64.toNat (Hashable.hash rsym)
          let resName := Name.mkSimple s!"ls_resolve_dat_{sanitizeSymIdent rsym}_{hash}"
          let env ← getEnv
          if !env.contains resName then
            let resId := mkIdent resName
            elabCommand (← `(command|
              @[simp, arm64_norm, wp_norm]
              theorem $resId:ident (pl : MultiPlacement) :
                  libsignalSessionLib.resolve pl $symLit:str = pl.ρ $symLit:str :=
                ls_resolve_data_chars (cs := str_chars% $symLit:str) (by rfl_kernel) (by decide +kernel)
            ))
  | _ => throwUnsupportedSyntax

end MetaGenLsBlock

-- Emit `@[simp, arm64_norm, wp_norm]` resolution lemmas for all 101 external symbols
gen_ls_extern_resolves

/-- No-op drop-in replacement for `code_fetches` when stepping a `gen_ls_block` placed program:
    all fetches and relaxable pairs are registered globally in `tryCloseFetchFromHasCode` and
    `tryPairStepHook`. -/
macro "placed_fetches_blk" : tactic => `(tactic| skip)

end LibsignalBinary.Proofs.Placed.PlacedCallSym

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification
export LibsignalBinary.Proofs.Placed.PlacedCallSym (prog_eq_blockProgram IsLsBlockProg ls_externAt?_blockProgram_eq_of_externs_eq)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (LibsignalCodeLoaded LsBlockBound withLsCodeLoaded withMemEq extract_withLsCodeLoaded)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (extract_withMemEq subroutine_ok_withLsCodeLoaded_of_plain)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (subroutine_ok_withCodeLoaded_of_withLsCodeLoaded sepWP_seq_lscl sepWP_mono_lscl)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_extern_resolve_eq ls_extern_resolve_of_getElem? ls_blockPlacement_ρ_extern)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (lsExterns_offs_nodup_at ls_externAt?_of_blockProg ls_hook_ok ls_hook_ok_panics)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_externAt?_panicSymbol ls_subroutine_ok_of_block lscall_blk_cl lscall_blk lsjump_blk)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_blockPlacement_ρ ls_blockPlacement_base add_off_add_sub_sub_cancel)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (add_add_sub_cancel_bv add_sub_cancel_left_bv ls_resolve_block_chars)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_fnAddr_block_chars ls_blockProgram_fnAddr_chars lsProg_fnAddr_of_blockProg_chars)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_resolve_block ls_fnAddr_block ls_blockProgram_fnAddr lsProg_fnAddr_of_blockProg)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_resolve_logFilter ls_resolve_tokenStorage ls_resolve_tokenOnce)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (ls_resolve_basepointTable sepWP_rebase_adrpPlain_of_tree fetch_rebase_ldstLo12_of_tree)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (whnfAll evalNatExpr? evalIntLit sanitizeSymIdent targetExprForReloc)
export LibsignalBinary.Proofs.Placed.PlacedCallSym (elabGenLsExternResolves elabGenLsBlock)
end CryptoVerification
namespace CryptoVerification.LibsignalCodeLoaded
export LibsignalBinary.Proofs.Placed.PlacedCallSym.LibsignalCodeLoaded (of_keepsFrozen of_codeLoaded)
end CryptoVerification.LibsignalCodeLoaded
namespace CryptoVerification.IsLsBlockProg
export LibsignalBinary.Proofs.Placed.PlacedCallSym.IsLsBlockProg (mk eq_blockProgram externs_eq)
end CryptoVerification.IsLsBlockProg
namespace CryptoVerification.LsBlockBound
export LibsignalBinary.Proofs.Placed.PlacedCallSym.LsBlockBound (mk le_blocks)
end CryptoVerification.LsBlockBound
-- AUTO-BRIDGE END
