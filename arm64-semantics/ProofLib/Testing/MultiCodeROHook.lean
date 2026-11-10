/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.SepLogic.Exists
public import ProofLib.Testing.MultiSubroutineHook

/-!
# Multi-Block Read-Only Code Hook Tests

Positive and negative tests for `MultiCodeROHook`: default hook lifting (including `.allowOom`),
`codeRO`-only caller contracts without `PermsRX` or `CodeLoaded`, existential ghost witnesses
with internal call frames, execution on `Perm.ro` code pages, and `#guard_msgs` rejections.
-/

@[expose] public section

namespace Examples.Testing.MultiCodeROHookTest

open Arm64 Arm64.Obj ProofLib
open Examples.Testing.MultiSubroutineHookTest

/-! ## Default `Spec.codeROMultiSubroutineHook` Lifting -/

theorem alphaEntry_codeRODefaultHook_ok {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.codeROSubroutineHook mpl "alpha_entry")
      (alphaMultiLib.codeROSubroutineHookSpec mpl "alpha_entry" alphaEntrySpec) :=
  subroutineHook_ok_codeROMultiSubroutineHook hpl alphaEntry_subroutineOk

theorem alphaLeafOom_codeRODefaultHook_ok {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.codeROSubroutineHook mpl "alpha_leaf")
      (Spec.codeROMultiSubroutineHook alphaMultiLib mpl "alpha_leaf"
        (fun _ => alphaLeafSpec.allowOom)) :=
  subroutineHook_ok_codeROMultiSubroutineHook hpl alphaLeafOom_subroutineOk

/-! ## Pure `SepProp` Caller Contract (`codeRO` Only) -/

/-- Caller-facing contract for `"alpha_entry"` backed purely by `alphaMultiLib.codeRO mpl`,
    carrying zero `CodeLoaded` or `PermsRX` side conditions. -/
def alphaEntryCodeROSpec (mpl : MultiPlacement) : Spec (BitVec 64) where
  pre := fun v _ => alphaMultiLib.codeRO mpl ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)
  post := fun v _ sf =>
    ⌜sf.readReg64 .x0 = v⌝ ∗ alphaMultiLib.codeRO mpl ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)

theorem alphaEntryCodeRO_hookOk {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (multiCodeROSubroutineHook alphaMultiLib mpl "alpha_entry")
      (alphaEntryCodeROSpec mpl) := by
  refine subroutineHook_ok_of_multiCodeRO hpl alphaEntry_subroutineOk
    (fun _ _ => Entails.refl _)
    (fun v s0 sf' _ _ _ => ?_)
  dsimp only [alphaEntrySpec, alphaEntryCodeROSpec, ToBaseSpec.toSpec]
  rw [← sepConj_assoc (alphaMultiLib.codeRO mpl),
      sepConj_comm (alphaMultiLib.codeRO mpl) ⌜sf'.readReg64 .x0 = v⌝,
      sepConj_assoc]
  refine Entails.pure_left fun hx0 => ?_
  have hx0_exit :
      (multiCodeROHookExit alphaMultiLib mpl
        (alphaMultiLib.fnBlockIdx "alpha_entry") s0 sf').readReg64 .x0 = v := by
    rwa [multiCodeROHookExit_readReg64 _ _ _ _ _ .x0 (by decide)]
  exact Entails.pure_right hx0_exit (Entails.refl _)

/-- Hook bundle of an external caller library requiring `"alpha_entry"` via `alphaEntryCodeROSpec`. -/
structure AlphaCodeROHooks (mpl : MultiPlacement)
    (hooks : String → Option (State → State)) : Prop where
  alpha_entry : HookSat hooks "alpha_entry" (alphaEntryCodeROSpec mpl)

noncomputable def alphaCodeROHookTable (mpl : MultiPlacement) : String → Option (State → State) :=
  hookMap [("alpha_entry", multiCodeROSubroutineHook alphaMultiLib mpl "alpha_entry")] (fun _ => none)

theorem alphaCodeROHookTable_sat {mpl : MultiPlacement} (hpl : alphaMultiLib.Placeable mpl) :
    AlphaCodeROHooks mpl (alphaCodeROHookTable mpl) where
  alpha_entry := by
    simp only [alphaCodeROHookTable, HookSat_hookMap_cons_self]
    exact alphaEntryCodeRO_hookOk hpl

theorem betaClient_linked_with_alphaCodeRO {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    betaClientLib.subroutineOk "beta_call"
      (fun _ => alphaEntryCodeROSpec mpl) (alphaCodeROHookTable mpl) := by
  refine ⟨by decide, fun pl hpl_b => ?_⟩
  obtain ⟨f, hf, hok⟩ := (alphaCodeROHookTable_sat hpl).alpha_entry
  have hext : (betaClientLib.program pl (alphaCodeROHookTable mpl)).externAt?
      (pl.ρ "alpha_entry") = some f := by
    have h := PlacedLib.externAt?_program (lib := betaClientLib) (pl := pl)
      (X := alphaCodeROHookTable mpl) (O := fun _ => none) (svc := Syscall.standard)
      (e := "alpha_entry") (by simp [betaClientLib]) (by decide)
    simpa [PlacedLib.program, hf] using h
  have htarget_ok : subroutine_ok (betaClientLib.program pl (alphaCodeROHookTable mpl))
      (pl.ρ "alpha_entry") (alphaEntryCodeROSpec mpl) :=
    subroutine_ok_of_hookOk hext hok
  have hfn : betaClientLib.fnAddr pl "beta_call" = pl.base := by
    simp [PlacedLib.fnAddr, lookup, betaClientLib]
  rw [hfn]
  have hnh : ((betaClientLib.program pl).rebase pl.base (alphaCodeROHookTable mpl)).hookAtOff? 0 =
      none := by
    have hext_ge := (hpl_b.text.externs_ok "alpha_entry" (by decide)).2
    have hge4 : 4 ≤ (pl.ρ "alpha_entry" - pl.base).toNat := by
      simpa [betaClientLib, wordsLE] using hext_ge
    simp only [Program.hookAtOff?, Program.rebase, PlacedLib.program, Option.or_eq_none_iff,
      List.findSome?_eq_none_iff, List.mem_map]
    refine ⟨fun x ⟨e, he, hx⟩ => ?_, fun _ _ => by split <;> rfl⟩
    subst hx
    have heq : e = "alpha_entry" := by simpa [betaClientLib] using he
    subst heq
    simp only [beq_false_of_ne (by omega : (pl.ρ "alpha_entry" - pl.base).toNat ≠ 0),
      Bool.false_eq_true, ↓reduceIte]
  have hfetch : (betaClientLib.program pl (alphaCodeROHookTable mpl)).fetch pl.base =
      some (.b (pl.ρ "alpha_entry" - pl.base)) := by
    have hf0 := ProofLib.GenPlacedFetches.fetch_rebase_of_externBranch
      betaClient_code_eq betaClient_tree_size (off := 0)
      (r := { off := 0, kind := .jump26, sym := "alpha_entry" })
      (e := "alpha_entry") false (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide) rfl rfl rfl (w := 0x14000000#32) rfl (by decide)
      (pl := pl) (b := pl.base) (X := alphaCodeROHookTable mpl) hpl_b hnh
    change ((betaClientLib.program pl).rebase pl.base (alphaCodeROHookTable mpl)).fetch pl.base = _
    simpa using hf0
  have hadd : pl.base + (pl.ρ "alpha_entry" - pl.base) = pl.ρ "alpha_entry" := by bv_arith
  exact subroutine_ok_of_b (spec := alphaEntryCodeROSpec mpl) hfetch hadd (h := htarget_ok)

/-! ## Existential Ghost Witness, Internal Frame, and `.allowOom` -/

/-- State-indexed pool specification hiding existential witness `v : BitVec 64`, carrying extra
    caller frame `(slack ↦₆₄ w)` across `.Running`, and admitting `.OutOfMemory` (`allowOom`) where
    both `codeRO` and `(slack ↦₆₄ w)` are dropped cleanly. -/
def alphaExistentialPoolSpec (mpl : MultiPlacement) (tp : BitVec 64)
    (ptr slack : BitVec 64) : Spec (BitVec 64) where
  pre := fun w s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧ s0.tpidrEl0 = tp⌝ ∗
      alphaMultiLib.codeRO mpl ∗
      (∃∗ v : BitVec 64, ptr ↦₆₄ᵣ v) ∗
      (slack ↦₆₄ w)
  post := fun w _ sf =>
    (∃∗ v : BitVec 64, ⌜sf.readReg64 .x0 = v⌝ ∗ (ptr ↦₆₄ᵣ v)) ∗
      alphaMultiLib.codeRO mpl ∗
      (slack ↦₆₄ w)
  onOom := fun _ _ _ => ⌜True⌝

theorem alphaLeafExistentialPool_hookOk {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) (tp ptr slack : BitVec 64) :
    HookOk (alphaMultiLib.codeROSubroutineHook mpl "alpha_leaf")
      (alphaExistentialPoolSpec mpl tp ptr slack) := by
  obtain ⟨_, i, off, hlook, hall⟩ := alphaLeafOom_subroutineOk
  have hi_eq : i = 1 := by
    have h0 : lookupBlockSym "alpha_leaf" alphaMultiLib.blocks = some (1, 0) := rfl
    rw [h0] at hlook
    exact (Prod.mk.inj (Option.some.inj hlook)).1.symm
  subst hi_eq
  refine subroutineHook_ok_of_multiCodeRO_at
    (Q := fun w _ _ => slack ↦₆₄ w)
    (φ := fun _ pv s0 => pv.1 = ptr ∧ s0.tpidrEl0 = tp)
    hpl hlook (hall mpl hpl)
    (fun w s0 => ?_)
    (fun w pv s0 sf' hφ _ _ _ => ?_)
  · dsimp only [alphaExistentialPoolSpec, Spec.allowOom, alphaLeafSpec]
    refine Entails.pure_left fun ⟨hx0, htp⟩ => ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun v => Entails.sepExists_right (ptr, v) ?_
    refine Entails.pure_right ⟨rfl, htp⟩ ?_
    have hx0' :
        (multiCodeROHookEntry alphaMultiLib mpl 1
          (alphaMultiLib.fnAddr mpl "alpha_leaf") s0).readReg64 .x0 = ptr := by
      rwa [multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0 (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (Entails.pure_right hx0' (Entails.refl _)))
  · rcases pv with ⟨p', v⟩
    have hp' : p' = ptr := hφ.1
    subst p'
    dsimp only [alphaExistentialPoolSpec, Spec.allowOom, alphaLeafSpec]
    rw [← sepConj_assoc (alphaMultiLib.codeRO mpl) (⌜_⌝ ∗ (ptr ↦₆₄ᵣ v)),
        ← sepConj_assoc (alphaMultiLib.codeRO mpl) ⌜_⌝,
        sepConj_comm (alphaMultiLib.codeRO mpl) ⌜_⌝,
        sepConj_assoc ⌜_⌝, sepConj_assoc ⌜_⌝]
    refine Entails.pure_left fun ⟨hx0, _⟩ => ?_
    have hx0_exit :
        (multiCodeROHookExit alphaMultiLib mpl 1 s0 sf').readReg64 .x0 = v := by
      rwa [multiCodeROHookExit_readReg64 _ _ _ _ _ .x0 (by decide)]
    rw [sepConj_comm (alphaMultiLib.codeRO mpl) (ptr ↦₆₄ᵣ v), sepConj_assoc]
    exact Entails.sepExists_intro_frame v
      (sepConj_mono_left (Entails.pure_right hx0_exit (Entails.refl _)))

/-! ## Non-Executable (`Perm.ro`) Caller Memory Witness -/

theorem alphaEntry_codeRO_runs_on_ro_memory {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) {v w : BitVec 64} {scratch : BitVec 64} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hperm0 : s0.mem.perm (mpl.base 0) = some .ro)
    (hmem : s0.mem ⊨
      (alphaMultiLib.codeRO mpl ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)) ∗ (scratch ↦₆₄ w)) :
    ¬ alphaMultiLib.PermsRX mpl s0.mem ∧
    ¬ alphaMultiLib.CodeLoaded mpl s0.mem ∧
    let sf := (multiCodeROSubroutineHook alphaMultiLib mpl "alpha_entry") s0
    s0.mem.KeepsFrozen sf.mem ∧
    Returned s0 sf ∧
    CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨
      (⌜sf.readReg64 .x0 = v⌝ ∗ alphaMultiLib.codeRO mpl ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)) ∗
      (scratch ↦₆₄ w)) := by
  have hnot_rx : ¬ alphaMultiLib.PermsRX mpl s0.mem := by
    intro hrx
    have hin : InRegion (mpl.base 0) alphaMultiLib.blocks[0].code.length (mpl.base 0) := by
      simp only [InRegion, BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod]
      decide
    have hp := (hrx 0 (by decide) (mpl.base 0) hin).1
    rw [hperm0] at hp
    cases hp
  have hnot_cl : ¬ alphaMultiLib.CodeLoaded mpl s0.mem :=
    fun hcl => hnot_rx ((alphaMultiLib.codeLoaded_iff_codeRO hpl).mp hcl).1
  obtain ⟨hkf, _, hout⟩ :=
    alphaEntryCodeRO_hookOk hpl v (scratch ↦₆₄ w) s0 hrun hmem hsp
  refine ⟨hnot_rx, hnot_cl, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact ⟨hkf, hret, hcc, hpost⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## Negative `#guard_msgs` Tests -/

-- Negative 1: `subroutineHook_ok_of_multiCodeRO` rejects a caller spec (`missingCodeLoadedSpec`)
-- that omits `alphaMultiLib.codeRO mpl` from `spec.pre`.
/--
error: Type mismatch
  Entails.refl ((missingCodeLoadedSpec mpl).pre x s0)
has type
  (missingCodeLoadedSpec mpl).pre x s0 ⊢ (missingCodeLoadedSpec mpl).pre x s0
-/
#guard_msgs (error, drop info, substring := true) in
example {mpl : MultiPlacement} (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.codeROSubroutineHook mpl "alpha_entry")
      (missingCodeLoadedSpec mpl) :=
  subroutineHook_ok_of_multiCodeRO hpl alphaEntry_subroutineOk
    (fun x s0 => Entails.refl ((missingCodeLoadedSpec mpl).pre x s0))
    (fun _ _ _ _ _ _ => Entails.top_right fun _ => trivial)

-- Negative 2: `subroutineHook_ok_of_multiCodeLoaded` rejects `alphaEntryCodeROSpec` because
-- `alphaEntryCodeROSpec` carries only `alphaMultiLib.codeRO mpl` without `CodeLoaded`.
/--
error: Type mismatch
  Entails.refl ((alphaEntryCodeROSpec mpl).pre x s0)
has type
  (alphaEntryCodeROSpec mpl).pre x s0 ⊢ (alphaEntryCodeROSpec mpl).pre x s0
-/
#guard_msgs (error, drop info, substring := true) in
example {mpl : MultiPlacement} (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.subroutineHook mpl "alpha_entry")
      (alphaEntryCodeROSpec mpl) :=
  subroutineHook_ok_of_multiCodeLoaded hpl alphaEntry_subroutineOk
    (fun x s0 => Entails.refl ((alphaEntryCodeROSpec mpl).pre x s0))
    (fun _ _ _ _ => Entails.top_right fun _ => trivial)

-- Negative 3: `HookOk` for `multiSubroutineHook` cannot be substituted where
-- `multiCodeROSubroutineHook` is expected.
/--
error: Type mismatch
  alphaEntryCaller_hookOk hpl
has type
  HookOk (multiSubroutineHook alphaMultiLib mpl "alpha_entry") (alphaEntryCallerSpec mpl)
-/
#guard_msgs (error, drop info, substring := true) in
example {mpl : MultiPlacement} (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (multiCodeROSubroutineHook alphaMultiLib mpl "alpha_entry")
      (alphaEntryCallerSpec mpl) :=
  alphaEntryCaller_hookOk hpl

end Examples.Testing.MultiCodeROHookTest
