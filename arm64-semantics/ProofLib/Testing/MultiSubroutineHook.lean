/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed
public import ProofLib.GenPlacedFetches
public import ProofLib.Hoare.HookMap
public meta import ProofLib.ProgramReflection

/-!
# Multi-Block Placed Library Hook Tests

Regression tests for `Obj.MultiPlacedLib.subroutineHook`, `multiSubroutineHook`,
`subroutineHook_ok_of_multiCodeLoaded`, and `Obj.MultiPlacedLib.codeRO`. Covers cross-block call
lifting to `HookOk` and `HookSat`, read-only code ownership compatibility in caller frames, and
negative `#guard_msgs` checks.
-/

@[expose] public section

namespace Examples.Testing.MultiSubroutineHookTest

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w =>
    [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-! ## Synthetic Two-Block Library -/

def alphaBlk0 : CodeBlock where
  code := wordsLE [
    0x90000000#32, 0x91000000#32, 0xaa1e03e9#32,
    0x94000000#32, 0xaa0903fe#32, 0xd65f03c0#32]
  align := 4
  symbols := [("alpha_entry", 0)]
  relocs := [
    { off := 0, kind := .adrpHi21, sym := "tab" },
    { off := 4, kind := .addLo12, sym := "tab" },
    { off := 12, kind := .call26, sym := "alpha_leaf" }]
  externs := ["alpha_leaf"]

def alphaBlk1 : CodeBlock where
  code := wordsLE [0xf9400000#32, 0xd65f03c0#32]
  align := 4
  symbols := [("alpha_leaf", 0), ("internal_only", 4)]
  relocs := []

def alphaMultiLib : MultiPlacedLib where
  name := "alpha_multi"
  blocks := [alphaBlk0, alphaBlk1]
  data := [{ sym := "tab", align := 8, readOnly := true, bytes := List.replicate 8 0#8 }]
  exports := ["alpha_entry", "alpha_leaf"]

def alphaLib0 : PlacedLib := alphaMultiLib.blockLib 0
def alphaLib1 : PlacedLib := alphaMultiLib.blockLib 1

class AlphaPlacement where
  mpl : MultiPlacement
  placeable : alphaMultiLib.Placeable mpl

def alphaPl0 [AlphaPlacement] : Placement :=
  alphaMultiLib.blockPlacement AlphaPlacement.mpl 0

theorem alphaPlaceable0 [AlphaPlacement] : alphaLib0.Placeable alphaPl0 :=
  alphaMultiLib.placeable_blockLib (by decide) AlphaPlacement.placeable

def alphaPl1 [AlphaPlacement] : Placement :=
  alphaMultiLib.blockPlacement AlphaPlacement.mpl 1

theorem alphaPlaceable1 [AlphaPlacement] : alphaLib1.Placeable alphaPl1 :=
  alphaMultiLib.placeable_blockLib (by decide) AlphaPlacement.placeable

def alphaPC0 [AlphaPlacement] : Program := alphaLib0.program alphaPl0
def alphaPC1 [AlphaPlacement] : Program := alphaLib1.program alphaPl1

def alphaProg0 : Program := { code := alphaBlk0.code, symbols := alphaBlk0.symbols }
def alphaProg1 : Program := { code := alphaBlk1.code, symbols := alphaBlk1.symbols }

def alphaTree0 : WordTree := word_tree_of% alphaProg0
def alphaTree1 : WordTree := word_tree_of% alphaProg1

theorem alpha0_code_eq : alphaLib0.text.code = alphaTree0.toBytes := by rfl_kernel
theorem alpha0_tree_size : alphaTree0.checkSize? = some 6 := by rfl_kernel

theorem alpha1_code_eq : alphaLib1.text.code = alphaTree1.toBytes := by rfl_kernel
theorem alpha1_tree_size : alphaTree1.checkSize? = some 2 := by rfl_kernel

def alphaSymChars0 : List (List Char × Nat) := sym_chars_of% alphaProg0
theorem alpha0_symbols_eq : alphaLib0.text.symbols = toStringSymbols alphaSymChars0 := by
  rfl_kernel
theorem alpha0_symbols_fresh : allFreshCharSymbols alphaSymChars0 = true := by rfl_kernel

def alphaSymChars1 : List (List Char × Nat) := sym_chars_of% alphaProg1
theorem alpha1_symbols_eq : alphaLib1.text.symbols = toStringSymbols alphaSymChars1 := by
  rfl_kernel
theorem alpha1_symbols_fresh : allFreshCharSymbols alphaSymChars1 = true := by rfl_kernel

gen_placed_fetches alphaPC0 alphaLib0 alphaTree0 alpha0_code_eq alpha0_tree_size
  via_placement alphaPl0 alphaPlaceable0 [0x0 → 0x14]
gen_placed_fnOffs alphaPC0 alphaLib0 alphaSymChars0 alpha0_symbols_eq alpha0_symbols_fresh

gen_placed_fetches alphaPC1 alphaLib1 alphaTree1 alpha1_code_eq alpha1_tree_size
  via_placement alphaPl1 alphaPlaceable1 [0x0 → 0x4]
gen_placed_fnOffs alphaPC1 alphaLib1 alphaSymChars1 alpha1_symbols_eq alpha1_symbols_fresh

abbrev aMpl [AlphaPlacement] : MultiPlacement := AlphaPlacement.mpl

def alphaLeafSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (ptr, v) s0 => ⌜s0.readReg64 .x0 = ptr⌝ ∗ (ptr ↦₆₄ᵣ v)
  post := fun (ptr, v) s0 sf =>
    ⌜sf.readReg64 .x0 = v ∧ sf.readReg64 .x9 = s0.readReg64 .x9⌝ ∗ (ptr ↦₆₄ᵣ v)

theorem alphaLeaf_ok [AlphaPlacement] :
    subroutine_ok (alphaPC1.rebase alphaPl1.base (fun _ => none))
      alphaPl1.base (alphaMultiLib.withCodeLoaded aMpl alphaLeafSpec) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, alphaLeafSpec]
  wp_entry "alpha_leaf" pv s0
  wp_steps
  wp_done

theorem alphaLeaf_subroutineOk :
    alphaMultiLib.subroutineOk "alpha_leaf" (fun _ => alphaLeafSpec) :=
  ⟨by decide, 1, 0, rfl, fun mpl hpl => by
    have hfn : alphaMultiLib.fnAddr mpl "alpha_leaf" = mpl.base 1 := by
      simp [MultiPlacedLib.fnAddr, lookupBlockSym, lookupBlockSymAux, lookup,
        alphaMultiLib, alphaBlk0, alphaBlk1]
    rw [hfn]
    exact @alphaLeaf_ok ⟨mpl, hpl⟩⟩

def alphaEntrySpec (mpl : MultiPlacement) : Spec (BitVec 64) where
  pre := fun v _ => (mpl.ρ "tab") ↦₆₄ᵣ v
  post := fun v _ sf => ⌜sf.readReg64 .x0 = v⌝ ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)

theorem alphaEntry_ok [AlphaPlacement] :
    subroutine_ok (alphaPC0.rebase alphaPl0.base (fun _ => none))
      alphaPl0.base (alphaMultiLib.withCodeLoaded aMpl (alphaEntrySpec aMpl)) := by
  dsimp only [MultiPlacedLib.withCodeLoaded, alphaEntrySpec]
  wp_entry "alpha_entry" v s0
  have hpc0 : s0.pc = alphaPl0.base + 0#64 := by simp [hpc]
  wp_steps
  wp_call_block alphaLeaf_ok (aMpl.ρ "tab", v)
  wp_steps
  wp_done

theorem alphaEntry_subroutineOk :
    alphaMultiLib.subroutineOk "alpha_entry" alphaEntrySpec :=
  ⟨by decide, 0, 0, rfl, fun mpl hpl => by
    have hfn : alphaMultiLib.fnAddr mpl "alpha_entry" = mpl.base 0 := by
      simp [MultiPlacedLib.fnAddr, lookupBlockSym, lookupBlockSymAux, lookup,
        alphaMultiLib, alphaBlk0, alphaBlk1]
    rw [hfn]
    exact @alphaEntry_ok ⟨mpl, hpl⟩⟩

/-! ## Lifting to HookOk and HookSat -/

theorem alphaEntry_codeLoadedHook_ok {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.subroutineHook mpl "alpha_entry")
      (alphaMultiLib.codeLoadedSubroutineHook mpl "alpha_entry" alphaEntrySpec) :=
  subroutineHook_ok_codeLoadedMultiSubroutineHook hpl alphaEntry_subroutineOk

def alphaEntryCallerSpec (mpl : MultiPlacement) : Spec (BitVec 64) where
  pre := fun v s0 => ⌜alphaMultiLib.CodeLoaded mpl s0.mem⌝ ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)
  post := fun v _ sf =>
    ⌜sf.readReg64 .x0 = v ∧ alphaMultiLib.CodeLoaded mpl sf.mem⌝ ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)

theorem alphaEntryCaller_hookOk {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (multiSubroutineHook alphaMultiLib mpl "alpha_entry")
      (alphaEntryCallerSpec mpl) := by
  refine subroutineHook_ok_of_multiCodeLoaded hpl alphaEntry_subroutineOk
    (fun _ _ => Entails.refl _)
    (fun v s0 sf' hL0 => ?_)
  refine Entails.pure_left fun hLf => ?_
  dsimp only [alphaEntrySpec, alphaEntryCallerSpec, ToBaseSpec.toSpec]
  refine Entails.pure_left fun hx0 => ?_
  have hx0_exit :
      (subroutineHookExit
        (alphaMultiLib.blockProgram mpl (alphaMultiLib.fnBlockIdx "alpha_entry")) s0 sf').readReg64 .x0 = v := by
    rwa [subroutineHookExit_readReg64 _ _ _ .x0 (by decide)]
  have hLf_exit :
      alphaMultiLib.CodeLoaded mpl
        (subroutineHookExit
          (alphaMultiLib.blockProgram mpl (alphaMultiLib.fnBlockIdx "alpha_entry")) s0 sf').mem := by
    rwa [alphaMultiLib.subroutineHookExit_mem_of_codeLoaded hL0 hLf (by decide)]
  exact Entails.pure_right ⟨hx0_exit, hLf_exit⟩ (Entails.refl _)

theorem alphaLeafOom_subroutineOk :
    alphaMultiLib.subroutineOk "alpha_leaf" (fun _ => alphaLeafSpec.allowOom) := by
  obtain ⟨hexp, i, off, hlook, hall⟩ := alphaLeaf_subroutineOk
  refine ⟨hexp, i, off, hlook, fun mpl hpl => ?_⟩
  exact subroutine_ok_mono (hall mpl hpl)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ h => False.elim (not_satisfies_false_sepConj h))

theorem alphaLeafOom_codeLoadedHook_ok {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.subroutineHook mpl "alpha_leaf")
      (Spec.codeLoadedMultiSubroutineHook alphaMultiLib mpl "alpha_leaf"
        (fun _ => alphaLeafSpec.allowOom)) :=
  subroutineHook_ok_codeLoadedMultiSubroutineHook hpl alphaLeafOom_subroutineOk

structure AlphaHooks (mpl : MultiPlacement)
    (hooks : String → Option (State → State)) : Prop where
  alpha_entry : HookSat hooks "alpha_entry" (alphaEntryCallerSpec mpl)

noncomputable def alphaHookTable (mpl : MultiPlacement) : String → Option (State → State) :=
  hookMap [("alpha_entry", multiSubroutineHook alphaMultiLib mpl "alpha_entry")] (fun _ => none)

theorem alphaHookTable_sat {mpl : MultiPlacement} (hpl : alphaMultiLib.Placeable mpl) :
    AlphaHooks mpl (alphaHookTable mpl) where
  alpha_entry := by
    simp only [alphaHookTable, HookSat_hookMap_cons_self]
    exact alphaEntryCaller_hookOk hpl

/-! ## Client Library Hook Composition -/

def betaClientLib : PlacedLib where
  name := "beta_client"
  text := {
    code := wordsLE [0x14000000#32]
    align := 4
    symbols := [("beta_call", 0)]
    relocs := [{ off := 0, kind := .jump26, sym := "alpha_entry" }]
    externs := ["alpha_entry"] }
  exports := ["beta_call"]

def betaClientProg : Program := { code := betaClientLib.text.code }
def betaClientTree : WordTree := word_tree_of% betaClientProg
theorem betaClient_code_eq : betaClientLib.text.code = betaClientTree.toBytes := by rfl_kernel
theorem betaClient_tree_size : betaClientTree.checkSize? = some 1 := by rfl_kernel

theorem betaClient_subroutineOk_of_hooks {mpl : MultiPlacement}
    {hooks : String → Option (State → State)} (hH : AlphaHooks mpl hooks) :
    betaClientLib.subroutineOk "beta_call" (fun _ => alphaEntryCallerSpec mpl) hooks := by
  refine ⟨by decide, fun pl hpl => ?_⟩
  obtain ⟨f, hf, hok⟩ := hH.alpha_entry
  have hext : (betaClientLib.program pl hooks).externAt? (pl.ρ "alpha_entry") = some f := by
    have h := PlacedLib.externAt?_program (lib := betaClientLib) (pl := pl)
      (X := hooks) (O := fun _ => none) (svc := Syscall.standard) (e := "alpha_entry")
      (by simp [betaClientLib]) (by decide)
    simpa [PlacedLib.program, hf] using h
  have htarget_ok : subroutine_ok (betaClientLib.program pl hooks)
      (pl.ρ "alpha_entry") (alphaEntryCallerSpec mpl) :=
    subroutine_ok_of_hookOk hext hok
  have hfn : betaClientLib.fnAddr pl "beta_call" = pl.base := by
    simp [PlacedLib.fnAddr, lookup, betaClientLib]
  rw [hfn]
  have hnh : ((betaClientLib.program pl).rebase pl.base hooks).hookAtOff? 0 = none := by
    have hext_ge := (hpl.text.externs_ok "alpha_entry" (by decide)).2
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
  have hfetch : (betaClientLib.program pl hooks).fetch pl.base =
      some (.b (pl.ρ "alpha_entry" - pl.base)) := by
    have hf0 := ProofLib.GenPlacedFetches.fetch_rebase_of_externBranch
      betaClient_code_eq betaClient_tree_size (off := 0)
      (r := { off := 0, kind := .jump26, sym := "alpha_entry" })
      (e := "alpha_entry") false (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide) rfl rfl rfl (w := 0x14000000#32) rfl (by decide)
      (pl := pl) (b := pl.base) (X := hooks) hpl hnh
    change ((betaClientLib.program pl).rebase pl.base hooks).fetch pl.base = _
    simpa using hf0
  have hadd : pl.base + (pl.ρ "alpha_entry" - pl.base) = pl.ρ "alpha_entry" := by bv_arith
  exact subroutine_ok_of_b (spec := alphaEntryCallerSpec mpl) hfetch hadd (h := htarget_ok)

theorem betaClient_linked_with_alpha {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) :
    betaClientLib.subroutineOk "beta_call"
      (fun _ => alphaEntryCallerSpec mpl) (alphaHookTable mpl) :=
  betaClient_subroutineOk_of_hooks (alphaHookTable_sat hpl)

/-! ## Read-Only Code Ownership and CodeLoaded Bridges -/

theorem alphaEntry_hook_preserves_caller_codeRO {mpl : MultiPlacement}
    (hpl : alphaMultiLib.Placeable mpl) {v w : BitVec 64} {scratch : BitVec 64} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hL0 : alphaMultiLib.CodeLoaded mpl s0.mem)
    (hmem : s0.mem ⊨ ((mpl.ρ "tab") ↦₆₄ᵣ v) ∗ (alphaMultiLib.codeRO mpl ∗ (scratch ↦₆₄ w))) :
    let sf := (multiSubroutineHook alphaMultiLib mpl "alpha_entry") s0
    s0.mem.KeepsFrozen sf.mem ∧
    Returned s0 sf ∧
    CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨
      (⌜sf.readReg64 .x0 = v ∧ alphaMultiLib.CodeLoaded mpl sf.mem⌝ ∗ ((mpl.ρ "tab") ↦₆₄ᵣ v)) ∗
      (alphaMultiLib.codeRO mpl ∗ (scratch ↦₆₄ w))) := by
  have hpre : s0.mem ⊨ (alphaEntryCallerSpec mpl).pre v s0 ∗
      (alphaMultiLib.codeRO mpl ∗ (scratch ↦₆₄ w)) := by
    dsimp only [alphaEntryCallerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL0, hmem⟩
  obtain ⟨hkf, _, hout⟩ :=
    alphaEntryCaller_hookOk hpl v (alphaMultiLib.codeRO mpl ∗ (scratch ↦₆₄ w)) s0 hrun hpre hsp
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact ⟨hkf, hret, hcc, hpost⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

example {mpl : MultiPlacement} {s0 sf' : State}
    (hL0 : alphaMultiLib.CodeLoaded mpl s0.mem)
    (hLf : alphaMultiLib.CodeLoaded mpl sf'.mem) :
    loadCodeMem (alphaMultiLib.blockProgram mpl 0) s0.mem = s0.mem ∧
    restoreCodeMem (alphaMultiLib.blockProgram mpl 0) s0.mem sf'.mem = sf'.mem ∧
    (subroutineHookEntry (alphaMultiLib.blockProgram mpl 0)
      (alphaMultiLib.fnAddr mpl "alpha_entry") s0).mem = s0.mem ∧
    (subroutineHookExit (alphaMultiLib.blockProgram mpl 0) s0 sf').mem = sf'.mem :=
  ⟨alphaMultiLib.loadCodeMem_eq_of_codeLoaded hL0 (by decide),
   alphaMultiLib.restoreCodeMem_eq_of_codeLoaded hL0 hLf (by decide),
   alphaMultiLib.subroutineHookEntry_mem_of_codeLoaded hL0 (by decide),
   alphaMultiLib.subroutineHookExit_mem_of_codeLoaded hL0 hLf (by decide)⟩

example {mpl : MultiPlacement} {m : Memory} (hpl : alphaMultiLib.Placeable mpl) :
    (alphaMultiLib.CodeLoaded mpl m ↔
      alphaMultiLib.PermsRX mpl m ∧ (m ⊨ alphaMultiLib.codeRO mpl)) ∧
    ((alphaMultiLib.codeRO mpl ∗ alphaMultiLib.codeRO mpl) = alphaMultiLib.codeRO mpl) :=
  ⟨alphaMultiLib.codeLoaded_iff_codeRO hpl, alphaMultiLib.codeRO_dup mpl⟩

example {P : Program} {mpl : MultiPlacement} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (hL : alphaMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP P mid s Pre (fun sm Pm =>
      alphaMultiLib.CodeLoaded mpl sm.mem → SepWP P target sm Pm post)) :
    SepWP P target s Pre (fun sf Pf => post sf Pf ∧ alphaMultiLib.CodeLoaded mpl sf.mem) :=
  SepWP.mono_multiCodeLoaded hL (SepWP.seq_multiCodeLoaded hL h1)
    (fun _ _ _ _ hLf hp => ⟨hp, hLf⟩)

/-! ## Negative Regression Tests -/

def missingCodeLoadedSpec (mpl : MultiPlacement) : Spec (BitVec 64) where
  pre := fun v _ => (mpl.ρ "tab") ↦₆₄ᵣ v
  post := fun _ _ _ => anyHeap

-- `subroutineHook_ok_of_multiCodeLoaded` rejects `Entails.refl _` when `spec.pre` omits
-- `⌜alphaMultiLib.CodeLoaded mpl s0.mem⌝`.
/--
error: Type mismatch
  Entails.refl ((missingCodeLoadedSpec mpl).pre x s0)
has type
  (missingCodeLoadedSpec mpl).pre x s0 ⊢ (missingCodeLoadedSpec mpl).pre x s0
-/
#guard_msgs (error, drop info, substring := true) in
example {mpl : MultiPlacement} (hpl : alphaMultiLib.Placeable mpl) :
    HookOk (alphaMultiLib.subroutineHook mpl "alpha_entry") (missingCodeLoadedSpec mpl) :=
  subroutineHook_ok_of_multiCodeLoaded hpl alphaEntry_subroutineOk
    (fun x s0 => Entails.refl ((missingCodeLoadedSpec mpl).pre x s0))
    (fun _ _ _ _ => Entails.top_right fun _ => trivial)

-- Unexported internal symbol `"internal_only"` is rejected by `alphaMultiLib.exports`.
/--
error: Tactic `decide` proved that the proposition
  "internal_only" ∈ alphaMultiLib.exports
is false
-/
#guard_msgs (error, drop info) in
example : "internal_only" ∈ alphaMultiLib.exports := by decide

-- `codeLoaded_of_codeRO` requires `MultiPlacedLib.PermsRX` (`Perm.rx`), rejecting `m.RO`.
/--
error: Application type mismatch: The argument
  hro
has type
  ∀ (i : Nat) (hi : i < alphaMultiLib.blocks.length), m.RO (mpl.base i) alphaMultiLib.blocks[i].code.length
but is expected to have type
  alphaMultiLib.PermsRX mpl m
-/
#guard_msgs (error, drop info, substring := true) in
example {mpl : MultiPlacement} {m : Memory} {R : SepProp}
    (hpl : alphaMultiLib.Placeable mpl)
    (hro : ∀ (i : Nat) (hi : i < alphaMultiLib.blocks.length),
      m.RO (mpl.base i) alphaMultiLib.blocks[i].code.length)
    (hsat : m ⊨ alphaMultiLib.codeRO mpl ∗ R) :
    alphaMultiLib.CodeLoaded mpl m :=
  alphaMultiLib.codeLoaded_of_codeRO hpl hro hsat

/-! ## Indexed Symbol Resolution -/

gen_multi_sym_index alphaSymIdx alphaMultiLib

example (mpl : MultiPlacement) :
    alphaMultiLib.fnAddr mpl "alpha_entry" = mpl.base 0 + 0#64 ∧
    alphaMultiLib.fnAddr mpl "alpha_leaf" = mpl.base 1 + 0#64 ∧
    alphaMultiLib.resolve mpl "tab" = mpl.ρ "tab" ∧
    (alphaSymIdx.blockProgram_fnAddr_eq (X := fun _ => none) (O := fun _ => none)
      (svc := Syscall.standard) mpl (name := "internal_only") (i := 1) (off := 4)
      (by decide +kernel) :
      (alphaMultiLib.blockProgram mpl 1).fnAddr "internal_only" = mpl.base 1 + 4#64) =
      alphaSymIdx.blockProgram_fnAddr_eq mpl (by decide +kernel) :=
  ⟨alphaSymIdx.fnAddr_eq_base mpl (by decide +kernel),
   alphaSymIdx.fnAddr_eq_base mpl (by decide +kernel),
   alphaSymIdx.resolve_eq_rho mpl (by decide +kernel),
   rfl⟩

end Examples.Testing.MultiSubroutineHookTest
