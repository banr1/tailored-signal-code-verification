/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHooksUnfetchedPerPc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection

/-!
# Concrete `externAt?` Witnesses and Step-Lifting Corollaries for `cliProgExtPlacedAt`

**Not trusted (`Role::Proof`, Card `STEPS-LIFT-R2` / Consumer Leaf `L1`, `CliElfLib`).**

Stock-clean concrete side-fact layer (`SR3` consumer leaf `L1`) plus step-lifting corollaries for the real two-placement CLI
program `P_real_W := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` under
`hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl`, plugging directly into
`ElfSlicesPqOomH2FirstStopGeneric` (`29805d70c5`, `h2fsgen_StepsVisitedIn` and
`h2fsgen_HooksUnfetched`) with **zero duplicate inductives**:

1. **Consumer Leaf `L1` (`h2sl_realW_noExtern_keepSub` & `h2sl_realW_noExtern_keepExec`):**
   - `h2sl_keepExec` (`[0x4686a0, 0x468724) ∪ [0x469000, 0x46f000)`), containing all `132` code
     bytes of `hole2_str1Prog mpl` (block `623`) and all `24,576` bytes of `f3TrialRxProg`
     (`seg[2]`), while excluding all hooked addresses in `lsPlacedCompactLit` (`< 0x469000` and
     disjoint from `[0x4686a0, 0x468724)`);
   - Non-`Sig` compact-tag reduction (`h2sl_realW_externAt_eq_compact`) + `rfl_kernel` disjointness
     row on `lsPlacedCompactLit`, establishing `h2sl_realW_noExtern_keepExec` and
     `h2sl_realW_noExtern_keepSub` (`∀ pc, hole2_keepSub pc = true → P_real_W.externAt? pc = none`).
2. **Symbol Pins, `hole2_strCloneProg` Extern Containment, & Dehooked Symbols:**
   - `h2sl_realW_externAt_handleError`, `h2sl_strCloneProg_externAt_sub_realW`,
     `h2sl_str1Prog_codeLoaded_keepExec_iff_keep`, and `h2sl_rxProg_codeLoaded_keepExec_iff_keep`;
   - `h2sl_realW_dehooked_witness`: `externAt? = none` + `DirectOrBranchStub` on every symbol in
     `cliDehookedSymsPlaced`.
3. **Stock-Clean Per-Address `HooksUnfetchedPerPc` & Lift Corollaries:**
   - `h2sl_realW_hooksUnfetchedPerPc_keepSub`, `h2sl_realW_hooksUnfetchedPerPc_keepExec`,
     `h2sl_realW_hooksUnfetchedPerPc_strClone`, and `h2sl_realW_hooksUnfetchedPerPc_strClone_on`;
   - Ready-to-apply `Steps P_real_W` corollaries `h2sl_steps_realW_of_visitedIn_keepSub`,
     `h2sl_steps_realW_of_visitedIn_keepExec`, `h2sl_stepsUntil_emptyProg_to_realW_perPc`,
     `h2sl_stepsUntil_emptyProg_to_realW_of_allProg`, and `h2sl_stepsUntil_strClone_to_realW_perPc`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession
  (CliHooks cliDehookedSymsPlaced cliElfBytes cliElfImage cliExternsPlaced
   cliHookTablePlaced cliPanicSymbolsPlaced isCliPanicSymbolPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (DirectOrBranchStub)
open LibsignalBinary.Heap.Fine (f3RxWordCount)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt externAt?_cliProgExtPlacedSigAt_eq_none)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3HandleErrorIdx f3HandleErrorSym f3HandleError_pin_ok f3LsBlockBases f3LsBlocksLen
   f3LsSymAddrs libsignalBlocks_len lsHookNamesPlaced lsInternedMultiLib lsPlacedCompactLit
   lsPlacedStubPairs lsPlacedStubPairs_eq lsPlacedTagTableLit lsSharedExterns
   ls_block617_externs_eq ls_blockSymsMatch_ok ls_idsOk ls_names_nodup ls_sharedExterns_lt
   ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_dehooked_witness_of_inElf f3CliElf_libsignal_inElf_unique
   f3CliElf_rho_handleError_eq_of_linkedAt f3LsMpl f3TrialElf_parse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHooksUnfetchedPerPc
  (HooksUnfetchedPerPc hooksUnfetchedPerPc_of_noNewExternOn hooksUnfetchedPerPc_of_perPc
   stepsUntil_strClone_to_realW_perPc stepsVisitedIn_of_allProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_keep hole2_keepSub hole2_str1Prog hole2_strCloneProg)

/-! ## Executable Domain `h2sl_keepExec` -/

/-- Executable PC domain `[0x4686a0, 0x468724) ∪ [0x469000, 0x46f000)` (`<String as Clone>::clone` and `:text_b`),
covering all 132 bytes of `hole2_str1Prog mpl` and all 24,576 bytes of `f3TrialRxProg` while excluding
`:text_a`'s hooked stub/function range `[0x468724, 0x469000)`. -/
def h2sl_keepExec (a : BitVec 64) : Bool :=
  decide ((0x4686a0 ≤ a.toNat ∧ a.toNat < 0x468724) ∨ (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000))

theorem h2sl_keepSub_imp_keepExec {a : BitVec 64} (h : hole2_keepSub a = true) :
    h2sl_keepExec a = true := by
  unfold hole2_keepSub at h
  unfold h2sl_keepExec
  rw [decide_eq_true_eq] at h ⊢
  exact Or.inr h

theorem h2sl_keepExec_imp_keep {a : BitVec 64} (h : h2sl_keepExec a = true) :
    hole2_keep a = true := by
  unfold h2sl_keepExec at h
  unfold hole2_keep
  rw [decide_eq_true_eq] at h ⊢
  rcases h with ⟨h1, h2⟩ | hsub
  · exact Or.inl ⟨h1, by omega⟩
  · exact Or.inr hsub

theorem h2sl_keepExec_false_of_keep_false {a : BitVec 64} (h : hole2_keep a = false) :
    h2sl_keepExec a = false := by
  cases hk : h2sl_keepExec a with
  | false => rfl
  | true =>
    rw [h2sl_keepExec_imp_keep hk] at h
    cases h

theorem h2sl_realW_svc (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

theorem h2sl_emptyProg_svc : hole2_emptyProg.svc = Syscall.standard :=
  rfl

theorem h2sl_emptyProg_externAt (pc : BitVec 64) : hole2_emptyProg.externAt? pc = none :=
  rfl

theorem h2sl_strCloneProg_svc (mpl : MultiPlacement) :
    (hole2_strCloneProg mpl).svc = Syscall.standard :=
  rfl

/-! ## Compact-Tag Extern Disjointness on `h2sl_keepExec` and `hole2_keepSub` -/

section RawCompactTagTable
set_option maxRecDepth 200000

private theorem h2sl_list_findSome?_congr {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.findSome?_cons, h a List.mem_cons_self]
    cases g a with
    | none => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | some _ => rfl

private theorem h2sl_externAt?_cliProgExtPlacedAt (mpl mmpl : MultiPlacement) (W : CliHooks)
    (pc : BitVec 64) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc =
      (libsignalSessionLib.blockLib 617).text.externs.findSome? fun e =>
        if libsignalSessionLib.resolve mpl e == pc then cliExternsPlaced mmpl W e else none := by
  have key : ∀ (b : BitVec 64) (e : String),
      ((libsignalSessionLib.resolve mpl e - b).toNat == (pc - b).toNat) =
        (libsignalSessionLib.resolve mpl e == pc) := by
    intro b e
    cases h : libsignalSessionLib.resolve mpl e == pc with
    | true =>
      have heq := beq_iff_eq.mp h
      subst heq
      simp
    | false =>
      rw [beq_eq_false_iff_ne] at h ⊢
      intro hnat
      apply h
      have hbv := BitVec.eq_of_toNat_eq hnat
      have : (libsignalSessionLib.resolve mpl e - b) + b = (pc - b) + b := congrArg (· + b) hbv
      simpa [BitVec.sub_add_cancel] using this
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [cliProgExtPlacedAt, MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
    MultiPlacedLib.blockPlacement, Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none, List.findSome?_map, Function.comp_def, key]

private theorem h2sl_mem_lsNames_of_getD {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s) :
    s ∈ lsInternedMultiLib.names := by
  rw [← heq, Obj.Interned.getD_of_lt hlt]
  exact List.getElem_mem hlt

private theorem h2sl_lookupBlockSym_none_of_idx {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
  rw [← heq, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hlt]
  exact hid

private theorem h2sl_cliProgExtPlacedAt_externAt_eq_of_linkedAt {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (pc : BitVec 64) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc =
      (cliProgExtPlacedAt f3LsMpl (cliExternsPlaced mmpl) 617 W).externAt? pc := by
  obtain ⟨_, hp, hpl, hin⟩ := hLs
  cases f3TrialElf_parse.symm.trans hp
  have hres := (f3CliElf_libsignal_inElf_unique hpl hin).2.1
  rw [h2sl_externAt?_cliProgExtPlacedAt, h2sl_externAt?_cliProgExtPlacedAt,
    ls_block617_externs_eq]
  refine h2sl_list_findSome?_congr (l := lsSharedExterns.map _) fun e he => ?_
  simp only [List.mem_map] at he
  obtain ⟨idx, hidx, rfl⟩ := he
  have hlt := Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  rw [hres _ (h2sl_mem_lsNames_of_getD hlt rfl)]

private def h2sl_lookupKeyIdx : List String → String → Option Nat
  | [], _ => none
  | k :: ks, s => if k == s then some 0 else (h2sl_lookupKeyIdx ks s).map Nat.succ

private theorem h2sl_lookup_zip_eq_map {α : Type} (d : α) :
    ∀ (keys : List String) (vals : List α) (s : String),
      keys.length ≤ vals.length →
      (List.zip keys vals).lookup s = (h2sl_lookupKeyIdx keys s).map (fun i => vals.getD i d)
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | k :: ks, v :: vs, s, h => by
    simp only [List.zip_cons_cons, List.lookup, h2sl_lookupKeyIdx]
    have hcomm : (s == k) = (k == s) := BEq.comm
    rw [hcomm]
    cases hs : k == s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h2sl_lookup_zip_eq_map d ks vs s (Nat.le_of_succ_le_succ h)]
      cases h2sl_lookupKeyIdx ks s <;> rfl
    · rfl

private noncomputable def h2sl_cliHookVals (mmpl : MultiPlacement) (W : CliHooks) :
    List (State → State) :=
  (cliHookTablePlaced mmpl W).map Prod.snd

private theorem h2sl_cliHookTablePlaced_eq_zip (mmpl : MultiPlacement) (W : CliHooks) :
    cliHookTablePlaced mmpl W = List.zip lsHookNamesPlaced (h2sl_cliHookVals mmpl W) := by
  rfl_kernel

private theorem h2sl_lsHookNamesPlaced_eq_fst (mmpl : MultiPlacement) (W : CliHooks) :
    lsHookNamesPlaced = (cliHookTablePlaced mmpl W).map Prod.fst := by
  rfl_kernel

private theorem h2sl_lsHookNamesPlaced_len (mmpl : MultiPlacement) (W : CliHooks) :
    lsHookNamesPlaced.length ≤ (h2sl_cliHookVals mmpl W).length := by
  rw [h2sl_lsHookNamesPlaced_eq_fst mmpl W, h2sl_cliHookVals, List.length_map, List.length_map]

private noncomputable def h2sl_placedExternTag (s : String) : Option Nat :=
  if isCliPanicSymbolPlaced s then some 0
  else (h2sl_lookupKeyIdx lsHookNamesPlaced s).map Nat.succ

private noncomputable def h2sl_evalCliTagRaw (mmpl : MultiPlacement) (W : CliHooks) :
    Nat → State → State
  | 0 => Rust.panicked
  | k + 1 => (h2sl_cliHookVals mmpl W).getD k Rust.panicked

private theorem h2sl_cliExternsPlaced_eq_tag (mmpl : MultiPlacement) (W : CliHooks)
    (s : String) :
    cliExternsPlaced mmpl W s = (h2sl_placedExternTag s).map (h2sl_evalCliTagRaw mmpl W) := by
  unfold cliExternsPlaced h2sl_placedExternTag
  cases isCliPanicSymbolPlaced s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h2sl_cliHookTablePlaced_eq_zip mmpl W,
      h2sl_lookup_zip_eq_map Rust.panicked _ _ s (h2sl_lsHookNamesPlaced_len mmpl W)]
    cases h2sl_lookupKeyIdx lsHookNamesPlaced s <;> rfl
  · rfl

private theorem h2sl_findSome_map_val {α β γ : Type} (f : β → γ) :
    ∀ (L : List α) (g : α → Option β),
      L.findSome? (fun x => (g x).map f) = (L.findSome? g).map f
  | [], _ => rfl
  | x :: xs, g => by
    simp only [List.findSome?_cons]
    cases g x <;> simp [h2sl_findSome_map_val f xs g]

private noncomputable def h2sl_placedTagAt (pc : BitVec 64) : Option Nat :=
  lsPlacedStubPairs.findSome? fun (n, a) =>
    if a == pc then h2sl_placedExternTag n else none

private theorem h2sl_placedTagAt_eq_sharedExterns (pc : BitVec 64) :
    h2sl_placedTagAt pc = lsSharedExterns.findSome? (fun idx =>
      if f3LsSymAddrs.getD idx 0#64 == pc then
        h2sl_placedExternTag (lsInternedMultiLib.names.getD idx "")
      else none) := by
  unfold h2sl_placedTagAt
  rw [lsPlacedStubPairs_eq, List.findSome?_map]
  rfl

private theorem h2sl_cliProgExtPlacedAt_f3Ls_externAt_tag (mmpl : MultiPlacement) (W : CliHooks)
    (pc : BitVec 64) :
    (cliProgExtPlacedAt f3LsMpl (cliExternsPlaced mmpl) 617 W).externAt? pc =
      (h2sl_placedTagAt pc).map (h2sl_evalCliTagRaw mmpl W) := by
  rw [h2sl_placedTagAt_eq_sharedExterns, h2sl_externAt?_cliProgExtPlacedAt,
    ls_block617_externs_eq, List.findSome?_map]
  have hstep : (lsSharedExterns.findSome? (Function.comp
      (fun e => if libsignalSessionLib.resolve f3LsMpl e == pc then
        cliExternsPlaced mmpl W e else none)
      (fun idx => lsInternedMultiLib.names.getD idx ""))) =
      lsSharedExterns.findSome? (fun idx =>
        ((if f3LsSymAddrs.getD idx 0#64 == pc then
          h2sl_placedExternTag (lsInternedMultiLib.names.getD idx "") else none)).map
          (h2sl_evalCliTagRaw mmpl W)) := by
    refine h2sl_list_findSome?_congr (l := lsSharedExterns) fun idx hidx => ?_
    dsimp only [Function.comp_def]
    have hlt : idx < lsInternedMultiLib.names.length :=
      Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
    have hres : libsignalSessionLib.resolve f3LsMpl (lsInternedMultiLib.names.getD idx "") =
        f3LsSymAddrs.getD idx 0#64 := by
      rw [ls_toMultiPlacedLib_eq]
      change lsInternedMultiLib.toMultiPlacedLib.resolve
        (ElfCodeMatchesPlaced.f3LsLayout.toMultiPlacement lsInternedMultiLib.names) _ = _
      rw [Obj.Interned.toMultiPlacement_resolve_eq ls_names_nodup ls_idsOk ls_blockSymsMatch_ok,
        Obj.Interned.idxOf_getD ls_names_nodup hlt]
      rfl
    rw [hres, h2sl_cliExternsPlaced_eq_tag]
    cases f3LsSymAddrs.getD idx 0#64 == pc <;> rfl
  rw [hstep, h2sl_findSome_map_val]

private theorem h2sl_string_startsWith_eq_isPrefixOf (s pat : String) :
    s.startsWith pat = List.isPrefixOf pat.toList s.toList := by
  rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

private def h2sl_panicPrefixChars : List Char :=
  ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']

private theorem h2sl_core_panicking_toList_eq :
    "core::panicking::".toList = h2sl_panicPrefixChars := by
  rfl_kernel

private def h2sl_isPanicSymbolFast (name : String) : Bool :=
  List.isPrefixOf h2sl_panicPrefixChars name.toList ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

private theorem h2sl_isPanicSymbol_eq_fast (name : String) :
    Rust.isPanicSymbol name = h2sl_isPanicSymbolFast name := by
  unfold Rust.isPanicSymbol h2sl_isPanicSymbolFast
  rw [h2sl_string_startsWith_eq_isPrefixOf, h2sl_core_panicking_toList_eq]

private noncomputable def h2sl_placedExternTagFast (s : String) : Option Nat :=
  if cliPanicSymbolsPlaced.contains s || h2sl_isPanicSymbolFast s then some 0
  else (h2sl_lookupKeyIdx lsHookNamesPlaced s).map Nat.succ

private theorem h2sl_placedExternTag_eq_fast (s : String) :
    h2sl_placedExternTag s = h2sl_placedExternTagFast s := by
  unfold h2sl_placedExternTag h2sl_placedExternTagFast isCliPanicSymbolPlaced
  rw [h2sl_isPanicSymbol_eq_fast]

private def h2sl_lookupAddrTag (tbl : List (BitVec 64 × Option Nat)) (pc : BitVec 64) :
    Option Nat :=
  tbl.findSome? fun (a, t) => if a == pc then t else none

private noncomputable def h2sl_lsPlacedTagTable : List (BitVec 64 × Option Nat) :=
  lsPlacedStubPairs.map fun (n, a) => (a, h2sl_placedExternTagFast n)

private theorem h2sl_placedTagAt_eq_table (pc : BitVec 64) :
    h2sl_placedTagAt pc = h2sl_lookupAddrTag h2sl_lsPlacedTagTable pc := by
  unfold h2sl_placedTagAt h2sl_lookupAddrTag h2sl_lsPlacedTagTable
  rw [List.findSome?_map]
  refine h2sl_list_findSome?_congr (l := lsPlacedStubPairs) fun ⟨n, a⟩ _ => ?_
  dsimp only [Function.comp_def]
  rw [h2sl_placedExternTag_eq_fast]

private def h2sl_compactTagTbl : List (BitVec 64 × Option Nat) → List (Nat × Nat)
  | [] => []
  | (_, none) :: xs => h2sl_compactTagTbl xs
  | (a, some t) :: xs => (a.toNat, t) :: h2sl_compactTagTbl xs

private def h2sl_lookupAddrTagNat : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (a, t) :: xs, pc => if Nat.beq a pc then some t else h2sl_lookupAddrTagNat xs pc

private theorem h2sl_bv64_beq_eq_nat_beq (a b : BitVec 64) :
    (a == b) = Nat.beq a.toNat b.toNat := by
  cases h : a == b
  · symm
    rw [Bool.eq_false_iff]
    intro h'
    rw [Nat.beq_eq] at h'
    exact absurd (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h')) (by simp [h])
  · rw [beq_iff_eq] at h
    subst h
    exact (Nat.beq_refl _).symm

private theorem h2sl_lookupAddrTag_eq_compact :
    ∀ (tbl : List (BitVec 64 × Option Nat)) (pc : BitVec 64),
      h2sl_lookupAddrTag tbl pc = h2sl_lookupAddrTagNat (h2sl_compactTagTbl tbl) pc.toNat
  | [], _ => rfl
  | (_, none) :: xs, pc => by
    simp only [h2sl_lookupAddrTag, h2sl_compactTagTbl, List.findSome?_cons, ite_self]
    exact h2sl_lookupAddrTag_eq_compact xs pc
  | (a, some t) :: xs, pc => by
    simp only [h2sl_lookupAddrTag, h2sl_compactTagTbl, h2sl_lookupAddrTagNat,
      List.findSome?_cons]
    rw [h2sl_bv64_beq_eq_nat_beq a pc]
    cases Nat.beq a.toNat pc.toNat
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h2sl_lookupAddrTag_eq_compact xs pc
    · rfl

private theorem h2sl_lsPlacedTagTable_eq_lit :
    h2sl_lsPlacedTagTable = lsPlacedTagTableLit := by
  rfl_kernel

private theorem h2sl_compactTagTbl_placed_eq_lit :
    h2sl_compactTagTbl lsPlacedTagTableLit = lsPlacedCompactLit := by
  rfl_kernel

private theorem h2sl_placedTagAt_eq_compact (pc : BitVec 64) :
    h2sl_placedTagAt pc = h2sl_lookupAddrTagNat lsPlacedCompactLit pc.toNat := by
  rw [h2sl_placedTagAt_eq_table, h2sl_lsPlacedTagTable_eq_lit, h2sl_lookupAddrTag_eq_compact,
    h2sl_compactTagTbl_placed_eq_lit]

private theorem h2sl_realW_externAt_eq_compact {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (pc : BitVec 64) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc =
      (h2sl_lookupAddrTagNat lsPlacedCompactLit pc.toNat).map (h2sl_evalCliTagRaw mmpl W) := by
  rw [h2sl_cliProgExtPlacedAt_externAt_eq_of_linkedAt hLs mmpl W pc,
    h2sl_cliProgExtPlacedAt_f3Ls_externAt_tag, h2sl_placedTagAt_eq_compact]

private theorem h2sl_lookupAddrTagNat_none_of_all_ne :
    ∀ (xs : List (Nat × Nat)) (pc : Nat),
      (xs.all fun p => (!Nat.beq p.1 pc)) = true →
      h2sl_lookupAddrTagNat xs pc = none
  | [], _, _ => rfl
  | (a, _) :: xs, pc, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    simp only [h2sl_lookupAddrTagNat, hall.1, Bool.false_eq_true, ↓reduceIte]
    exact h2sl_lookupAddrTagNat_none_of_all_ne xs pc hall.2

private def h2sl_notInRangeNat (lo hi a : Nat) : Bool :=
  !(Nat.ble lo a && Nat.blt a hi)

private theorem h2sl_lsPlacedCompactLit_disjoint_keepExec :
    (lsPlacedCompactLit.all fun p =>
      h2sl_notInRangeNat 0x4686a0 0x468724 p.1 &&
      h2sl_notInRangeNat 0x469000 0x46f000 p.1) = true := by
  rfl_kernel

private theorem h2sl_beq_false_of_notInRange {lo hi a x : Nat}
    (hn : h2sl_notInRangeNat lo hi a = true)
    (hlo : lo ≤ x) (hhi : x < hi) :
    (!Nat.beq a x) = true := by
  cases hbeq : Nat.beq a x with
  | false => rfl
  | true =>
    have heq : a = x := Nat.beq_eq.mp hbeq
    subst heq
    unfold h2sl_notInRangeNat at hn
    rw [Nat.ble_eq.mpr hlo, Nat.blt_eq.mpr hhi] at hn
    cases hn

/-- Every `pc` with `h2sl_keepExec pc = true` (`[0x4686a0, 0x468724) ∪ [0x469000, 0x46f000)`) has `externAt? pc = none` in `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`. -/
theorem h2sl_realW_noExtern_keepExec
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (pc : BitVec 64)
    (hk : h2sl_keepExec pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  have hall : (lsPlacedCompactLit.all fun p => (!Nat.beq p.1 pc.toNat)) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hd := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp h2sl_lsPlacedCompactLit_disjoint_keepExec p hp)
    unfold h2sl_keepExec at hk
    rw [decide_eq_true_eq] at hk
    rcases hk with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact h2sl_beq_false_of_notInRange hd.1 hlo hhi
    · exact h2sl_beq_false_of_notInRange hd.2 hlo hhi
  rw [h2sl_realW_externAt_eq_compact hLs mmpl W pc,
    h2sl_lookupAddrTagNat_none_of_all_ne lsPlacedCompactLit pc.toNat hall]
  rfl

/-- Every `pc` with `hole2_keepSub pc = true` (`[0x469000, 0x46f000)`) has `externAt? pc = none` in `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`. -/
theorem h2sl_realW_noExtern_keepSub
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (pc : BitVec 64)
    (hk : hole2_keepSub pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  h2sl_realW_noExtern_keepExec hLs mmpl W pc (h2sl_keepSub_imp_keepExec hk)

/-! ## Symbol Pins and `hole2_strCloneProg` Extern Lookups -/

private noncomputable def h2sl_memcpyIdx : Nat :=
  lsInternedMultiLib.names.idxOf "memcpy"

private theorem h2sl_memcpy_pin_ok :
    (Nat.blt h2sl_memcpyIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD h2sl_memcpyIdx "" == "memcpy") &&
     (Obj.Interned.lookupBlockSymId h2sl_memcpyIdx lsInternedMultiLib.blocks == none) &&
     (f3LsSymAddrs.getD h2sl_memcpyIdx 0#64 == 0x469650#64)) = true := by
  rfl_kernel

private theorem h2sl_handleError_addr_ok :
    f3LsSymAddrs.getD f3HandleErrorIdx 0#64 = 0x468964#64 := by
  rfl_kernel

private theorem h2sl_handleError_tag_ok :
    h2sl_lookupAddrTagNat lsPlacedCompactLit 0x468964 = some 0 := by
  rfl_kernel

private theorem h2sl_blk623_lt_ok : Nat.blt 623 f3LsBlocksLen = true := by
  rfl_kernel

private theorem h2sl_blk623_base_ok : f3LsBlockBases.getD 623 0#64 = 0x4686a0#64 := by
  rfl_kernel

private theorem h2sl_blk623_len_ok :
    (libsignalSessionLib.blockLib 623).text.code.length = 132 := by
  rfl_kernel

private theorem h2sl_f3LsMpl_rho_of_idx {s : String} {idx : Nat}
    (hidx : lsInternedMultiLib.names.idxOf s = idx) :
    f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
  have h : f3LsMpl.ρ s =
      f3LsSymAddrs.getD (lsInternedMultiLib.names.idxOf s) 0#64 := rfl
  rw [h, hidx]

theorem h2sl_mpl_rho_memcpy {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.ρ "memcpy" = 0x469650#64 := by
  obtain ⟨_, hp, hpl, hin⟩ := hLs
  cases f3TrialElf_parse.symm.trans hp
  have hc := h2sl_memcpy_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨hlt, hnm⟩, hid⟩, haddr⟩
  have hρ := (f3CliElf_libsignal_inElf_unique hpl hin).2.2.1 _
    (h2sl_mem_lsNames_of_getD hlt hnm)
    (h2sl_lookupBlockSym_none_of_idx hlt hnm hid)
  exact hρ.trans ((h2sl_f3LsMpl_rho_of_idx rfl).trans haddr)

theorem h2sl_mpl_rho_handleError {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = 0x468964#64 := by
  have hρ := f3CliElf_rho_handleError_eq_of_linkedAt hLs
  have hp := f3HandleError_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hp
  rcases hp with ⟨⟨hlt, hnm⟩, _⟩
  have hidx : lsInternedMultiLib.names.idxOf f3HandleErrorSym = f3HandleErrorIdx := by
    rw [← hnm]
    exact Obj.Interned.idxOf_getD ls_names_nodup hlt
  exact hρ.trans ((h2sl_f3LsMpl_rho_of_idx hidx).trans h2sl_handleError_addr_ok)

theorem h2sl_mpl_base623 {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.base 623 = 0x4686a0#64 ∧
      (libsignalSessionLib.blockProgram mpl 623).code.length = 132 := by
  obtain ⟨_, hp, hpl, hin⟩ := hLs
  cases f3TrialElf_parse.symm.trans hp
  have h623_lt : 623 < f3LsBlocksLen := Nat.blt_eq.mp h2sl_blk623_lt_ok
  have hlen_ls : libsignalSessionLib.blocks.length = f3LsBlocksLen :=
    Nat.beq_eq.mp libsignalBlocks_len
  have h623 : 623 < libsignalSessionLib.blocks.length := by omega
  have hb := (f3CliElf_libsignal_inElf_unique hpl hin).1 623 h623
  have hb0 : f3LsMpl.base 623 = f3LsBlockBases.getD 623 0#64 := rfl
  have hlen_prog : (libsignalSessionLib.blockProgram mpl 623).code.length = 132 := by
    simp only [MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
      libsignalSessionLib.blockLib_text h623]
    rw [Obj.CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok 623 h623).len_aligned]
    rw [← libsignalSessionLib.blockLib_text h623]
    exact h2sl_blk623_len_ok
  exact ⟨hb.trans (hb0.trans h2sl_blk623_base_ok), hlen_prog⟩

theorem h2sl_realW_externAt_handleError
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (mpl.ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Arm64.Rust.panicked := by
  rw [h2sl_mpl_rho_handleError hLs,
    h2sl_realW_externAt_eq_compact hLs mmpl W 0x468964#64]
  change (h2sl_lookupAddrTagNat lsPlacedCompactLit 0x468964).map
    (h2sl_evalCliTagRaw mmpl W) = some Arm64.Rust.panicked
  rw [h2sl_handleError_tag_ok]
  rfl

end RawCompactTagTable

/-! ## `CodeLoaded` Equivalences, Dehooked Stubs, and `Steps` Lift Corollaries -/

/-- Every extern stub in `hole2_strCloneProg mpl` resolves to the same hook in `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (vacuously, since `hole2_strCloneProg` has `stubs := []` on the stock link). -/
theorem h2sl_strCloneProg_externAt_sub_realW
    {mpl : MultiPlacement}
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks)
    (pc : BitVec 64) (f : State → State)
    (he : (hole2_strCloneProg mpl).externAt? pc = some f) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f := by
  cases he

private theorem h2sl_mkProg_code (b : BitVec 64) (c : List (BitVec 8)) (sv : State → State) :
    ({ base := b, code := c, svc := sv : Program }).code = c := rfl

/-- `CodeLoaded` on `hole2_str1Prog mpl` (`132` bytes in `[0x4686a0, 0x468724)`) agrees between `stripExecOutside h2sl_keepExec` and `stripExecOutside hole2_keep`. -/
theorem h2sl_str1Prog_codeLoaded_keepExec_iff_keep
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (m : Memory) :
    (hole2_str1Prog mpl).CodeLoaded (stripExecOutside h2sl_keepExec m) ↔
      (hole2_str1Prog mpl).CodeLoaded (stripExecOutside hole2_keep m) := by
  obtain ⟨hb, hlen623⟩ := h2sl_mpl_base623 hLs
  have hbase : (hole2_str1Prog mpl).base = 0x4686a0#64 := hb
  have hlen : (hole2_str1Prog mpl).code.length = 132 := by
    unfold hole2_str1Prog
    rw [h2sl_mkProg_code]
    exact hlen623
  rw [Program.codeLoaded_iff, Program.codeLoaded_iff]
  constructor <;> rintro ⟨hal, hfit, hbytes⟩ <;> refine ⟨hal, hfit, fun i hi => ?_⟩
  · obtain ⟨hr, hp, hlz⟩ := hbytes i hi
    have hi132 : i < 132 := by rwa [hlen] at hi
    have hk_exec : h2sl_keepExec ((hole2_str1Prog mpl).base + BitVec.ofNat 64 i) = true := by
      rw [hbase]; unfold h2sl_keepExec; rw [decide_eq_true_eq]; left; bv_omega
    have hk_keep : hole2_keep ((hole2_str1Prog mpl).base + BitVec.ofNat 64 i) = true :=
      h2sl_keepExec_imp_keep hk_exec
    rw [strip_read8] at hr ⊢
    rw [strip_isLazyFree] at hlz ⊢
    rw [strip_perm, hk_exec] at hp
    rw [strip_perm, hk_keep]
    exact ⟨hr, hp, hlz⟩
  · obtain ⟨hr, hp, hlz⟩ := hbytes i hi
    have hi132 : i < 132 := by rwa [hlen] at hi
    have hk_exec : h2sl_keepExec ((hole2_str1Prog mpl).base + BitVec.ofNat 64 i) = true := by
      rw [hbase]; unfold h2sl_keepExec; rw [decide_eq_true_eq]; left; bv_omega
    have hk_keep : hole2_keep ((hole2_str1Prog mpl).base + BitVec.ofNat 64 i) = true :=
      h2sl_keepExec_imp_keep hk_exec
    rw [strip_read8] at hr ⊢
    rw [strip_isLazyFree] at hlz ⊢
    rw [strip_perm, hk_keep] at hp
    rw [strip_perm, hk_exec]
    exact ⟨hr, hp, hlz⟩

/-- `CodeLoaded` on `f3TrialRxProg` (`24,576` bytes in `[0x469000, 0x46f000)`) agrees between `stripExecOutside h2sl_keepExec` and `stripExecOutside hole2_keep`. -/
theorem h2sl_rxProg_codeLoaded_keepExec_iff_keep (m : Memory) :
    f3TrialRxProg.CodeLoaded (stripExecOutside h2sl_keepExec m) ↔
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep m) := by
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hbase : f3TrialRxProg.base = 0x469000#64 := f3TrialRxProg_base
  rw [Program.codeLoaded_iff, Program.codeLoaded_iff]
  constructor <;> rintro ⟨hal, hfit, hbytes⟩ <;> refine ⟨hal, hfit, fun i hi => ?_⟩
  · obtain ⟨hr, hp, hlz⟩ := hbytes i hi
    have hi_lt : i < 24576 := by rw [hlen] at hi; exact hi
    have hk_exec : h2sl_keepExec (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
      rw [hbase]; unfold h2sl_keepExec; rw [decide_eq_true_eq]; right; bv_omega
    have hk_keep : hole2_keep (f3TrialRxProg.base + BitVec.ofNat 64 i) = true :=
      h2sl_keepExec_imp_keep hk_exec
    rw [strip_read8] at hr ⊢
    rw [strip_isLazyFree] at hlz ⊢
    rw [strip_perm, hk_exec] at hp
    rw [strip_perm, hk_keep]
    exact ⟨hr, hp, hlz⟩
  · obtain ⟨hr, hp, hlz⟩ := hbytes i hi
    have hi_lt : i < 24576 := by rw [hlen] at hi; exact hi
    have hk_exec : h2sl_keepExec (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
      rw [hbase]; unfold h2sl_keepExec; rw [decide_eq_true_eq]; right; bv_omega
    have hk_keep : hole2_keep (f3TrialRxProg.base + BitVec.ofNat 64 i) = true :=
      h2sl_keepExec_imp_keep hk_exec
    rw [strip_read8] at hr ⊢
    rw [strip_isLazyFree] at hlz ⊢
    rw [strip_perm, hk_keep] at hp
    rw [strip_perm, hk_exec]
    exact ⟨hr, hp, hlz⟩

/-- Every symbol in `cliDehookedSymsPlaced` has `externAt? = none` at both `mpl.ρ sym` and
`targetVa`, with `DirectOrBranchStub cliElfImage (mpl.ρ sym) targetVa`. -/
theorem h2sl_realW_dehooked_witness
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {sym : String} (hsym : sym ∈ cliDehookedSymsPlaced) :
    (∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? (mpl.ρ sym) = none) ∧
    ∃ targetVa : BitVec 64,
      Obj.lookupUnique sym cliElfImage.symbols = some targetVa ∧
      DirectOrBranchStub cliElfImage (mpl.ρ sym) targetVa ∧
      ∀ W : CliHooks,
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? targetVa = none := by
  obtain ⟨_, hp, hpl, hin⟩ := hLs
  cases f3TrialElf_parse.symm.trans hp
  obtain ⟨hstub_sig, targetVa, hlu, hdir, htgt_sig⟩ :=
    f3CliElf_dehooked_witness_of_inElf (mmpl := mmpl) hpl hin hsym
  refine ⟨fun W => ?_, targetVa, hlu, hdir, fun W => ?_⟩
  · exact externAt?_cliProgExtPlacedSigAt_eq_none.mp (hstub_sig W)
  · exact externAt?_cliProgExtPlacedSigAt_eq_none.mp (htgt_sig W)

/-- Lifts `Steps` to `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` when visited PCs stay in `hole2_keepSub`. -/
theorem h2sl_steps_realW_of_visitedIn_keepSub
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks)
    {s sf : State}
    (hvis : h2fsgen_StepsVisitedIn hole2_keepSub hole2_emptyProg s sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf :=
  h2fsgen_steps_lift_of_visitedIn_noExtern
    (P1 := hole2_emptyProg)
    (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
    (h2sl_emptyProg_svc.trans (h2sl_realW_svc mpl mmpl W).symm)
    (fun pc _ => h2sl_emptyProg_externAt pc)
    (h2sl_realW_noExtern_keepSub hLs mmpl W)
    hvis

/-- Lifts `Steps` to `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` when visited PCs stay in `h2sl_keepExec`. -/
theorem h2sl_steps_realW_of_visitedIn_keepExec
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks)
    {s sf : State}
    (hvis : h2fsgen_StepsVisitedIn h2sl_keepExec hole2_emptyProg s sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf :=
  h2fsgen_steps_lift_of_visitedIn_noExtern
    (P1 := hole2_emptyProg)
    (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
    (h2sl_emptyProg_svc.trans (h2sl_realW_svc mpl mmpl W).symm)
    (fun pc _ => h2sl_emptyProg_externAt pc)
    (h2sl_realW_noExtern_keepExec hLs mmpl W)
    hvis

/-! ## Stock-Clean Per-Address `HooksUnfetchedPerPc` and `StepsUntil` Lifts -/

/-- Per-address stock-clean replacement for `h2sl_realW_hooksUnfetched` on `hole2_keepSub` and
    `hole2_emptyProg`: requires zero `F3CodeInv` and zero `[0, 0, 0, 0]` stub checks. -/
theorem h2sl_realW_hooksUnfetchedPerPc_keepSub
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (m : Memory) :
    HooksUnfetchedPerPc hole2_keepSub hole2_emptyProg
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) m :=
  hooksUnfetchedPerPc_of_noNewExternOn m fun pc hD _ =>
    h2sl_realW_noExtern_keepSub hLs mmpl W pc hD

/-- Per-address stock-clean replacement for `h2sl_realW_hooksUnfetched` on `h2sl_keepExec` and
    `hole2_emptyProg`: requires zero `F3CodeInv` and zero `[0, 0, 0, 0]` stub checks. -/
theorem h2sl_realW_hooksUnfetchedPerPc_keepExec
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (m : Memory) :
    HooksUnfetchedPerPc h2sl_keepExec hole2_emptyProg
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) m :=
  hooksUnfetchedPerPc_of_noNewExternOn m fun pc hD _ =>
    h2sl_realW_noExtern_keepExec hLs mmpl W pc hD

/-- Per-address `HooksUnfetchedPerPc` for `hole2_strCloneProg mpl` on `h2sl_keepExec`
    (zero `F3CodeInv`, zero `[0, 0, 0, 0]` stub check). -/
theorem h2sl_realW_hooksUnfetchedPerPc_strClone
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (m : Memory) :
    HooksUnfetchedPerPc h2sl_keepExec (hole2_strCloneProg mpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) m :=
  hooksUnfetchedPerPc_of_noNewExternOn m fun pc hD _ =>
    h2sl_realW_noExtern_keepExec hLs mmpl W pc hD

/-- Generic per-address `HooksUnfetchedPerPc` for `hole2_strCloneProg mpl` on any domain `D`
    where every `P_real_W`-hooked `pc` either lies outside `D` or is already hooked in
    `hole2_strCloneProg mpl` (Clause C1/C2, zero address literals). -/
theorem h2sl_realW_hooksUnfetchedPerPc_strClone_on
    {D : BitVec 64 → Bool} {mpl mmpl : MultiPlacement}
    (W : CliHooks) (m : Memory)
    (hper : ∀ pc : BitVec 64,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc ≠ none →
        D pc = false ∨ (hole2_strCloneProg mpl).externAt? pc ≠ none) :
    HooksUnfetchedPerPc D (hole2_strCloneProg mpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) m :=
  hooksUnfetchedPerPc_of_perPc fun pc hne =>
    match hper pc hne with
    | Or.inl hDf => Or.inl hDf
    | Or.inr hP1 => Or.inr (Or.inl hP1)

/-- Lifts first-stop `StepsUntil` from `hole2_emptyProg` to `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` via `h2fsgen_StepsVisitedIn hole2_keepSub` (stock-clean per-address). -/
theorem h2sl_stepsUntil_emptyProg_to_realW_perPc
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks)
    {u sf : State} {entryTarget : BitVec 64}
    (hvis : h2fsgen_StepsVisitedIn hole2_keepSub hole2_emptyProg (u.setPC entryTarget) sf)
    (_hstop : SubroutineStop u sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (u.setPC entryTarget) sf :=
  h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W hvis

/-- Lifts first-stop `StepsUntil` from `hole2_emptyProg` to `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` via the standard universal `(R)` quantifier `hAllP` (stock-clean). -/
theorem h2sl_stepsUntil_emptyProg_to_realW_of_allProg
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks)
    {u sf : State} {entryTarget : BitVec 64}
    (hAllP : ∀ (Q : Program), Q.svc = Syscall.standard →
      (∀ pc : BitVec 64, hole2_keepSub pc = true → Q.externAt? pc = none) →
      ∃ sf' : State, StepsUntil Q (SubroutineStop u) (u.setPC entryTarget) sf' ∧
        SubroutineStop u sf')
    (huntil : StepsUntil hole2_emptyProg (SubroutineStop u) (u.setPC entryTarget) sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (u.setPC entryTarget) sf :=
  h2sl_steps_realW_of_visitedIn_keepSub hLs mmpl W
    (stepsVisitedIn_of_allProg
      (fun pc _ => h2sl_emptyProg_externAt pc)
      (fun Q hsvc hno => hAllP Q (hsvc.trans h2sl_emptyProg_svc) hno)
      huntil)

/-- Lifts first-stop `StepsUntil` from `hole2_strCloneProg mpl` to `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` on any domain `D` satisfying `HooksUnfetchedPerPc` (stock-clean). -/
theorem h2sl_stepsUntil_strClone_to_realW_perPc
    {D : BitVec 64 → Bool}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks)
    {u sa sf : State}
    (hunf : HooksUnfetchedPerPc D (hole2_strCloneProg mpl)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u.mem)
    (hkf : u.mem.KeepsFrozen sa.mem)
    (hvis : h2fsgen_StepsVisitedIn D (hole2_strCloneProg mpl) sa sf)
    (hstop : SubroutineStop u sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) sa sf :=
  stepsUntil_strClone_to_realW_perPc W
    (h2sl_strCloneProg_svc mpl)
    (fun pc f _ he => h2sl_strCloneProg_externAt_sub_realW hLs mmpl W pc f he)
    hunf hkf hvis hstop

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
