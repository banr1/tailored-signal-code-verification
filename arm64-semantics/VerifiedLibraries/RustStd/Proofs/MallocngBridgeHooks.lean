/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# `MultiCodeROHook`-Backed Rust Allocator Hooks for `mallocng`

Lifts `VerifiedLibraries.mallocngLib.codeROSubroutineHook` under `Syscall.standard` to
`HookOk` contracts for the C allocator entry points (`malloc`, `free`, `realloc`,
`aligned_alloc`, `posix_memalign`) and constructs the Rust global-allocator hooks
(`mallocngRustAllocHook`, `mallocngRustDeallocHook`, `mallocngRustReallocHook`,
`mallocngRustCliHookMap`) satisfying `RustStdAllocHooks`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `mallocngCHook` and Hook State Transport -/

/-- Subroutine hook running `fnName` of `VerifiedLibraries.mallocngLib` at multi-placement `mpl`
    under `Syscall.standard`. -/
noncomputable def mallocngCHook (mpl : Obj.MultiPlacement) (fnName : String) : State → State :=
  VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl fnName
    (fun _ => none) (fun _ => none) Syscall.standard

/-- Combined `mallocngRustCliHookAllocOf` pool and `StdErrnoCell` predicate at state `s`. -/
def mallocngCHookPool (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (s : State) : SepProp :=
  (mallocngRustCliHookAllocOf J hIf γ mpl).pool 0 0 s ∗ StdErrnoCell s.tpidrEl0

private theorem allocCallPreserved_hookExit {mpl : Obj.MultiPlacement} {i : Nat}
    {fnAddr : BitVec 64} {s0 sf' : State}
    (h : MallocngProcPreserved
      (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i fnAddr s0) sf') :
    AllocCallPreserved s0 (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') := by
  have hp := allocCallPreserved_of_mallocngProcPreserved h
  rcases hp with ⟨hfs, htr, hsig, htp, hbs, horc, hsym⟩
  simp only [AllocCallPreserved, multiCodeROHookEntry_fs, multiCodeROHookEntry_trace,
    multiCodeROHookEntry_sigActions, multiCodeROHookEntry_tpidrEl0,
    multiCodeROHookEntry_brkStart, multiCodeROHookEntry_oracle, multiCodeROHookEntry_symtab,
    multiCodeROHookExit_fs, multiCodeROHookExit_trace, multiCodeROHookExit_sigActions,
    multiCodeROHookExit_tpidrEl0, multiCodeROHookExit_brkStart, multiCodeROHookExit_oracle,
    multiCodeROHookExit_symtab] at hfs htr hsig htp hbs horc hsym ⊢
  exact ⟨hfs, htr, hsig, htp, hbs, horc, hsym⟩

private theorem oomPreserved_hookExit {svc : State → State} {req peak : Nat}
    {mpl : Obj.MultiPlacement} {i : Nat} {fnAddr : BitVec 64} {s0 sf' : State}
    (h : MallocngOomCond svc req peak
      (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i fnAddr s0) sf') :
    OomPreserved s0 (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') := by
  rcases oomCond_imp_preserved h with ⟨hfs, htr, hsig⟩
  simp only [OomPreserved, multiCodeROHookEntry_fs, multiCodeROHookEntry_trace,
    multiCodeROHookEntry_sigActions, multiCodeROHookExit_fs, multiCodeROHookExit_trace,
    multiCodeROHookExit_sigActions] at hfs htr hsig ⊢
  exact ⟨hfs, htr, hsig⟩

private theorem cHookPool_entails_codeRO_env {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (i : Nat) (fnAddr : BitVec 64) (s0 : State) :
    mallocngCHookPool J hIf γ mpl s0 ⊢
      ∃∗ b : MallocngBudget, ∃∗ ivs0 : List (BitVec 64 × Nat),
        VerifiedLibraries.mallocngLib.codeRO mpl ∗
          MallocngEnv J γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart b ivs0
            (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i fnAddr s0) := by
  unfold mallocngCHookPool mallocngRustCliHookAllocOf
  rw [mallocngRustCliPoolWithOf_sep_stdErrnoCell_eq hIf (VerifiedLibraries.mallocngLib.codeRO mpl)
      γ (mallocngAddrsOfPlacement mpl) 0 0 s0]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun b => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun ivs0 => ?_
  rw [sepConj_comm _ (VerifiedLibraries.mallocngLib.codeRO mpl)]
  refine sepConj_mono_right ?_
  unfold MallocngEnv
  simp only [multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart,
    multiCodeROHookEntry_brk]
  exact Entails.pure_right ⟨trivial, trivial⟩ (Entails.refl _)

private theorem codeRO_postEnv_entails_cHookPool {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (bf : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) {i : Nat} {fnAddr : BitVec 64} {s0 sf' : State}
    (hproc : MallocngProcPreserved
      (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i fnAddr s0) sf') :
    VerifiedLibraries.mallocngLib.codeRO mpl ∗
      MallocngPostEnv J γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart bf ivs0
        (multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i fnAddr s0) sf' ⊢
      mallocngCHookPool J hIf γ mpl
        (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf') := by
  let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
  have hpool_eq :
      (mallocngRustCliHookAllocOf J hIf γ mpl).pool 0 0 sf =
        (mallocngRustCliHookAllocOf J hIf γ mpl).pool 0 0 sf' :=
    (mallocngRustCliHookAllocOf J hIf γ mpl).pool_transport 0 0 sf' sf
      ⟨multiCodeROHookExit_brkStart _ _ _ _ _, multiCodeROHookExit_brk _ _ _ _ _,
       multiCodeROHookExit_tpidrEl0 _ _ _ _ _⟩
  have htp_sf : sf.tpidrEl0 = s0.tpidrEl0 := by
    have h1 := hproc.2.2.1; rw [multiCodeROHookEntry_tpidrEl0] at h1
    dsimp only [sf]; rwa [multiCodeROHookExit_tpidrEl0]
  unfold mallocngCHookPool
  rw [hpool_eq, htp_sf, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      sepConj_comm ((mallocngRustCliHookAllocOf J hIf γ mpl).pool 0 0 sf')]
  exact postEnv_withExtra_entails_errno_pool hIf (VerifiedLibraries.mallocngLib.codeRO mpl)
    γ (mallocngAddrsOfPlacement mpl) bf ivs0 0 0 s0 _ sf'

private theorem pull_pure_from_codeRO {P Q : SepProp} {φ : Prop} :
    P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) := by ac_rfl

private theorem preEnv_pull_pure {C E I S : SepProp} {φ : Prop} :
    (C ∗ E) ∗ ((⌜φ⌝ ∗ I) ∗ S) = ⌜φ⌝ ∗ (C ∗ (I ∗ E ∗ S)) := by ac_rfl

private theorem postEnv_reord {C B E S P' B' : SepProp}
    (hpool : C ∗ E ⊢ P') (hblk : B ⊢ B') : C ∗ (B ∗ E ∗ S) ⊢ P' ∗ S ∗ B' :=
  Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono hpool (sepConj_mono_right hblk))

private theorem postEnv_reord2 {C B1 B2 E S P' B' : SepProp}
    (hpool : C ∗ E ⊢ P') (hblk : B1 ∗ B2 ⊢ B') : C ∗ (B1 ∗ B2 ∗ E ∗ S) ⊢ P' ∗ S ∗ B' :=
  Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono hpool (sepConj_mono_right hblk))

private theorem optOwn_mallocngBlock_entails {J : MallocngIface} {γ : GhostName}
    {ret : BitVec 64} {ok : Bool} {sz al : Nat}
    (hwf : (OptOwn (MallocngBlock J γ)).pureWf ret (if ok then some (sz, al) else none)) :
    (OptOwn (MallocngBlock J γ)).interp ret (if ok then some (sz, al) else none) ⊢
      (if ok then ⌜ret ≠ 0#64 ∧ al ∣ ret.toNat ∧ ret.toNat + sz < 2 ^ 64⌝ ∗
        J.Block γ ret sz ∗ memRegion ret sz else ⌜ret = 0#64⌝) := by
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, OptOwn_interp_none]; exact Entails.refl _
  · simp only [↓reduceIte, OptOwn_interp_some] at hwf ⊢
    exact Entails.pure_right hwf.2 (Entails.refl _)

/-! ## C Allocator `HookOk` Contracts -/

/-- `HookOk` contract for `mallocngCHook mpl "malloc"` over `mallocngCHookPool`. -/
def cMallocHookSpec (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) : Spec (BitVec 64) where
  pre := fun req s0 =>
    ⌜s0.readReg64 .x0 = req⌝ ∗
      mallocngCHookPool J hIf γ mpl s0 ∗ stackFrameAt s0.sp mallocngStackBytes
  post := fun req s0 sf =>
    let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
    let ret := sf.readReg64 .x0
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngCHookPool J hIf γ mpl sf ∗ stackFrameAt s0.sp mallocngStackBytes ∗
      (if ok then
        ⌜ret ≠ 0#64 ∧ 16 ∣ ret.toNat ∧ ret.toNat + req.toNat < 2 ^ 64⌝ ∗
          J.Block γ ret req.toNat ∗ memRegion ret req.toNat
       else ⌜ret = 0#64⌝)
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

theorem cMalloc_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngCHook mpl "malloc") (cMallocHookSpec J hIf γ mpl) := by
  obtain ⟨_, i, off, hlook, hsub⟩ := hEntries.malloc_ok γ
  refine subroutineHook_ok_of_multiCodeRO_at
    (Q := fun _ _ _ => emp)
    (φ := fun req (req', sp', tp', brkStart', _, _) s0 =>
      req' = req ∧ sp' = s0.sp ∧ tp' = s0.tpidrEl0 ∧ brkStart' = s0.brkStart)
    hPl hlook hsub ?_ ?_ (Or.inl rfl)
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
  · intro req s0
    dsimp only [cMallocHookSpec]
    refine Entails.pure_left fun hx0 => ?_
    refine Entails.trans (sepConj_mono_left
      (cHookPool_entails_codeRO_env hIf γ mpl i
        (VerifiedLibraries.mallocngLib.fnAddr mpl "malloc") s0)) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun b => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ivs0 => ?_
    refine Entails.sepExists_right (req, s0.sp, s0.tpidrEl0, s0.brkStart, b, ivs0) ?_
    refine Entails.pure_right ⟨rfl, rfl, rfl, rfl⟩ ?_
    dsimp only [ToBaseSpec.toSpec, mallocngMallocSpec]
    simp only [ctype_simp, multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0,
      multiCodeROHookEntry_sp, hx0, eq_self, and_self, pure_true_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  · rintro req ⟨req', sp', tp', brkStart', b, ivs0⟩ s0 sf' ⟨hreq', hsp', htp', hbrk'⟩ _ _ _
    subst req' sp' tp' brkStart'
    dsimp only [ToBaseSpec.toSpec, mallocngMallocSpec, cMallocHookSpec]
    rw [sepConj_emp, pull_pure_from_codeRO]
    refine Entails.pure_left fun ⟨hwf, hacc⟩ => ?_
    have hpool := codeRO_postEnv_entails_cHookPool hIf γ mpl
      (mallocngAllocBudget (decide (req.toNat ≤ MallocngMaxAllocSize)) req.toNat b) ivs0 hacc.1
    rw [multiCodeROHookExit_readReg64 _ _ _ _ _ .x0]
    exact Entails.pure_right (allocCallPreserved_hookExit hacc.1)
      (postEnv_reord hpool (optOwn_mallocngBlock_entails hwf))
  · rintro _ _ s0 sf' _ _ _
    left; dsimp only [ToBaseSpec.toSpec, mallocngMallocSpec, cMallocHookSpec]
    exact Entails.pure_mono oomPreserved_hookExit

/-- `HookOk` contract for `mallocngCHook mpl "free"` (`onOom = ⌜False⌝`). -/
def cFreeHookSpec (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) : Spec (BitVec 64 × Nat) where
  pre := fun (ptr, sz) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗
      mallocngCHookPool J hIf γ mpl s0 ∗
      (if ptr = 0#64 then emp else J.Block γ ptr sz ∗ memRegion ptr sz) ∗
      stackFrameAt s0.sp mallocngStackBytes
  post := fun _ s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngCHookPool J hIf γ mpl sf ∗ stackFrameAt s0.sp mallocngStackBytes

theorem cFree_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngCHook mpl "free") (cFreeHookSpec J hIf γ mpl) := by
  obtain ⟨_, i, off, hlook, hsub⟩ := hEntries.free_ok γ
  refine subroutineHook_ok_of_multiCodeRO_at
    (Q := fun _ _ _ => emp)
    (φ := fun (ptr, sz) (ptr', sp', nEff, tp', brkStart', _, _) s0 =>
      ptr' = ptr ∧ sp' = s0.sp ∧ nEff = (if ptr = 0#64 then 0 else sz) ∧
        tp' = s0.tpidrEl0 ∧ brkStart' = s0.brkStart)
    hPl hlook hsub ?_ ?_ (Or.inl rfl)
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
  · rintro ⟨ptr, sz⟩ s0
    dsimp only [cFreeHookSpec]
    refine Entails.pure_left fun hx0 => ?_
    let nEff : Nat := if ptr = 0#64 then 0 else sz
    have hblk_ent :
        (if ptr = 0#64 then emp else J.Block γ ptr sz ∗ memRegion ptr sz) ⊢
          ⌜(MallocngFreeableBlock J γ).pureWf ptr nEff⌝ ∗
            (MallocngFreeableBlock J γ).interp ptr nEff := by
      by_cases hp0 : ptr = 0#64
      · subst hp0; simp only [nEff, ↓reduceIte]; exact Entails.pure_right trivial (Entails.refl _)
      · simp only [nEff, hp0, ↓reduceIte]
        refine Entails.trans (sepConj_mono_left (hIf.block_nonnull γ ptr sz)) ?_
        rw [sepConj_assoc]
        refine Entails.pure_left fun ⟨_, h16, hbnd48, _⟩ =>
          Entails.pure_right ⟨h16, Nat.lt_of_le_of_lt hbnd48 (by decide)⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left
      (cHookPool_entails_codeRO_env hIf γ mpl i
        (VerifiedLibraries.mallocngLib.fnAddr mpl "free") s0)) ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun b => ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun ivs0 => ?_
    refine Entails.sepExists_right (ptr, s0.sp, nEff, s0.tpidrEl0, s0.brkStart, b, ivs0)
      (Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl⟩ ?_)
    dsimp only [ToBaseSpec.toSpec, mallocngFreeSpec]
    simp only [multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0,
      multiCodeROHookEntry_sp, hx0, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hblk_ent)) ?_
    rw [preEnv_pull_pure]
    exact Entails.pure_left fun hwf =>
      sepConj_mono_right (Entails.pure_right ⟨trivial, trivial, hwf⟩ (Entails.refl _))
  · rintro ⟨ptr, sz⟩ ⟨ptr', sp', nEff, tp', brkStart', b, ivs0⟩ s0 sf'
      ⟨hptr', hsp', _, htp', hbrk'⟩ _ _ _
    subst ptr' sp' tp' brkStart'
    dsimp only [ToBaseSpec.toSpec, mallocngFreeSpec, cFreeHookSpec]
    rw [sepConj_emp, pull_pure_from_codeRO]
    refine Entails.pure_left fun hacc => ?_
    have hpool := codeRO_postEnv_entails_cHookPool hIf γ mpl
      (mallocngFreeBudget (ptr == 0#64) nEff b) ivs0 hacc.1
    refine Entails.pure_right (allocCallPreserved_hookExit hacc.1) ?_
    rw [← sepConj_assoc]; exact sepConj_mono_left hpool
  · rintro _ _ _ _ _ _ _; left
    dsimp only [ToBaseSpec.toSpec, mallocngFreeSpec, cFreeHookSpec]; exact Entails.refl _

/-- `HookOk` contract for `mallocngCHook mpl "aligned_alloc"` under `align.toNat ≤ MaxAlignedAllocAlign`. -/
def cAlignedAllocHookSpec (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (align, len) s0 =>
    ⌜s0.readReg64 .x0 = align ∧ s0.readReg64 .x1 = len ∧
      align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
      mallocngCHookPool J hIf γ mpl s0 ∗ stackFrameAt s0.sp mallocngStackBytes
  post := fun (align, len) s0 sf =>
    let ok := mallocngAlignedAllocOk align len
    let ret := sf.readReg64 .x0
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngCHookPool J hIf γ mpl sf ∗ stackFrameAt s0.sp mallocngStackBytes ∗
      (if ok then
        ⌜ret ≠ 0#64 ∧ max align.toNat 16 ∣ ret.toNat ∧ ret.toNat + len.toNat < 2 ^ 64⌝ ∗
          J.Block γ ret len.toNat ∗ memRegion ret len.toNat
       else ⌜ret = 0#64⌝)
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

theorem cAlignedAlloc_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngCHook mpl "aligned_alloc") (cAlignedAllocHookSpec J hIf γ mpl) := by
  obtain ⟨_, i, off, hlook, hsub⟩ := hEntries.alignedAlloc_ok γ
  refine subroutineHook_ok_of_multiCodeRO_at
    (Q := fun _ _ _ => emp)
    (φ := fun (align, len) (align', len', sp', tp', brkStart', _, _) s0 =>
      align' = align ∧ len' = len ∧ sp' = s0.sp ∧
        tp' = s0.tpidrEl0 ∧ brkStart' = s0.brkStart)
    hPl hlook hsub ?_ ?_ (Or.inl rfl)
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
  · rintro ⟨align, len⟩ s0
    dsimp only [cAlignedAllocHookSpec]
    refine Entails.pure_left fun ⟨hx0, hx1, hAlMax⟩ => ?_
    refine Entails.trans (sepConj_mono_left
      (cHookPool_entails_codeRO_env hIf γ mpl i
        (VerifiedLibraries.mallocngLib.fnAddr mpl "aligned_alloc") s0)) ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun b => ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun ivs0 => ?_
    refine Entails.sepExists_right (align, len, s0.sp, s0.tpidrEl0, s0.brkStart, b, ivs0)
      (Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl⟩ ?_)
    dsimp only [ToBaseSpec.toSpec, mallocngAlignedAllocSpec]
    simp only [ctype_simp, multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0,
      multiCodeROHookEntry_readReg64 _ _ _ _ _ .x1,
      multiCodeROHookEntry_sp, hx0, hx1, eq_self, true_and, sepConj_emp]
    rw [sepConj_assoc]
    exact sepConj_mono_right (Entails.pure_right hAlMax (Entails.refl _))
  · rintro ⟨align, len⟩ ⟨align', len', sp', tp', brkStart', b, ivs0⟩ s0 sf'
      ⟨hal', hlen', hsp', htp', hbrk'⟩ _ _ _
    subst align' len' sp' tp' brkStart'
    dsimp only [ToBaseSpec.toSpec, mallocngAlignedAllocSpec, cAlignedAllocHookSpec]
    rw [sepConj_emp, pull_pure_from_codeRO]
    refine Entails.pure_left fun ⟨hwf, hacc⟩ => ?_
    have hpool := codeRO_postEnv_entails_cHookPool hIf γ mpl
      (mallocngAlignedBudget (mallocngAlignedAllocOk align len) align.toNat len.toNat b) ivs0 hacc.1
    rw [multiCodeROHookExit_readReg64 _ _ _ _ _ .x0]
    exact Entails.pure_right (allocCallPreserved_hookExit hacc.1)
      (postEnv_reord hpool (optOwn_mallocngBlock_entails hwf))
  · rintro _ _ s0 sf' _ _ _
    left; dsimp only [ToBaseSpec.toSpec, mallocngAlignedAllocSpec, cAlignedAllocHookSpec]
    exact Entails.pure_mono oomPreserved_hookExit

/-- Old-block ownership passed to `cReallocHookSpec`: `⌜ptr = 0#64⌝` when `oldBlk = none`, or
    `⌜bs.length ≤ oldSz⌝ ∗ J.Block γ ptr oldSz ∗ (ptr ↦ₛ bs) ∗ memRegion (ptr + bs.length) (oldSz - bs.length)`
    when `oldBlk = some (oldSz, bs)`. -/
def cReallocOld (J : MallocngIface) (γ : GhostName) (ptr : BitVec 64) :
    Option (Nat × List (BitVec 8)) → SepProp
  | none => ⌜ptr = 0#64⌝
  | some (oldSz, bs) =>
      ⌜bs.length ≤ oldSz⌝ ∗ J.Block γ ptr oldSz ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (oldSz - bs.length)

private theorem cReallocOld_to_condOwn {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    {γ : GhostName} (ptr : BitVec 64) (oldBlk : Option (Nat × List (BitVec 8))) :
    cReallocOld J γ ptr oldBlk ⊢
      ⌜(CondOwn (OptOwn (MallocngInitBlock J γ))).pureWf ptr (some oldBlk)⌝ ∗
        (CondOwn (OptOwn (MallocngInitBlock J γ))).interp ptr (some oldBlk) := by
  cases oldBlk with
  | none =>
    simp only [cReallocOld, CondOwn_pureWf_some, OptOwn_pureWf_none,
      CondOwn_interp_some, OptOwn_interp_none]
    exact Entails.pure_right trivial (Entails.refl _)
  | some pair =>
    rcases pair with ⟨oldSz, bs⟩
    simp only [cReallocOld, CondOwn_pureWf_some, OptOwn_pureWf_some,
      CondOwn_interp_some, OptOwn_interp_some]
    refine Entails.pure_left fun hle => ?_
    refine Entails.trans (sepConj_mono_left (hIf.block_nonnull γ ptr oldSz)) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpNe, h16, hbnd48, _⟩ => ?_
    exact Entails.pure_right
      ⟨hpNe, hpNe, h16, Nat.lt_of_le_of_lt hbnd48 (by decide), hle⟩
      (Entails.refl _)

/-- `HookOk` contract for `mallocngCHook mpl "realloc"`. -/
def cReallocHookSpec (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × Option (Nat × List (BitVec 8))) where
  pre := fun (ptr, newSize, oldBlk) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧ s0.readReg64 .x1 = newSize⌝ ∗
      mallocngCHookPool J hIf γ mpl s0 ∗
      cReallocOld J γ ptr oldBlk ∗
      stackFrameAt s0.sp mallocngStackBytes
  post := fun (ptr, newSize, oldBlk) s0 sf =>
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let keptBs := ((oldBlk.map Prod.snd).getD []).take newSize.toNat
    let ret := sf.readReg64 .x0
    ⌜AllocCallPreserved s0 sf⌝ ∗
      mallocngCHookPool J hIf γ mpl sf ∗ stackFrameAt s0.sp mallocngStackBytes ∗
      (if ok then
        ⌜ret ≠ 0#64 ∧ 16 ∣ ret.toNat ∧ ret.toNat + newSize.toNat < 2 ^ 64⌝ ∗
          J.Block γ ret newSize.toNat ∗ (ret ↦ₛ keptBs) ∗
          memRegion (ret + BitVec.ofNat 64 keptBs.length) (newSize.toNat - keptBs.length)
       else
        ⌜ret = 0#64⌝ ∗ cReallocOld J γ ptr oldBlk)
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

theorem cRealloc_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngCHook mpl "realloc") (cReallocHookSpec J hIf γ mpl) := by
  obtain ⟨_, i, off, hlook, hsub⟩ := hEntries.realloc_ok γ
  refine subroutineHook_ok_of_multiCodeRO_at
    (Q := fun _ _ _ => emp)
    (φ := fun (ptr, newSize, oldBlk) (ptr', newSize', sp', oldBlk', tp', brkStart', _, _) s0 =>
      ptr' = ptr ∧ newSize' = newSize ∧ sp' = s0.sp ∧ oldBlk' = oldBlk ∧
        tp' = s0.tpidrEl0 ∧ brkStart' = s0.brkStart)
    hPl hlook hsub ?_ ?_ (Or.inl rfl)
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
  · rintro ⟨ptr, newSize, oldBlk⟩ s0
    dsimp only [cReallocHookSpec]
    refine Entails.pure_left fun ⟨hx0, hx1⟩ => ?_
    refine Entails.trans (sepConj_mono_left
      (cHookPool_entails_codeRO_env hIf γ mpl i
        (VerifiedLibraries.mallocngLib.fnAddr mpl "realloc") s0)) ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun b => ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun ivs0 => ?_
    refine Entails.sepExists_right (ptr, newSize, s0.sp, oldBlk, s0.tpidrEl0, s0.brkStart, b, ivs0)
      (Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_)
    dsimp only [ToBaseSpec.toSpec, mallocngReallocSpec]
    simp only [multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0,
      multiCodeROHookEntry_readReg64 _ _ _ _ _ .x1,
      multiCodeROHookEntry_sp, hx0, hx1, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (cReallocOld_to_condOwn hIf ptr oldBlk))) ?_
    rw [preEnv_pull_pure]
    exact Entails.pure_left fun hwf =>
      sepConj_mono_right (Entails.pure_right ⟨trivial, trivial, trivial, hwf, trivial⟩ (Entails.refl _))
  · rintro ⟨ptr, newSize, oldBlk⟩ ⟨ptr', newSize', sp', oldBlk', tp', brkStart', b, ivs0⟩ s0 sf'
      ⟨hptr', hns', hsp', hold', htp', hbrk'⟩ _ _ _
    subst ptr' newSize' sp' oldBlk' tp' brkStart'
    dsimp only [ToBaseSpec.toSpec, mallocngReallocSpec, cReallocHookSpec]
    rw [sepConj_emp, pull_pure_from_codeRO]
    refine Entails.pure_left fun ⟨hwf_ptr, hwf_ret, hacc⟩ => ?_
    let keptBs := ((oldBlk.map Prod.snd).getD []).take newSize.toNat
    have hpool := codeRO_postEnv_entails_cHookPool hIf γ mpl
      (mallocngReallocBudget (decide (newSize.toNat ≤ MallocngMaxAllocSize)) oldBlk newSize.toNat b)
      ivs0 hacc.1
    rw [multiCodeROHookExit_readReg64 _ _ _ _ _ .x0]
    have hblk :
        (CondOwn (OptOwn (MallocngInitBlock J γ))).interp ptr
          (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then none else some oldBlk) ∗
        (OptOwn (MallocngInitBlock J γ)).interp (sf'.readReg64 .x0)
          (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then some (newSize.toNat, keptBs)
           else none) ⊢
        (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then
          ⌜sf'.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf'.readReg64 .x0).toNat ∧
            (sf'.readReg64 .x0).toNat + newSize.toNat < 2 ^ 64⌝ ∗
            J.Block γ (sf'.readReg64 .x0) newSize.toNat ∗ (sf'.readReg64 .x0 ↦ₛ keptBs) ∗
            memRegion (sf'.readReg64 .x0 + BitVec.ofNat 64 keptBs.length)
              (newSize.toNat - keptBs.length)
         else ⌜sf'.readReg64 .x0 = 0#64⌝ ∗ cReallocOld J γ ptr oldBlk) := by
      by_cases hok : decide (newSize.toNat ≤ MallocngMaxAllocSize) = true
      · simp only [hok, ↓reduceIte, CondOwn_interp_none, OptOwn_interp_some, emp_sepConj] at hwf_ret ⊢
        exact Entails.pure_right ⟨hwf_ret.2.1, hwf_ret.2.2.1, hwf_ret.2.2.2.1⟩ (Entails.refl _)
      · simp only [Bool.not_eq_true] at hok
        simp only [hok, Bool.false_eq_true, ↓reduceIte, CondOwn_interp_some, OptOwn_interp_none] at hwf_ptr ⊢
        rw [sepConj_comm]; refine sepConj_mono_right ?_
        cases oldBlk with
        | none => simp only [cReallocOld, OptOwn_interp_none]; exact Entails.refl _
        | some pair =>
          rcases pair with ⟨oldSz, bs⟩
          simp only [cReallocOld, OptOwn_interp_some, CondOwn_pureWf_some, OptOwn_pureWf_some] at hwf_ptr ⊢
          exact Entails.pure_right hwf_ptr.2.2.2.2 (Entails.refl _)
    exact Entails.pure_right (allocCallPreserved_hookExit hacc.1) (postEnv_reord2 hpool hblk)
  · rintro _ _ s0 sf' _ _ _
    left; dsimp only [ToBaseSpec.toSpec, mallocngReallocSpec, cReallocHookSpec]
    exact Entails.pure_mono oomPreserved_hookExit

/-! ## Rust Global-Allocator Hooks -/

/-- Subroutine hook implementing `__rustc::__rust_dealloc(ptr = x0, size = x1, align = x2)`
    by calling `mallocng`'s `free(ptr = x0)`. -/
noncomputable def mallocngRustDeallocHook (mpl : Obj.MultiPlacement) : State → State :=
  VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "free"
    (svc := Syscall.standard)

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

theorem mallocngRustDealloc_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngRustDeallocHook mpl)
      (rustStdDeallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl)) := by
  let A := mallocngRustCliHookAllocOf J hIf γ mpl
  rintro ⟨p, size, align, lb, lk⟩ R s0 hrun hpre hsp
  change s0.mem.KeepsFrozen (mallocngCHook mpl "free" s0).mem ∧ _
  have hpre_free :
      s0.mem ⊨ (cFreeHookSpec J hIf γ mpl).pre (p, size) s0 ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [rustStdDeallocSpec, cFreeHookSpec, A, mallocngRustCliHookAllocOf,
      mallocngRustCliAllocWithOf, mallocngRustCliLiveOf, mallocngCHookPool]
    rw [hookFrame_eq_stack1024 s0.sp]
    have hreord1 : ∀ (φ1 φ2 : Prop) (P B M E S1 S2 : SepProp),
        (⌜φ1⌝ ∗ P ∗ (⌜φ2⌝ ∗ B) ∗ M ∗ E ∗ (S1 ∗ S2)) ∗ R =
          ⌜φ1⌝ ∗ ⌜φ2⌝ ∗ (B ∗ ((P ∗ E) ∗ S1 ∗ M ∗ (S2 ∗ R))) := by intros; ac_rfl
    rw [hreord1]
    refine Entails.pure_left fun ⟨hx0, _, _⟩ => Entails.pure_left fun _ => ?_
    refine Entails.trans (sepConj_mono_left (hIf.block_nonnull γ p size)) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpNe, _, _, _⟩ => ?_
    simp only [hpNe, ↓reduceIte]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact Entails.pure_right hx0 (entails_of_eq (by ac_rfl))
  obtain ⟨hkf, hsym, hout⟩ :=
    cFree_hookOk hIf γ hPl hEntries (p, size)
      (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) s0 hrun hpre_free hsp
  refine ⟨hkf, hsym, ?_⟩
  let sf := mallocngCHook mpl "free" s0
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono ?_ hpost
    dsimp only [cFreeHookSpec, rustStdDeallocSpec, A, mallocngCHookPool,
      mallocngRustDeallocHook, mallocngCHook, mallocngRustCliHookAllocOf,
      mallocngRustCliAllocWithOf]
    rw [sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun hpres => ?_
    have htp : sf.tpidrEl0 = s0.tpidrEl0 := hpres.2.2.2.1
    dsimp only [sf, mallocngCHook] at htp
    rw [htp, hookFrame_eq_stack1024 s0.sp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_right hpres ?_
    refine entails_of_eq ?_
    ac_rfl
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
  rcases h12 with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
  exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
    h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28,
    hfp'.trans hfp, hv'.trans hv⟩

private theorem calleeSavedPreserved_writeReg64_x0 (s : State) (v : BitVec 64) :
    CalleeSavedPreserved s (s.writeReg64 .x0 v) := by unfold CalleeSavedPreserved; simp [Reg.fp, Reg.x0]

private theorem calleeSavedPreserved_writeReg64_x1 (s : State) (v : BitVec 64) :
    CalleeSavedPreserved s (s.writeReg64 .x1 v) := by unfold CalleeSavedPreserved; simp [Reg.fp, Reg.x1]

private theorem calleeSavedPreserved_writeReg64_lr (s : State) (v : BitVec 64) :
    CalleeSavedPreserved s (s.writeReg64 Reg.lr v) := by unfold CalleeSavedPreserved; simp [Reg.fp, Reg.lr]

private theorem calleeSavedPreserved_setMem (s : State) (m : Memory) :
    CalleeSavedPreserved s (s.setMem m) := by unfold CalleeSavedPreserved; simp

private theorem cHookPost_rearrange_lem (P E S1 S2 Q R : SepProp) :
    ((P ∗ E) ∗ S1 ∗ Q) ∗ (S2 ∗ R) = (E ∗ (S1 ∗ S2) ∗ (P ∗ Q)) ∗ R := by ac_rfl

private theorem entails_intro_pure (φ : Prop) {P : SepProp} (hφ : φ) : P ⊢ ⌜φ⌝ ∗ P :=
  Entails.pure_right hφ (Entails.refl P)

/-- Subroutine hook implementing `__rustc::__rust_alloc(size = x0, align = x1)` by swapping
    `.x0` and `.x1` and calling `mallocng`'s `aligned_alloc(align = x0, len = x1)`. -/
noncomputable def mallocngRustAllocHook (mpl : Obj.MultiPlacement) (s : State) : State :=
  let s_in := (s.writeReg64 .x0 (s.readReg64 .x1)).writeReg64 .x1 (s.readReg64 .x0)
  (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "aligned_alloc"
    (svc := Syscall.standard)) s_in

theorem mallocngRustAlloc_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngRustAllocHook mpl)
      (rustStdAllocSpec (mallocngRustCliHookAllocOf J hIf γ mpl)) := by
  let A := mallocngRustCliHookAllocOf J hIf γ mpl
  rintro ⟨size, align, lb, lk⟩ R s0 hrun hpre hsp
  let szBv := s0.readReg64 .x0
  let alBv := s0.readReg64 .x1
  let s_in := (s0.writeReg64 .x0 alBv).writeReg64 .x1 szBv
  change s0.mem.KeepsFrozen (mallocngCHook mpl "aligned_alloc" s_in).mem ∧
    (mallocngCHook mpl "aligned_alloc" s_in).symtab = s0.symtab ∧
    SubroutineOutcome (rustStdAllocSpec A) (size, align, lb, lk) R s0
      (mallocngCHook mpl "aligned_alloc" s_in)
  have hpure : szBv.toNat = size ∧ alBv.toNat = align ∧ RustLayoutOk size align := by
    have hp0 :
        s0.mem ⊨ ⌜szBv.toNat = size ∧ alBv.toNat = align ∧
            RustLayoutOk size align ∧ A.CanAlloc lb lk size align⌝ ∗
          ((A.pool lb lk s0 ∗ StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp) ∗ R) := by
      dsimp only [rustStdAllocSpec, szBv, alBv] at hpre; rwa [sepConj_assoc] at hpre
    rw [satisfies_pure_sepConj] at hp0
    rcases hp0.1 with ⟨h1, h2, h3, _⟩; exact ⟨h1, h2, h3⟩
  rcases hpure with ⟨hsz, hal, hpos, ⟨k, hk⟩, hsum, halMax⟩
  have hpow2 : IsPow2Align alBv := isPow2Align_of_toNat_pow2 (hal.trans hk)
  have halBound : alBv.toNat ≤ MaxAlignedAllocAlign := by unfold MaxAlignedAllocAlign; omega
  have hx0_in : s_in.readReg64 .x0 = alBv := by simp [s_in, Reg.x0, Reg.x1]
  have hx1_in : s_in.readReg64 .x1 = szBv := by simp [s_in, Reg.x0, Reg.x1]
  have hlr_in : s_in.readReg64 Reg.lr = s0.readReg64 Reg.lr := by simp [s_in, Reg.x0, Reg.x1, Reg.lr]
  have hcs_in : CalleeSavedPreserved s0 s_in :=
    calleeSavedPreserved_trans (calleeSavedPreserved_writeReg64_x0 s0 alBv)
      (calleeSavedPreserved_writeReg64_x1 _ szBv)
  have hpre_aa :
      s_in.mem ⊨ (cAlignedAllocHookSpec J hIf γ mpl).pre (alBv, szBv) s_in ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) := by
    change s0.mem ⊨ _; refine Satisfies.mono ?_ hpre
    dsimp only [rustStdAllocSpec, cAlignedAllocHookSpec, A, mallocngCHookPool,
      mallocngRustCliHookAllocOf, mallocngRustCliAllocWithOf]
    rw [hookFrame_eq_stack1024 s0.sp, sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    rw [sepConj_assoc (⌜s_in.readReg64 .x0 = alBv ∧ s_in.readReg64 .x1 = szBv ∧
      alBv.toNat ≤ MaxAlignedAllocAlign⌝)]
    exact Entails.pure_right ⟨hx0_in, hx1_in, halBound⟩ (entails_of_eq (by ac_rfl))
  obtain ⟨hkf, hsym, hout⟩ :=
    cAlignedAlloc_hookOk hIf γ hPl hEntries (alBv, szBv)
      (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) s_in hrun hpre_aa hsp
  refine ⟨hkf, hsym, ?_⟩
  generalize _hsf : mallocngCHook mpl "aligned_alloc" s_in = sf at hout ⊢
  have hsp_in : s_in.sp = s0.sp := rfl
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨⟨hlr_in ▸ hret.1, hsp_in ▸ hret.2.1, hret.2.2⟩,
      ⟨hsp_in ▸ hcc.1, calleeSavedPreserved_trans hcs_in hcc.2⟩, Satisfies.mono ?_ hpost⟩
    dsimp only [cAlignedAllocHookSpec, rustStdAllocSpec, A, mallocngCHookPool,
      mallocngRustCliHookAllocOf, mallocngRustCliAllocWithOf, mallocngRustCliLiveOf]
    rw [sepConj_assoc (⌜AllocCallPreserved s_in sf⌝)]
    refine Entails.pure_left fun hpres => ?_
    have hpres0 : AllocCallPreserved s0 sf := hpres
    have htp : sf.tpidrEl0 = s0.tpidrEl0 := hpres0.2.2.2.1
    have hok_eq : mallocngAlignedAllocOk alBv szBv = decide (MallocngLayoutFit szBv alBv) := by
      unfold mallocngAlignedAllocOk MallocngLayoutFit
      rw [isPow2Align_alignedAllocOk hpow2, Bool.true_and]; rfl
    rw [hsp_in, htp, hok_eq, hookFrame_eq_stack1024 s0.sp,
      sepConj_assoc (⌜AllocCallPreserved s0 sf⌝)]
    refine Entails.pure_right hpres0 ?_
    rw [cHookPost_rearrange_lem]
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ?_))
    let P := mallocngRustCliPoolWithOf J (VerifiedLibraries.mallocngLib.codeRO mpl)
      γ (mallocngAddrsOfPlacement mpl) sf
    change P ∗ _ ⊢ _
    by_cases hfit : MallocngLayoutFit szBv alBv
    · simp only [decide_eq_true hfit, ↓reduceIte]
      rw [← sepConj_assoc P, sepConj_comm P (⌜_⌝), sepConj_assoc]
      refine Entails.pure_left fun ⟨hne0, hdvdMax, _⟩ => ?_
      have hne0' : sf.readReg64 .x0 ≠ 0 := hne0
      simp only [hne0', ↓reduceIte, hsz]
      have hdvdAl : align ∣ (sf.readReg64 .x0).toNat := by
        rw [← hal]; exact Nat.dvd_trans (isPow2Align_dvd_max16 hpow2) hdvdMax
      have hmod0 : (sf.readReg64 .x0).toNat % align = 0 := Nat.mod_eq_zero_of_dvd hdvdAl
      refine Entails.pure_right hmod0
        (Entails.trans (entails_intro_pure
          ((sf.readReg64 .x0).toNat % align = 0 ∧ RustLayoutOk size align)
          ⟨hmod0, ⟨hpos, ⟨k, hk⟩, hsum, halMax⟩⟩)
          (entails_of_eq (by dsimp only [P]; ac_rfl)))
    · simp only [decide_eq_false hfit, Bool.false_eq_true, ↓reduceIte]
      rw [sepConj_comm P]
      refine Entails.pure_left fun heq0 => ?_
      have heq0' : sf.readReg64 .x0 = 0 := heq0
      simp only [heq0', ↓reduceIte]
      have hnull : NullAllowed size align := by
        unfold NullAllowed; have hg := not_layoutFit_imp_gt_2pow62 hfit; omega
      exact Entails.pure_right hnull (Entails.refl _)
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, satisfies_drop_mid ho⟩))

private theorem reallocHook_extract_pure {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    {p : BitVec 64} {old align new : Nat} {bs : List (BitVec 8)} {lb lk : Nat}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl)).pre
      (p, old, align, new, bs, lb, lk) s0 ∗ R) :
    (s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
      (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
      RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new) ∧
    (p.toNat % align = 0 ∧ RustLayoutOk old align) := by
  let A := mallocngRustCliHookAllocOf J hIf γ mpl
  have hp0 :
      s0.mem ⊨ (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
            A.CanAlloc lb lk new align⌝ ∗
          ⌜p.toNat % align = 0 ∧ RustLayoutOk old align⌝) ∗
        (A.pool lb lk s0 ∗ J.Block γ p old ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [rustStdReallocSpec, A, mallocngRustCliHookAllocOf,
      mallocngRustCliAllocWithOf, mallocngRustCliLiveOf]
    exact entails_of_eq (by ac_rfl)
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hp0
  rcases hp0 with ⟨⟨hx0, hold, hal, hnew, hLayNew, hbsOld, hbsNew, _⟩, holdLive, _⟩
  exact ⟨⟨hx0, hold, hal, hnew, hLayNew, hbsOld, hbsNew⟩, holdLive⟩

private theorem reallocHook_le16_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard)
    (p : BitVec 64) (old align new : Nat) (bs : List (BitVec 8)) (lb lk : Nat)
    (R : SepProp) (s0 : State)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl)).pre
      (p, old, align, new, bs, lb, lk) s0 ∗ R)
    (hsp : s0.spAligned = true)
    (hle16 : (s0.readReg64 .x2).toNat ≤ 16) :
    let s_r := s0.writeReg64 .x1 (s0.readReg64 .x3)
    let sf := mallocngCHook mpl "realloc" s_r
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl))
        (p, old, align, new, bs, lb, lk) R s0 sf := by
  let A := mallocngRustCliHookAllocOf J hIf γ mpl
  let alBv := s0.readReg64 .x2
  let newBv := s0.readReg64 .x3
  let s_r := s0.writeReg64 .x1 newBv
  rcases reallocHook_extract_pure hIf γ hpre with
    ⟨⟨hx0, _, hal, hnew, hLayNew, hbsOld, hbsNew⟩, holdLive⟩
  change alBv.toNat = align at hal; change newBv.toNat = new at hnew
  rcases hLayNew with ⟨hpos, ⟨k, hk⟩, hsum, halMax⟩
  have hpow2 : IsPow2Align alBv := isPow2Align_of_toNat_pow2 (hal.trans hk)
  have hx0_r : s_r.readReg64 .x0 = p := by simp [s_r, hx0, Reg.x0, Reg.x1]
  have hx1_r : s_r.readReg64 .x1 = newBv := by simp [s_r, Reg.x1]
  have hlr_r : s_r.readReg64 Reg.lr = s0.readReg64 Reg.lr := by simp [s_r, Reg.x1, Reg.lr]
  have hcs_r : CalleeSavedPreserved s0 s_r := calleeSavedPreserved_writeReg64_x1 s0 newBv
  have hpre_r :
      s_r.mem ⊨ (cReallocHookSpec J hIf γ mpl).pre (p, newBv, some (old, bs)) s_r ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) := by
    change s0.mem ⊨ _
    refine Satisfies.mono ?_ hpre
    dsimp only [rustStdReallocSpec, cReallocHookSpec, cReallocOld, A, mallocngCHookPool,
      mallocngRustCliHookAllocOf, mallocngRustCliAllocWithOf, mallocngRustCliLiveOf]
    rw [hookFrame_eq_stack1024 s0.sp, sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_left fun _ => Entails.refl _)))) ?_
    rw [sepConj_assoc (⌜s_r.readReg64 .x0 = p ∧ s_r.readReg64 .x1 = newBv⌝)]
    refine Entails.pure_right ⟨hx0_r, hx1_r⟩
      (Entails.trans (entails_intro_pure (bs.length ≤ old) hbsOld) (entails_of_eq (by ac_rfl)))
  obtain ⟨hkf, hsym, hout⟩ :=
    cRealloc_hookOk hIf γ hPl hEntries (p, newBv, some (old, bs))
      (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) s_r hrun hpre_r hsp
  refine ⟨hkf, hsym, ?_⟩
  generalize _hsf : mallocngCHook mpl "realloc" s_r = sf at hout ⊢
  have hsp_r : s_r.sp = s0.sp := rfl
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨⟨hlr_r ▸ hret.1, hsp_r ▸ hret.2.1, hret.2.2⟩,
      ⟨hsp_r ▸ hcc.1, calleeSavedPreserved_trans hcs_r hcc.2⟩, Satisfies.mono ?_ hpost⟩
    dsimp only [cReallocHookSpec, cReallocOld, rustStdReallocSpec, A, mallocngCHookPool,
      mallocngRustCliHookAllocOf, mallocngRustCliAllocWithOf, mallocngRustCliLiveOf]
    rw [sepConj_assoc (⌜AllocCallPreserved s_r sf⌝)]
    refine Entails.pure_left fun hpres => ?_
    have hpres0 : AllocCallPreserved s0 sf := hpres
    have htp : sf.tpidrEl0 = s0.tpidrEl0 := hpres0.2.2.2.1
    rw [hsp_r, htp, hookFrame_eq_stack1024 s0.sp,
      sepConj_assoc (⌜AllocCallPreserved s0 sf⌝)]
    refine Entails.pure_right hpres0 ?_
    rw [cHookPost_rearrange_lem]
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ?_))
    let P := mallocngRustCliPoolWithOf J (VerifiedLibraries.mallocngLib.codeRO mpl)
      γ (mallocngAddrsOfPlacement mpl) sf
    change P ∗ _ ⊢ _
    have hkept : (((some (old, bs)).map Prod.snd).getD []).take newBv.toNat = bs := by
      dsimp only [Option.map, Option.getD]; rw [hnew]; exact List.take_of_length_le hbsNew
    rw [hkept]
    by_cases hmax : newBv.toNat ≤ MallocngMaxAllocSize
    · simp only [decide_eq_true hmax, ↓reduceIte]
      rw [← sepConj_assoc P, sepConj_comm P (⌜_⌝), sepConj_assoc]
      refine Entails.pure_left fun ⟨hne0, hdvd16, _⟩ => ?_
      have hne0' : sf.readReg64 .x0 ≠ 0 := hne0
      simp only [hne0', ↓reduceIte, hnew]
      have hdvdAl : align ∣ (sf.readReg64 .x0).toNat := by
        rw [← hal]; exact Nat.dvd_trans (isPow2Align_dvd_16 hpow2 hle16) hdvd16
      have hmod0 : (sf.readReg64 .x0).toNat % align = 0 := Nat.mod_eq_zero_of_dvd hdvdAl
      refine Entails.pure_right hmod0
        (Entails.trans (entails_intro_pure
          ((sf.readReg64 .x0).toNat % align = 0 ∧ RustLayoutOk new align)
          ⟨hmod0, ⟨hpos, ⟨k, hk⟩, hsum, halMax⟩⟩)
          (entails_of_eq (by dsimp only [P]; ac_rfl)))
    · simp only [decide_eq_false hmax, Bool.false_eq_true, ↓reduceIte]
      have hpull :
          P ∗ (⌜sf.readReg64 .x0 = 0#64⌝ ∗ ⌜bs.length ≤ old⌝ ∗ J.Block γ p old ∗
              (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)) =
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗ ⌜bs.length ≤ old⌝ ∗
            (P ∗ J.Block γ p old ∗ (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)) := by ac_rfl
      rw [hpull]
      refine Entails.pure_left fun heq0 => Entails.pure_left fun _ => ?_
      have heq0' : sf.readReg64 .x0 = 0 := heq0
      simp only [heq0', ↓reduceIte]
      have hnull : NullAllowed new align := by unfold MallocngMaxAllocSize at hmax; unfold NullAllowed; omega
      refine Entails.pure_right hnull
        (Entails.trans (entails_intro_pure
          (p.toNat % align = 0 ∧ RustLayoutOk old align) holdLive)
          (entails_of_eq (by dsimp only [P]; ac_rfl)))
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, satisfies_drop_mid ho⟩))

private theorem reallocHook_gt16_copy {m1 : Memory} {p q : BitVec 64} {bs : List (BitVec 8)}
    {old new copyLen : Nat} {R_frame : SepProp}
    (h1 : bs.length ≤ copyLen) (h2 : copyLen ≤ old) (h3 : copyLen ≤ new)
    (h4 : old ≤ 2 ^ 64) (h5 : new ≤ 2 ^ 64)
    (hm1 : m1 ⊨ ((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
      memRegion q new) ∗ R_frame) :
    let m2 := m1.writeBytes q (m1.readBytes p copyLen)
    m1.KeepsFrozen m2 ∧
      (m2 ⊨ (memRegion p old ∗ (q ↦ₛ bs) ∗
        memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length)) ∗ R_frame) := by
  have hm_prep := Satisfies.mono
    (sepConj_mono_left (copyPrep_entails p q bs old new copyLen h1 h2 h3 h4 h5)) hm1
  rw [sepExists_sepConj_left] at hm_prep
  obtain ⟨dstBs, hm_prep1⟩ := (satisfies_sepExists _ _).mp hm_prep
  rw [sepExists_sepConj_left] at hm_prep1
  obtain ⟨midBs, hm_prep2⟩ := (satisfies_sepExists _ _).mp hm_prep1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_prep2
  rcases hm_prep2 with ⟨⟨hdstLen, hsrcLen⟩, hm_cells⟩
  let Tail := memRegion (p + BitVec.ofNat 64 copyLen) (old - copyLen) ∗
    memRegion (q + BitVec.ofNat 64 copyLen) (new - copyLen)
  have hm_p : m1 ⊨ (p ↦ₛ (bs ++ midBs)) ∗ ((q ↦ₛ dstBs) ∗ Tail ∗ R_frame) :=
    Satisfies.mono (entails_of_eq (by dsimp only [Tail]; ac_rfl)) hm_cells
  have hread : m1.readBytes p copyLen = bs ++ midBs := by
    rw [← hsrcLen]; exact ((IsBlock.pointsToBytes p (bs ++ midBs)).read hm_p).2
  have hm_q : m1 ⊨ (q ↦ₛ dstBs) ∗ ((p ↦ₛ (bs ++ midBs)) ∗ Tail ∗ R_frame) :=
    Satisfies.mono (entails_of_eq (by dsimp only [Tail]; ac_rfl)) hm_cells
  have hkf : m1.KeepsFrozen (m1.writeBytes q (m1.readBytes p copyLen)) := by
    have hm_qreg : m1 ⊨ memRegion q copyLen ∗ ((p ↦ₛ (bs ++ midBs)) ∗ Tail ∗ R_frame) := by
      rw [← hdstLen]
      exact Satisfies.mono (sepConj_mono_left (IsBlock.pointsToBytes q dstBs).entails_memRegion) hm_q
    have hlen_rb : (m1.readBytes p copyLen).length = copyLen := Memory.readBytes_length m1 p copyLen
    exact keepsFrozen_writeBytes_of_memRegion (m1.readBytes p copyLen)
      (by rw [hlen_rb]; omega) (by rw [hlen_rb]; exact hm_qreg)
  refine ⟨hkf, ?_⟩
  show m1.writeBytes q (m1.readBytes p copyLen) ⊨ _; rw [hread]
  have hm2_reord :
      m1.writeBytes q (bs ++ midBs) ⊨
        ((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs)) ∗ Tail) ∗ R_frame :=
    Satisfies.mono (entails_of_eq (by ac_rfl))
      (writeBytes_satisfies (hdstLen.trans hsrcLen.symm) hm_q)
  exact Satisfies.mono
    (sepConj_mono_left (copyFinish_entails p q bs midBs old new copyLen hsrcLen h2 h3 h4 h5))
    hm2_reord

private theorem reallocHook_gt16_fit_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard)
    (p : BitVec 64) (old align new : Nat) (bs : List (BitVec 8)) (lb lk : Nat)
    (R : SepProp) (s0 s1 : State)
    (hsp : s0.spAligned = true) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp)
    (hkf1 : s0.mem.KeepsFrozen s1.mem) (hsym1 : s1.symtab = s0.symtab)
    (hcs1 : CalleeSavedPreserved s0 s1) (hpres1 : AllocCallPreserved s0 s1)
    (hx0 : s0.readReg64 .x0 = p) (hold : (s0.readReg64 .x1).toNat = old)
    (hnew : (s0.readReg64 .x3).toNat = new) (hLayNew : RustLayoutOk new align)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new) (holdLe64 : old ≤ 2 ^ 64)
    (hqNe : s1.readReg64 .x0 ≠ 0#64) (hqMod : (s1.readReg64 .x0).toNat % align = 0)
    (hm1_copy : s1.mem ⊨ ((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
        memRegion (s1.readReg64 .x0) new) ∗
      (mallocngCHookPool J hIf γ mpl s1 ∗ stackFrameAt s0.sp mallocngStackBytes ∗
        stackFrameAt (s0.sp - 1024#64) 3072 ∗ J.Block γ p old ∗
        J.Block γ (s1.readReg64 .x0) new ∗ R)) :
    let q := s1.readReg64 .x0
    let copyLen := min (s0.readReg64 .x1).toNat (s0.readReg64 .x3).toNat
    let m2 := s1.mem.writeBytes q (s1.mem.readBytes (s0.readReg64 .x0) copyLen)
    let s2 := ((s1.setMem m2).writeReg64 .x0 (s0.readReg64 .x0)).writeReg64 Reg.lr
      (s0.readReg64 Reg.lr)
    let s3 := mallocngCHook mpl "free" s2
    let sf := s3.writeReg64 .x0 q
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl))
        (p, old, align, new, bs, lb, lk) R s0 sf := by
  intro q copyLen m2 s2 s3 sf
  let A := mallocngRustCliHookAllocOf J hIf γ mpl
  have hnewLe64 : new ≤ 2 ^ 64 := by have := hLayNew.2.2.1; omega
  have hbsCopy : bs.length ≤ copyLen := by dsimp only [copyLen]; omega
  have hcopyOld : copyLen ≤ old := by dsimp only [copyLen]; omega
  have hcopyNew : copyLen ≤ new := by dsimp only [copyLen]; omega
  obtain ⟨hkf2_p, hm2_p⟩ :=
    reallocHook_gt16_copy hbsCopy hcopyOld hcopyNew holdLe64 hnewLe64 hm1_copy
  have hm2_eq : m2 = s1.mem.writeBytes q (s1.mem.readBytes p copyLen) := by
    dsimp only [m2]; rw [hx0]
  have hkf2 : s1.mem.KeepsFrozen m2 := hm2_eq ▸ hkf2_p
  have hm2 :
      m2 ⊨ (memRegion p old ∗ (q ↦ₛ bs) ∗
          memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length)) ∗
        (mallocngCHookPool J hIf γ mpl s1 ∗ stackFrameAt s0.sp mallocngStackBytes ∗
          stackFrameAt (s0.sp - 1024#64) 3072 ∗ J.Block γ p old ∗ J.Block γ q new ∗ R) :=
    hm2_eq ▸ hm2_p
  have hrun2 : s2.status = .Running := hrun1
  have hsp2_eq : s2.sp = s0.sp := hsp1
  have hsp2 : s2.spAligned = true := by
    unfold State.spAligned at hsp ⊢
    rwa [hsp2_eq]
  have hx0_2 : s2.readReg64 .x0 = p := by simp [s2, hx0, Reg.x0, Reg.lr]
  have hlr_2 : s2.readReg64 Reg.lr = s0.readReg64 Reg.lr := by simp [s2, Reg.lr]
  have hcs_12 : CalleeSavedPreserved s1 s2 :=
    calleeSavedPreserved_trans (calleeSavedPreserved_setMem s1 m2)
      (calleeSavedPreserved_trans (calleeSavedPreserved_writeReg64_x0 _ _)
        (calleeSavedPreserved_writeReg64_lr _ _))
  have hpool_s2 : mallocngCHookPool J hIf γ mpl s1 = mallocngCHookPool J hIf γ mpl s2 := rfl
  let R_free := stackFrameAt (s0.sp - 1024#64) 3072 ∗ J.Block γ q new ∗ (q ↦ₛ bs) ∗
    memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R
  have hpre_free : s2.mem ⊨ (cFreeHookSpec J hIf γ mpl).pre (p, old) s2 ∗ R_free := by
    change m2 ⊨ _
    refine Satisfies.mono ?_ hm2
    dsimp only [cFreeHookSpec, R_free]
    rw [hsp2_eq, hpool_s2]
    have hpull_blk :
        (memRegion p old ∗ (q ↦ₛ bs) ∗
            memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length)) ∗
          (mallocngCHookPool J hIf γ mpl s2 ∗ stackFrameAt s0.sp mallocngStackBytes ∗
            stackFrameAt (s0.sp - 1024#64) 3072 ∗ J.Block γ p old ∗ J.Block γ q new ∗ R) =
        J.Block γ p old ∗
          (memRegion p old ∗ (q ↦ₛ bs) ∗
            memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
            mallocngCHookPool J hIf γ mpl s2 ∗ stackFrameAt s0.sp mallocngStackBytes ∗
            stackFrameAt (s0.sp - 1024#64) 3072 ∗ J.Block γ q new ∗ R) := by ac_rfl
    rw [hpull_blk]
    refine Entails.trans (sepConj_mono_left (hIf.block_nonnull γ p old)) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpNe, _, _, _⟩ => ?_
    simp only [hpNe, ↓reduceIte]
    rw [sepConj_assoc (⌜s2.readReg64 .x0 = p⌝)]
    exact Entails.pure_right hx0_2 (entails_of_eq (by ac_rfl))
  obtain ⟨hkf3, hsym3, hout3⟩ :=
    cFree_hookOk hIf γ hPl hEntries (p, old) R_free s2 hrun2 hpre_free hsp2
  dsimp only [sf, s3]
  generalize _hs3 : mallocngCHook mpl "free" s2 = s3_out at hkf3 hsym3 hout3 ⊢
  rcases hout3 with ⟨hret3, hcc3, hpost3⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · let sf_out := s3_out.writeReg64 .x0 q
    have hmem_s2 : s2.mem = m2 := rfl
    have hsym_s2 : s2.symtab = s1.symtab := rfl
    refine ⟨hkf1.trans (hkf2.trans (hmem_s2 ▸ hkf3)), (hsym3.trans hsym_s2).trans hsym1,
      Or.inl ⟨⟨hlr_2 ▸ hret3.1, hsp2_eq ▸ hret3.2.1, hret3.2.2⟩,
        ⟨hsp2_eq ▸ hret3.2.1,
          calleeSavedPreserved_trans hcs1
            (calleeSavedPreserved_trans hcs_12
              (calleeSavedPreserved_trans hcc3.2 (calleeSavedPreserved_writeReg64_x0 s3_out q)))⟩,
        ?_⟩⟩
    change s3_out.mem ⊨ (rustStdReallocSpec A).post (p, old, align, new, bs, lb, lk) s0 sf_out ∗ R
    refine Satisfies.mono ?_ hpost3
    dsimp only [cFreeHookSpec, rustStdReallocSpec, A, mallocngCHookPool,
      mallocngRustCliHookAllocOf, mallocngRustCliAllocWithOf, mallocngRustCliLiveOf, R_free]
    rw [sepConj_assoc (⌜AllocCallPreserved s2 s3_out⌝)]
    refine Entails.pure_left fun hpres3_s2 => ?_
    have hpres_all : AllocCallPreserved s0 sf_out := allocCallPreserved_trans hpres1 hpres3_s2
    have htp3 : s3_out.tpidrEl0 = s0.tpidrEl0 := hpres_all.2.2.2.1
    have hsf_x0 : sf_out.readReg64 .x0 = q := by simp [sf_out]
    have hqNe' : q ≠ 0 := hqNe
    have hpool_sf :
        mallocngRustCliPoolWithOf J (VerifiedLibraries.mallocngLib.codeRO mpl)
          γ (mallocngAddrsOfPlacement mpl) s3_out =
        mallocngRustCliPoolWithOf J (VerifiedLibraries.mallocngLib.codeRO mpl)
          γ (mallocngAddrsOfPlacement mpl) sf_out := rfl
    simp only [hsp2_eq, htp3, hsf_x0, hqNe', ↓reduceIte, hookFrame_eq_stack1024 s0.sp, hpool_sf]
    rw [sepConj_assoc (⌜AllocCallPreserved s0 sf_out⌝)]
    refine Entails.pure_right hpres_all ?_
    refine Entails.trans (entails_intro_pure (q.toNat % align = 0) hqMod) ?_
    refine Entails.trans (entails_intro_pure
      (q.toNat % align = 0 ∧ RustLayoutOk new align) ⟨hqMod, hLayNew⟩) ?_
    exact entails_of_eq (by dsimp only [q]; ac_rfl)
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem reallocHook_gt16_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard)
    (p : BitVec 64) (old align new : Nat) (bs : List (BitVec 8)) (lb lk : Nat)
    (R : SepProp) (s0 : State) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl)).pre
      (p, old, align, new, bs, lb, lk) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    let s_aa := (s0.writeReg64 .x0 (s0.readReg64 .x2)).writeReg64 .x1 (s0.readReg64 .x3)
    let s1 := mallocngCHook mpl "aligned_alloc" s_aa
    let sf :=
      if s1.status != .Running || s1.readReg64 .x0 == 0#64 then s1
      else
        let q := s1.readReg64 .x0
        let copyLen := min (s0.readReg64 .x1).toNat (s0.readReg64 .x3).toNat
        let m2 := s1.mem.writeBytes q (s1.mem.readBytes (s0.readReg64 .x0) copyLen)
        let s2 := ((s1.setMem m2).writeReg64 .x0 (s0.readReg64 .x0)).writeReg64 Reg.lr
          (s0.readReg64 Reg.lr)
        let s3 := mallocngCHook mpl "free" s2
        s3.writeReg64 .x0 q
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl))
        (p, old, align, new, bs, lb, lk) R s0 sf := by
  intro s_aa
  dsimp only
  let A := mallocngRustCliHookAllocOf J hIf γ mpl
  let alBv := s0.readReg64 .x2
  let newBv := s0.readReg64 .x3
  rcases reallocHook_extract_pure hIf γ hpre with
    ⟨⟨hx0, hold, hal, hnew, hLayNew, hbsOld, hbsNew⟩, holdLive⟩
  change alBv.toNat = align at hal
  change newBv.toNat = new at hnew
  rcases hLayNew with ⟨hpos, ⟨k, hk⟩, hsum, halMax⟩
  have hpow2 : IsPow2Align alBv := isPow2Align_of_toNat_pow2 (hal.trans hk)
  have halBound : alBv.toNat ≤ MaxAlignedAllocAlign := by unfold MaxAlignedAllocAlign; omega
  have holdLe64 : old ≤ 2 ^ 64 := by have := holdLive.2.2.1; omega
  have hx0_aa : s_aa.readReg64 .x0 = alBv := by simp [s_aa, alBv, Reg.x0, Reg.x1]
  have hx1_aa : s_aa.readReg64 .x1 = newBv := by simp [s_aa, newBv, Reg.x0, Reg.x1]
  have hlr_aa : s_aa.readReg64 Reg.lr = s0.readReg64 Reg.lr := by simp [s_aa, Reg.x0, Reg.x1, Reg.lr]
  have hcs_aa : CalleeSavedPreserved s0 s_aa :=
    calleeSavedPreserved_trans (calleeSavedPreserved_writeReg64_x0 s0 alBv)
      (calleeSavedPreserved_writeReg64_x1 _ newBv)
  let S_rest := stackFrameAt (s0.sp - 1024#64) 3072
  let OldOwn := J.Block γ p old ∗ (p ↦ₛ bs) ∗
    memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
  have hpre_aa :
      s_aa.mem ⊨ (cAlignedAllocHookSpec J hIf γ mpl).pre (alBv, newBv) s_aa ∗
        (S_rest ∗ OldOwn ∗ R) := by
    change s0.mem ⊨ _
    refine Satisfies.mono ?_ hpre
    dsimp only [rustStdReallocSpec, cAlignedAllocHookSpec, A, mallocngCHookPool,
      mallocngRustCliHookAllocOf, mallocngRustCliAllocWithOf, mallocngRustCliLiveOf,
      S_rest, OldOwn]
    rw [hookFrame_eq_stack1024 s0.sp, sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_left fun _ => Entails.refl _)))) ?_
    rw [sepConj_assoc (⌜s_aa.readReg64 .x0 = alBv ∧ s_aa.readReg64 .x1 = newBv ∧
      alBv.toNat ≤ MaxAlignedAllocAlign⌝)]
    exact Entails.pure_right ⟨hx0_aa, hx1_aa, halBound⟩ (entails_of_eq (by ac_rfl))
  obtain ⟨hkf1, hsym1, hout1⟩ :=
    cAlignedAlloc_hookOk hIf γ hPl hEntries (alBv, newBv)
      (S_rest ∗ OldOwn ∗ R) s_aa hrun hpre_aa hsp
  generalize _hs1 : mallocngCHook mpl "aligned_alloc" s_aa = s1_out at hkf1 hsym1 hout1 ⊢
  have hsp_aa : s_aa.sp = s0.sp := rfl
  rcases hout1 with ⟨hret1, hcc1, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho_st, ho⟩
  · have hpc1 : s1_out.pc = s0.readReg64 Reg.lr := hlr_aa ▸ hret1.1
    have hsp1 : s1_out.sp = s0.sp := hsp_aa ▸ hret1.2.1
    have hrun1 : s1_out.status = .Running := hret1.2.2
    have hcs1 : CalleeSavedPreserved s0 s1_out := calleeSavedPreserved_trans hcs_aa hcc1.2
    have hok_eq : mallocngAlignedAllocOk alBv newBv = decide (MallocngLayoutFit newBv alBv) := by
      unfold mallocngAlignedAllocOk MallocngLayoutFit
      rw [isPow2Align_alignedAllocOk hpow2, Bool.true_and]; rfl
    by_cases hfit : MallocngLayoutFit newBv alBv
    · have hp1 :
          s1_out.mem ⊨ (⌜AllocCallPreserved s_aa s1_out⌝ ∗
              ⌜s1_out.readReg64 .x0 ≠ 0#64 ∧ max alBv.toNat 16 ∣ (s1_out.readReg64 .x0).toNat ∧
                (s1_out.readReg64 .x0).toNat + new < 2 ^ 64⌝) ∗
            (((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
                memRegion (s1_out.readReg64 .x0) new) ∗
              (mallocngCHookPool J hIf γ mpl s1_out ∗ stackFrameAt s0.sp mallocngStackBytes ∗
                S_rest ∗ J.Block γ p old ∗ J.Block γ (s1_out.readReg64 .x0) new ∗ R)) := by
        refine Satisfies.mono ?_ hpost1
        dsimp only [cAlignedAllocHookSpec, OldOwn]
        rw [hsp_aa, hok_eq]
        simp only [decide_eq_true hfit, ↓reduceIte, hnew]
        exact entails_of_eq (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hp1
      rcases hp1 with ⟨hpres1_aa, ⟨hqNe, hqDvdMax, _⟩, hm1_copy⟩
      have hcond : (s1_out.status != .Running || s1_out.readReg64 .x0 == 0#64) = false := by
        rw [hrun1]
        exact Bool.or_eq_false_iff.mpr ⟨rfl, beq_eq_false_iff_ne.mpr hqNe⟩
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have hdvdAl : align ∣ (s1_out.readReg64 .x0).toNat := by
        rw [← hal]; exact Nat.dvd_trans (isPow2Align_dvd_max16 hpow2) hqDvdMax
      exact reallocHook_gt16_fit_ok hIf γ hPl hEntries p old align new bs lb lk R s0 s1_out
        hsp hrun1 hsp1 hkf1 hsym1 hcs1 hpres1_aa hx0 hold hnew ⟨hpos, ⟨k, hk⟩, hsum, halMax⟩
        hbsOld hbsNew holdLe64 hqNe (Nat.mod_eq_zero_of_dvd hdvdAl) hm1_copy
    · have hp1 :
          s1_out.mem ⊨ (⌜AllocCallPreserved s_aa s1_out⌝ ∗ ⌜s1_out.readReg64 .x0 = 0#64⌝) ∗
            (mallocngCHookPool J hIf γ mpl s1_out ∗ stackFrameAt s0.sp mallocngStackBytes ∗
              S_rest ∗ OldOwn ∗ R) := by
        refine Satisfies.mono ?_ hpost1
        dsimp only [cAlignedAllocHookSpec]
        rw [hsp_aa, hok_eq]
        simp only [decide_eq_false hfit, Bool.false_eq_true, ↓reduceIte]
        exact entails_of_eq (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hp1
      rcases hp1 with ⟨hpres1, hq0, hm1_null⟩
      have hcond : (s1_out.status != .Running || s1_out.readReg64 .x0 == 0#64) = true := by
        rw [hrun1, hq0]; rfl
      simp only [hcond, ↓reduceIte]
      refine ⟨hkf1, hsym1, Or.inl ⟨⟨hpc1, hsp1, hrun1⟩, ⟨hsp1, hcs1⟩, ?_⟩⟩
      have hpres0 : AllocCallPreserved s0 s1_out := hpres1
      have htp1 : s1_out.tpidrEl0 = s0.tpidrEl0 := hpres0.2.2.2.1
      have hq0' : s1_out.readReg64 .x0 = 0 := hq0
      have hnull : NullAllowed new align := by
        unfold NullAllowed; have hg := not_layoutFit_imp_gt_2pow62 hfit; omega
      refine Satisfies.mono ?_ hm1_null
      dsimp only [rustStdReallocSpec, A, mallocngCHookPool, mallocngRustCliHookAllocOf,
        mallocngRustCliAllocWithOf, mallocngRustCliLiveOf, S_rest, OldOwn]
      simp only [hq0', ↓reduceIte, htp1, hookFrame_eq_stack1024 s0.sp]
      rw [sepConj_assoc (⌜AllocCallPreserved s0 s1_out⌝)]
      refine Entails.pure_right hpres0 ?_
      refine Entails.trans (entails_intro_pure (NullAllowed new align) hnull) ?_
      refine Entails.trans (entails_intro_pure
        (p.toNat % align = 0 ∧ RustLayoutOk old align) holdLive) ?_
      exact entails_of_eq (by ac_rfl)
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · have hcond : (s1_out.status != .Running || s1_out.readReg64 .x0 == 0#64) = true := by
      rw [ho_st]; rfl
    simp only [hcond, ↓reduceIte]
    have ho' :
        s1_out.mem ⊨ (rustStdReallocSpec A).onOom (p, old, align, new, bs, lb, lk) s0 s1_out ∗
          ((S_rest ∗ OldOwn) ∗ R) := by
      refine Satisfies.mono (entails_of_eq ?_) ho
      dsimp only [cAlignedAllocHookSpec, rustStdReallocSpec, A, s_aa]
      ac_rfl
    exact ⟨hkf1, hsym1, Or.inr (Or.inr (Or.inr ⟨ho_st, satisfies_drop_mid ho'⟩))⟩

/-- Subroutine hook implementing `__rustc::__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)`:
    delegates to `realloc` when `align ≤ 16`, and otherwise runs `aligned_alloc(align, new)`,
    copies `min old new` bytes in memory, frees `ptr` (preserving `lr`), and returns the new block. -/
noncomputable def mallocngRustReallocHook (mpl : Obj.MultiPlacement) (s : State) : State :=
  if (s.readReg64 .x2).toNat ≤ 16 then
    let s_r := s.writeReg64 .x1 (s.readReg64 .x3)
    (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "realloc"
      (svc := Syscall.standard)) s_r
  else
    let s_aa := (s.writeReg64 .x0 (s.readReg64 .x2)).writeReg64 .x1 (s.readReg64 .x3)
    let s1 := (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "aligned_alloc"
      (svc := Syscall.standard)) s_aa
    if s1.status != .Running || s1.readReg64 .x0 == 0#64 then
      s1
    else
      let q := s1.readReg64 .x0
      let copyLen := min (s.readReg64 .x1).toNat (s.readReg64 .x3).toNat
      let m2 := s1.mem.writeBytes q (s1.mem.readBytes (s.readReg64 .x0) copyLen)
      let s2 := ((s1.setMem m2).writeReg64 .x0 (s.readReg64 .x0)).writeReg64 Reg.lr
        (s.readReg64 Reg.lr)
      let s3 := (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "free"
        (svc := Syscall.standard)) s2
      s3.writeReg64 .x0 q

theorem mallocngRustRealloc_hookOk {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    HookOk (mallocngRustReallocHook mpl)
      (rustStdReallocSpec (mallocngRustCliHookAllocOf J hIf γ mpl)) := by
  rintro ⟨p, old, align, new, bs, lb, lk⟩ R s0 hrun hpre hsp
  unfold mallocngRustReallocHook
  by_cases hle16 : (s0.readReg64 .x2).toNat ≤ 16
  · simp only [hle16, ↓reduceIte]
    exact reallocHook_le16_ok hIf γ hPl hEntries p old align new bs lb lk R s0 hrun hpre hsp hle16
  · simp only [hle16, ↓reduceIte]
    exact reallocHook_gt16_ok hIf γ hPl hEntries p old align new bs lb lk R s0 hrun hpre hsp

/-! ## `mallocngRustCliHookMap` and `RustStdAllocHooks` Bundles -/

/-- Hook table mapping Rust global-allocator symbols and `musl` C allocator entry points to
    `VerifiedLibraries.mallocngLib` hooks at multi-placement `mpl`. -/
noncomputable def mallocngRustCliHookMap (mpl : Obj.MultiPlacement) : String → Option (State → State)
  | "__rustc::__rust_alloc"   => some (mallocngRustAllocHook mpl)
  | "__rustc::__rust_dealloc" => some (mallocngRustDeallocHook mpl)
  | "__rustc::__rust_realloc" => some (mallocngRustReallocHook mpl)
  | "malloc"                  => some (mallocngCHook mpl "malloc")
  | "free"                    => some (mallocngCHook mpl "free")
  | "realloc"                 => some (mallocngCHook mpl "realloc")
  | "aligned_alloc"           => some (mallocngCHook mpl "aligned_alloc")
  | "posix_memalign"          => some (mallocngCHook mpl "posix_memalign")
  | "calloc"                  => some (mallocngCHook mpl "calloc")
  | _                         => none

theorem mallocngRustCliHooksOf_placed_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    RustStdAllocHooks (mallocngRustCliHookAllocOf J hIf γ mpl) (mallocngRustCliHookMap mpl) where
  alloc := ⟨mallocngRustAllocHook mpl, rfl, mallocngRustAlloc_hookOk hIf γ hPl hEntries⟩
  dealloc := ⟨mallocngRustDeallocHook mpl, rfl, mallocngRustDealloc_hookOk hIf γ hPl hEntries⟩
  realloc := ⟨mallocngRustReallocHook mpl, rfl, mallocngRustRealloc_hookOk hIf γ hPl hEntries⟩

theorem mallocngRustCliHooks_placed_ok (γ : GhostName) {mpl : Obj.MultiPlacement}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hEntries : MallocngPlacedEntryContracts mallocngIface mpl Syscall.standard) :
    RustStdAllocHooks (mallocngRustCliHookAlloc γ mpl) (mallocngRustCliHookMap mpl) :=
  mallocngRustCliHooksOf_placed_ok mallocngRustCliIfaceFacts γ hPl hEntries

/-- Wrapping any `hooks` table with `Rust.withPanics` preserves `RustStdAllocHooks` because none of
    `__rustc::__rust_alloc`, `__rustc::__rust_dealloc`, or `__rustc::__rust_realloc` is a panic symbol. -/
theorem RustStdAllocHooks.withPanics {oom : State → State → Prop}
    {A : RustStdAlloc oom} {hooks : String → Option (State → State)}
    (h : RustStdAllocHooks A hooks) :
    RustStdAllocHooks A (Rust.withPanics hooks) where
  alloc := by
    obtain ⟨f, hf, hok⟩ := h.alloc
    exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩
  dealloc := by
    obtain ⟨f, hf, hok⟩ := h.dealloc
    exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩
  realloc := by
    obtain ⟨f, hf, hok⟩ := h.realloc
    exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

end VerifiedLibraries.RustStd
