/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.Musl.Proofs.MemOps
public import VerifiedLibraries.Mallocng.Spec.Top
public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import

/-!
# Region-Local `memcpy` Code Proof (`blk20`) & Master Spec (`HooksDehook.MemcpyCode`)

Design-independent core Step 1 & Step 2 for de-hooking `memcpy` (`mallocngLib` block 20, `396` B =
`99` words) on the `F3` / `K`-ghost route:

1. **Block 20 word identity (`mallocngLib` ↔ `memcpySymWords`):**
   - `mallocngLib_block20_eq`: `mallocngLib.blocks[20]? = some mallocng_blk20_memcpy`.
   - `mallocng_blk20_code_eq_memcpySymWords`: `mallocng_blk20_memcpy.code = mallocngWordsLE memcpySymWords`
     by `rfl`.
   - `mallocngBlockProg20_hasWords`: `(mallocngBlockProg mmpl 20 svc).hasWords (mmpl.base 20) memcpySymWords`
     for arbitrary `mmpl` and `svc` (`relocs = []`).
2. **Master specification (`masterMemcpySpec`) & `K`-narrowed wrapper (`memcpySpecK`):**
   - Indexed by `(ro, dst, src, bs) : Bool × BitVec 64 × BitVec 64 × List (BitVec 8)` over
     `VerifiedLibraries.Musl.memcpySrc ro src bs` so both RW (`↦ₛ`, `ro = false`) and RO (`↦ᵣ`,
     `ro = true`) sources are covered by one ghost hook.
   - Zero-stack precondition, preserves `MemcpyStatePreserved` (`fs`, `trace`, `tpidrEl0`,
     `sigActions`, `brk`, `brkStart`, `physMemAvail`), keeping `SpecStripSInvariant` definitional.
3. **Region-local `subroutine_ok` & consumer `HookOk` consequence lifts.**
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (StdStatePreserved stdMemcpySpec stdMemcpyROSpec)
open VerifiedLibraries (mallocngWordsLE mallocng_blk20_memcpy mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (
  memcpySymWords memcpySrc memcpySymSpec memcpyROSymSpec
  memcpy_codeAt_ok_sym memcpyRO_codeAt_ok_sym
  stdMemcpy_ok_of_hasWords stdMemcpyRO_ok_of_hasWords
)
open CryptoVerification.LibsignalTripleRatchet (
  sessionMemcpyRegionSpec sessionMemcpySpec framelessMemcpySpec memcpyROExtSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)
open CryptoVerification.SignalSession.CliExt (memcpySpec memcpyROSpec)
open LibsignalBinary.Heap (
  AllocCallPreserved VmPreserved OomPreserved PoolPreserved
  allocMemcpyVmSpec allocMemcpyVm_ok_of_hasWords
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)

/-! ## 1. Master `memcpy` Specification & Wrappers -/

/-- Non-memory process/VM state fields preserved across real `memcpy` (`blk20`) and `hookMemcpy`.
    Separating `mem.perm` out of `post` ensures `SpecStripSInvariant keep masterMemcpySpec` holds
    definitionally (`rfl`) for arbitrary `keep : BitVec 64 → Bool`; `VmPreserved` and `oracle`
    preservation are established pointwise on the ghost hook. -/
@[expose] def MemcpyStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
    sf.trace = s0.trace ∧
    sf.tpidrEl0 = s0.tpidrEl0 ∧
    sf.sigActions = s0.sigActions ∧
    sf.brk = s0.brk ∧
    sf.brkStart = s0.brkStart ∧
    sf.physMemAvail = s0.physMemAvail

theorem MemcpyStatePreserved.refl (s : State) : MemcpyStatePreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MemcpyStatePreserved.of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : MemcpyStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem MemcpyStatePreserved.toAllocCallPreserved {s0 sf : State}
    (h : MemcpyStatePreserved s0 sf) (horc : sf.oracle = s0.oracle)
    (hsym : sf.symtab = s0.symtab) : AllocCallPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2.1, horc, hsym⟩

/-- Master separation-logic contract for `memcpy(dst, src, len)` indexed by `(ro, dst, src, bs)`:
    requires zero stack bytes (`memRegion dst bs.length ∗ memcpySrc ro src bs`), returns `dst` in
    `x0`, copies `bs` to `dst ↦ₛ bs` while preserving `memcpySrc ro src bs` (`src ↦ᵣ bs` when
    `ro = true`, `src ↦ₛ bs` when `ro = false`) and `MemcpyStatePreserved`, and never panics,
    exits, or OOMs. -/
@[expose] def masterMemcpySpec :
    Spec (Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗
      memcpySrc ro src bs
  post := fun (ro, dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ MemcpyStatePreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗
      memcpySrc ro src bs
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `K`-route precondition narrowing: conjoins `⌜keep (s.readReg64 .lr) = false⌝` to `spec.pre`,
    leaving `post`, `onPanic`, `onExit`, and `onOom` unchanged (mirrors `h2k_*SpecK`). -/
@[expose] def memcpySpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

/-! ## 2. `mallocngLib` Block 20 Word Identity & Region-Local `subroutine_ok` -/

/-- `mallocngLib` block 20 is `mallocng_blk20_memcpy` (`396` bytes = `99` words, `relocs = []`). -/
theorem mallocngLib_block20_eq :
    mallocngLib.blocks[20]? = some mallocng_blk20_memcpy := by
  simp only [mallocngLib, List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- `(mallocngLib.blockLib 20).text` is `mallocng_blk20_memcpy`. -/
theorem mallocngLib_blockLib20_text :
    (mallocngLib.blockLib 20).text = mallocng_blk20_memcpy :=
  mallocngLib.blockLib_text (by decide : 20 < mallocngLib.blocks.length)

/-- Byte-length of `mallocng_blk20_memcpy` is `396` (`99` AArch64 words). -/
theorem mallocng_blk20_code_length :
    mallocng_blk20_memcpy.code.length = 396 := by
  decide +kernel

/-- `memcpySymWords` has `99` words (`396` bytes). -/
theorem memcpySymWords_length :
    memcpySymWords.length = 99 := rfl

/-- `mallocng_blk20_memcpy.code` is definitionally `mallocngWordsLE memcpySymWords`. -/
theorem mallocng_blk20_code_eq_memcpySymWords :
    mallocng_blk20_memcpy.code = mallocngWordsLE memcpySymWords := rfl

/-- `mallocng_blk20_memcpy.code` is byte-identical to `(Program.ofWords 0#64 memcpySymWords).code`. -/
theorem mallocng_blk20_code_eq_ofWords :
    mallocng_blk20_memcpy.code = (Program.ofWords 0#64 memcpySymWords).code := by
  decide +kernel

private theorem patchedWord_of_relocs_nil {blk : Obj.CodeBlock} (hrel : blk.relocs = [])
    (pl : Obj.Placement) (off : Nat) :
    blk.patchedWord pl off = blk.wordAt off := by
  simp [Obj.CodeBlock.patchedWord, Obj.CodeBlock.relocAt?, hrel]

private theorem patched_indep_of_relocs_nil {blk : Obj.CodeBlock} (hrel : blk.relocs = [])
    (pl1 pl2 : Obj.Placement) :
    blk.patched pl1 = blk.patched pl2 := by
  simp [Obj.CodeBlock.patched, patchedWord_of_relocs_nil hrel]

private theorem mallocng_blk20_patched_zero :
    mallocng_blk20_memcpy.patched { base := 0#64, ρ := fun _ => 0#64 } =
      (Program.ofWords 0#64 memcpySymWords).code := by
  decide +kernel

private theorem ofWords_memcpy_readWordOff_all :
    ((List.range memcpySymWords.length).all fun i =>
      (Program.ofWords 0#64 memcpySymWords).readWordOff (4 * i) == memcpySymWords[i]?) = true := by
  decide +kernel

private theorem readWordOff_eq_of_code_eq {P Q : Program} (h : P.code = Q.code) (off : Nat) :
    P.readWordOff off = Q.readWordOff off := by
  unfold Program.readWordOff
  rw [h]

/-- `pureWordsProg base memcpySymWords` holds `memcpySymWords` at `base` for any `base`. -/
theorem pureWordsProg_memcpy_hasWords (base : BitVec 64) :
    (pureWordsProg base memcpySymWords).hasWords base memcpySymWords := by
  refine pureWordsProg_hasWords (by decide) ?_
  have hcode : (pureWordsProg base memcpySymWords).code =
      (Program.ofWords 0#64 memcpySymWords).code := rfl
  simp only [readWordOff_eq_of_code_eq hcode]
  exact ofWords_memcpy_readWordOff_all

private theorem blockProgram_code_eq (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (i : Nat)
    (externs overrides : String → Option (State → State)) (svc : State → State) :
    (lib.blockProgram mpl i externs overrides svc).code =
      (lib.blockLib i).text.patched (lib.blockPlacement mpl i) := rfl

private theorem mallocng_blk20_relocs_nil :
    mallocng_blk20_memcpy.relocs = [] := by
  decide +kernel

/-- `mallocngBlockProg mmpl 20 svc` holds `memcpySymWords` at `mmpl.base 20` for any placement
    `mmpl` and syscall handler `svc` (since `mallocng_blk20_memcpy.relocs = []`). -/
theorem mallocngBlockProg20_hasWords (mmpl : Obj.MultiPlacement) (svc : State → State) :
    (mallocngBlockProg mmpl 20 svc).hasWords (mmpl.base 20) memcpySymWords := by
  unfold Program.hasWords Program.hasWordsOff
  have hbase : (mallocngBlockProg mmpl 20 svc).base = mmpl.base 20 := rfl
  have hsub : (mmpl.base 20 - (mallocngBlockProg mmpl 20 svc).base).toNat = 0 := by
    rw [hbase]; simp
  have hcode : (mallocngBlockProg mmpl 20 svc).code =
      (Program.ofWords 0#64 memcpySymWords).code :=
    (blockProgram_code_eq mallocngLib mmpl 20 _ _ svc).trans <|
      (congrArg (Obj.CodeBlock.patched · (mallocngLib.blockPlacement mmpl 20))
        mallocngLib_blockLib20_text).trans <|
      (patched_indep_of_relocs_nil mallocng_blk20_relocs_nil _
        { base := 0#64, ρ := fun _ => 0#64 }).trans mallocng_blk20_patched_zero
  rw [hsub, Nat.zero_add]
  refine ⟨by decide, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hmem : i ∈ List.range memcpySymWords.length := List.mem_range.mpr hi
  have hall := beq_iff_eq.mp (List.all_eq_true.mp ofWords_memcpy_readWordOff_all i hmem)
  rw [Nat.zero_add, readWordOff_eq_of_code_eq hcode, hall, List.getElem?_eq_getElem hi]

/-- `mallocngBlockProg mmpl 20 svc` has no external hooks (`externAt? pc = none`). -/
theorem mallocngBlockProg20_externAt_none (mmpl : Obj.MultiPlacement) (svc : State → State)
    (pc : BitVec 64) :
    (mallocngBlockProg mmpl 20 svc).externAt? pc = none :=
  mallocngLib.externAt?_blockProgram_none mmpl 20 pc

/-- `pureWordsProg base words` has no external hooks (`externAt? pc = none`). -/
theorem pureWordsProg_externAt_none (base : BitVec 64) (words : List (BitVec 32))
    (pc : BitVec 64) :
    (pureWordsProg base words).externAt? pc = none := by
  unfold Program.externAt? pureWordsProg Program.ofWords
  rfl

/-- Convert `masterMemcpySpec.pre (false, dst, src, bs)` to `stdMemcpySpec.pre (dst, src, bs)`. -/
theorem stdMemcpy_pre_of_masterMemcpy_pre {dst src : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {s0 : State}
    (hp : s0.mem ⊨ masterMemcpySpec.pre (false, dst, src, bs) s0 ∗ R) :
    s0.mem ⊨ stdMemcpySpec.pre (dst, src, bs) s0 ∗ R := by
  dsimp only [masterMemcpySpec, stdMemcpySpec, memcpySrc, cond] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2' : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2', hlt⟩, by rwa [sepConj_assoc]⟩

/-- Convert `masterMemcpySpec.pre (true, dst, src, bs)` to `stdMemcpyROSpec.pre (dst, src, bs)`. -/
theorem stdMemcpyRO_pre_of_masterMemcpy_pre {dst src : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {s0 : State}
    (hp : s0.mem ⊨ masterMemcpySpec.pre (true, dst, src, bs) s0 ∗ R) :
    s0.mem ⊨ stdMemcpyROSpec.pre (dst, src, bs) s0 ∗ R := by
  dsimp only [masterMemcpySpec, stdMemcpyROSpec, memcpySrc, cond] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2' : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2', hlt⟩, by rwa [sepConj_assoc]⟩

/-- Region-local `subroutine_ok` for `memcpySymSpec` on any `P_sub` holding `memcpySymWords`. -/
theorem subroutine_ok_memcpySym_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry memcpySymSpec :=
  memcpy_codeAt_ok_sym P_sub entry hwords

/-- Region-local `subroutine_ok` for `memcpyROSymSpec` on any `P_sub` holding `memcpySymWords`. -/
theorem subroutine_ok_memcpyROSym_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry memcpyROSymSpec :=
  memcpyRO_codeAt_ok_sym P_sub entry hwords

/-- Region-local `subroutine_ok` for `stdMemcpySpec` on any hook-free `P_sub` holding
    `memcpySymWords`. -/
theorem subroutine_ok_stdMemcpy_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry stdMemcpySpec :=
  stdMemcpy_ok_of_hasWords P_sub entry hsub_no hwords

/-- Region-local `subroutine_ok` for `stdMemcpyROSpec` on any hook-free `P_sub` holding
    `memcpySymWords`. -/
theorem subroutine_ok_stdMemcpyRO_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry stdMemcpyROSpec :=
  stdMemcpyRO_ok_of_hasWords P_sub entry hsub_no hwords

/-- Region-local `subroutine_ok` for `allocMemcpyVmSpec` on any hook-free `P_sub` holding
    `memcpySymWords`. -/
theorem subroutine_ok_allocMemcpyVm_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry allocMemcpyVmSpec :=
  allocMemcpyVm_ok_of_hasWords P_sub entry hsub_no hwords

/-- Region-local `subroutine_ok` for `masterMemcpySpec` (covering both `ro = false` RW and
    `ro = true` RO sources) on any hook-free `P_sub` holding `memcpySymWords`. -/
theorem subroutine_ok_masterMemcpy_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry masterMemcpySpec := by
  refine subroutine_ok_outcome_intro fun ⟨ro, dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  cases ro
  · have hpre' := stdMemcpy_pre_of_masterMemcpy_pre hpre
    refine (stdMemcpy_ok_of_hasWords P_sub entry hsub_no hwords).mono_outcome
      (dst, src, bs) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | hpan | hex)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [stdMemcpySpec, masterMemcpySpec, memcpySrc, cond] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.1.1, MemcpyStatePreserved.of_stdStatePreserved hq.1.2⟩, by
        rw [← sepConj_assoc]; exact hq.2⟩
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hpre' := stdMemcpyRO_pre_of_masterMemcpy_pre hpre
    refine (stdMemcpyRO_ok_of_hasWords P_sub entry hsub_no hwords).mono_outcome
      (dst, src, bs) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | hpan | hex)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [stdMemcpyROSpec, masterMemcpySpec, memcpySrc, cond] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.1.1, MemcpyStatePreserved.of_stdStatePreserved hq.1.2⟩, by
        rw [← sepConj_assoc]; exact hq.2⟩
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)

/-- Region-local `subroutine_ok` for `memcpySpecK keep masterMemcpySpec` on any hook-free `P_sub`
    holding `memcpySymWords`. -/
theorem subroutine_ok_masterMemcpyK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry (memcpySpecK keep masterMemcpySpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterMemcpy_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [memcpySpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- `mallocngBlockProg mmpl 20 svc` satisfies `memcpySymSpec` at `mmpl.base 20`. -/
theorem mallocngBlock20_memcpySym_ok (mmpl : Obj.MultiPlacement)
    (svc : State → State := Syscall.standard) :
    subroutine_ok (mallocngBlockProg mmpl 20 svc) (mmpl.base 20) memcpySymSpec :=
  subroutine_ok_memcpySym_of_hasWords (mallocngBlockProg20_hasWords mmpl svc)

/-- `mallocngBlockProg mmpl 20 svc` satisfies `memcpyROSymSpec` at `mmpl.base 20`. -/
theorem mallocngBlock20_memcpyROSym_ok (mmpl : Obj.MultiPlacement)
    (svc : State → State := Syscall.standard) :
    subroutine_ok (mallocngBlockProg mmpl 20 svc) (mmpl.base 20) memcpyROSymSpec :=
  subroutine_ok_memcpyROSym_of_hasWords (mallocngBlockProg20_hasWords mmpl svc)

/-- `mallocngBlockProg mmpl 20 Syscall.standard` satisfies `stdMemcpySpec` at `mmpl.base 20`. -/
theorem mallocngBlock20_stdMemcpy_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) stdMemcpySpec :=
  subroutine_ok_stdMemcpy_of_hasWords
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-- `mallocngBlockProg mmpl 20 Syscall.standard` satisfies `stdMemcpyROSpec` at `mmpl.base 20`. -/
theorem mallocngBlock20_stdMemcpyRO_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) stdMemcpyROSpec :=
  subroutine_ok_stdMemcpyRO_of_hasWords
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-- `mallocngBlockProg mmpl 20 Syscall.standard` satisfies `allocMemcpyVmSpec` at `mmpl.base 20`. -/
theorem mallocngBlock20_allocMemcpyVm_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) allocMemcpyVmSpec :=
  subroutine_ok_allocMemcpyVm_of_hasWords
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-- `mallocngBlockProg mmpl 20 Syscall.standard` satisfies `masterMemcpySpec` at `mmpl.base 20`. -/
theorem mallocngBlock20_masterMemcpy_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20) masterMemcpySpec :=
  subroutine_ok_masterMemcpy_of_hasWords
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-- `mallocngBlockProg mmpl 20 Syscall.standard` satisfies `memcpySpecK keep masterMemcpySpec` at
    `mmpl.base 20`. -/
theorem mallocngBlock20_masterMemcpyK_ok (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)
      (memcpySpecK keep masterMemcpySpec) :=
  subroutine_ok_masterMemcpyK_of_hasWords keep
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `memcpySymSpec` at `mmpl.base 20`. -/
theorem pureWordsProg20_memcpySym_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20) memcpySymSpec :=
  subroutine_ok_memcpySym_of_hasWords (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `memcpyROSymSpec` at `mmpl.base 20`. -/
theorem pureWordsProg20_memcpyROSym_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20) memcpyROSymSpec :=
  subroutine_ok_memcpyROSym_of_hasWords (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `stdMemcpySpec` at `mmpl.base 20`. -/
theorem pureWordsProg20_stdMemcpy_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20) stdMemcpySpec :=
  subroutine_ok_stdMemcpy_of_hasWords
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `stdMemcpyROSpec` at `mmpl.base 20`. -/
theorem pureWordsProg20_stdMemcpyRO_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20) stdMemcpyROSpec :=
  subroutine_ok_stdMemcpyRO_of_hasWords
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `allocMemcpyVmSpec` at `mmpl.base 20`. -/
theorem pureWordsProg20_allocMemcpyVm_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20) allocMemcpyVmSpec :=
  subroutine_ok_allocMemcpyVm_of_hasWords
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `masterMemcpySpec` at `mmpl.base 20`. -/
theorem pureWordsProg20_masterMemcpy_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20) masterMemcpySpec :=
  subroutine_ok_masterMemcpy_of_hasWords
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-- `pureWordsProg (mmpl.base 20) memcpySymWords` satisfies `memcpySpecK keep masterMemcpySpec`
    at `mmpl.base 20`. -/
theorem pureWordsProg20_masterMemcpyK_ok (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20)
      (memcpySpecK keep masterMemcpySpec) :=
  subroutine_ok_masterMemcpyK_of_hasWords keep
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

/-! ## 3. Fallback `hookMemcpy` Soundness for `masterMemcpySpec` -/

/-- `hookMemcpy` satisfies `masterMemcpySpec` for both `ro = false` (`↦ₛ`) and `ro = true` (`↦ᵣ`). -/
theorem hookMemcpy_masterMemcpy_ok : HookOk hookMemcpy masterMemcpySpec := by
  refine retHook_ok fun ⟨ro, dst, src, bs⟩ R s0 _ hpre _ => ?_
  dsimp only [masterMemcpySpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : bs.length ≤ 2 ^ 64 := hx2 ▸ Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hread : s0.mem.readBytes src bs.length = bs := by
    cases ro
    · dsimp only [memcpySrc, cond] at hmem
      have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ R) := by
        rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
      exact ((IsBlock.pointsToBytes src bs).read hsrc_front).2
    · dsimp only [memcpySrc, cond] at hmem
      have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
        rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
      exact (IsBlockRO.pointsToBytesRO src bs hlen).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only []
    rw [hx0, hx1, hx2, hread]
    exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · dsimp only [masterMemcpySpec, State.setMem]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    have hx0_ret : (hookMemcpy s0).readReg64 .x0 = dst := by
      simpa [hookMemcpy, retHook, State.readReg64_setPC, State.readReg64_setMem] using hx0
    rw [hx0, hx1, hx2, hread]
    exact ⟨⟨hx0_ret, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

/-- `hookMemcpy` satisfies `memcpySpecK keep masterMemcpySpec` for any `keep`. -/
theorem hookMemcpy_masterMemcpyK_ok (keep : BitVec 64 → Bool) :
    HookOk hookMemcpy (memcpySpecK keep masterMemcpySpec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hookMemcpy_masterMemcpy_ok x R s0 hrun hpre.2 hsp

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterMemcpySpec` -/

/-- General non-aborting ghost-reindexing frame/consequence lemma for `HookOk`. -/
theorem hookOk_map_frame_pureAbort {α β : Type} {f : State → State}
    {base : Spec α} {target : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f base)
    (hpre : ∀ y s0, target.pre y s0 ⊢ base.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → sf.symtab = s0.symtab →
      base.post (g y) s0 sf ∗ F y s0 ⊢ target.post y s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f target := by
  intro y R s0 hrun hp hsp
  have hp' : s0.mem ⊨ base.pre (g y) s0 ∗ (F y s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) (F y s0 ∗ R) s0 hrun hp' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp_sat⟩ | ⟨code, _, he_sat⟩ | ⟨_, ho_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost y s0 (f s0) rfl hsym)) hq
  · rw [hpan (g y) s0 (f s0), satisfies_pure_sepConj] at hp_sat
    exact False.elim hp_sat.1
  · rw [hex (g y) code s0 (f s0), satisfies_pure_sepConj] at he_sat
    exact False.elim he_sat.1
  · rw [hoom (g y) s0 (f s0), satisfies_pure_sepConj] at ho_sat
    exact False.elim ho_sat.1

/-- Any `HookOk f spec` weakens to `HookOk f (memcpySpecK keep spec)`. -/
theorem hookOk_memcpySpecK_of_plain (keep : BitVec 64 → Bool) {α : Type} {f : State → State}
    {spec : Spec α} (hh : HookOk f spec) :
    HookOk f (memcpySpecK keep spec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hh x R s0 hrun hpre.2 hsp

/-- Lift a ghost-reindexing frame/consequence derivation across `memcpySpecK keep`. -/
theorem hookOk_memcpySpecK_map_frame_pureAbort (keep : BitVec 64 → Bool)
    {α β : Type} {f : State → State} {base : Spec α} {target : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f (memcpySpecK keep base))
    (hpre : ∀ y s0, target.pre y s0 ⊢ base.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → sf.symtab = s0.symtab →
      base.post (g y) s0 sf ∗ F y s0 ⊢ target.post y s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (memcpySpecK keep target) := by
  refine hookOk_map_frame_pureAbort g F hh
    (fun y s0 => ?_)
    (fun y s0 sf hsf hsym => hpost y s0 sf hsf hsym)
    (fun x s0 sf => hpan x s0 sf)
    (fun x code s0 sf => hex x code s0 sf)
    (fun x s0 sf => hoom x s0 sf)
  dsimp only [memcpySpecK]
  rw [sepConj_assoc]
  exact Entails.pure_left fun hlr => Entails.pure_right hlr (hpre y s0)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f (libcMemcpySpec stk)` (`ro = false`). -/
theorem hookOk_libcMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (stk : Nat := 4096) :
    HookOk f (libcMemcpySpec stk) := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [libcMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, libcMemcpySpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep (libcMemcpySpec stk))`. -/
theorem hookOk_libcMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) (stk : Nat := 4096) :
    HookOk f (memcpySpecK keep (libcMemcpySpec stk)) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [libcMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, libcMemcpySpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f (sessionMemcpySpec stk)` (`ro = false`). -/
theorem hookOk_sessionMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (stk : Nat := 4096) :
    HookOk f (sessionMemcpySpec stk) := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep (sessionMemcpySpec stk))`. -/
theorem hookOk_sessionMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) (stk : Nat := 4096) :
    HookOk f (memcpySpecK keep (sessionMemcpySpec stk)) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f CliExt.memcpySpec` (`= sessionMemcpySpec 4096`). -/
theorem hookOk_cliMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f memcpySpec :=
  hookOk_sessionMemcpy_of_master hh 4096

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep CliExt.memcpySpec)`. -/
theorem hookOk_cliMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep memcpySpec) :=
  hookOk_sessionMemcpyK_of_master keep hh 4096

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f memcpyRegionSpec` (`ro = false`). -/
theorem hookOk_memcpyRegion_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f memcpyRegionSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (sepConj_emp _).symm
  · dsimp only [masterMemcpySpec, memcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep memcpyRegionSpec)`. -/
theorem hookOk_memcpyRegionK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep memcpyRegionSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (sepConj_emp _).symm
  · dsimp only [masterMemcpySpec, memcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f sessionMemcpyRegionSpec` (`ro = false`). -/
theorem hookOk_sessionMemcpyRegion_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f sessionMemcpyRegionSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (sepConj_emp _).symm
  · dsimp only [masterMemcpySpec, sessionMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep sessionMemcpyRegionSpec)`. -/
theorem hookOk_sessionMemcpyRegionK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep sessionMemcpyRegionSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (sepConj_emp _).symm
  · dsimp only [masterMemcpySpec, sessionMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f framelessMemcpySpec` (`ro = false`). -/
theorem hookOk_framelessMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f framelessMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [framelessMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, framelessMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep framelessMemcpySpec)`. -/
theorem hookOk_framelessMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep framelessMemcpySpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [framelessMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, framelessMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to
    `HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec` (`ro = true`). -/
theorem hookOk_sessionMemcpyRegionRO_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec, masterMemcpySpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)`. -/
theorem hookOk_sessionMemcpyRegionROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec, masterMemcpySpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f (memcpyROExtSpec stk)` (`ro = true`). -/
theorem hookOk_memcpyROExt_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (stk : Nat := 16384) :
    HookOk f (memcpyROExtSpec stk) := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [memcpyROExtSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, memcpyROExtSpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep (memcpyROExtSpec stk))`. -/
theorem hookOk_memcpyROExtK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) (stk : Nat := 16384) :
    HookOk f (memcpySpecK keep (memcpyROExtSpec stk)) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [memcpyROExtSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, memcpyROExtSpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to `HookOk f CliExt.memcpyROSpec` (`ro = true`). -/
theorem hookOk_cliMemcpyRO_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f memcpyROSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp 4096) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · simp only [memcpyROSpec, CryptoVerification.SignalSession.CliExt.withStack,
      CryptoVerification.SignalSession.CliExt.memHookStack, masterMemcpySpec, memcpySrc, cond,
      sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · simp only [masterMemcpySpec, memcpyROSpec, CryptoVerification.SignalSession.CliExt.withStack,
      CryptoVerification.SignalSession.CliExt.memHookStack, memcpySrc, cond, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep CliExt.memcpyROSpec)`. -/
theorem hookOk_cliMemcpyROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep memcpyROSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp 4096) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · simp only [memcpyROSpec, CryptoVerification.SignalSession.CliExt.withStack,
      CryptoVerification.SignalSession.CliExt.memHookStack, masterMemcpySpec, memcpySrc, cond,
      sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · simp only [masterMemcpySpec, memcpyROSpec, CryptoVerification.SignalSession.CliExt.withStack,
      CryptoVerification.SignalSession.CliExt.memHookStack, memcpySrc, cond, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` to
    `HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K` (`ro = true`). -/
theorem hookOk_sessionMemcpyRO4K_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K :=
  hookOk_sessionMemcpyRegionRO_of_master hh

/-- Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HookOk f (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K)`. -/
theorem hookOk_sessionMemcpyRO4KK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K) :=
  hookOk_sessionMemcpyRegionROK_of_master keep hh

/-- Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` to flat
    `DefsBudget.framelessMemcpyBudgetSpec`. -/
theorem hookOk_framelessMemcpyBudgetFlat_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf _ => ?_)
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hvm s0⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_framelessMemcpyBudgetFlat_of_master`. -/
theorem hookOk_framelessMemcpyBudgetFlatK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      (memcpySpecK keep
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf _ => ?_)
  · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hvm s0⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` to
    `Hooks4KBudget.sessionMemcpyROSpec4K` (`ro = true`). -/
theorem hookOk_sessionMemcpyRO4KBudget_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K := by
  intro x R s0 hrun hpre hsp
  rcases hookOk_sessionMemcpyRO4K_of_master hh x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K,
      withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm s0, hpost⟩
  · exact Or.inr hrest

/-- `K`-narrowed counterpart of `hookOk_sessionMemcpyRO4KBudget_of_master`. -/
theorem hookOk_sessionMemcpyRO4KBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      (memcpySpecK keep LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K) := by
  intro x R s0 hrun hpre hsp
  rcases hookOk_sessionMemcpyRO4KK_of_master keep hh x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [memcpySpecK,
      LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K, withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm s0, hpost⟩
  · exact Or.inr hrest

/-- Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` + `oracle` preservation to
    `ConcatBudgetAux.framelessMemcpyAcpSpec` (`AllocCallPreserved ∧ VmPreserved`, `ro = false`). -/
theorem hookOk_framelessMemcpyAcp_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_framelessMemcpyAcp_of_master`. -/
theorem hookOk_framelessMemcpyAcpK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f
      (memcpySpecK keep
        LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` + `oracle` preservation to
    `ConcatBudgetAux.sessionMemcpyRegionROSpec` (`AllocCallPreserved ∧ VmPreserved`, `ro = true`). -/
theorem hookOk_sessionMemcpyRegionROAcp_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_sessionMemcpyRegionROAcp_of_master`. -/
theorem hookOk_sessionMemcpyRegionROAcpK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f
      (memcpySpecK keep
        LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec,
      memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` + `oracle` preservation to
    `allocMemcpyVmSpec` (`AllocCallPreserved ∧ VmPreserved`, `ro = false`). -/
theorem hookOk_allocMemcpyVm_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f allocMemcpyVmSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [allocMemcpyVmSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, hlt⟩ =>
      have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
        rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      Entails.pure_right ⟨hx0, hx1, hx2_nat⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec, allocMemcpyVmSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_allocMemcpyVm_of_master`. -/
theorem hookOk_allocMemcpyVmK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f (memcpySpecK keep allocMemcpyVmSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [allocMemcpyVmSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, hlt⟩ =>
      have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
        rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      Entails.pure_right ⟨hx0, hx1, hx2_nat⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec, allocMemcpyVmSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- `memcpySpecK keep` commutes definitionally with `.keepsFs`, `withVmPreserved`, and
    `withOomPoolPreserved`. -/
theorem memcpySpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (memcpySpecK keep spec).keepsFs = memcpySpecK keep spec.keepsFs := rfl

theorem memcpySpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (memcpySpecK keep spec) = memcpySpecK keep (withVmPreserved spec) := rfl

theorem memcpySpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (memcpySpecK keep spec) =
      memcpySpecK keep (withOomPoolPreserved spec) := rfl

theorem memcpySpecK_sessionMemcpyBudget (keep : BitVec 64 → Bool) (stk : Nat := 4096) :
    withVmPreserved (memcpySpecK keep (sessionMemcpySpec stk)) =
      memcpySpecK keep (sessionMemcpyBudgetSpec stk) := rfl

theorem memcpySpecK_sessionMemcpyRegionBudget (keep : BitVec 64 → Bool) :
    withVmPreserved (memcpySpecK keep sessionMemcpyRegionSpec) =
      memcpySpecK keep sessionMemcpyRegionBudgetSpec := rfl

theorem memcpySpecK_framelessMemcpyBudget (keep : BitVec 64 → Bool) :
    withVmPreserved (memcpySpecK keep framelessMemcpySpec) =
      memcpySpecK keep framelessMemcpyBudgetSpec := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
