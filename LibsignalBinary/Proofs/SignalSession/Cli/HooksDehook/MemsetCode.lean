/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import VerifiedLibraries.Musl.Proofs.MemsetSym
public import VerifiedLibraries.Musl.Proofs.MemOps
public import VerifiedLibraries.Mallocng.Spec.Top
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import

/-!
# Region-Local `memset` Code Verification & Master Spec (`HooksDehook.MemsetCode`)

Design-independent core Step 1 + spec-refinement combinators for de-hooking `memset`
(`VerifiedLibraries.mallocngLib` block 21, `mallocng_blk21_memset`, 65 words = 260 bytes):

1. **Exact word identity at `mallocngLib` block 21**:
   `mallocng_blk21_memset` has `relocs = []` and its 65 little-endian words equal
   `VerifiedLibraries.Musl.memsetWordsSym` (`mallocng_blk21_checkSegment_memsetWordsSym`,
   `mallocngBlockProg21_hasWords`, `pureWordsProg_memset_hasWords`).
2. **Region-local `subroutine_ok` on any hook-free program holding the words**:
   `subroutine_ok P_sub entry memsetSymSpec`, `stdMemsetSpec`, `masterMemsetSpec`, and
   `memsetSpecK keep masterMemsetSpec` for any `P_sub` with `P_sub.hasWords entry memsetWordsSym`,
   instantiated at `mallocngBlockProg mmpl 21 svc` and `pureWordsProg (mmpl.base 21) memsetWordsSym`.
3. **Strip-invariant master spec (`masterMemsetSpec`) and `K`-narrowing (`memsetSpecK`)**:
   `masterMemsetSpec` records the 7 memory-permission-independent state equalities
   (`MemsetStatePreserved`: `fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`,
   `physMemAvail`) so `SpecStripSInvariant keep masterMemsetSpec` holds definitionally for any
   `keep : BitVec 64 → Bool`, while `VmPreserved` (including `mem.perm`) is proved pointwise on the
   ghost hook in `MemsetGhost.lean`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (StdStatePreserved stdMemsetSpec)
open VerifiedLibraries (mallocngWordsLE mallocng_blk21_memset mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym memsetSymSpec memset_codeAt_ok_sym stdMemset_ok_of_hasWords)
open CryptoVerification.LibsignalTripleRatchet (
  sessionMemsetRegionSpec sessionMemsetSpec
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemsetRegionBudgetSpec sessionMemsetBudgetSpec
)
open CryptoVerification.SignalSession.CliExt (memsetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)

/-! ## 1. Master `memset` Specification & Wrappers -/

/-- Non-memory process/VM state fields preserved across real `memset` (`blk21`) and `hookMemset`.
    Separating `mem.perm` out of `post` ensures `SpecStripSInvariant keep masterMemsetSpec` holds
    for arbitrary `keep : BitVec 64 → Bool`; `VmPreserved` (`mem.perm` + `brkStart`/`brk`/
    `tpidrEl0`/`physMemAvail`) is established as a pointwise state theorem on the ghost hook. -/
@[expose] def MemsetStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
    sf.trace = s0.trace ∧
    sf.tpidrEl0 = s0.tpidrEl0 ∧
    sf.sigActions = s0.sigActions ∧
    sf.brk = s0.brk ∧
    sf.brkStart = s0.brkStart ∧
    sf.physMemAvail = s0.physMemAvail

theorem MemsetStatePreserved.refl (s : State) : MemsetStatePreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MemsetStatePreserved.of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : MemsetStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Master separation-logic contract for `memset(dst, c, len)`: requires zero stack bytes
    (`memRegion dst len` only), returns `dst` in `x0`, writes `List.replicate len byteVal` at `dst`,
    preserves `MemsetStatePreserved`, and never panics, exits, or OOMs. -/
@[expose] def masterMemsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, byteVal, len) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      (s0.readReg32 .x1).truncate 8 = byteVal ∧
      (s0.readReg64 .x2).toNat = len⌝ ∗
      memRegion dst len
  post := fun (dst, byteVal, len) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ MemsetStatePreserved s0 sf⌝ ∗
      (dst ↦ₛ List.replicate len byteVal)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `K`-route precondition narrowing: conjoins `⌜keep (s.readReg64 .lr) = false⌝` to `spec.pre`,
    leaving `post`, `onPanic`, `onExit`, and `onOom` unchanged (mirrors `h2k_*SpecK` on the
    `K`-ghost route). -/
@[expose] def memsetSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

/-! ## 2. `mallocngLib` Block 21 Word Identity & Region-Local `subroutine_ok` -/

/-- `mallocngLib` block 21 is `mallocng_blk21_memset` (`260` bytes = `65` words, `relocs = []`). -/
theorem mallocngLib_block21_eq :
    mallocngLib.blocks[21]? = some mallocng_blk21_memset := by
  simp only [mallocngLib, List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- `(mallocngLib.blockLib 21).text` is `mallocng_blk21_memset`. -/
theorem mallocngLib_blockLib21_text :
    (mallocngLib.blockLib 21).text = mallocng_blk21_memset :=
  mallocngLib.blockLib_text (by decide : 21 < mallocngLib.blocks.length)

/-- Byte-length of `mallocng_blk21_memset` is `260` (`65` AArch64 words). -/
theorem mallocng_blk21_code_length :
    mallocng_blk21_memset.code.length = 260 := by
  decide +kernel

/-- `memsetWordsSym` has `65` words (`260` bytes). -/
theorem memsetWordsSym_length :
    memsetWordsSym.length = 65 := rfl

/-- `mallocng_blk21_memset.code` is definitionally `mallocngWordsLE memsetWordsSym`. -/
theorem mallocng_blk21_code_eq_memsetWordsSym :
    mallocng_blk21_memset.code = mallocngWordsLE memsetWordsSym := rfl

/-- `mallocng_blk21_memset.code` is byte-identical to `(Program.ofWords 0#64 memsetWordsSym).code`. -/
theorem mallocng_blk21_code_eq_ofWords :
    mallocng_blk21_memset.code = (Program.ofWords 0#64 memsetWordsSym).code := by
  decide +kernel

private theorem patchedWord_of_relocs_nil {blk : Obj.CodeBlock} (hrel : blk.relocs = [])
    (pl : Obj.Placement) (off : Nat) :
    blk.patchedWord pl off = blk.wordAt off := by
  simp [Obj.CodeBlock.patchedWord, Obj.CodeBlock.relocAt?, hrel]

private theorem patched_indep_of_relocs_nil {blk : Obj.CodeBlock} (hrel : blk.relocs = [])
    (pl1 pl2 : Obj.Placement) :
    blk.patched pl1 = blk.patched pl2 := by
  simp [Obj.CodeBlock.patched, patchedWord_of_relocs_nil hrel]

private theorem mallocng_blk21_patched_zero :
    mallocng_blk21_memset.patched { base := 0#64, ρ := fun _ => 0#64 } =
      (Program.ofWords 0#64 memsetWordsSym).code := by
  decide +kernel

private theorem ofWords_memset_readWordOff_all :
    ((List.range memsetWordsSym.length).all fun i =>
      (Program.ofWords 0#64 memsetWordsSym).readWordOff (4 * i) == memsetWordsSym[i]?) = true := by
  decide +kernel

private theorem ofWords_code_indep (base : BitVec 64) (words : List (BitVec 32)) :
    (Program.ofWords base words).code = (Program.ofWords 0#64 words).code := rfl

private theorem readWordOff_eq_of_code_eq {P Q : Program} (h : P.code = Q.code) (off : Nat) :
    P.readWordOff off = Q.readWordOff off := by
  unfold Program.readWordOff
  rw [h]

/-- `pureWordsProg base memsetWordsSym` holds `memsetWordsSym` at `base` for any `base`. -/
theorem pureWordsProg_memset_hasWords (base : BitVec 64) :
    (pureWordsProg base memsetWordsSym).hasWords base memsetWordsSym := by
  refine pureWordsProg_hasWords (by decide) ?_
  have hcode : (pureWordsProg base memsetWordsSym).code =
      (Program.ofWords 0#64 memsetWordsSym).code := rfl
  simp only [readWordOff_eq_of_code_eq hcode]
  exact ofWords_memset_readWordOff_all

private theorem blockProgram_code_eq (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (i : Nat)
    (externs overrides : String → Option (State → State)) (svc : State → State) :
    (lib.blockProgram mpl i externs overrides svc).code =
      (lib.blockLib i).text.patched (lib.blockPlacement mpl i) := rfl

private theorem mallocng_blk21_relocs_nil :
    mallocng_blk21_memset.relocs = [] := by
  decide +kernel

/-- `mallocngBlockProg mmpl 21 svc` holds `memsetWordsSym` at `mmpl.base 21` for any placement
    `mmpl` and syscall handler `svc` (since `mallocng_blk21_memset.relocs = []`). -/
theorem mallocngBlockProg21_hasWords (mmpl : Obj.MultiPlacement) (svc : State → State) :
    (mallocngBlockProg mmpl 21 svc).hasWords (mmpl.base 21) memsetWordsSym := by
  unfold Program.hasWords Program.hasWordsOff
  have hbase : (mallocngBlockProg mmpl 21 svc).base = mmpl.base 21 := rfl
  have hsub : (mmpl.base 21 - (mallocngBlockProg mmpl 21 svc).base).toNat = 0 := by
    rw [hbase]; simp
  have hcode : (mallocngBlockProg mmpl 21 svc).code =
      (Program.ofWords 0#64 memsetWordsSym).code :=
    (blockProgram_code_eq mallocngLib mmpl 21 _ _ svc).trans <|
      (congrArg (Obj.CodeBlock.patched · (mallocngLib.blockPlacement mmpl 21))
        mallocngLib_blockLib21_text).trans <|
      (patched_indep_of_relocs_nil mallocng_blk21_relocs_nil _
        { base := 0#64, ρ := fun _ => 0#64 }).trans mallocng_blk21_patched_zero
  rw [hsub, Nat.zero_add]
  refine ⟨by decide, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hmem : i ∈ List.range memsetWordsSym.length := List.mem_range.mpr hi
  have hall := beq_iff_eq.mp (List.all_eq_true.mp ofWords_memset_readWordOff_all i hmem)
  rw [Nat.zero_add, readWordOff_eq_of_code_eq hcode, hall, List.getElem?_eq_getElem hi]

/-- `mallocngBlockProg mmpl 21 svc` has no external hooks (`externAt? pc = none`). -/
theorem mallocngBlockProg21_externAt_none (mmpl : Obj.MultiPlacement) (svc : State → State)
    (pc : BitVec 64) :
    (mallocngBlockProg mmpl 21 svc).externAt? pc = none :=
  mallocngLib.externAt?_blockProgram_none mmpl 21 pc

/-- `pureWordsProg base words` has no external hooks (`externAt? pc = none`). -/
theorem pureWordsProg_externAt_none (base : BitVec 64) (words : List (BitVec 32))
    (pc : BitVec 64) :
    (pureWordsProg base words).externAt? pc = none := by
  unfold Program.externAt? pureWordsProg Program.ofWords
  rfl

/-- Equivalence helper converting `masterMemsetSpec.pre` to `stdMemsetSpec.pre` on any frame `R`. -/
theorem stdMemset_pre_of_masterMemset_pre {x : BitVec 64 × BitVec 8 × Nat} {R : SepProp}
    {s0 : State} (hp : s0.mem ⊨ masterMemsetSpec.pre x s0 ∗ R) :
    s0.mem ⊨ stdMemsetSpec.pre x s0 ∗ R := by
  rcases x with ⟨dst, byteVal, len⟩
  dsimp only [masterMemsetSpec, stdMemsetSpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : len < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2' : s0.readReg64 .x2 = BitVec.ofNat 64 len := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact ⟨⟨hx0, hx1, hx2', hlt⟩, hm⟩

/-- Region-local `subroutine_ok` for `memsetSymSpec` on any `P_sub` holding `memsetWordsSym`. -/
theorem subroutine_ok_memsetSym_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hwords : P_sub.hasWords entry memsetWordsSym) :
    subroutine_ok P_sub entry memsetSymSpec :=
  memset_codeAt_ok_sym P_sub entry hwords

/-- Region-local `subroutine_ok` for `stdMemsetSpec` on any hook-free `P_sub` holding
    `memsetWordsSym`. -/
theorem subroutine_ok_stdMemset_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memsetWordsSym) :
    subroutine_ok P_sub entry stdMemsetSpec :=
  stdMemset_ok_of_hasWords P_sub entry hsub_no hwords

/-- Region-local `subroutine_ok` for `masterMemsetSpec` on any hook-free `P_sub` holding
    `memsetWordsSym`. -/
theorem subroutine_ok_masterMemset_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memsetWordsSym) :
    subroutine_ok P_sub entry masterMemsetSpec := by
  refine subroutine_ok_mono (stdMemset_ok_of_hasWords P_sub entry hsub_no hwords)
    (fun x R s0 hp => stdMemset_pre_of_masterMemset_pre hp)
    (fun ⟨dst, byteVal, len⟩ R s0 sf hq => ?_)
  dsimp only [stdMemsetSpec, masterMemsetSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, MemsetStatePreserved.of_stdStatePreserved hq.1.2⟩, hq.2⟩

/-- Region-local `subroutine_ok` for `memsetSpecK keep masterMemsetSpec` on any hook-free `P_sub`
    holding `memsetWordsSym`. -/
theorem subroutine_ok_masterMemsetK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memsetWordsSym) :
    subroutine_ok P_sub entry (memsetSpecK keep masterMemsetSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
    (fun _ R s0 hp => ?_)
    (fun _ R s0 sf hq => hq)
  dsimp only [memsetSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- `mallocngBlockProg mmpl 21 svc` satisfies `memsetSymSpec` at `mmpl.base 21`. -/
theorem mallocngBlock21_memsetSym_ok (mmpl : Obj.MultiPlacement)
    (svc : State → State := Syscall.standard) :
    subroutine_ok (mallocngBlockProg mmpl 21 svc) (mmpl.base 21) memsetSymSpec :=
  subroutine_ok_memsetSym_of_hasWords (mallocngBlockProg21_hasWords mmpl svc)

/-- `mallocngBlockProg mmpl 21 Syscall.standard` satisfies `stdMemsetSpec` at `mmpl.base 21`. -/
theorem mallocngBlock21_stdMemset_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21) stdMemsetSpec :=
  subroutine_ok_stdMemset_of_hasWords
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

/-- `mallocngBlockProg mmpl 21 Syscall.standard` satisfies `masterMemsetSpec` at `mmpl.base 21`. -/
theorem mallocngBlock21_masterMemset_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21) masterMemsetSpec :=
  subroutine_ok_masterMemset_of_hasWords
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

/-- `mallocngBlockProg mmpl 21 Syscall.standard` satisfies `memsetSpecK keep masterMemsetSpec` at
    `mmpl.base 21`. -/
theorem mallocngBlock21_masterMemsetK_ok (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) :
    subroutine_ok (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)
      (memsetSpecK keep masterMemsetSpec) :=
  subroutine_ok_masterMemsetK_of_hasWords keep
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

/-- `pureWordsProg (mmpl.base 21) memsetWordsSym` satisfies `memsetSymSpec` at `mmpl.base 21`. -/
theorem pureWordsProg21_memsetSym_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 21) memsetWordsSym) (mmpl.base 21) memsetSymSpec :=
  subroutine_ok_memsetSym_of_hasWords (pureWordsProg_memset_hasWords (mmpl.base 21))

/-- `pureWordsProg (mmpl.base 21) memsetWordsSym` satisfies `stdMemsetSpec` at `mmpl.base 21`. -/
theorem pureWordsProg21_stdMemset_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 21) memsetWordsSym) (mmpl.base 21) stdMemsetSpec :=
  subroutine_ok_stdMemset_of_hasWords
    (pureWordsProg_externAt_none (mmpl.base 21) memsetWordsSym)
    (pureWordsProg_memset_hasWords (mmpl.base 21))

/-- `pureWordsProg (mmpl.base 21) memsetWordsSym` satisfies `masterMemsetSpec` at `mmpl.base 21`. -/
theorem pureWordsProg21_masterMemset_ok (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 21) memsetWordsSym) (mmpl.base 21) masterMemsetSpec :=
  subroutine_ok_masterMemset_of_hasWords
    (pureWordsProg_externAt_none (mmpl.base 21) memsetWordsSym)
    (pureWordsProg_memset_hasWords (mmpl.base 21))

/-- `pureWordsProg (mmpl.base 21) memsetWordsSym` satisfies `memsetSpecK keep masterMemsetSpec`
    at `mmpl.base 21`. -/
theorem pureWordsProg21_masterMemsetK_ok (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) :
    subroutine_ok (pureWordsProg (mmpl.base 21) memsetWordsSym) (mmpl.base 21)
      (memsetSpecK keep masterMemsetSpec) :=
  subroutine_ok_masterMemsetK_of_hasWords keep
    (pureWordsProg_externAt_none (mmpl.base 21) memsetWordsSym)
    (pureWordsProg_memset_hasWords (mmpl.base 21))

/-! ## 3. Fallback `hookMemset` Soundness for `masterMemsetSpec` -/

/-- `hookMemset` satisfies `masterMemsetSpec` (note `len = (s0.readReg64 .x2).toNat < 2 ^ 64` holds
    without any stack-frame size hypothesis). -/
theorem hookMemset_masterMemset_ok : HookOk hookMemset masterMemsetSpec := by
  refine retHook_ok fun ⟨dst, byteVal, len⟩ R s0 _ hpre _ => ?_
  simp only [masterMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : (List.replicate len byteVal).length ≤ 2 ^ 64 := by
    rw [List.length_replicate, ← hx2]
    exact Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hmem_rep : s0.mem ⊨ memRegion dst (List.replicate len byteVal).length ∗ R := by
    rwa [List.length_replicate]
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2]
    exact keepsFrozen_writeBytes_of_memRegion (List.replicate len byteVal) hlen hmem_rep
  · dsimp only [masterMemsetSpec, State.setMem]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hx0_ret : (hookMemset s0).readReg64 .x0 = dst := by
      simpa [hookMemset, retHook, State.readReg64_setPC, State.readReg64_setMem] using hx0
    rw [hx0, hx1, hx2]
    exact ⟨⟨hx0_ret, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      satisfies_writeBytes (List.replicate len byteVal) hlen hmem_rep⟩

/-- `hookMemset` satisfies `memsetSpecK keep masterMemsetSpec` for any `keep`. -/
theorem hookMemset_masterMemsetK_ok (keep : BitVec 64 → Bool) :
    HookOk hookMemset (memsetSpecK keep masterMemsetSpec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hookMemset_masterMemset_ok x R s0 hrun hpre.2 hsp

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterMemsetSpec` -/

/-- General non-aborting frame/consequence lemma for `HookOk` from `masterMemsetSpec` (or any spec
    with `onPanic = onExit = onOom = ⌜False⌝`). -/
theorem hookOk_frame_pureAbort {α : Type} {f : State → State} {base target : Spec α}
    (F : α → State → SepProp)
    (hh : HookOk f base)
    (hpre : ∀ x s0, target.pre x s0 ⊢ base.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, base.post x s0 sf ∗ F x s0 ⊢ target.post x s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f target := by
  intro x R s0 hrun hp hsp
  have hp' : s0.mem ⊨ base.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  obtain ⟨hkf, hsym, hout⟩ := hh x (F x s0 ∗ R) s0 hrun hp' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp_sat⟩ | ⟨code, _, he_sat⟩ | ⟨_, ho_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 (f s0))) hq
  · rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp_sat
    exact False.elim hp_sat.1
  · rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he_sat
    exact False.elim he_sat.1
  · rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho_sat
    exact False.elim ho_sat.1

/-- Any `HookOk f spec` weakens to `HookOk f (memsetSpecK keep spec)`. -/
theorem hookOk_memsetSpecK_of_plain (keep : BitVec 64 → Bool) {α : Type} {f : State → State}
    {spec : Spec α} (hh : HookOk f spec) :
    HookOk f (memsetSpecK keep spec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hh x R s0 hrun hpre.2 hsp

/-- Lift a frame/consequence derivation across `memsetSpecK keep`. -/
theorem hookOk_memsetSpecK_frame_pureAbort (keep : BitVec 64 → Bool)
    {α : Type} {f : State → State} {base target : Spec α}
    (F : α → State → SepProp)
    (hh : HookOk f (memsetSpecK keep base))
    (hpre : ∀ x s0, target.pre x s0 ⊢ base.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, base.post x s0 sf ∗ F x s0 ⊢ target.post x s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (memsetSpecK keep target) := by
  refine hookOk_frame_pureAbort F hh
    (fun x s0 => ?_)
    (fun x s0 sf => hpost x s0 sf)
    (fun x s0 sf => hpan x s0 sf)
    (fun x code s0 sf => hex x code s0 sf)
    (fun x s0 sf => hoom x s0 sf)
  dsimp only [memsetSpecK]
  rw [sepConj_assoc]
  exact Entails.pure_left fun hlr => Entails.pure_right hlr (hpre x s0)

/-- Lift `HookOk f masterMemsetSpec` to `HookOk f (libcMemsetSpec stk)` for any `stk : Nat`. -/
theorem hookOk_libcMemset_of_master {f : State → State}
    (hh : HookOk f masterMemsetSpec) (stk : Nat := 4096) :
    HookOk f (libcMemsetSpec stk) := by
  refine hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨ptr, c, len⟩ s0 => by
      dsimp only [libcMemsetSpec, masterMemsetSpec]
      exact Entails.of_eq (sepConj_assoc _ _ _).symm)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  dsimp only [masterMemsetSpec, libcMemsetSpec]
  rw [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f (memsetSpecK keep masterMemsetSpec)` to `HookOk f (memsetSpecK keep (libcMemsetSpec stk))`. -/
theorem hookOk_libcMemsetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memsetSpecK keep masterMemsetSpec)) (stk : Nat := 4096) :
    HookOk f (memsetSpecK keep (libcMemsetSpec stk)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨ptr, c, len⟩ s0 => by
      dsimp only [libcMemsetSpec, masterMemsetSpec]
      exact Entails.of_eq (sepConj_assoc _ _ _).symm)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  dsimp only [masterMemsetSpec, libcMemsetSpec]
  rw [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f masterMemsetSpec` to `HookOk f (sessionMemsetSpec stk)` for any `stk : Nat`. -/
theorem hookOk_sessionMemset_of_master {f : State → State}
    (hh : HookOk f masterMemsetSpec) (stk : Nat := 4096) :
    HookOk f (sessionMemsetSpec stk) := by
  refine hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨ptr, c, len⟩ s0 => by
      dsimp only [sessionMemsetSpec, libcMemsetSpec, masterMemsetSpec]
      exact Entails.of_eq (sepConj_assoc _ _ _).symm)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  dsimp only [masterMemsetSpec, sessionMemsetSpec]
  rw [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memsetSpecK keep masterMemsetSpec)` to `HookOk f (memsetSpecK keep (sessionMemsetSpec stk))`. -/
theorem hookOk_sessionMemsetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memsetSpecK keep masterMemsetSpec)) (stk : Nat := 4096) :
    HookOk f (memsetSpecK keep (sessionMemsetSpec stk)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨ptr, c, len⟩ s0 => by
      dsimp only [sessionMemsetSpec, libcMemsetSpec, masterMemsetSpec]
      exact Entails.of_eq (sepConj_assoc _ _ _).symm)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  dsimp only [masterMemsetSpec, sessionMemsetSpec]
  rw [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemsetSpec` to `HookOk f CliExt.memsetSpec` (`= sessionMemsetSpec 4096`). -/
theorem hookOk_cliMemset_of_master {f : State → State}
    (hh : HookOk f masterMemsetSpec) :
    HookOk f memsetSpec :=
  hookOk_sessionMemset_of_master hh 4096

/-- Lift `HookOk f (memsetSpecK keep masterMemsetSpec)` to `HookOk f (memsetSpecK keep CliExt.memsetSpec)`. -/
theorem hookOk_cliMemsetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memsetSpecK keep masterMemsetSpec)) :
    HookOk f (memsetSpecK keep memsetSpec) :=
  hookOk_sessionMemsetK_of_master keep hh 4096

/-- Lift `HookOk f masterMemsetSpec` to `HookOk f memsetRegionSpec`. -/
theorem hookOk_memsetRegion_of_master {f : State → State}
    (hh : HookOk f masterMemsetSpec) :
    HookOk f memsetRegionSpec := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun ⟨ptr, c, len⟩ s0 => ?_)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  · dsimp only [memsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [memsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f (memsetSpecK keep masterMemsetSpec)` to `HookOk f (memsetSpecK keep memsetRegionSpec)`. -/
theorem hookOk_memsetRegionK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memsetSpecK keep masterMemsetSpec)) :
    HookOk f (memsetSpecK keep memsetRegionSpec) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp) hh
    (fun ⟨ptr, c, len⟩ s0 => ?_)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  · dsimp only [memsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [memsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f masterMemsetSpec` to `HookOk f sessionMemsetRegionSpec`. -/
theorem hookOk_sessionMemsetRegion_of_master {f : State → State}
    (hh : HookOk f masterMemsetSpec) :
    HookOk f sessionMemsetRegionSpec := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun ⟨ptr, c, len⟩ s0 => ?_)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  · dsimp only [sessionMemsetRegionSpec, memsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [sessionMemsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memsetSpecK keep masterMemsetSpec)` to `HookOk f (memsetSpecK keep sessionMemsetRegionSpec)`. -/
theorem hookOk_sessionMemsetRegionK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memsetSpecK keep masterMemsetSpec)) :
    HookOk f (memsetSpecK keep sessionMemsetRegionSpec) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp) hh
    (fun ⟨ptr, c, len⟩ s0 => ?_)
    (fun ⟨ptr, c, len⟩ s0 sf => ?_)
  · dsimp only [sessionMemsetRegionSpec, memsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [sessionMemsetRegionSpec, masterMemsetSpec]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

private theorem readReg32_truncate8_eq (s : State) (r : Reg) :
    (s.readReg32 r).truncate 8 = (s.readReg64 r).truncate 8 := by
  change ((s.readReg64 r).setWidth 32).setWidth 8 = (s.readReg64 r).setWidth 8
  exact BitVec.setWidth_setWidth_of_le (s.readReg64 r) (by decide : 8 ≤ 32)

/-- Lift `HookOk f masterMemsetSpec` to `HookOk f (HkdfExt.session2MemsetExternSpec stk)` for any `stk : Nat`. -/
theorem hookOk_session2MemsetExtern_of_master {f : State → State}
    (hh : HookOk f masterMemsetSpec) (stk : Nat := 16384) :
    HookOk f (session2MemsetExternSpec stk) := by
  refine hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, val, n⟩ s0 => ?_)
    (fun ⟨dst, val, n⟩ s0 sf => ?_)
  · dsimp only [session2MemsetExternSpec, masterMemsetSpec]
    rw [sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2⟩ =>
      Entails.pure_right ⟨hx0, (readReg32_truncate8_eq s0 .x1).trans hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemsetSpec, session2MemsetExternSpec]
    rw [sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f (memsetSpecK keep masterMemsetSpec)` to
    `HookOk f (memsetSpecK keep (HkdfExt.session2MemsetExternSpec stk))`. -/
theorem hookOk_session2MemsetExternK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memsetSpecK keep masterMemsetSpec)) (stk : Nat := 16384) :
    HookOk f (memsetSpecK keep (session2MemsetExternSpec stk)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ s0 => stackAt s0.sp stk) hh
    (fun ⟨dst, val, n⟩ s0 => ?_)
    (fun ⟨dst, val, n⟩ s0 sf => ?_)
  · dsimp only [session2MemsetExternSpec, masterMemsetSpec]
    rw [sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2⟩ =>
      Entails.pure_right ⟨hx0, (readReg32_truncate8_eq s0 .x1).trans hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemsetSpec, session2MemsetExternSpec]
    rw [sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ => Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/--Notice `memsetSpecK keep` commutes definitionally with `.keepsFs`, `withVmPreserved`, and
   `withOomPoolPreserved` (which only touch `post`), so `HookOk.keepsFs`, `hookOk_withVmPreserved`,
   and `hookOk_withOomPoolPreserved` apply identically to `memsetSpecK keep spec`. -/
theorem memsetSpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (memsetSpecK keep spec).keepsFs = memsetSpecK keep spec.keepsFs := rfl

theorem memsetSpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (memsetSpecK keep spec) = memsetSpecK keep (withVmPreserved spec) := rfl

theorem memsetSpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (memsetSpecK keep spec) =
      memsetSpecK keep (withOomPoolPreserved spec) := rfl

theorem memsetSpecK_sessionMemsetBudget (keep : BitVec 64 → Bool) (stk : Nat := 4096) :
    withVmPreserved (memsetSpecK keep (sessionMemsetSpec stk)) =
      memsetSpecK keep (sessionMemsetBudgetSpec stk) := rfl

theorem memsetSpecK_sessionMemsetRegionBudget (keep : BitVec 64 → Bool) :
    withVmPreserved (memsetSpecK keep sessionMemsetRegionSpec) =
      memsetSpecK keep sessionMemsetRegionBudgetSpec := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
