/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Musl.Proofs.MemOps
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsMusl
import ProofLib.Process
import ProofLib.Process.FastParse
import ProofLib.Process.FsLemmas
meta import ProofLib
meta import ProofLib.ProgramReflection

/-!
# `mallocng` Keep-Sub Bounds and Deterministic `open` Helpers

**Checked by Lean.**

Proves `mallocngLib` `hole2_keepSub` bounds, `RustCliAllocBudgetEntriesBase` instantiation,
`memcpy` and `__rust_no_alloc_shim_is_unstable_v2` `subroutine_ok` lemmas, and deterministic
`muslOpenRdonlyDetSpec` on `f3TrialRxProg` for `ElfSlicesPqOomH2FirstStopReads`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper

open Arm64 (GhostName Program subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage)
open LibsignalBinary.Heap (RustCliAllocBudgetEntriesBase)
open LibsignalBinary.Heap.Fine (f3RdlAddrs f3StubAddrs fineCostModel)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (muslOpenRdonlyDetSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)

abbrev h2fsreads_hookStack : Nat := extHookStack

/-- Guard set `[0x469000, 0x46f000)` (`seg[2]`, `rfl` with `hole2_keepSub`). -/
abbrev h2fsreads_keepSub (a : BitVec 64) : Bool :=
  decide (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000)

/-- Guard set `[0x4686a0, 0x468724) ∪ [0x469000, 0x46f000)` (`rfl` with `hole2_keep`). -/
abbrev h2fsreads_keep (a : BitVec 64) : Bool :=
  decide ((0x4686a0 ≤ a.toNat ∧ a.toNat < 0x468724) ∨ (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000))

abbrev h2fsreads_emptyProg : Program :=
  Program.ofSvc Arm64.Syscall.standard

section H2FsReadsHelperPriv

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib.SepLogic SepProp
open VerifiedLibraries.Musl (stdMemcpy_ok_of_hasWords)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng ProgContainsMultiLib)
open VerifiedLibraries.RustStd (RustStdThunkCode mallocngPlacedCAddrs rustStdThunkCode_of_wordTree)
open CryptoVerification.SignalSession (PathOk blockingAncestor? pathComps)
open LibsignalBinary.Heap.Fine (f3MallocngMpl f3RxWordCount f3StdLayout)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVm_ret_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudgetEntries fineHookRustCliAllocBudgetEntries_thunks)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  execOpenat_rdonly_cloexec_dir muslOpenNoCreatCloexecLocalExecSpec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  GoodComp ancestorWalkErrno?_eq_of_pathOk blockingAncestor?_ne_some_dir
  classifyOpenRdonly classifyOpenRdonly_err_cases classifyOpenRdonly_ok_spec
  goodComp_of_mem_pathComps hasDotDot_strOfComps hasLeadingSlash_strOfComps
  isEmpty_false_of_pathOk normalizePath_ne_nil_of_pathOk
  pathComps_ne_nil strOfComps_pathComps trailingDir_false_of_pathOk validRelCPath_of_pathOk
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (
  f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_linkedAt_unique
  f3TrialElf f3TrialElf_parse mallocngLib_in_f3TrialElf
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_stubs f3TrialRxProg_svc
  f3TrialRxProg_symbols f3TrialRxWordTree_eq f3TrialRxWordTree_size
  f3Trial_allocMemcpyVm_ok f3Trial_progContainsMallocng f3Trial_seg5ShimBundle
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsMusl (
  h2fsreads_muslOpenNoCreatCloexecLocalExec_ok
)

/-! ## `mallocngLib` Keep-Sub Bounds and `fineHookAllocEntries` -/

private theorem h2fsreads_mng_placeable (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

private theorem h2fsreads_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

theorem h2fsreads_toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

theorem h2fsreads_keepSub_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → h2fsreads_keepSub a = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := ProofLib.findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      ProofLib.findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((h2fsreads_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (h2fsreads_mng_placeable mmpl hMm) (h2fsreads_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hlo : 0x469000 ≤ f3MngCodeLo := by decide
    have hhi : f3MngCodeHi ≤ 0x46f000 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat :=
      h2fsreads_toNat_add_ofNat_of_lt (by omega)
    rw [heq_a] at ht
    unfold h2fsreads_keepSub
    exact decide_eq_true ⟨by omega, by omega⟩

private theorem h2fsreads_mng_fnAddr_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (name : String) :
    mallocngLib.fnAddr mmpl name = mallocngLib.fnAddr f3MallocngMpl name := by
  unfold MultiPlacedLib.fnAddr
  cases hlk : lookupBlockSym name mallocngLib.blocks with
  | none =>
    exact (f3CliElf_mallocng_linkedAt_unique hMm).1 0 (Nat.zero_lt_succ 23)
  | some p =>
    rcases p with ⟨i, off⟩
    dsimp only
    rw [(f3CliElf_mallocng_linkedAt_unique hMm).1 i (ProofLib.lookupBlockSym_lt hlk)]

private theorem h2fsreads_mng_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  unfold mallocngPlacedCAddrs
  simp only [h2fsreads_mng_fnAddr_eq mmpl hMm]

private theorem h2fsreads_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hPl1 := h2fsreads_mng_placeable mmpl hMm
  have hIn1 := h2fsreads_mng_inElf mmpl hMm
  have hPl2 := mallocngLib_in_f3TrialElf.1
  have hIn2 := mallocngLib_in_f3TrialElf.2.1
  have hF3 := f3Trial_progContainsMallocng
  refine ProgContainsMultiLib.of_noExterns hPl1 f3TrialRxProg_svc
    (fun m hPm i hi => ?_) f3TrialRxProg_no_ext
  have hcl_f3 := hF3.codeLoaded m hPm i hi
  have hbase_i : mmpl.base i = f3MallocngMpl.base i :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 i hi
  have hbase_prog : (mallocngLib.blockProgram mmpl i).base =
      (mallocngLib.blockProgram f3MallocngMpl i).base := hbase_i
  have hcode_mmpl : (mallocngLib.blockProgram mmpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hcode_f3 : (mallocngLib.blockProgram f3MallocngMpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement f3MallocngMpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hlen1 : (mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i)).length =
      mallocngLib.blocks[i].code.length :=
    CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok i hi).len_aligned
  have hlen2 : (mallocngLib.blocks[i].patched (mallocngLib.blockPlacement f3MallocngMpl i)).length =
      mallocngLib.blocks[i].code.length :=
    CodeBlock.length_patched_of_aligned _ (hPl2.blocks_ok i hi).len_aligned
  have hcode_prog : (mallocngLib.blockProgram mmpl i).code =
      (mallocngLib.blockProgram f3MallocngMpl i).code := by
    rw [hcode_mmpl, hcode_f3]
    refine List.ext_getElem (hlen1.trans hlen2.symm) (fun k hk1 hk2 => ?_)
    obtain ⟨p1, hc1, _⟩ := hIn1.blocks i hi k hk1
    obtain ⟨p2, hc2, _⟩ := hIn2.blocks i hi k hk2
    rw [hbase_i] at hc1
    have hsome := hc1.symm.trans hc2
    exact (Prod.mk.inj (Option.some.inj hsome)).2
  rw [Program.codeLoaded_iff] at hcl_f3 ⊢
  rwa [hbase_prog, hcode_prog]

theorem h2fsreads_fineHookAllocEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      f3TrialRxProg f3RdlAddrs := by
  have hShims := f3Trial_seg5ShimBundle.rdlShims
  rw [← h2fsreads_mng_cAddrs_eq mmpl hMm] at hShims
  exact fineHookRustCliAllocBudgetEntries
    (h2fsreads_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hShims
    f3Trial_allocMemcpyVm_ok

theorem h2fsreads_fineHookAllocEntries_thunks (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      f3TrialRxProg f3StubAddrs := by
  have hThunks : RustStdThunkCode f3TrialRxProg f3StubAddrs.toRustStd f3RdlAddrs.toRustStd :=
    rustStdThunkCode_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by intro _; rfl) (by intro _; rfl) (by rw [f3TrialRxProg_base]; rfl_kernel)
  have hShims := f3Trial_seg5ShimBundle.rdlShims
  rw [← h2fsreads_mng_cAddrs_eq mmpl hMm] at hShims
  exact fineHookRustCliAllocBudgetEntries_thunks
    (h2fsreads_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hThunks hShims
    f3Trial_allocMemcpyVm_ok

theorem h2fsreads_stdMemcpy_ok :
    subroutine_ok f3TrialRxProg 0x469650#64 stdMemcpySpec :=
  stdMemcpy_ok_of_hasWords f3TrialRxProg f3StdLayout.memcpyAddr f3TrialRxProg_no_ext
    (hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
      (by rfl_kernel))

theorem h2fsreads_noAllocShim_ok :
    subroutine_ok f3TrialRxProg 0x469640#64 rustAllocShimVmSpec :=
  rustAllocShimVm_ret_ok f3Trial_seg5ShimBundle.noAllocShimV2

/-! ## Deterministic `open` (`O_RDONLY | O_CLOEXEC`) on `f3TrialRxProg` -/

private theorem h2fsreads_setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp only [State.setFs, State.appendTrace, List.append_nil]

private theorem h2fsreads_execOpenat_rdonly_cloexec_err_anc {s : State} {path : String}
    {err : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = some err) :
    execOpenat s = (s.writeReg64 .x0 (-err)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  rw [ProofLib.ancestorWalkErrno_eq_strict] at hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres]
  cases hsanc : strictAncestorWalkErrno? s.fs path with
  | some e =>
    rw [hsanc] at hanc
    injection hanc with he; subst he; rfl
  | none =>
    rw [hsanc] at hanc
    cases hlast : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
    | true =>
      rw [hlast] at hanc
      simp only [↓reduceIte, Option.some.injEq] at hanc
      subst hanc; rfl
    | false =>
      rw [hlast] at hanc; cases hanc

private theorem h2fsreads_execOpenat_rdonly_cloexec_missing {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hnone : s.fs.files path = none) :
    execOpenat s = (s.writeReg64 .x0 (-ENOENT)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = none := hnone
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge]
  simp

private theorem h2fsreads_execOpenat_rdonly_cloexec_emfile_dir {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hdir : s.fs.files path = some .dir)
    (halloc : s.fs.allocFd = none) :
    execOpenat s = (s.writeReg64 .x0 (-EMFILE)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hrd_ne : (FdAccessMode.rdonly != FdAccessMode.rdonly) = false := rfl
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some .dir := hdir
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, hrd_ne, halloc]
  simp

private theorem h2fsreads_execOpenat_rdonly_cloexec_file_or_emfile {s : State} {path : String}
    {bs : List (BitVec 8)}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (htd : trailingDir path = false)
    (hnorm_ne : normalizePath path ≠ [])
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hfile : s.fs.files path = some (.file bs)) :
    execOpenat s =
      match s.fs.allocFd with
      | none => (s.writeReg64 .x0 (-EMFILE)).advancePC
      | some fd =>
        ((s.setFs (s.fs.setFd fd (some
            { path := path, accMode := .rdonly, append := false, cloexec := true,
              offset := 0, kind := .localFile }))).writeReg64 .x0 fd).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hf_ap : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CLOEXEC_W32 != 0#32) = true := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some (.file bs) := hfile
  have hself : s.fs.setEntry (normalizePath path) (some (.file bs)) = s.fs :=
    FsState.setEntry_self_of_nonEmpty hnorm_ne hge
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, Bool.and_false, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, htd]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases s.fs.allocFd with
  | none => rfl
  | some fd => simp [hself]

private theorem h2fsreads_classifyOpenRdonly_err_of_none_some
    (fs : FsState) (path : String) (e : FsEntry) {errno : Nat}
    (hb : blockingAncestor? fs path = none)
    (hf : fs.files path = some e)
    (hcl : classifyOpenRdonly fs path = .err errno) :
    fs.allocFd = none ∧ errno = 24 := by
  unfold classifyOpenRdonly at hcl
  rw [hb, hf] at hcl
  cases ha : fs.allocFd with
  | none =>
    rw [ha] at hcl
    cases e <;> (dsimp only at hcl; injection hcl with he; exact ⟨rfl, he.symm⟩)
  | some fd =>
    rw [ha] at hcl
    cases e <;> nomatch hcl

private theorem h2fsreads_execOpenat_of_classifyOpenRdonly_err {s : State} {path : String} {errno : Nat}
    (hpok : PathOk path = true)
    (hmax : ((pathComps path).all fun c => decide (c.length ≤ NAME_MAX)) = true)
    (hcl : classifyOpenRdonly s.fs path = .err errno)
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path) :
    execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC := by
  have hcs_ne := pathComps_ne_nil path
  have hg : ∀ c ∈ pathComps path, GoodComp c :=
    fun c hc => goodComp_of_mem_pathComps hpok hc
  have hp_eq := strOfComps_pathComps path
  have hne : path.isEmpty = false := isEmpty_false_of_pathOk hpok
  have hlead : hasLeadingSlash path = false := by
    rw [← hp_eq]; exact hasLeadingSlash_strOfComps hcs_ne hg
  have hdot : hasDotDot path = false := by
    rw [← hp_eq]; exact hasDotDot_strOfComps hcs_ne hg
  have htd : trailingDir path = false := trailingDir_false_of_pathOk hpok
  have hnorm_ne : normalizePath path ≠ [] := normalizePath_ne_nil_of_pathOk hpok
  have hanc_eq := ancestorWalkErrno?_eq_of_pathOk s.fs hpok hmax
  have hcl0 := hcl
  unfold classifyOpenRdonly at hcl
  cases hb : blockingAncestor? s.fs path with
  | some a =>
    rw [hb] at hcl hanc_eq
    cases a with
    | none =>
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact h2fsreads_execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
    | some e =>
      cases e with
      | dir => exact absurd hb (blockingAncestor?_ne_some_dir s.fs path)
      | file _ =>
        have he : errno = 20 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
        subst he
        exact h2fsreads_execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
  | none =>
    rw [hb] at hcl hanc_eq
    cases hf : s.fs.files path with
    | none =>
      rw [hf] at hcl
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact h2fsreads_execOpenat_rdonly_cloexec_missing hdfd hflags hcs hne hlead hdot hanc_eq hf
    | some e =>
      obtain ⟨ha, rfl⟩ := h2fsreads_classifyOpenRdonly_err_of_none_some s.fs path e hb hf hcl0
      cases e with
      | dir =>
        exact h2fsreads_execOpenat_rdonly_cloexec_emfile_dir hdfd hflags hcs hne hlead hdot hanc_eq hf ha
      | file bs =>
        have hexec := h2fsreads_execOpenat_rdonly_cloexec_file_or_emfile hdfd hflags hcs hne hlead hdot
          htd hnorm_ne hanc_eq hf
        rw [ha] at hexec
        exact hexec

theorem h2fsreads_muslOpenRdonlyDet_ok :
    subroutine_ok f3TrialRxProg 0x46bb24#64 muslOpenRdonlyDetSpec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨cstr, path, e0⟩ R s0 hpc hrun hpre hsp _hL
  simp only [muslOpenRdonlyDetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpok, hmax, hlen, hlat⟩, hm⟩
  obtain ⟨hcp, hlead, hdot⟩ := validRelCPath_of_pathOk hpok hlen hlat
  have hne := isEmpty_false_of_pathOk hpok
  have htd := trailingDir_false_of_pathOk hpok
  have hnorm_ne := normalizePath_ne_nil_of_pathOk hpok
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x00404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  cases hcl : classifyOpenRdonly s0.fs path with
  | ok fd kind =>
    obtain ⟨hb_none, halloc, _, hfd_max, _, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl
    have hfd_lt : fd.toNat < 2 ^ 31 := by
      have hmmax : FsState.maxOpenFds = 1024 := rfl
      rw [hmmax] at hfd_max
      have h1024_lt : (1024 : Nat) < 2 ^ 31 := by decide
      exact Nat.lt_trans hfd_max h1024_lt
    have hanc_none : ancestorWalkErrno? s0.fs path = none := by
      rw [ancestorWalkErrno?_eq_of_pathOk s0.fs hpok hmax, hb_none]
    let desc : FdEntry :=
      { path := path, accMode := .rdonly, append := false, cloexec := true,
        offset := 0, kind := kind }
    let fs' : FsState := s0.fs.setFd fd (some desc)
    refine h2fsreads_muslOpenNoCreatCloexecLocalExec_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      rcases hkind_cases with ⟨rfl, hdir⟩ | ⟨rfl, bs, hfile⟩
      · have hexec := execOpenat_rdonly_cloexec_dir hs_x0 (hfl_eq ▸ hs_x2) hcs hne hlead hdot
          (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hdir) (hs_fs.symm ▸ halloc)
        rw [hs_fs] at hexec
        refine ⟨hfd_lt, by simp only [fs', FsState.setFd, beq_self_eq_true, ↓reduceIte], Or.inr rfl, rfl, ?_⟩
        rw [h2fsreads_setFs_appendTrace_nil]; exact hexec
      · have hexec := h2fsreads_execOpenat_rdonly_cloexec_file_or_emfile hs_x0 (hfl_eq ▸ hs_x2) hcs hne
          hlead hdot htd hnorm_ne (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hfile)
        rw [hs_fs, halloc] at hexec
        refine ⟨hfd_lt, by simp only [fs', FsState.setFd, beq_self_eq_true, ↓reduceIte], Or.inl rfl, rfl, ?_⟩
        rw [h2fsreads_setFs_appendTrace_nil]; exact hexec
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simpa only [muslOpenNoCreatCloexecLocalExecSpec, muslOpenRdonlyDetSpec, hcl,
          List.append_nil] using hq
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))
  | err errno =>
    have herr_cases := classifyOpenRdonly_err_cases hcl
    have herr_bounds : 1 ≤ errno ∧ errno ≤ 4095 := by
      rcases herr_cases with rfl | rfl | rfl <;> decide
    refine h2fsreads_muslOpenNoCreatCloexecLocalExec_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .err (· = errno)) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      refine ⟨errno, herr_bounds.1, herr_bounds.2, rfl, ?_⟩
      exact h2fsreads_execOpenat_of_classifyOpenRdonly_err hpok hmax (hs_fs.symm ▸ hcl) hs_x0
        (hfl_eq ▸ hs_x2) hcs
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simp only [muslOpenNoCreatCloexecLocalExecSpec, muslOpenRdonlyDetSpec, hcl,
          sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
        rcases hq with ⟨errno', ⟨_, _, rfl, hx0', hfs', htr', hpres'⟩, hm_cells⟩
        exact ⟨⟨hx0', hfs', htr', hpres'⟩, hm_cells⟩
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))


end H2FsReadsHelperPriv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper
