/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import VerifiedLibraries.Musl.Proofs.SyscallProof
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
import ProofLib.Process
import ProofLib.Process.FastParse
import ProofLib.Process.FsLemmas
import ProofLib.SepLogic.WP.StepsProcess
meta import ProofLib
meta import ProofLib.ProgramReflection

/-!
# 9-Block `musl` Syscall Sub-Library Lemmas on `f3TrialRxProg`

**Checked by Lean.**

Proves `subroutine_ok` contracts on `f3TrialRxProg` (`seg[5]`) for the 9-block `musl` syscall
sub-library (`___errno_location`, `close`, `read` on directories/files/stdin, and `open` with
`O_RDONLY | O_CLOEXEC`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsMusl

section H2FsReadsMuslPriv

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib.SepLogic SepProp
open VerifiedLibraries.Musl (
  MuslSysPlacement muslSysPlacedLib
  muslBlk00_errno_location muslBlk01_syscall_ret muslBlk02_sccp
  muslBlk03_syscall_cp muslBlk04_aio_close muslBlk05_close
  muslBlk06_read muslBlk07_write muslBlk08_open
  muslBlk09_fstat muslBlk10_fstatat
  muslSysLib00 muslSysLib01 muslSysLib02 muslSysLib03
  muslSysLib04 muslSysLib05 muslSysLib06 muslSysLib08
  muslSysPl00 muslSysPC00 muslSysPl01 muslSysPC01
  muslSysPl02 muslSysPC02 muslSysPl03 muslSysPC03
  muslSysPl04 muslSysPC04 muslSysPl05 muslSysPC05
  muslSysPl06 muslSysPC06 muslSysPl08 muslSysPC08
  muslErrnoLocationSpec
  ValidCPath
  placed_program_rebase_self
  sxtw64_truncate32 ofNat64_le_maxSyscallOk
  step_str64_perm_c step_stp64_perm step_str32_perm
)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMultiLib)
open LibsignalBinary.Heap.Fine (f3RxWordCount)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (progContainsMultiLib_of_wordTree)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  OpenatLocalExecSpec OpenatLocalOutcome dirReadErrno32 dirReadErrno32_cases
  dirReadErrno32_ne_eintr dirReadErrnoNat dirReadErrnoNat_bounds
  muslClose48LocalSpec muslOpenNoCreatCloexecLocalExecSpec muslReadDir32Spec
  step_svc_close_fd_local
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadFileOrStdio32Spec muslReadStdin32Spec
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_svc
  f3TrialRxWordTree_eq f3TrialRxWordTree_size
)

/-! ## 9-Block `musl` Syscall Sub-Library (`h2fsreads_musl9Lib`) -/

private def h2fsreads_muslFullMpl : MultiPlacement where
  base i :=
    [0x46ba94#64, 0x46bbc0#64, 0x46e1c4#64, 0x46e1e8#64, 0x46e1f8#64,
     0x46e1fc#64, 0x46e240#64, 0x46e274#64, 0x46bb24#64, 0x4b0000#64, 0x4b1000#64].getD i 0#64
  ρ s :=
    if s == "muslEmptyCStr" then 0x4b2000#64
    else if s == "__procfdname" then 0x4b3000#64
    else if s == "fstat" then 0x4b0000#64
    else if s == "fstatat" then 0x4b1000#64
    else 0#64

private theorem h2fsreads_muslFullMpl_placeable :
    muslSysPlacedLib.Placeable h2fsreads_muslFullMpl :=
  muslSysPlacedLib.placeable_of_checkPlaceable (by rfl_kernel)

@[reducible] private local instance h2fsreads_instMuslSysPlacement : MuslSysPlacement where
  mpl := h2fsreads_muslFullMpl
  placeable := h2fsreads_muslFullMpl_placeable

private def h2fsreads_musl9Lib : MultiPlacedLib where
  name := "musl_sys"
  blocks := [
    muslBlk00_errno_location, muslBlk01_syscall_ret, muslBlk02_sccp,
    muslBlk03_syscall_cp, muslBlk04_aio_close, muslBlk05_close,
    muslBlk06_read, muslBlk07_write, muslBlk08_open]
  data := []
  exports := [
    "___errno_location", "__errno_location", "__syscall_ret",
    "__syscall_cp", "__aio_close", "close", "read", "write", "open"]

private theorem h2fsreads_musl9_placeable :
    h2fsreads_musl9Lib.Placeable h2fsreads_muslFullMpl :=
  h2fsreads_musl9Lib.placeable_of_checkPlaceable (by rfl_kernel)

private theorem h2fsreads_progContainsMusl9 :
    ProgContainsMultiLib h2fsreads_musl9Lib f3TrialRxProg h2fsreads_muslFullMpl :=
  progContainsMultiLib_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    h2fsreads_musl9_placeable f3TrialRxProg_svc f3TrialRxProg_no_ext
    (by rw [f3TrialRxProg_base]; rfl_kernel)

private theorem h2fsreads_musl9_resolve_eq :
    h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl =
      muslSysPlacedLib.resolve h2fsreads_muslFullMpl := by
  funext sym
  unfold MultiPlacedLib.resolve lookupBlockSym h2fsreads_musl9Lib muslSysPlacedLib
  dsimp only [lookupBlockSymAux]
  cases lookup sym muslBlk00_errno_location.symbols <;> try rfl
  cases lookup sym muslBlk01_syscall_ret.symbols <;> try rfl
  cases lookup sym muslBlk02_sccp.symbols <;> try rfl
  cases lookup sym muslBlk03_syscall_cp.symbols <;> try rfl
  cases lookup sym muslBlk04_aio_close.symbols <;> try rfl
  cases lookup sym muslBlk05_close.symbols <;> try rfl
  cases lookup sym muslBlk06_read.symbols <;> try rfl
  cases lookup sym muslBlk07_write.symbols <;> try rfl
  cases lookup sym muslBlk08_open.symbols <;> try rfl
  dsimp only [h2fsreads_muslFullMpl, muslBlk09_fstat, muslBlk10_fstatat, lookup]
  by_cases h9 : (sym == "fstat") = true
  · rcases beq_iff_eq.mp h9 with rfl; decide
  · by_cases h10 : (sym == "fstatat") = true
    · rcases beq_iff_eq.mp h10 with rfl; decide
    · have h9f : ("fstat" == sym) = false :=
        beq_eq_false_iff_ne.mpr (fun h => h9 (beq_iff_eq.mpr h.symm))
      have h10f : ("fstatat" == sym) = false :=
        beq_eq_false_iff_ne.mpr (fun h => h10 (beq_iff_eq.mpr h.symm))
      have h9f' : (sym == "fstat") = false := Bool.eq_false_iff.mpr h9
      have h10f' : (sym == "fstatat") = false := Bool.eq_false_iff.mpr h10
      simp only [List.find?, h9f, h10f, h9f', h10f', Option.map]

private theorem h2fsreads_musl9_blockPlacement_eq (i : Nat) :
    h2fsreads_musl9Lib.blockPlacement h2fsreads_muslFullMpl i =
      muslSysPlacedLib.blockPlacement h2fsreads_muslFullMpl i := by
  simp only [MultiPlacedLib.blockPlacement, h2fsreads_musl9_resolve_eq]

private theorem h2fsreads_musl9_blockProgram_eq (i : Nat) (lib : PlacedLib) (pl : Placement)
    (ht : (h2fsreads_musl9Lib.blockLib i).text = lib.text)
    (hpl : muslSysPlacedLib.blockPlacement h2fsreads_muslFullMpl i = pl) :
    h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl i =
      (lib.program pl).rebase pl.base (fun _ => none) := by
  rw [← placed_program_rebase_self lib pl]
  unfold MultiPlacedLib.blockProgram PlacedLib.program Program.rebase
  rw [ht, h2fsreads_musl9_blockPlacement_eq i, hpl]

@[local simp] private theorem h2fsreads_lk_errno :
    lookupBlockSymAux "___errno_location" 0 muslSysPlacedLib.blocks = some (0, 0) := by decide
@[local simp] private theorem h2fsreads_lk_sysret :
    lookupBlockSymAux "__syscall_ret" 0 muslSysPlacedLib.blocks = some (1, 0) := by decide
@[local simp] private theorem h2fsreads_lk_sccp :
    lookupBlockSymAux "__syscall_cp" 0 muslSysPlacedLib.blocks = some (3, 0) := by decide
@[local simp] private theorem h2fsreads_lk_aioclose :
    lookupBlockSymAux "__aio_close" 0 muslSysPlacedLib.blocks = some (4, 0) := by decide
@[local simp] private theorem h2fsreads_muslSysMpl_eq :
    MuslSysPlacement.mpl = h2fsreads_muslFullMpl := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base0 :
    h2fsreads_muslFullMpl.base 0 = 0x46ba94#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base1 :
    h2fsreads_muslFullMpl.base 1 = 0x46bbc0#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base2 :
    h2fsreads_muslFullMpl.base 2 = 0x46e1c4#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base3 :
    h2fsreads_muslFullMpl.base 3 = 0x46e1e8#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base4 :
    h2fsreads_muslFullMpl.base 4 = 0x46e1f8#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base5 :
    h2fsreads_muslFullMpl.base 5 = 0x46e1fc#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base6 :
    h2fsreads_muslFullMpl.base 6 = 0x46e240#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base7 :
    h2fsreads_muslFullMpl.base 7 = 0x46e274#64 := rfl
@[local simp] private theorem h2fsreads_muslFullMpl_base8 :
    h2fsreads_muslFullMpl.base 8 = 0x46bb24#64 := rfl

private theorem h2fsreads_condHI_adds_4096_false {a : BitVec 64} (ha : a.toNat ≤ 2 ^ 64 - 4096) :
    ConditionHolds .HI (addsPState64 a 4096#64) = false := by
  rw [conditionHolds_hi_addsPState64]
  by_cases heq : a = -4096#64
  · subst heq; decide
  · have hlt_strict : a.toNat < 2 ^ 64 - 4096 := by
      refine Nat.lt_of_le_of_ne ha fun h => heq (BitVec.eq_of_toNat_eq ?_)
      have : (-4096#64 : BitVec 64).toNat = 2 ^ 64 - 4096 := by decide
      omega
    have hadd : (a + 4096#64).toNat = a.toNat + 4096 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : 4096 % 2 ^ 64 = 4096 := by decide
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (a + 4096#64) a = false := by
      simp only [BitVec.ult, hadd, decide_eq_false_iff_not]; omega
    rw [hult, Bool.false_and]

private theorem h2fsreads_condHI_adds_4096_true {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ConditionHolds .HI (addsPState64 (-BitVec.ofNat 64 err) 4096#64) = true := by
  rw [conditionHolds_hi_addsPState64]
  have herr_mod : err % 2 ^ 64 = err := Nat.mod_eq_of_lt (by omega)
  have h4096_mod : 4096 % 2 ^ 64 = 4096 := by decide
  have hneg : (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, herr_mod, Nat.mod_eq_of_lt (by omega)]
  have hsum : (-BitVec.ofNat 64 err + 4096#64).toNat = 4096 - err := by
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, h4096_mod]
    have : 2 ^ 64 - err + 4096 = 2 ^ 64 + (4096 - err) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hult : BitVec.ult (-BitVec.ofNat 64 err + 4096#64) (-BitVec.ofNat 64 err) = true := by
    simp only [BitVec.ult, hneg, hsum, decide_eq_true_eq]; omega
  have hne : (-BitVec.ofNat 64 err + 4096#64 != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [hsum, BitVec.toNat_ofNat] at this
    omega
  rw [hult, hne]; rfl

private theorem h2fsreads_neg_truncate32_neg_ofNat (err : Nat) :
    0#32 - (-BitVec.ofNat 64 err).truncate 32 = BitVec.ofNat 32 err := by bv_omega

private def h2fsreads_muslSyscallRetOkSpec : Spec (BitVec 64) where
  pre := fun retVal s0 =>
    ⌜s0.readReg64 .x0 = retVal ∧ retVal.toNat ≤ 2 ^ 64 - 4096⌝ ∗ stackAt s0.sp 32
  post := fun retVal s0 sf =>
    ⌜sf.readReg64 .x0 = retVal ∧ StdStatePreserved s0 sf⌝ ∗ stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def h2fsreads_muslSyscallRetErrSpec : Spec (Nat × BitVec 32) where
  pre := fun (err, e0) s0 =>
    ⌜s0.readReg64 .x0 = -BitVec.ofNat 64 err ∧ 1 ≤ err ∧ err ≤ 4095⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (err, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧ StdStatePreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def h2fsreads_muslAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem h2fsreads_muslErrnoLocation_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 0)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "___errno_location")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl muslErrnoLocationSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 0 =
    muslSysPC00.rebase muslSysPl00.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 0 muslSysLib00 muslSysPl00 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "___errno_location" = muslSysPl00.base from rfl]
  wp_entry; wp_sym_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp only [wp_norm, arm64_norm, muslErrnoAddr], rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩

private theorem h2fsreads_muslAioClose_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 4)
      (h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__aio_close")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslAioCloseSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 4 =
    muslSysPC04.rebase muslSysPl04.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 4 muslSysLib04 muslSysPl04 rfl rfl]
  rw [show h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__aio_close" = muslSysPl04.base from rfl]
  wp_entry; wp_sym_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp only [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private theorem h2fsreads_muslSyscallRetOk_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 1)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "__syscall_ret")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslSyscallRetOkSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 1 muslSysLib01 muslSysPl01 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "__syscall_ret" = muslSysPl01.base from rfl]
  wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepConj_assoc]; repeat (apply SepWP.exists_left; intro)
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 2
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = false := h2fsreads_condHI_adds_4096_false ‹_›
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp only [wp_norm, arm64_norm, hm2, hm1]⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [wp_norm, arm64_norm]

private theorem h2fsreads_muslSyscallRetErr_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 1)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "__syscall_ret")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslSyscallRetErrSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 1 muslSysLib01 muslSysPl01 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "__syscall_ret" = muslSysPl01.base from rfl]
  wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 2
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = true := h2fsreads_condHI_adds_4096_true ‹_› ‹_›
  simp only [hcond, ↓reduceIte]; wp_sym_steps
  wp_call_block h2fsreads_muslErrnoLocation_blk_ok ()
  rcases ‹StdStatePreserved _ sf› with ⟨hbrk_sf, hfs_sf, htpidr_sf, htr_sf, hoidx_sf, horacle_sf, hphys_sf, _⟩
  simp only [wp_norm, arm64_norm] at hbrk_sf hfs_sf htpidr_sf htr_sf hoidx_sf horacle_sf hphys_sf
  simp only [muslErrnoAddr] at *; wp_sym_steps 3
  apply step_str32_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm3
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm3
  wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, ‹sf.status = .Running›])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm]; rfl, by simp only [wp_norm, arm64_norm, hbrk_sf.symm],
      by simp only [wp_norm, arm64_norm, hfs_sf.symm], by simp only [wp_norm, arm64_norm, htpidr_sf.symm],
      by simp only [wp_norm, arm64_norm, htr_sf.symm], by simp only [wp_norm, arm64_norm, hoidx_sf.symm],
      by simp only [wp_norm, arm64_norm, horacle_sf.symm], by simp only [wp_norm, arm64_norm, hphys_sf.symm],
      fun _ => by simp only [wp_norm, arm64_norm, hm3, ‹sf.mem = _›, hm2, hm1]⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm, htpidr_sf.symm, h2fsreads_neg_truncate32_neg_ofNat]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem h2fsreads_muslSyscallCp_step {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : h2fsreads_musl9Lib.CodeLoaded h2fsreads_muslFullMpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := rfl
  rw [hsccp]
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp only [MultiPlacedLib.externAt?_blockProgram_rebase_none])
    rfl (h2fsreads_musl9_blockProgram_eq 2 muslSysLib02 muslSysPl02 rfl rfl ▸ hcl 2 (by decide)) ?_
  wp_sym_steps
  simpa only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

private def h2fsreads_muslSccpCloseLocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir)⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem h2fsreads_muslSccpCloseLocal_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3)
      (h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslSccpCloseLocalSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine h2fsreads_muslSyscallCp_step hpc hrun h ?_
  refine step_svc_close_fd_local (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem h2fsreads_muslClose48Local_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 5)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "close")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl muslClose48LocalSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 5 =
    muslSysPC05.rebase muslSysPl05.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 5 muslSysLib05 muslSysPl05 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "close" = muslSysPl05.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep h2fsreads_muslAioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep h2fsreads_muslSccpCloseLocal_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block h2fsreads_muslSyscallRetOk_blk_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem h2fsreads_readReg32_slt_zero_false {w : BitVec 32} {fd : BitVec 64}
    (hfd : w.zeroExtend 64 = fd) (hlt : fd.toNat < 2 ^ 31) :
    w.slt 0#32 = false := by
  subst hfd
  have hw : w.toNat < 2 ^ 31 := by
    have := w.isLt
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth] at hlt
    omega
  unfold BitVec.slt BitVec.toInt
  simp; omega

private theorem h2fsreads_step_svc_read_dir {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 63#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir)
    (hrd : desc.accMode.canRead = true)
    (hnext :
      let s' := (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRead s) :
    SepWP prog target_pc s P post oom := by
  have hpc_eq : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hslt : (s.readReg32 .x0).slt 0#32 = false := h2fsreads_readReg32_slt_zero_false hfd hfd_lt
  have hexec : execRead s =
      (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64) := by
    have hk_dir : (FdKind.localDir == FdKind.localDir) = true := rfl
    have hadv : (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).advancePC =
        (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64) := by
      subst hpc; rfl
    refine Eq.trans ?_ hadv
    dsimp only [execRead, execReadCommon, dirReadErrnoNat]
    rw [hslt, hfd, hbuf, hcnt, hopen]; dsimp only
    rw [hkind, hrd, hk_dir]
    by_cases hva : buf.toNat + count.toNat > USER_VA_LIMIT
    · simp [hva, EFAULT_RET]
    · simp [hva, EISDIR]
  exact SepWP.step_pure hpc hrun hfetch (by rw [hpc_eq, hsvc, hexec]) (by cases s; rfl) hnext

private def h2fsreads_muslSccpReadDirSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry) where
  pre := fun (fd, buf, count, desc) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localDir ∧
      desc.accMode.canRead = true⌝
  post := fun (_, buf, count, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 (dirReadErrnoNat buf count) ∧
      sf.fs = s0.fs ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem h2fsreads_muslSccpReadDir_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3)
      (h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslSccpReadDirSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine h2fsreads_muslSyscallCp_step hpc hrun h ?_
  refine h2fsreads_step_svc_read_dir (fd := a_1) (buf := a) (count := a_2) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6])
    h_7 h_8 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem h2fsreads_muslReadDir32_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 6)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "read")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl muslReadDir32Spec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 6 muslSysLib06 muslSysPl06 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "read" = muslSysPl06.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep h2fsreads_muslSccpReadDir_blk_ok (a_1, a, a_2, a_3)
  rcases ‹SyscallPreserved _ sf› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
  wp_conv_pre => rw [htp_e]
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have ⟨h1_err, h2_err⟩ := dirReadErrnoNat_bounds a a_2
  wp_call_block h2fsreads_muslSyscallRetErr_blk_ok (dirReadErrnoNat a a_2, a_rest_1)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], dirReadErrno32_cases a a_2,
      dirReadErrno32_ne_eintr a a_2, by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [dirReadErrno32, muslErrnoAddr, wp_norm, arm64_norm, *] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def h2fsreads_muslSccpReadFileOrStdioSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE) ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind == .localFile || desc.kind == .stdio) = true ∧
      desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem h2fsreads_muslSccpReadFileOrStdio_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3)
      (h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslSccpReadFileOrStdioSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine h2fsreads_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x0 = 63#64›])
    (by simpa [wp_norm, arm64_norm] using ‹(s0.readReg32 .x1).zeroExtend 64 = a_1›)
    ‹a_1.toNat < 2 ^ 31›
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x2 = a›])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x3 = a_2›])
    ‹a_rest_1.length = a_2.toNat›
    ‹s0.fs.fds a_1 = some a_3›
    ‹(a_3.kind == .localFile || a_3.kind == .stdio) = true›
    ‹a_3.accMode.canRead = true› ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, ‹s0.readReg64 .x0 = 63#64›])
    ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    ‹a.toNat + a_2.toNat ≤ Arm64.USER_VA_LIMIT›
    ‹a_3.kind = .localFile → a_3.offset + a_2.toNat ≤ Arm64.MAX_LFS_FILESIZE›
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem h2fsreads_muslReadFileOrStdio32_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 6)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "read")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl muslReadFileOrStdio32Spec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 6 muslSysLib06 muslSysPl06 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "read" = muslSysPl06.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep h2fsreads_muslSccpReadFileOrStdio_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length < 2 ^ 63 := by
    simp only [List.length_take]
    have := ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    simp only [Arm64.MAX_RW_COUNT] at this
    omega
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block h2fsreads_muslSyscallRetOk_blk_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def h2fsreads_muslSccpOpenatLocalExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × FsState × List TraceEvent × OpenatLocalOutcome) where
  pre := fun (cstr, path, flags, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatLocalExecSpec fs0 tr0 path flags out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        (desc.kind = .localFile ∨ desc.kind = .localDir) ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem h2fsreads_muslSccpOpenatLocalExec_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3)
      (h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl h2fsreads_muslSccpOpenatLocalExecSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show h2fsreads_musl9Lib.resolve h2fsreads_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_8
  refine h2fsreads_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
  cases a_rest with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [h2fsreads_muslSccpOpenatLocalExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, Arm64.calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [h2fsreads_muslSccpOpenatLocalExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_6], rfl,
        by simp [wp_norm, arm64_norm, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem h2fsreads_truncate32_and64 (x y : BitVec 64) :
    (x &&& y).truncate 32 = x.truncate 32 &&& y.truncate 32 := by ext i hi; simp

private theorem h2fsreads_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow hfd

private theorem h2fsreads_truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, h2fsreads_getLsbD_31_false_of_lt hfd]; decide

private theorem h2fsreads_mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem h2fsreads_setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using h2fsreads_mask32_or_zero_of_lt31 hfd

private theorem h2fsreads_sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [h2fsreads_getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem h2fsreads_neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem h2fsreads_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, h2fsreads_neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem h2fsreads_truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, h2fsreads_getLsbD_31_neg_ofNat h1 h2]; decide

private theorem h2fsreads_sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem h2fsreads_sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [h2fsreads_getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine h2fsreads_sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, h2fsreads_neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem h2fsreads_zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem h2fsreads_zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem h2fsreads_tmpfile_mask_eq_zero {flags : BitVec 32} (h : flags &&& 0x00404000#32 = 0#32) :
    (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = 0#32 := by
  have heq : (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = flags &&& 0x00404000#32 := by bv_bits
  rw [heq, h]

private theorem h2fsreads_or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 131072#64).truncate 32 = flags ||| 0x00020000#32
  bv_bits

set_option maxHeartbeats 400000 in
private theorem h2fsreads_muslOpenNoCreatCloexecLocalExec_blk_ok :
    subroutine_ok (h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 8)
      (h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "open")
      (h2fsreads_musl9Lib.withCodeLoaded h2fsreads_muslFullMpl muslOpenNoCreatCloexecLocalExecSpec) := by
  rw [show h2fsreads_musl9Lib.blockProgram h2fsreads_muslFullMpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from h2fsreads_musl9_blockProgram_eq 8 muslSysLib08 muslSysPl08 rfl rfl]
  rw [show h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "open" = muslSysPl08.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 1
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps 1
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm3
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, h2fsreads_zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 3
  have htmp := h2fsreads_tmpfile_mask_eq_zero h_5
  (conv => arg 3; simp only [wp_norm, arm64_norm, h2fsreads_truncate32_and64, h_3, htmp])
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := h2fsreads_or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep h2fsreads_muslSccpOpenatLocalExec_blk_ok (a_1, a, a_2, s0.fs, s0.trace, a_rest_1)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    wp_conv_pre => try dsimp only [h2fsreads_muslSccpOpenatLocalExecSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
    have hsxtw := h2fsreads_sxtw64_eq_self_of_lt31 hfd_lt
    have hmask0 := h2fsreads_mask32_or_zero_of_lt31 hfd_lt
    have hfd_ze_mask := h2fsreads_setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
    have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
    have htbnz := h2fsreads_getLsbD_31_false_of_lt hfd_lt
    have htbnz32 := h2fsreads_truncate32_getLsbD_31_false_of_lt hfd_lt
    wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
    wp_sym_steps 2
    simp only [wp_norm, arm64_norm, h2fsreads_zeroExtend64_getLsbD_19, h_6]
    have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
      cases desc; simp at hclo; subst hclo; rfl
    have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
      rw [hdesc_eq]; exact FsState.setFd_eq_self hfds
    have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
    wp_sym_steps
    refine step_svc_fcntl_setfd_local (fd := fd) (arg := 1#64) rfl
      (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hfd_ze]) hfd_lt
      (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
      (by simp [wp_norm, arm64_norm, *])
    dsimp only
    (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
    wp_sym_steps
    have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
    wp_cut_codeLoaded
    wp_call_block h2fsreads_muslSyscallRetOk_blk_ok fd
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
  | err errPred =>
    wp_conv_pre => try dsimp only [h2fsreads_muslSccpOpenatLocalExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro errno
    apply SepWP.pure_elim
    rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsxtw := h2fsreads_sxtw64_neg_ofNat h1 h2
    have htbnz := h2fsreads_getLsbD_31_neg_ofNat h1 h2
    have htbnz32 := h2fsreads_truncate32_getLsbD_31_neg_ofNat h1 h2
    have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
    wp_conv_pre => rw [htp_e]
    wp_cut_codeLoaded; wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
    wp_sym_steps
    wp_call_block h2fsreads_muslSyscallRetErr_blk_ok (errno, a_3)
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
        by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
        ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem h2fsreads_f3Rx_hooksUnfetched (m : Memory) (_ : f3TrialRxProg.CodeLoaded m) :
    f3TrialRxProg.HooksUnfetched m :=
  fun _ pc _ he => False.elim (he (f3TrialRxProg_no_ext pc))

theorem h2fsreads_muslErrnoLocation_ok :
    subroutine_ok f3TrialRxProg 0x46ba94#64 muslErrnoLocationSpec := by
  have hfn : h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "___errno_location" = 0x46ba94#64 := by decide
  rw [← hfn]
  exact h2fsreads_musl9Lib.subroutine_ok_of_pureMem (j := 0) (by decide) h2fsreads_muslErrnoLocation_blk_ok
    h2fsreads_progContainsMusl9.codeLoaded h2fsreads_f3Rx_hooksUnfetched f3TrialRxProg_svc

theorem h2fsreads_muslClose48Local_ok :
    subroutine_ok f3TrialRxProg 0x46e1fc#64 muslClose48LocalSpec := by
  have hfn : h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "close" = 0x46e1fc#64 := by decide
  rw [← hfn]
  exact h2fsreads_musl9Lib.subroutine_ok_of_pureMem (j := 5) (by decide) h2fsreads_muslClose48Local_blk_ok
    h2fsreads_progContainsMusl9.codeLoaded h2fsreads_f3Rx_hooksUnfetched f3TrialRxProg_svc

theorem h2fsreads_muslReadDir32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadDir32Spec := by
  have hfn : h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "read" = 0x46e240#64 := by decide
  rw [← hfn]
  exact h2fsreads_musl9Lib.subroutine_ok_of_pureMem (j := 6) (by decide) h2fsreads_muslReadDir32_blk_ok
    h2fsreads_progContainsMusl9.codeLoaded h2fsreads_f3Rx_hooksUnfetched f3TrialRxProg_svc

theorem h2fsreads_muslReadFileOrStdio32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadFileOrStdio32Spec := by
  have hfn : h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "read" = 0x46e240#64 := by decide
  rw [← hfn]
  exact h2fsreads_musl9Lib.subroutine_ok_of_pureMem (j := 6) (by decide) h2fsreads_muslReadFileOrStdio32_blk_ok
    h2fsreads_progContainsMusl9.codeLoaded h2fsreads_f3Rx_hooksUnfetched f3TrialRxProg_svc

theorem h2fsreads_muslOpenNoCreatCloexecLocalExec_ok :
    subroutine_ok f3TrialRxProg 0x46bb24#64 muslOpenNoCreatCloexecLocalExecSpec := by
  have hfn : h2fsreads_musl9Lib.fnAddr h2fsreads_muslFullMpl "open" = 0x46bb24#64 := by decide
  rw [← hfn]
  exact h2fsreads_musl9Lib.subroutine_ok_of_pureMem (j := 8) (by decide)
    h2fsreads_muslOpenNoCreatCloexecLocalExec_blk_ok
    h2fsreads_progContainsMusl9.codeLoaded h2fsreads_f3Rx_hooksUnfetched f3TrialRxProg_svc

theorem h2fsreads_muslReadStdin32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadStdin32Spec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨buf, count, desc, oldBuf⟩ R s0 hpc hrun hpre hsp _hL
  simp only [muslReadStdin32Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcnt_le, hva_le, hlen, hfds0, hkind, hrd⟩, hm⟩
  have hx0_ze : (s0.readReg32 .x0).zeroExtend 64 = 0#64 := by rw [hx0]; rfl
  have h0_lt : (0#64 : BitVec 64).toNat < 2 ^ 31 := by decide
  have hk_or : (desc.kind == .localFile || desc.kind == .stdio) = true := by rw [hkind]; rfl
  have hlfs : desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
    rw [hkind]; intro h; cases h
  have hfdbytes : s0.fs.fdBytes desc = s0.fs.stdin := by simp only [FsState.fdBytes, hkind]
  refine h2fsreads_muslReadFileOrStdio32_ok.mono_outcome (0#64, buf, count, desc, oldBuf) R s0 hpc hrun
    ?_ hsp (fun sf hout => ?_)
  · simp only [muslReadFileOrStdio32Spec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_ze, h0_lt, hx1, hx2, hcnt_le, hva_le, hlfs, hlen, hfds0, hk_or, hrd⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [muslReadFileOrStdio32Spec, muslReadStdin32Spec, hfdbytes] using hq
    · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

end H2FsReadsMuslPriv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsMusl
