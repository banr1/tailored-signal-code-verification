/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Proofs.StdCli.MallocngBridge
import CaseStudies.Hashbrown.Proofs.StdCli.StartupAndExit
import CaseStudies.Hashbrown.Proofs.StdCli.Lib
import CaseStudies.Hashbrown.Proofs.StdCli.Stdout
import CaseStudies.Hashbrown.Proofs.StdCli.MainEpilogue
import CaseStudies.Hashbrown.Proofs.StdCli.MainReadAndScan
import CaseStudies.Hashbrown.Proofs.StdCli.MainCmdLoop

/-!
# Placement-Generic Whole-`ElfImage` Driver Theorem

Proves `hbCli_runsTo` over an arbitrary `Program`, `HbCliLayout`, `HbStartupLayout`,
`ElfImage`, and `Obj.MultiPlacement`, composing startup, `userMain`, and `exit_group`
without concrete binary addresses.
-/

set_option autoImplicit false

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs
open CaseStudies.Hashbrown.Proofs.StdCli.MainReadScanInternal

/-! ## Code Bundle and `WordTree` Validator -/

/-- Instruction and word verification bundle across the RX segment `P`. -/
structure HbCliCode (P : Program) (C : HbCliLayout) (S : HbStartupLayout) : Prop where
  preMain  : HbPreMainCode P C S
  postMain : HbPostMainCode P C S
  shims    : HbShimsCode P C
  memOps   : HbMemOpsCode P C
  sys      : HbSyscallsAndStderrCode P C
  stdin    : HbStdinAndVecCode P C
  stdout   : HbStdoutCode P C
  fmt      : HbFmtCode P C
  userMain : HbUserMainCode P C
  cmd      : HbMainCmdCode P C

/-- Boolean `WordTree` validator checking all 10 RX code bundles on `P`. -/
def checkHbSeg3Code (C : HbCliLayout) (S : HbStartupLayout)
    (base : BitVec 64) (t : WordTree) : Bool :=
  checkHbPreMainCode C S base t &&
  checkHbPostMainCode C S base t &&
  checkHbShimsCode C base t &&
  checkHbMemOpsCode C base t &&
  checkHbSyscallsAndStderrCode C base t &&
  checkHbStdinAndVecCode C base t &&
  checkHbStdoutCode C base t &&
  checkHbFmtCode C base t &&
  checkHbUserMainCode C base t &&
  checkHbMainCmdCode C base t

theorem hbCliCode_of_wordTree {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {tP : WordTree} (nP : Nat)
    (hcodeP : P.code = tP.toBytes) (hwfP : tP.checkSize? = some nP)
    (hsvcP : P.svc = Syscall.standard := by rfl)
    (hstubsP : P.stubs = [] := by rfl) (hsymsP : P.symbols = [] := by rfl)
    (hextP : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovrP : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hokP : checkHbSeg3Code C S P.base tP = true) :
    HbCliCode P C S := by
  unfold checkHbSeg3Code at hokP
  simp only [Bool.and_eq_true] at hokP
  rcases hokP with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hPre, hPost⟩, hShims⟩, hMem⟩, hSys⟩, hStdin⟩, hOut⟩, hFmt⟩, hMain⟩, hCmd⟩
  have cMem := hbMemOpsCode_of_wordTree nP hcodeP hwfP hextP hovrP hMem
  exact
    { preMain  := hbPreMainCode_of_wordTree nP hcodeP hwfP hsvcP hstubsP hsymsP hextP hovrP hPre
      postMain := hbPostMainCode_of_wordTree nP hcodeP hwfP hsvcP hstubsP hsymsP hextP hovrP hPost
      shims    := hbShimsCode_of_wordTree nP hcodeP hwfP hextP hovrP hShims
      memOps   := cMem
      sys      := hbSyscallsAndStderrCode_of_wordTree nP hcodeP hwfP hstubsP hsymsP hextP hovrP hSys
      stdin    := hbStdinAndVecCode_of_wordTree nP hcodeP hwfP hstubsP hsymsP hextP hovrP hStdin
      stdout   := hbStdoutCode_of_wordTree nP hcodeP hwfP hstubsP hsymsP hextP hovrP hOut
      fmt      := hbFmtCode_of_wordTree nP hcodeP hwfP hstubsP hsymsP hextP hovrP hFmt
      userMain := hbUserMainCode_of_wordTree nP hcodeP hwfP hstubsP hsymsP hextP hovrP hMain
      cmd      := hbMainCmdCode_of_wordTree nP hcodeP hwfP hstubsP hsymsP hextP hovrP hCmd }

/-- Placement-generic validator checking that every `VerifiedLibraries.mallocngLib` block at `mpl` lies
    inside `img.segments[C.std.rxSegIdx]` (with earlier segments strictly below `rxSeg.start`) and
    that `C.mallocng` matches `mpl`. -/
def checkHbMallocngInRx (C : HbCliLayout) (mpl : Obj.MultiPlacement) (img : ElfImage) : Bool :=
  match img.segments[C.std.rxSegIdx]? with
  | none => false
  | some rxSeg =>
    withForcedNat (fastLen512 4096 rxSeg.bytes) fun rxLen =>
      (img.segments.take C.std.rxSegIdx).all
        (fun q => decide (q.start.toNat + fastLen512 4096 q.bytes ≤ rxSeg.start.toNat)) &&
      decide (rxSeg.start.toNat + rxLen ≤ 2 ^ 64) &&
      (List.range VerifiedLibraries.mallocngLib.blocks.length).all
        (fun i =>
          (mpl.base i).toNat % 4 == 0 &&
          decide (rxSeg.start.toNat ≤ (mpl.base i).toNat) &&
          decide ((mpl.base i).toNat +
            (VerifiedLibraries.mallocngLib.blocks[i]?.map (fun b => fastLen512 4096 b.code)).getD 0 ≤
            rxSeg.start.toNat + rxLen)) &&
      decide (C.mallocng.brkBase.toNat ≤ 3 * 2 ^ 20) &&
      (VerifiedLibraries.mallocngLib.fnAddr mpl "malloc" == C.mallocng.mallocAddr) &&
      (VerifiedLibraries.mallocngLib.fnAddr mpl "free" == C.mallocng.freeAddr) &&
      (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc" == C.mallocng.callocAddr) &&
      (VerifiedLibraries.mallocngLib.fnAddr mpl "realloc" == C.mallocng.reallocAddr) &&
      (VerifiedLibraries.mallocngLib.fnAddr mpl "aligned_alloc" == C.mallocng.alignedAllocAddr) &&
      (VerifiedLibraries.mallocngLib.fnAddr mpl "posix_memalign" == C.mallocng.posixMemalignAddr) &&
      (mpl.ρ "__malloc_size_classes" == C.mallocng.roTablesAddr) &&
      (mpl.ρ "debruijn32.4681" == C.mallocng.roTablesAddr + 96#64) &&
      (mpl.ρ "med_cnt_tab" == C.mallocng.roTablesAddr + 128#64) &&
      (mpl.ρ "small_cnt_tab" == C.mallocng.roTablesAddr + 136#64) &&
      (mpl.ρ "debruijn32.5048" == C.mallocng.roTablesAddr + 168#64) &&
      (mpl.ρ "__malloc_context" == C.mallocng.mallocCtxAddr) &&
      (mpl.ρ "__malloc_lock" == C.mallocng.mallocLockAddr) &&
      (mpl.ρ "__malloc_replaced" == C.mallocng.mallocReplacedAddr) &&
      (mpl.ρ "__aligned_alloc_replaced" == C.mallocng.alignedAllocReplacedAddr) &&
      (C.mallocng.libcNeedLocksAddr == mpl.ρ "__libc" + 3#64) &&
      (C.mallocng.libcAuxvAddr == mpl.ρ "__libc" + 8#64) &&
      (C.mallocng.libcPageSizeAddr == mpl.ρ "__libc" + 48#64)

theorem hbMallocngPlaced_of_inElf {C : HbCliLayout} {mpl : Obj.MultiPlacement} {img : ElfImage}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hin : VerifiedLibraries.mallocngLib.InElf img mpl)
    (hok : checkHbMallocngInRx C mpl img = true) :
    HbMallocngPlaced (C.std.rxProgram img) C mpl := by
  unfold checkHbMallocngInRx at hok
  split at hok <;> try contradiction
  rename_i rxSeg hrxSeg
  simp only [withForcedNat_eq, fastLen512_eq_length, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpre, hwrap⟩, hblks⟩, hbrk⟩, hm⟩, hf⟩, hc⟩, hr⟩,
    haa⟩, hpm⟩, hsc⟩, hdb1⟩, hmc⟩, hsm⟩, hdb2⟩, hctx⟩, hlck⟩, hrep⟩, haar⟩, hnl⟩, haux⟩, hpg⟩ := hok
  have hrx_lt : C.std.rxSegIdx < img.segments.length := by
    apply Classical.byContradiction
    intro hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hrxSeg
    contradiction
  have hrx_eq : img.segments[C.std.rxSegIdx] = rxSeg := by
    rw [List.getElem?_eq_getElem hrx_lt] at hrxSeg
    exact Option.some.inj hrxSeg
  have hsplit : img.segments =
      img.segments.take C.std.rxSegIdx ++ rxSeg :: img.segments.drop (C.std.rxSegIdx + 1) := by
    rw [← hrx_eq, List.getElem_cons_drop, List.take_append_drop]
  have hpre' : (img.segments.take C.std.rxSegIdx).all (Snapshot.Below rxSeg.start) = true := hpre
  refine
    { noHooks   := fun pc => congrFun (StdBinaryLayout.rxProgram_externAt? C.std img) pc
      svc_std   := StdBinaryLayout.rxProgram_svc C.std img
      placeable := hpl
      codeLoaded := fun m hPm i hi => ?_
      brkBase_le         := hbrk
      malloc_addr        := hm
      free_addr          := hf
      calloc_addr        := hc
      realloc_addr       := hr
      alignedAlloc_addr  := haa
      posixMemalign_addr := hpm
      sizeClasses_addr   := hsc
      debruijnFree_addr  := hdb1
      medCntTab_addr     := hmc
      smallCntTab_addr   := hsm
      debruijnAlloc_addr := hdb2
      ctx_addr           := hctx
      lock_addr          := hlck
      replaced_addr      := hrep
      aaReplaced_addr    := haar
      needLocks_addr     := hnl
      auxv_addr          := haux
      pageSize_addr      := hpg }
  have hP_eq : C.std.rxProgram img =
      { base := rxSeg.start, code := rxSeg.bytes, svc := Syscall.standard } := by
    simp [StdBinaryLayout.rxProgram, hrxSeg]
  rw [hP_eq] at hPm
  rw [Program.codeLoaded_iff] at hPm ⊢
  obtain ⟨_, _, hP_bytes⟩ := hPm
  have hbi := List.all_eq_true.mp hblks i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at hbi
  rcases hbi with ⟨⟨hal_i, hle_i⟩, hfit_i⟩
  have hbase_eq : (VerifiedLibraries.mallocngLib.blockProgram mpl i).base = mpl.base i := rfl
  have hcode_eq : (VerifiedLibraries.mallocngLib.blockProgram mpl i).code =
      VerifiedLibraries.mallocngLib.blocks[i].patched (VerifiedLibraries.mallocngLib.blockPlacement mpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, VerifiedLibraries.mallocngLib.blockLib_text hi]
  have hlen_i : (VerifiedLibraries.mallocngLib.blockProgram mpl i).code.length =
      VerifiedLibraries.mallocngLib.blocks[i].code.length := by
    rw [hcode_eq]
    exact CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok i hi).len_aligned
  refine ⟨by rw [hbase_eq]; exact hal_i, by rw [hbase_eq, hlen_i]; omega, fun k hk => ?_⟩
  let idx := ((mpl.base i).toNat - rxSeg.start.toNat) + k
  have hidx_lt : idx < rxSeg.bytes.length := by rw [hlen_i] at hk; omega
  have hk_pat : k < (VerifiedLibraries.mallocngLib.blocks[i].patched
      (VerifiedLibraries.mallocngLib.blockPlacement mpl i)).length := by rwa [← hcode_eq]
  obtain ⟨p, hcell1, _⟩ := hin.blocks i hi k hk_pat
  have haddr_eq : rxSeg.start + BitVec.ofNat 64 idx = mpl.base i + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : idx < 2 ^ 64 := by omega
    have : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt ‹idx < 2 ^ 64›, Nat.mod_eq_of_lt ‹k < 2 ^ 64›,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hcell2 : Snapshot.cellAt img.segments (rxSeg.start + BitVec.ofNat 64 idx) =
      some (some rxSeg.perm, rxSeg.bytes[idx]) := by
    rw [hsplit]
    exact Snapshot.cellAt_of_split hpre' hidx_lt hwrap
  rw [← haddr_eq, hcell2, Option.some.injEq, Prod.mk.injEq] at hcell1
  obtain ⟨hrd, hperm⟩ := hP_bytes idx hidx_lt
  rw [hbase_eq, ← haddr_eq]
  have hbyte_eq : (VerifiedLibraries.mallocngLib.blockProgram mpl i).code[k] = rxSeg.bytes[idx] := by
    simp only [hcode_eq]
    exact hcell1.2.symm
  exact ⟨hrd.trans hbyte_eq.symm, hperm⟩

/-! ## Spatial and Read-Only Splitting Helpers -/

private theorem hbCmdRoData_dup_osFunctionsGot (C : HbCliLayout) :
    HbCmdRoData C ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) = HbCmdRoData C := by
  unfold HbCmdRoData
  have h : (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      ((C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr)) =
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) := by
    rw [← sepConj_assoc,
        sepConj_comm (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) (C.captureUsedAddr ↦₈ᵣ 0#8),
        sepConj_assoc, pointsTo64RO_dup, sepConj_comm]
  simpa only [sepConj_assoc] using
    congrArg (fun X =>
      HbParseRoData C ∗
      (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
      (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
      (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
      StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
      HbAdapterWriteVtableRo C ∗ X) h

private theorem hbCliRoData_entails (C : HbCliLayout) :
    HbCliRoData C ⊢
      HbCmdRoData C ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) := by
  rw [hbCliRoData_eq_cmdRoData C]
  have h := congrArg (fun X => X ∗
    (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
    StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
    (C.globalPanicCountAddr ↦₆₄ᵣ 0#64)) (hbCmdRoData_dup_osFunctionsGot C)
  simp only [sepConj_assoc] at h ⊢
  rw [← h]
  exact Entails.refl _

private theorem hashbrownCliPost_of_cmdLoop {stdinBytes core : List (BitVec 8)} {s_ret : State}
    (hany : (splitLines stdinBytes).any (·.length > MaxLineLen) = false)
    (hsplit : splitLines stdinBytes = splitOnByte 0x0a#8 core)
    (hx0 : (s_ret.readReg32 .x0).truncate 8 = 0#8)
    (hout : ProcessOutcome.traceStreamBytes .stdout s_ret.trace =
      (evalLines (splitOnByte 0x0a#8 core)).1)
    (herr : ProcessOutcome.traceStreamBytes .stderr s_ret.trace =
      (evalLines (splitOnByte 0x0a#8 core)).2) :
    HashbrownCliPost stdinBytes
      (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret) := by
  have hx0_64 : ((s_ret.readReg32 .x0).truncate 8).zeroExtend 64 = 0#64 := by
    rw [hx0]; rfl
  rw [hx0_64]
  unfold HashbrownCliPost ProcessOutcome.ofState
  rw [hany, hsplit]
  simp [hout, herr]

/-! ## Whole-`ElfImage` Execution Theorem -/

/-- Placement-generic end-to-end execution theorem for `hashbrown_cli`: for every valid input
    within `HashbrownStdinBudget inputs`, `img` executes from `_start` through `userMain` and
    `musl` `exit_group` without hooks or instruction overrides (`oom := fun _ => False`),
    terminating in a state satisfying `HashbrownCliPost inputs.stdin`. -/
theorem hbCli_runsTo {P : Program} {C : HbCliLayout} {S : HbStartupLayout} {img : ElfImage}
    {mpl : Obj.MultiPlacement} {inputs : ProcessInputs}
    (hc : HbCliCode P C S) (hv : C.Valid) (hS : S.Valid C) (hw : HbExternWiring C)
    (hmatch : HbMatchesImage C S img = true)
    (hrx : C.std.rxProgram img = P)
    (hPlaceable : hashbrownLib.Placeable C.hbMpl)
    (hInElf : hashbrownLib.InElf img C.hbMpl)
    (hMpl : HbMallocngPlaced P C mpl)
    (hvalid : inputs.Valid)
    (hbudget : HashbrownStdinBudget inputs) :
    ElfImageRunsTo img inputs (HashbrownCliPost inputs.stdin) (fun _ => False) := by
  let M := hbMallocngIface hMpl hbudget.1
  refine hbElfImage_runsTo hc.preMain hc.postMain hv hS hmatch hMpl hvalid hbudget hrx
    fun s0 s_main γ e_init R_frame hf => ?_
  refine ⟨fun _ => ⌜False⌝, fun _ _ hsat => not_satisfies_false_sepConj hsat, ?_⟩
  have hcodeHb0 : hashbrownLib.CodeLoaded C.hbMpl s0.mem :=
    MultiPlacedLib.codeLoaded_of_inElf hPlaceable hInElf hf.load_eq
  have hci_main : hbCliCodeInv P C s_main.mem :=
    ⟨hf.mainState.codeLoaded, hcodeHb0.of_keepsFrozen hf.steps_to_main.keepsFrozen⟩
  have hP_ext : ∀ pc, P.externAt? pc = none := hMpl.noHooks
  have hP_svc : P.svc = Syscall.standard := hMpl.svc_std
  have hMemSvc : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr :=
    hbStdMemOps (hc.memOps.withSvc hbStdioSvc)
  have hMemmoveSvc : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec :=
    hbMemmove_disjoint_ok (hc.memOps.withSvc hbStdioSvc)
  have hLib := hbCliLibContracts_ok hw hPlaceable hP_ext hP_svc hc.shims hc.memOps
    M.toMallocngCoreIface γ (hbCliCodeInv P C)
    (fun hkf hci => hbCliCodeInv_keepsFrozen hkf hci) (fun hci => hci)
  have hPrintBool : subroutine_ok P C.printBoolAddr
      (hbPrintBoolSpec C M.toMallocngCoreIface γ) :=
    hbPrintBool_ok M.toMallocngCoreIface γ hc.stdout hc.sys hc.fmt hc.postMain.onceCallPost
      hc.preMain.atomics.cas8Relax_ok hc.preMain.atomics.cas4Acq_ok hc.preMain.atomics.swp4Rel_ok
      hMemSvc hMemmoveSvc hv hv.stdoutGlobal_nz hP_svc hP_ext
  have hPrintU64 : subroutine_ok P C.printU64Addr
      (hbPrintU64Spec C M.toMallocngCoreIface γ) :=
    hbPrintU64_ok M.toMallocngCoreIface γ hc.stdout hc.sys hc.fmt hc.postMain.onceCallPost
      hc.preMain.atomics.cas8Relax_ok hc.preMain.atomics.cas4Acq_ok hc.preMain.atomics.swp4Rel_ok
      hMemSvc hMemmoveSvc hv hv.stdoutGlobal_nz hP_svc hP_ext
  have hPrintNone : subroutine_ok P C.stdioPrintAddr
      (hbStdioPrintNoneSpec C M.toMallocngCoreIface γ) :=
    hbStdioPrintNone_ok M.toMallocngCoreIface γ hc.stdout hc.sys hc.fmt hc.postMain.onceCallPost
      hc.preMain.atomics.cas8Relax_ok hc.preMain.atomics.cas4Acq_ok hc.preMain.atomics.swp4Rel_ok
      hMemSvc hMemmoveSvc hv hv.stdoutGlobal_nz hP_svc hP_ext
  let K : HbCmdCallees C M.toMallocngCoreIface γ (hbCliCodeInv P C)
      (fun hkf hci => hbCliCodeInv_keepsFrozen hkf hci) :=
    { hcCmd      := hc.cmd
      hcSys      := hc.sys
      hatom      := hc.preMain.atomics
      hv         := hv
      hext       := hP_ext
      hsvc       := hP_svc
      hNew       := hLib.new_ok
      hWithCap   := hLib.with_capacity_infallible_ok
      hIns       := hLib.insert_infallible_ok
      hGet       := hLib.get_ok
      hContains  := hLib.contains_key_ok
      hRem       := hLib.remove_ok
      hLen       := hLib.len_ok
      hIsEmpty   := hLib.is_empty_ok
      hClear     := hLib.clear_ok
      hDrop      := hLib.drop_ok
      hPrintBool := hPrintBool
      hPrintU64  := hPrintU64
      hPrintNone := hPrintNone }
  rw [← hf.mainState.lr_eq]
  have hsp_hr := hf.mainState.sp_headroom
  have hsp_lt := s_main.sp.isLt
  have h224 : (0xe0#64 : BitVec 64).toNat = 224 := rfl
  have hsp_m_lo : 0x310 ≤ (s_main.sp - 0xe0#64).toNat := by
    rw [BitVec.toNat_sub_of_le (by omega : (0xe0#64 : BitVec 64).toNat ≤ s_main.sp.toNat), h224]
    omega
  have hsp_m_hi : (s_main.sp - 0xe0#64).toNat + 0x80 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_sub_of_le (by omega : (0xe0#64 : BitVec 64).toNat ≤ s_main.sp.toNat), h224]
    omega
  have hopen_main : HbStdinOpen inputs.stdin s_main.fs :=
    HbStdinOpen.of_fs_eq hf.mainState.fs_eq (hbStdinOpen_initFsState inputs)
  apply sepWP_mono_atom (hbCliRoData_entails C)
  refine hbMain_readToEnd_wp hv hc.userMain hc.stdin hc.sys hc.postMain.onceCallPost
    hc.preMain.atomics (hbStdMemOps hc.memOps) M γ
    (lc0 := 0) (blk0 := 0) (stdinBytes := inputs.stdin)
    (haveLse := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8) (e0 := e_init)
    (F := hbRodata C.hbPl ∗ HbStdoutInv C M.toMallocngCoreIface γ false ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
      (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗ HbThreadIdInv C s_main.tpidrEl0)
    hP_svc hP_ext hv.stdinGlobal_nz rfl hbudget.1 (by omega) (by omega)
    hf.mainState.pc_eq hf.mainState.status_eq hf.mainState.spAligned_eq
    (by omega) hf.mainState.sp_userVa hopen_main
    (by sep_frame) ?_
  rintro s1 cap vecPtr e1 _ rfl hpc1 hrun1 hsp1 hal1 hcap_le _hopen1 hx28_1 hx29_1 hv1 htr1 htp1 _hsig1 hkf1
  have hci1 : hbCliCodeInv P C s1.mem := hbCliCodeInv_keepsFrozen hkf1 hci_main
  simp only [Nat.zero_add]
  refine hbMain_scanLines_wp hv hc.userMain hc.shims hc.sys hc.preMain.atomics M γ
    (sp_m := s_main.sp - 0xe0#64) (vecPtr := vecPtr)
    (cap := cap) (lcRest := mallocngBlockCost 8192) (blkRest := 1)
    (stdinBytes := inputs.stdin)
    (haveLse := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8) (e0 := e1)
    (F := hbRodata C.hbPl ∗ HbStdoutInv C M.toMallocngCoreIface γ false ∗ HbCmdRoData C ∗
      HbStdinInv C M.toMallocngCoreIface γ true ∗ ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      (C.globalPanicCountAddr ↦₆₄ᵣ 0#64))
    hP_svc hP_ext rfl hf.mainState.spAligned_eq hbudget.1
    hpc1 hrun1 hsp1 hx28_1 hv1
    (by rw [← htp1]; sep_frame)
    (fun s_ret e_ret Pf hsp_r _hcs_r _hfs_r _htp_r _hsig_r _hkf_r hpost_cli hPf => ?_)
    (fun s_cmd coreLen hne hany_false hcore_le hsplit_eq hpc_c hrun_c hsp_c hal_c
         hx9_c hx22_c hx28_c hx29_c hv_c hnv_c _hfs_c htr_c => ?_)
  · refine ⟨hsp_r, hpost_cli (htr1.trans hf.mainState.trace_eq),
      false, mallocngBlockCost 8192, 1, e_ret,
      stackAt (s_ret.sp - BitVec.ofNat 64 4304) (261984 - 4304) ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ (if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
        hbRodata C.hbPl ∗ HbCmdRoData C ∗
        HbStdinInv C M.toMallocngCoreIface γ true ∗ ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32) ∗
        StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
        (C.globalPanicCountAddr ↦₆₄ᵣ 0#64), ?_⟩
    refine Entails.trans hPf ?_
    rw [stackAt_split_main s_ret.sp 4304 (261984 - 4304) (n := 261984)]
    dsimp only [hbStdoutCost, hbStdoutBlocks]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    sep_entail
  · have hci_c : hbCliCodeInv P C s_cmd.mem := hbCliCodeInv_keepsFrozen hnv_c.keepsFrozen hci1
    have hx29_c' : s_cmd.readReg64 .x29 = (s_main.sp - 0xe0#64) + 0x80#64 :=
      hx29_c.trans hx29_1
    have htr_cmd0 : s_cmd.trace = [] := htr_c.trans (htr1.trans hf.mainState.trace_eq)
    rcases Nat.eq_zero_or_pos cap with rfl | hcap_pos
    · conv => arg 4; simp only [HbByteVec, HbByteVecBuf, ↓reduceIte, sepConj_assoc, sepConj_pull_pure]
      exact SepWP.pure_elim fun ⟨hemp, _⟩ => False.elim (hne hemp)
    · have hcap_ne : cap ≠ 0 := by omega
      let core := inputs.stdin.take coreLen
      have hcore_len : core.length = coreLen := List.length_take_of_le hcore_le
      have hstdin_split : (vecPtr ↦ₛ inputs.stdin) =
          (vecPtr ↦ₛ core) ∗
          ((vecPtr + BitVec.ofNat 64 coreLen) ↦ₛ inputs.stdin.drop coreLen) := by
        conv => lhs; rw [← List.take_append_drop coreLen inputs.stdin]
        rw [pointsToBytes_append]
        change (vecPtr ↦ₛ core) ∗
          ((vecPtr + BitVec.ofNat 64 core.length) ↦ₛ inputs.stdin.drop coreLen) = _
        rw [hcore_len]
      conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hcap_ne, ↓reduceIte,
        sepConj_assoc, sepConj_pull_pure]
      refine SepWP.pure_elim fun hvec_pure => ?_
      have hvec_nz : vecPtr ≠ 0#64 := hvec_pure.1
      have hvec_fit : vecPtr.toNat + core.length < 2 ^ 64 := by
        have := hvec_pure.2.2.1; have := hvec_pure.2.2.2; omega
      have hblk_le : 1 + hbByteVecBlocks cap ≤ 2 := by
        unfold hbByteVecBlocks; simp [hcap_ne]
      refine SepWP.weaken_pre ?_
        (hbMain_cmdLoop_wp M.toMallocngCoreIface γ (hbCliCodeInv P C)
          (fun hkf hci => hbCliCodeInv_keepsFrozen hkf hci) K
          (sp_m := s_main.sp - 0xe0#64) (vecPtr := vecPtr)
          (haveLse := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8)
          (baseLc := mallocngBlockCost 8192 + hbByteVecCost cap)
          (baseBlk := 1 + hbByteVecBlocks cap) (vecCap := cap) (core := core)
          (init0 := false) (e_err0 := e1)
          (F := memRegion (s_main.sp - 0xe0#64) 8 ∗
            (((s_main.sp - 0xe0#64) + 0x08#64) ↦₆₄ BitVec.ofNat 64 cap) ∗
            ((((s_main.sp - 0xe0#64) + 0x08#64) + 0x08#64) ↦₆₄ vecPtr) ∗
            ((((s_main.sp - 0xe0#64) + 0x08#64) + 0x10#64) ↦₆₄ BitVec.ofNat 64 inputs.stdin.length) ∗
            M.Block γ vecPtr cap ∗
            ((vecPtr + BitVec.ofNat 64 coreLen) ↦ₛ inputs.stdin.drop coreLen) ∗
            memRegion (vecPtr + BitVec.ofNat 64 inputs.stdin.length) (cap - inputs.stdin.length) ∗
            HbMainSavedRegs (s_main.sp - 0xe0#64) s_main ∗
            stackAt ((s_main.sp - 0xe0#64) - BitVec.ofNat 64 4432) (261984 - 224 - 4432) ∗
            (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
            (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
            HbStdinInv C M.toMallocngCoreIface γ true ∗ ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32) ∗
            StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
            (C.globalPanicCountAddr ↦₆₄ᵣ 0#64))
          hbudget.1 hsp_m_lo hsp_m_hi
          (Nat.le_refl _) hblk_le hcap_le (by rw [hcore_len]; exact hcore_le)
          hvec_nz hvec_fit
          hpc_c hrun_c hsp_c hal_c hci_c hx9_c (by rw [hcore_len]; exact hx22_c) hx29_c'
          fun sf init' e_err' hpc_f hrun_f hsp_f _hal_f _hfs_f _htp_f _hsig_f hv_f
              hx28_f _hx29_f _hci_f hout_f herr_f => ?_)
      · rw [hstdin_split,
            stackAt_split_main (s_main.sp - 0xe0#64) 4432 (261984 - 224 - 4432) (n := 261984 - 224)]
        dsimp only [hbStdoutCost, hbStdoutBlocks]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        sep_entail
      · have hvec_repack :
            (((s_main.sp - 0xe0#64) + 0x08#64) ↦₆₄ BitVec.ofNat 64 cap) ∗
            ((((s_main.sp - 0xe0#64) + 0x08#64) + 0x08#64) ↦₆₄ vecPtr) ∗
            ((((s_main.sp - 0xe0#64) + 0x08#64) + 0x10#64) ↦₆₄ BitVec.ofNat 64 inputs.stdin.length) ∗
            M.Block γ vecPtr cap ∗
            (vecPtr ↦ₛ core) ∗
            ((vecPtr + BitVec.ofNat 64 coreLen) ↦ₛ inputs.stdin.drop coreLen) ∗
            memRegion (vecPtr + BitVec.ofNat 64 inputs.stdin.length) (cap - inputs.stdin.length) ⊢
            HbByteVec M.toMallocngCoreIface γ ((s_main.sp - 0xe0#64) + 0x08#64) cap vecPtr inputs.stdin := by
          dsimp only [HbByteVec, HbByteVecBuf]
          simp only [hcap_ne, ↓reduceIte]
          rw [hstdin_split]
          exact Entails.trans (by sep_entail)
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (Entails.pure_right hvec_pure (Entails.refl _)))))
        have hlc_re : (mallocngBlockCost 8192 + hbByteVecCost cap) + hbStdoutCost init' =
            (mallocngBlockCost 8192 + hbStdoutCost init') + hbByteVecCost cap := by omega
        have hblk_re : (1 + hbByteVecBlocks cap) + hbStdoutBlocks init' =
            (1 + hbStdoutBlocks init') + hbByteVecBlocks cap := by omega
        refine hbMain_epilogue_from310_wp hc.userMain hc.shims M.toMallocngCoreIface γ
          (sp_m := s_main.sp - 0xe0#64) (vecPtr := vecPtr)
          (cap := cap) (lcRest := mallocngBlockCost 8192 + hbStdoutCost init')
          (blkRest := 1 + hbStdoutBlocks init') (bs := inputs.stdin) (e0 := e_err')
          (F := HbStdoutInv C M.toMallocngCoreIface γ init' ∗
            (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
            hbRodata C.hbPl ∗ HbCmdRoData C ∗
            (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
            (C.std.haveLseAtomicsAddr ↦₈ᵣ (if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
            HbThreadIdInv C sf.tpidrEl0 ∗
            (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
            HbStdinInv C M.toMallocngCoreIface γ true ∗ ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32) ∗
            StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
            (C.globalPanicCountAddr ↦₆₄ᵣ 0#64))
          hP_svc hP_ext rfl hf.mainState.spAligned_eq hpc_f hrun_f hsp_f
          (hx28_f.trans hx28_c) (hv_f.trans hv_c)
          ?_
          fun s_ret e_ret Pf hsp_r hx0_r _hcs_r hmsp_r hPf => ?_
        · rw [hlc_re, hblk_re,
              stackAt_split_main (s_main.sp - 0xe0#64) 4432 (261984 - 224 - 4432) (n := 261984 - 224)]
          refine Entails.trans ?_ (sepConj_mono_left hvec_repack)
          sep_entail
        · have hout_ret : ProcessOutcome.traceStreamBytes .stdout s_ret.trace =
              (evalLines (splitOnByte 0x0a#8 core)).1 := by
            rw [hmsp_r.2.1, hout_f, htr_cmd0]; simp [ProcessOutcome.traceStreamBytes]
          have herr_ret : ProcessOutcome.traceStreamBytes .stderr s_ret.trace =
              (evalLines (splitOnByte 0x0a#8 core)).2 := by
            rw [hmsp_r.2.1, herr_f, htr_cmd0]; simp [ProcessOutcome.traceStreamBytes]
          refine ⟨hsp_r,
            hashbrownCliPost_of_cmdLoop hany_false hsplit_eq hx0_r hout_ret herr_ret,
            init', mallocngBlockCost 8192, 1, e_ret,
            stackAt (s_ret.sp - BitVec.ofNat 64 4304) (261984 - 4304) ∗
              (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
              hbRodata C.hbPl ∗ HbCmdRoData C ∗
              (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
              (C.std.haveLseAtomicsAddr ↦₈ᵣ (if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
              (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
              HbStdinInv C M.toMallocngCoreIface γ true ∗ ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32) ∗
              StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
              (C.globalPanicCountAddr ↦₆₄ᵣ 0#64), ?_⟩
          refine Entails.trans hPf ?_
          rw [← hmsp_r.2.2.2.1,
              stackAt_split_main s_ret.sp 4304 (261984 - 4304) (n := 261984)]
          sep_entail

end CaseStudies.Hashbrown.Proofs.StdCli
