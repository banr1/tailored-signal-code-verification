/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoLoopBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.ProgramReflection

/-!
# Budget-Threaded `signal_session_io::read_file`

Verifies `readFileAnyBudgetCondSpec` (`ro : Bool`, covering heap `↦ₛ` and `.rodata` `↦ᵣ`) and
`readFileBudgetCondSpec` (`ro = false`, carrying `AllocCallPreserved`) on `signalSessionIoMultiLib`
block 3 (`signal_session_io::read_file`) for any `A : RustCliAllocBudget M` equipped with
`PoolErrnoSplit A tp brkStart`, and instantiates `PoolErrnoSplit` for the `mallocng` and
`fineCostModel` allocator budgets.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst

open Arm64 Arm64.Process
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open Arm64.Obj hiding bytesAt
open ProofLib hiding MallocngAddrs MallocngIface
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SignalSession (PathOk blockingAncestor? pathComps)
open CryptoVerification.SignalSession.Cli (ReadFileGhost ioVecAt)
open CryptoVerification.SignalSession.Cli.MainHops (
  blockingAncestorF cliIo cliRd cliWrOk pathStr readViewF
)
open CryptoVerification.SignalSession.CliExt (ReadFileCall bytesAt)
open VerifiedLibraries.Mallocng (MallocngAddrs MallocngRuntime mallocngAddrsOfPlacement)
open VerifiedLibraries.Musl (memcpySrc muslErrnoLocationSpec)
open VerifiedLibraries.RustStd (
  StdErrnoCell stdErrnoAddr vecHeader
  cPathOf rustSepWP_cut rustNz_byte_ze_beq_false
  allocAllocShimSpec
  MallocngLibcCells mallocngRuntime_eq_stdErrnoCell_sep
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents
  MallocngCostModelIface MallocngCostModelSound
  OomPreserved PoolPreserved RustAllocAddrs RustCliAllocBudget
  RustCliAllocBudgetEntriesBase VmMemPreserved VmPreserved
  mallocngBudgetPool mallocngBudgetPoolAt mallocngBudgetPoolAt_mapped_lt_userVa
  mallocngBudgetPoolAt_transport_mem
  mallocngBudgetPoolAt_split_runtime mallocngBudgetPoolInv mallocngBudgetPoolInv_transport_mem
  mallocngRustCliAllocBudget mallocngRustCliAllocBudgetAt
  rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
  stackAt_bounds_of_mapped
)
open LibsignalBinary.Heap.Fine (
  fineCostModel fineCostModelIface fineCostModelSound fineRustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX codeBlocksPermRX_of_perm_eq
  fineHookRustCliAllocBudget mallocngHookBudgetPool mallocngHookBudgetPool_mapped_lt_userVa
  mallocngHookBudgetPool_transport_mem
  mallocngHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure cliIoResolve_eq_base cliIoReadFile_lookup
  cliIoReadFileSym cliIoOpenSym cliIoReadSym cliIoCloseSym
  cliIoErrnoLocationSym cliIoMemcpySym cliIoFinishGrowSym
  cliIoRustAllocSym cliIoRustReallocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  OpenRdonlyDetResult classifyOpenRdonly classifyOpenRdonly_err_cases classifyOpenRdonly_ok_spec
  muslOpenRdonlyDetSpec setFd_none_setFd_of_fds_none
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslClose48LocalSpec muslReadDir32Spec dirReadErrno32 dirReadErrno32_cases
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (muslReadFileOrStdio32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  ExternPreservesOracleSymtab cliIo_sepWP_carry_oracle_symtab
  cliIoFileCap cliIoFinalCap cliIoReadCaps wantBytes
  bv64_beq_ofNat_false bv64_sub_ofNat
  cliIoSavedRegs12 memRegion4096_split_probe32 memRegion4096_refold_probe32
  cliIoReadFile_stack_split vecHeader_to_err_sret
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof (memRegion24_eq_exists_vecHeader)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_open_pc
  cliIoReadFile_errno1_pc cliIoReadFile_errno2_pc cliIoReadFile_errno3_pc
  cliIoReadFile_read_pc readReg32_of_readReg64_eq
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps (
  toList_cPathOf_length mem_toList_cPathOf_lt_256
  cstrBytes_cPathOf cstrBytes_cPathOf_length fdBytes_open_localFile
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir (muslErrnoAddr_eq_stdErrnoAddr)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof (cliIoOpenEntry)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign (
  cPathOf_eq_pathStr blockingAncestor_eq_blockingAncestorF ioResultErr_eq_ioVecAt_err
)
open LibsignalBinary.Proofs.SignalSession.CliIo.BridgePlaced (
  CliIoFilesOomPreserved memcpySrc_eq_bytesAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget (
  allocCallPreserved_refl allocCallPreserved_trans
  vmPreserved_of_seg vmMemPreserved_of_syscallPreserved
  cliIoVecBuf cliIoVecBuf_zero_intro vecHeader_cliIoVecBuf_entails_ioVecAt_ok
  cliIoFinishGrowBudgetSpec cliIoFinishGrow_budget_ok_withCodeLoaded
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  AllocCapNullInEvents readFileBudgetCondSpec readFileBudgetEvents readFileOverCapEvents
  cliWrOk_path_facts
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (
  readFileAnyBudgetCondSpec subroutine_ok_readFileAnyBudgetCondSpec_of_extHookStack
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoLoopBudget (
  vmPreserved_of_stdState
  cliIoFileLoopBudgetEvents cliIoFileLoopBudgetOut
  cliIoReadFile_ret_epilogue_vm cliIoReadFile_err_cap0_epilogue_vm
  cliIoReadFile_file_loop_budget
)

/-! ## `PoolErrnoSplit` Interface and Outcome / Event Alignment -/

/-- Splits `StdErrnoCell s.tpidrEl0` out of a budget-threaded allocator pool `A.pool lim st s`
    across `open` / `__errno_location` / `.localDir` steps while keeping a `VmPreserved`-invariant
    residual `core lim st s`, and re-absorbs `StdErrnoCell tp` back into `A.pool lim st s`. -/
structure PoolErrnoSplit {M : AllocCostModel} (A : RustCliAllocBudget M)
    (tp brkStart : BitVec 64) where
  core : BudgetLimits → M.σ → State → SepProp
  core_transport : ∀ lim st {s s' : State}, VmMemPreserved s s' → core lim st s' = core lim st s
  pool_mem_transport :
    ∀ lim st {s s' : State}, VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s
  pool_split : ∀ lim st (s : State),
    A.pool lim st s ⊢
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗ (core lim st s ∗ StdErrnoCell s.tpidrEl0)
  pool_join : ∀ lim st {s : State},
    s.tpidrEl0 = tp → s.brkStart = brkStart →
      core lim st s ∗ StdErrnoCell tp ⊢ A.pool lim st s
  pool_mapped_lt_userVa : ∀ lim st {s : State} {R : SepProp} {a : BitVec 64},
    lim.enforced = true → (s.mem ⊨ A.pool lim st s ∗ R) →
      (s.mem.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT

private theorem getLsbD_31_of_readReg32_eq {s : State} {r : Reg} {w : BitVec 32}
    (h : s.readReg32 r = w) :
    (s.readReg64 r).getLsbD 31 = w.getLsbD 31 := by
  have ht : (s.readReg64 r).truncate 32 = w := h
  rw [← ht]
  simp

private theorem getLsbD_31_of_fd_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  have hlt32 : fd.toNat < 2 ^ 32 := Nat.lt_trans hfd (by decide)
  have htr : (fd.truncate 32).toNat = fd.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt32]
  have hd : fd.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt hfd
  simp only [BitVec.getLsbD, htr, Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

private theorem readReg32_zeroExtend_of_truncate {w : BitVec 32} {fd : BitVec 64}
    (hw : w = fd.truncate 32) (hfd : fd.toNat < 2 ^ 32) :
    w.zeroExtend 64 = fd := by
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hfd, Nat.mod_eq_of_lt (Nat.lt_trans hfd (by decide))]

private theorem calleeSaved_x24 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 24#5) = s1.readReg64 (.gpr 24#5) :=
  h.2.2.2.2.2.1

private theorem calleeSaved_fp {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 29#5) = s1.readReg64 (.gpr 29#5) :=
  h.2.2.2.2.2.2.2.2.2.2.1

private theorem calleeSaved_vregs {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    calleeSavedVRegs s2 = calleeSavedVRegs s1 :=
  h.2.2.2.2.2.2.2.2.2.2.2

private theorem refold_cstr_buf4096 (base : BitVec 64) (pathBytes : List (BitVec 8))
    (hlt : pathBytes.length < 4096) :
    (base ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
      memRegion (base + BitVec.ofNat 64 (pathBytes.length + 1)) (4095 - pathBytes.length) ⊢
      memRegion base 4096 := by
  have hlen := cstrBytes_cPathOf_length pathBytes
  have hsub : 4096 - (cstrBytes (cPathOf pathBytes)).length = 4095 - pathBytes.length := by
    rw [hlen]; omega
  rw [← hlen, ← hsub]
  exact pointsToBytes_memRegion_entails base (cstrBytes (cPathOf pathBytes)) 4096
    (by rw [hlen]; omega) (by decide)

theorem vecHeader_empty_entails_ioVecAt_ok (R_alloc : RustAlloc) (sret : BitVec 64) :
    ((sret ↦₆₄ 0#64) ∗ ((sret + 8#64) ↦₆₄ 1#64) ∗ ((sret + 16#64) ↦₆₄ 0#64)) ⊢
      ioVecAt R_alloc sret (.ok []) := by
  have h0 : emp ⊢ cliIoVecBuf R_alloc 0#64 1#64 [] :=
    cliIoVecBuf_zero_intro R_alloc (ptr := 1#64) (by decide)
  have h1 :
      ((sret ↦₆₄ 0#64) ∗ ((sret + 8#64) ↦₆₄ 1#64) ∗ ((sret + 16#64) ↦₆₄ 0#64)) ⊢
        vecHeader sret 0#64 1#64 0#64 ∗ cliIoVecBuf R_alloc 0#64 1#64 [] := by
    refine Entails.trans (by rw [← sepConj_emp (_ ∗ _)]; exact Entails.refl _) ?_
    exact sepConj_mono (Entails.refl _) h0
  exact Entails.trans h1 (vecHeader_cliIoVecBuf_entails_ioVecAt_ok R_alloc sret 0#64 1#64 [])

private theorem cPathOf_eq_mainPathStr (path : List (BitVec 8)) :
    cPathOf path = pathStr path := rfl

private theorem blockingAncestor_eq_mainBlockingAncestorF (fs : FsState) (p : String) :
    blockingAncestor? fs p = blockingAncestorF fs.files p := rfl

private theorem ioResultErr_eq_cliIoVecAt_err (R_alloc : RustAlloc) (sret : BitVec 64) :
    ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) =
      ioVecAt R_alloc sret (.error ()) := rfl

private theorem bytesAt_false (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt false p bs = (p ↦ₛ bs) := by
  simp [bytesAt]

theorem classifyOpenRdonly_err2_align {fs : FsState} {path : List (BitVec 8)}
    (h : classifyOpenRdonly fs (cPathOf path) = .err 2) :
    cliIo.rd fs.files path = .ok [] ∧ readFileBudgetEvents fs.files path = [] := by
  have hrd : cliIo.rd fs.files path = .ok [] := by
    change cliRd fs.files path = .ok []
    unfold cliRd readViewF
    unfold classifyOpenRdonly at h
    rw [cPathOf_eq_mainPathStr, blockingAncestor_eq_mainBlockingAncestorF] at h
    cases hb : blockingAncestorF fs.files (pathStr path) with
    | some a =>
      rw [hb] at h
      cases a with
      | some _ => cases h
      | none => rfl
    | none =>
      rw [hb] at h
      cases hf : fs.files (pathStr path) with
      | none => rfl
      | some e =>
        rw [hf] at h
        cases e <;> (cases ha : fs.allocFd <;> rw [ha] at h <;> cases h)
  refine ⟨hrd, ?_⟩
  unfold readFileBudgetEvents
  rw [hrd]
  rfl

theorem classifyOpenRdonly_errNe2_align {fs : FsState} {path : List (BitVec 8)} {errno : Nat}
    (halloc : fs.allocFd ≠ none)
    (h : classifyOpenRdonly fs (cPathOf path) = .err errno) (hne2 : errno ≠ 2) :
    cliIo.rd fs.files path = .error () ∧ readFileBudgetEvents fs.files path = [] := by
  rcases ha : fs.allocFd with _ | fd0
  · exact absurd ha halloc
  · unfold classifyOpenRdonly at h
    rw [cPathOf_eq_mainPathStr, blockingAncestor_eq_mainBlockingAncestorF, ha] at h
    cases hb : blockingAncestorF fs.files (pathStr path) with
    | some a =>
      rw [hb] at h
      cases a with
      | none =>
        injection h with he
        exact absurd he.symm hne2
      | some _ =>
        have hrd : cliIo.rd fs.files path = .error () := by
          change cliRd fs.files path = .error ()
          unfold cliRd readViewF
          simp [hb]
        refine ⟨hrd, ?_⟩
        unfold readFileBudgetEvents
        simp [hrd, hb]
    | none =>
      rw [hb] at h
      cases hf : fs.files (pathStr path) with
      | none =>
        rw [hf] at h
        injection h with he
        exact absurd he.symm hne2
      | some e =>
        rw [hf] at h
        cases e <;> cases h

theorem classifyOpenRdonly_localDir_align {fs : FsState} {path : List (BitVec 8)} {fd : BitVec 64}
    (h : classifyOpenRdonly fs (cPathOf path) = .ok fd .localDir) :
    cliIo.rd fs.files path = .error () ∧ readFileBudgetEvents fs.files path = [] := by
  obtain ⟨hb, _, _, _, _, hcases⟩ := classifyOpenRdonly_ok_spec h
  rw [cPathOf_eq_mainPathStr, blockingAncestor_eq_mainBlockingAncestorF] at hb
  rcases hcases with ⟨_, hf⟩ | ⟨hk, _⟩
  swap
  · cases hk
  rw [cPathOf_eq_mainPathStr] at hf
  have hrd : cliIo.rd fs.files path = .error () := by
    change cliRd fs.files path = .error ()
    unfold cliRd readViewF
    simp [hb, hf]
  refine ⟨hrd, ?_⟩
  unfold readFileBudgetEvents
  simp [hrd, hb, hf]

theorem classifyOpenRdonly_localFile_align {fs : FsState} {path bs : List (BitVec 8)}
    (hb : blockingAncestor? fs (cPathOf path) = none)
    (hf : fs.files (cPathOf path) = some (.file bs)) :
    cliIoFileLoopBudgetOut bs = cliIo.rd fs.files path ∧
      cliIoFileLoopBudgetEvents bs = readFileBudgetEvents fs.files path := by
  rw [cPathOf_eq_mainPathStr, blockingAncestor_eq_mainBlockingAncestorF] at hb
  rw [cPathOf_eq_mainPathStr] at hf
  have hcap_eq : CryptoVerification.SignalSession.fileCapBytes = 2097152 := rfl
  by_cases hle : bs.length ≤ 2097152
  · have hrd : cliIo.rd fs.files path = .ok bs := by
      change cliRd fs.files path = .ok bs
      unfold cliRd readViewF
      simp [hb, hf, hcap_eq, hle]
    refine ⟨by simp [cliIoFileLoopBudgetOut, hle, hrd], ?_⟩
    unfold cliIoFileLoopBudgetEvents readFileBudgetEvents
    simp [hle, hrd]
  · have hgt : 2097152 < bs.length := Nat.lt_of_not_ge hle
    have hrd : cliIo.rd fs.files path = .error () := by
      change cliRd fs.files path = .error ()
      unfold cliRd readViewF
      simp [hb, hf, hcap_eq, hle]
    refine ⟨by simp [cliIoFileLoopBudgetOut, hle, hrd], ?_⟩
    unfold cliIoFileLoopBudgetEvents readFileBudgetEvents
    simp [hle, hgt, hrd, hb, hf]

/-! ## Valid-Path Pre-`open` Segment (`+0x00 .. +0x84`) -/

section
arm64_proof_prelude

private abbrev memcpySrc8 (ro : Bool) (a : BitVec 64) (b : BitVec 8) : SepProp :=
  bif ro then a ↦₈ᵣ b else a ↦₈ b

private theorem memcpySrc_cons (ro : Bool) (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    memcpySrc ro a (b :: bs) = (memcpySrc8 ro a b ∗ memcpySrc ro (a + 1#64) bs) := by
  cases ro <;> simp [memcpySrc, memcpySrc8]

private theorem memcpySrc_singleton (ro : Bool) (a : BitVec 64) (b : BitVec 8) :
    memcpySrc ro a [b] = memcpySrc8 ro a b := by
  cases ro <;> simp [memcpySrc, memcpySrc8]

private structure FileScanPreserved (s0 s1 : State) : Prop where
  run_eq : s1.status = .Running
  sp_eq : s1.sp = s0.sp
  spAligned_eq : s1.spAligned = true
  fs_eq : s1.fs = s0.fs
  trace_eq : s1.trace = s0.trace
  sig_eq : s1.sigActions = s0.sigActions
  tp_eq : s1.tpidrEl0 = s0.tpidrEl0
  bs_eq : s1.brkStart = s0.brkStart
  oracle_eq : s1.oracle = s0.oracle
  symtab_eq : s1.symtab = s0.symtab
  lr_eq : s1.readReg64 .lr = s0.readReg64 .lr
  x1_eq : s1.readReg64 .x1 = s0.readReg64 .x1
  x8_eq : s1.readReg64 .x8 = s0.readReg64 .x8
  x29_eq : s1.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5)
  vregs_eq : calleeSavedVRegs s1 = calleeSavedVRegs s0

private theorem FileScanPreserved.trans_right {s0 s1 s2 : State}
    (h12 : FileScanPreserved s1 s2) (h01 : FileScanPreserved s0 s1) :
    FileScanPreserved s0 s2 :=
  ⟨h12.run_eq, h12.sp_eq.trans h01.sp_eq, h12.spAligned_eq,
   h12.fs_eq.trans h01.fs_eq, h12.trace_eq.trans h01.trace_eq,
   h12.sig_eq.trans h01.sig_eq, h12.tp_eq.trans h01.tp_eq,
   h12.bs_eq.trans h01.bs_eq, h12.oracle_eq.trans h01.oracle_eq,
   h12.symtab_eq.trans h01.symtab_eq, h12.lr_eq.trans h01.lr_eq,
   h12.x1_eq.trans h01.x1_eq, h12.x8_eq.trans h01.x8_eq,
   h12.x29_eq.trans h01.x29_eq, h12.vregs_eq.trans h01.vregs_eq⟩

private theorem cliIoReadFile_nul_scan_loop_valid [CliIoPlacement] {ro : Bool} {tgt : BitVec 64}
    {post : State → SepProp → Prop}
    (rem : List (BitVec 8)) {idx n : Nat} {pathPtr dst scratchPtr : BitVec 64}
    {F : SepProp} {s : State} {sc0 : BitVec 8}
    (h1 : 1 ≤ rem.length) (hsum : idx + rem.length = n) (hn : n < 4096) (hnul : 0#8 ∉ rem)
    (hpc : s.pc = cliIoPl03.base + 84#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = pathPtr + BitVec.ofNat 64 idx)
    (hx9 : s.readReg64 (.gpr 9#5) = scratchPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = dst + BitVec.ofNat 64 idx)
    (hx12 : s.readReg64 (.gpr 12#5) = BitVec.ofNat 64 rem.length)
    (hnone : ∀ sf : State, ∀ sc1 : BitVec 8, sf.pc = cliIoPl03.base + 112#64 →
      FileScanPreserved s sf →
      SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) tgt sf
        (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
          ((dst + BitVec.ofNat 64 idx) ↦ₛ rem) ∗
          memRegion (dst + BitVec.ofNat 64 n) (4096 - n) ∗
          (scratchPtr ↦₈ sc1) ∗ F) post) :
    SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) tgt s
      (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
        memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) ∗
        (scratchPtr ↦₈ sc0) ∗ F) post := by
  induction rem generalizing idx F s sc0 with
  | nil => simp at h1
  | cons b rem' ih =>
    have hb0 : b ≠ 0#8 := fun he => hnul (he ▸ List.mem_cons_self ..)
    have hnul_tl : 0#8 ∉ rem' := fun hm => hnul (List.mem_cons_of_mem b hm)
    obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false hb0
    wp_conv_pre =>
      rw [show 4096 - idx = (4095 - idx) + 1 by simp at hsum; omega,
        memRegion_succ_off dst idx (4095 - idx) (by simp at hsum; omega)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro z_dst
    rcases rem' with _ | ⟨b2, rest⟩
    · have hlen1 : ([b] : List (BitVec 8)).length = 1 := rfl
      rw [hlen1] at hx12
      wp_conv_pre => rw [memcpySrc_singleton]
      apply rustSepWP_cut (mid := cliIoPl03.base + 112#64)
      cases ro <;>
      · dsimp only [memcpySrc, memcpySrc8, cond] at hnone ⊢
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
        refine SepWP.weaken_pre ?_
          (hnone _ b (by simp [arm64_norm])
            ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
             by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩)
        rw [show n = idx + 1 by simp at hsum; omega,
          show 4096 - (idx + 1) = 4095 - idx by omega]
        simp only [pointsToBytes_singleton, pointsToBytesRO_singleton, bv_lin_norm]
        sep_entail
    · have hlen_cons_lt : (b :: b2 :: rest).length < 4096 := by
        simp only [List.length_cons] at hsum ⊢; omega
      have hsub1 : BitVec.ofNat 64 (b :: b2 :: rest).length - 1#64 =
          BitVec.ofNat 64 (b2 :: rest).length :=
        bv64_sub_ofNat (b := 1) (by simp)
      have hne1 : (BitVec.ofNat 64 (b :: b2 :: rest).length != 1#64) = true := by
        rw [bne_iff_ne]
        intro heq
        have hto := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, List.length_cons] at hto hlen_cons_lt
        omega
      have hp_add1 : pathPtr + BitVec.ofNat 64 idx + 1#64 =
          pathPtr + BitVec.ofNat 64 (idx + 1) := by rw [BitVec.ofNat_add]; bv_lin
      have hd_add1 : dst + BitVec.ofNat 64 idx + 1#64 =
          dst + BitVec.ofNat 64 (idx + 1) := by rw [BitVec.ofNat_add]; bv_lin
      let DstHead : SepProp := (dst + BitVec.ofNat 64 idx) ↦₈ b
      wp_conv_pre => rw [memcpySrc_cons]; simp only [sepConj_assoc]
      apply rustSepWP_cut (mid := cliIoPl03.base + 84#64)
      cases ro
      · dsimp only [memcpySrc8, cond]
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
        let SrcHead : SepProp := (pathPtr + BitVec.ofNat 64 idx) ↦₈ b
        refine SepWP.weaken_pre
          (P' := memcpySrc false (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
            memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ∗
            (scratchPtr ↦₈ b) ∗ (SrcHead ∗ DstHead ∗ F))
          (by dsimp only [SrcHead, DstHead]
              rw [show 4096 - (idx + 1) = 4095 - idx by omega, ← hp_add1, ← hd_add1]
              sep_entail)
          (ih (idx := idx + 1) (F := SrcHead ∗ DstHead ∗ F) (sc0 := b)
            (by simp) (by simp only [List.length_cons] at hsum ⊢; omega) hnul_tl
            (by simp [arm64_norm])
            (by simpa [arm64_norm] using hrun)
            (by simpa [arm64_norm] using hsp)
            (by rw [← hp_add1]; simp only [arm64_norm])
            (by simpa [arm64_norm] using hx9)
            (by rw [← hd_add1]; simp only [arm64_norm])
            (by simp only [arm64_norm])
            (fun sf sc1 hpc_f hpres2 =>
              SepWP.weaken_pre ?_
                (hnone sf sc1 hpc_f
                  (hpres2.trans_right
                    ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                     by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                     by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩))))
        rw [memcpySrc_cons (b := b) (bs := b2 :: rest), pointsToBytes_cons_off dst idx b (b2 :: rest), hp_add1]
        dsimp only [memcpySrc8, cond, SrcHead, DstHead]; sep_entail
      · dsimp only [memcpySrc8, cond]
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
        let SrcHead : SepProp := (pathPtr + BitVec.ofNat 64 idx) ↦₈ᵣ b
        refine SepWP.weaken_pre
          (P' := memcpySrc true (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
            memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ∗
            (scratchPtr ↦₈ b) ∗ (SrcHead ∗ DstHead ∗ F))
          (by dsimp only [SrcHead, DstHead]
              rw [show 4096 - (idx + 1) = 4095 - idx by omega, ← hp_add1, ← hd_add1]
              sep_entail)
          (ih (idx := idx + 1) (F := SrcHead ∗ DstHead ∗ F) (sc0 := b)
            (by simp) (by simp only [List.length_cons] at hsum ⊢; omega) hnul_tl
            (by simp [arm64_norm])
            (by simpa [arm64_norm] using hrun)
            (by simpa [arm64_norm] using hsp)
            (by rw [← hp_add1]; simp only [arm64_norm])
            (by simpa [arm64_norm] using hx9)
            (by rw [← hd_add1]; simp only [arm64_norm])
            (by simp only [arm64_norm])
            (fun sf sc1 hpc_f hpres2 =>
              SepWP.weaken_pre ?_
                (hnone sf sc1 hpc_f
                  (hpres2.trans_right
                    ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                     by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                     by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩))))
        rw [memcpySrc_cons (b := b) (bs := b2 :: rest), pointsToBytes_cons_off dst idx b (b2 :: rest), hp_add1]
        dsimp only [memcpySrc8, cond, SrcHead, DstHead]; sep_entail

theorem cliIoReadFile_pre_open_valid_vm [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {ro : Bool} {s0 : State} {sret pathPtr : BitVec 64} {pathBytes : List (BitVec 8)}
    {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hlt : pathBytes.length < 4096) (hnul : 0#8 ∉ pathBytes)
    (hcl0 : signalSessionIoMultiLib.CodeLoaded cliIoMpl s0.mem)
    (hpc0 : s0.pc = cliIoPl03.base) (hrun0 : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = pathPtr)
    (hx1 : (s0.readReg64 .x1).toNat = pathBytes.length)
    (hx8 : s0.readReg64 .x8 = sret)
    (hat_open : ∀ (sm : State) (ev0 : BitVec 32) (v0 v1 v2 st0 st1 st2 st3 : BitVec 64),
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sm.mem →
      sm.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym →
      sm.status = .Running →
      sm.sp = s0.sp - 8320#64 →
      sm.spAligned = true →
      sm.readReg64 .lr = cliIoPl03.base + 136#64 →
      sm.readReg64 .x0 = s0.sp - 8320#64 →
      sm.readReg32 .x1 = O_CLOEXEC_W32 →
      sm.readReg64 (.gpr 24#5) = sret →
      sm.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      AllocCallPreserved s0 sm →
      SepWP P (s0.readReg64 .lr) sm
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
          memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
            (4095 - pathBytes.length) ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          memcpySrc ro pathPtr pathBytes ∗
          vecHeader sret v0 v1 v2 ∗
          (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗
          P_pool sm)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗
        memRegion sret 24 ∗ StdErrnoCell s0.tpidrEl0 ∗ P_pool s0)
      post oomProp := by
  have hlen_lt64 : pathBytes.length < 2 ^ 64 := hx1 ▸ (s0.readReg64 .x1).isLt
  have hx1_bv : s0.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := by
    rw [← hx1]; simp
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [cliIoReadFile_stack_split s0.sp hlo hhi,
      memRegion24_eq_exists_vecHeader sret,
      memRegion4096_split_probe32 (s0.sp - 8320#64),
      memRegion4096_split_probe32 (s0.sp - 4224#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
  refine SepWP.exists_elim fun ev0 =>
    SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 =>
    SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 =>
    SepWP.exists_elim fun r4 => SepWP.exists_elim fun r5 =>
    SepWP.exists_elim fun r6 => SepWP.exists_elim fun r7 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r9 =>
    SepWP.exists_elim fun r10 => SepWP.exists_elim fun r11 =>
    SepWP.exists_elim fun wp4224 => SepWP.exists_elim fun wp8320 => ?_
  have hrefold8320 :
      memRegion (s0.sp - 8320#64) 32 ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 8280#64) 4056 ⊢ memRegion (s0.sp - 8320#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 8320#64) 0#64
  have hrefold4224 :
      memRegion (s0.sp - 4224#64) 32 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 4056 ⊢ memRegion (s0.sp - 4224#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 4224#64) 0#64
  have hule_t : BitVec.ule (BitVec.ofNat 64 pathBytes.length) 4095#64 = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_f : BitVec.ult 4095#64 (BitVec.ofNat 64 pathBytes.length) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl0
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym)
  intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = cliIoPl03.base := hcpu1.pc_eq.trans hpc0
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx0_1' : s1'.readReg64 .x0 = pathPtr := (hcpu1.readReg64 .x0).trans hx0
  have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := (hcpu1.readReg64 .x1).trans hx1_bv
  have hx8_1' : s1'.readReg64 .x8 = sret := (hcpu1.readReg64 .x8).trans hx8
  by_cases hnil : pathBytes = []
  · subst hnil
    have hnil_len : ([] : List (BitVec 8)).length = 0 := rfl
    rw [hnil_len] at hx1_1'
    apply rustSepWP_cut (mid := cliIoPl03.base + 112#64)
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1') ?_
    have hcarve8320 :
        memRegion (s0.sp - 8320#64) 4096 =
          ((∃∗ z0 : BitVec 8, (s0.sp - 8320#64) ↦₈ z0) ∗ memRegion (s0.sp - 8319#64) 4095) := by
      simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 8320#64) 0 4095 (by decide)
    let KeepEmpty0 : SepProp :=
      memcpySrc ro pathPtr [] ∗
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        (((s0.sp - 96#64) ↦₆₄ s1'.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s1'.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s1'.readReg64 (.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s1'.readReg64 (.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s1'.readReg64 (.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s1'.readReg64 (.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s1'.readReg64 (.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s1'.readReg64 (.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s1'.readReg64 (.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s1'.readReg64 (.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s1'.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s1'.readReg64 (.gpr 19#5))) ∗
        vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool s0
    refine SepWP.weaken_pre
      (P' := ((∃∗ z0 : BitVec 8, (s0.sp - 8320#64) ↦₈ z0) ∗ memRegion (s0.sp - 8319#64) 4095) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗ KeepEmpty0)
      (by rw [← hcarve8320]
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hrefold8320 (sepConj_mono_left (Q := KeepEmpty0) hrefold4224))
              (by dsimp only [KeepEmpty0]; sep_entail))
          dsimp only [KeepEmpty0]; sep_entail) ?_
    wp_conv_pre => dsimp only [KeepEmpty0]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro z0
    wp_sym_steps
    refine SepWP.done cliIoReadFile_open_pc (by simpa [arm64_norm] using hrun1')
      fun sm hcpu_m0 hcl_m hnsp_m hsym_m => ?_
    have hcpu_m := hcpu_m0.1
    have ⟨hacp_0m, hvm_0m⟩ :=
      vmPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m hsym_m
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq : P_pool s0 = P_pool sm := (hP_vm hvm_0m.toVmMemPreserved).symm
    have hsp_m_eq : sm.sp = s0.sp - 8320#64 := hcpu_m.sp_eq.trans (by simp [arm64_norm])
    have hsp_m : sm.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hw1_m : sm.readReg32 .x1 = O_CLOEXEC_W32 := by
      rw [State.readReg32, hcpu_m.readReg64 .x1]; simp [arm64_norm, O_CLOEXEC_W32]
    refine SepWP.weaken_pre ?_
      (hat_open sm ev0 v0 v1 v2 st0 st1 st2 st3
        hcl_m (hcpu_m.pc_eq.trans cliIoReadFile_open_pc) (hcpu_m.status_eq.trans hrun1')
        hsp_m_eq hsp_m
        (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
        (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
        hw1_m
        (by rw [hcpu_m.readReg64]; simp [arm64_norm])
        (by rw [hcpu_m.readReg64]; simp [arm64_norm])
        (hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
        hacp_0m)
    have hcstr_nil : cstrBytes (cPathOf []) = [0#8] := by rw [cstrBytes_cPathOf]; rfl
    rw [hcstr_nil, pointsToBytes_singleton, hpool_eq,
      hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
      hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
      hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
      hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
      hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
      hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
    dsimp only [cliIoSavedRegs12]; simp only [bv_lin_norm]
    sep_entail
  · have h1_pos : 1 ≤ pathBytes.length := List.length_pos_iff.mpr hnil
    have hnez_len : (BitVec.ofNat 64 pathBytes.length == 0#64) = false :=
      bv64_beq_ofNat_false (b := 0) (by omega) (by omega) (by decide)
    apply rustSepWP_cut (mid := cliIoPl03.base + 84#64)
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm])
      (by simpa [arm64_norm] using hrun1') ?_
    let F_ok : SepProp :=
      memRegion (s0.sp - 4223#64) 4095 ∗
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool s0
    have hcarve4224' :
        memRegion (s0.sp - 4224#64) 4096 ⊢
          (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095 := by
      rw [show memRegion (s0.sp - 4224#64) 4096 =
        ((∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095) by
          simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 4224#64) 0 4095 (by decide)]
      exact Entails.refl _
    refine SepWP.weaken_pre
      (P' := memcpySrc ro (pathPtr + 0#64) pathBytes ∗
        memRegion ((s0.sp - 8320#64) + 0#64) 4096 ∗
        (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ F_ok) ?_ ?_
    · rw [hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
        hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
        hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
        hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
        hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
        hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
      dsimp only [F_ok, cliIoSavedRegs12]; simp only [bv_lin_norm]
      let KeepOk0 : SepProp :=
        memcpySrc ro pathPtr pathBytes ∗
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
          vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool s0
      refine Entails.trans ?_
        (Entails.trans
          (sepConj_mono hrefold8320
            (sepConj_mono_left (Q := KeepOk0) (Entails.trans hrefold4224 hcarve4224')))
          (by dsimp only [KeepOk0]; simp only [bv_lin_norm]; sep_entail))
      dsimp only [KeepOk0]; simp only [bv_lin_norm]; sep_entail
    · wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro sc0
      wp_conv_pre => simp only [← sepConj_assoc]
      refine SepWP.weaken_pre (by sep_entail)
        (cliIoReadFile_nul_scan_loop_valid pathBytes (idx := 0) (n := pathBytes.length)
          (pathPtr := pathPtr) (dst := s0.sp - 8320#64) (scratchPtr := s0.sp - 4224#64)
          (F := F_ok) (sc0 := sc0)
          h1_pos (Nat.zero_add _) hlt hnul
          (by simp [arm64_norm])
          (by simpa [arm64_norm] using hrun1')
          (by simp only [State.spAligned, arm64_norm]; exact hsp0)
          (by simp [arm64_norm, hx0_1', bv_lin_norm])
          (by simp only [arm64_norm])
          (by simp [arm64_norm, bv_lin_norm])
          (by simp [arm64_norm])
          (fun sf_scan sc1 hpc_scan hpres_scan => ?_))
      dsimp only [F_ok]
      wp_conv_pre =>
        rw [show 4096 - pathBytes.length = (4095 - pathBytes.length) + 1 by omega,
          memRegion_succ_off (s0.sp - 8320#64) pathBytes.length (4095 - pathBytes.length) (by omega)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro z_nul
      have hx1_scan : sf_scan.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
        hpres_scan.x1_eq.trans (by simp [arm64_norm, hx1_1'])
      have hx8_scan : sf_scan.readReg64 .x8 = sret :=
        hpres_scan.x8_eq.trans (by simp [arm64_norm, hx8_1'])
      have hsp_scan_eq : sf_scan.sp = s0.sp - 8320#64 :=
        hpres_scan.sp_eq.trans (by simp [arm64_norm])
      have hrun_scan := hpres_scan.run_eq
      have hsp_scan := hpres_scan.spAligned_eq
      wp_sym_steps
      refine SepWP.done cliIoReadFile_open_pc (by simpa [arm64_norm] using hrun_scan)
        fun sm hcpu_m0 hcl_m hnsp_m hsym_m => ?_
      have hcpu_m := hcpu_m0.1
      have ⟨hacp_0m, hvm_0m⟩ :=
        vmPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m hsym_m
          ((by simp [arm64_norm] : _ = sf_scan.tpidrEl0).trans
            (hpres_scan.tp_eq.trans (by simp [arm64_norm])))
          ((by simp [arm64_norm] : _ = sf_scan.sigActions).trans
            (hpres_scan.sig_eq.trans (by simp [arm64_norm])))
          ((by simp [arm64_norm] : _ = sf_scan.oracle).trans
            (hpres_scan.oracle_eq.trans (by simp [arm64_norm])))
      have hpool_eq : P_pool s0 = P_pool sm := (hP_vm hvm_0m.toVmMemPreserved).symm
      have hsp_m_eq : sm.sp = s0.sp - 8320#64 :=
        hcpu_m.sp_eq.trans (by simp [arm64_norm, hsp_scan_eq])
      have hsp_m : sm.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 8320#64 hsp0
      have hw1_m : sm.readReg32 .x1 = O_CLOEXEC_W32 := by
        rw [State.readReg32, hcpu_m.readReg64 .x1]; simp [arm64_norm, O_CLOEXEC_W32]
      have hx29_m : sm.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_m.readReg64 (.gpr 29#5)]; simp only [arm64_norm]
        exact hpres_scan.x29_eq.trans (by simp [arm64_norm])
      have hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
        hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sf_scan).trans
          (hpres_scan.vregs_eq.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)))
      refine SepWP.weaken_pre ?_
        (hat_open sm ev0 v0 v1 v2 st0 st1 st2 st3
          hcl_m (hcpu_m.pc_eq.trans cliIoReadFile_open_pc) (hcpu_m.status_eq.trans hrun_scan)
          hsp_m_eq hsp_m
          (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
          (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
          hw1_m
          (by rw [hcpu_m.readReg64]; simp [arm64_norm])
          hx29_m hvregs_m hacp_0m)
      have hmerge4224 :
          ((s0.sp - 4224#64) ↦₈ sc1) ∗ memRegion (s0.sp - 4223#64) 4095 ⊢
            memRegion (s0.sp - 4224#64) 4096 := by
        simpa only [bv_lin_norm] using memRegion_byte_merge (s0.sp - 4224#64) sc1 4095 (by decide)
      have hcstr_eq :
          ((s0.sp - 8320#64) ↦ₛ pathBytes) ∗
            (((s0.sp - 8320#64) + BitVec.ofNat 64 pathBytes.length) ↦₈ 0#8) =
          ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) := by
        rw [cstrBytes_cPathOf, pointsToBytes_snoc]
      rw [hpool_eq]
      let KeepOk1 : SepProp :=
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
          memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
            (4095 - pathBytes.length) ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          memcpySrc ro pathPtr pathBytes ∗
          vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool sm
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_left (Q := KeepOk1) hmerge4224)
          (by dsimp only [KeepOk1]; simp only [bv_lin_norm]; sep_entail))
      dsimp only [KeepOk1]
      rw [← hcstr_eq]
      simp only [bv_lin_norm]
      sep_entail

/-! ## Post-`open` `.err` and `.localDir` Paths -/

theorem cliIoReadFile_open_err_vm [CliIoPlacement]
    (R_alloc : RustAlloc)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 so : State} {sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {errno stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) (hsp0 : s0.spAligned = true)
    (herr_cases : errno = 2 ∨ errno = 20 ∨ errno = 24)
    (hcl_o : signalSessionIoMultiLib.CodeLoaded cliIoMpl so.mem)
    (hpc_o : so.pc = cliIoPl03.base + 136#64) (hrun_o : so.status = .Running)
    (hsp_o : so.sp = s0.sp - 8320#64)
    (hw0_o : so.readReg32 .x0 = 0xffffffff#32)
    (hx24_o : so.readReg64 (.gpr 24#5) = sret)
    (htp_o : so.tpidrEl0 = s0.tpidrEl0)
    (hvregs_o : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_o : so.fs = s0.fs) (htr_o : so.trace = s0.trace)
    (hsig_o : so.sigActions = s0.sigActions) (hbs_o : so.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (ioVecAt R_alloc sret (if errno = 2 then .ok [] else .error ()) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ BitVec.ofNat 32 errno) ∗ P_pool so)
      post oomProp := by
  let ev := BitVec.ofNat 32 errno
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_o
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl03.base + 136#64 := hcpu_o.pc_eq.trans hpc_o
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_o
  have hsp_o' : so'.spAligned = true := by
    rw [hcpu_o.spAligned]; simp only [State.spAligned]; rw [hsp_o]
    exact s0.spAligned_sub 8320#64 hsp0
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = true := by
    rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_o]; decide
  wp_sym_steps
  refine SepWP.done cliIoReadFile_errno1_pc (by simpa [arm64_norm] using hrun_o')
    fun sm1 hcpu_10 hcl_1 hnsp_1 hsym_1 => ?_
  have hcpu_1 := hcpu_10.1
  have ⟨hacp_o1, hvm_o1⟩ :=
    vmPreserved_of_seg hcpu_o0 hcpu_10 hnsp_1 hsym_1
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_o1 : P_pool so = P_pool sm1 := (hP_vm hvm_o1.toVmMemPreserved).symm
  have hpc_1 : sm1.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
    hcpu_1.pc_eq.trans cliIoReadFile_errno1_pc
  have hrun_1 : sm1.status = .Running := hcpu_1.status_eq.trans hrun_o'
  have hsp_1_eq : sm1.sp = s0.sp - 8320#64 :=
    hcpu_1.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_o))
  have hsp_1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_1_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_1 : sm1.readReg64 .lr = cliIoPl03.base + 144#64 := by
    rw [hcpu_1.readReg64 .lr]; simp [arm64_norm]
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_1.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx24_o
  have htp_1 : sm1.tpidrEl0 = s0.tpidrEl0 := hacp_o1.2.2.2.1.trans htp_o
  have hvregs_1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 :=
    hcpu_1.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_o))
  let T_el1 : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
      (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗ P_pool sm1
  apply seqCodeLoaded hcl_1 (mid := cliIoPl03.base + 144#64)
  apply (SepWP.call_subroutine_frame herrno (F := T_el1) (x := ())
    hpc_1 hrun_1 hsp_1 hlr_1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslErrnoLocationSpec, T_el1]; rw [emp_sepConj]
    rw [hpool_eq_o1] at hm'
    exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
  · intro se1 hpc_se1 hrun_se1 hsp_se1 hcs_1
    refine SepWP.done hpc_se1 hrun_se1 fun hcl_se1 => ?_
    wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el1]
    apply SepWP.pure_elim; rintro ⟨hx0_se1, _, hstd_1⟩
    have hpool_eq_1 : P_pool sm1 = P_pool se1 :=
      (hP_vm (vmPreserved_of_stdState hstd_1).toVmMemPreserved).symm
    have hsp_se1_eq : se1.sp = s0.sp - 8320#64 := hsp_se1.trans hsp_1_eq
    have hx0_se1' : se1.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
      rw [hx0_se1, muslErrnoAddr_eq_stdErrnoAddr, htp_1]
    have hx24_se1 : se1.readReg64 (.gpr 24#5) = sret := (calleeSaved_x24 hcs_1).trans hx24_1
    have htp_se1 : se1.tpidrEl0 = s0.tpidrEl0 := hstd_1.2.2.1.trans htp_1
    have hvregs_se1 : calleeSavedVRegs se1 = calleeSavedVRegs s0 :=
      (calleeSaved_vregs hcs_1).trans hvregs_1
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_se1
      (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
    intro se1' hcpu_e10; have hcpu_e1 := hcpu_e10.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_e1' : se1'.pc = cliIoPl03.base + 144#64 := hcpu_e1.pc_eq.trans hpc_se1
    have hrun_e1' : se1'.status = .Running := hcpu_e1.status_eq.trans hrun_se1
    have hsp_e1' : se1'.spAligned = true := by
      rw [hcpu_e1.spAligned]; simp only [State.spAligned]; rw [hsp_se1_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx0_e1' : se1'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
      (hcpu_e1.readReg64 _).trans hx0_se1'
    have hev_ne4 : (BitVec.setWidth 64 ev - 4#64 == 0#64) = false := by
      dsimp only [ev]; rcases herr_cases with rfl | rfl | rfl <;> decide
    wp_sym_steps
    have herrno2_pc :
        cliIoPl03.ρ "__errno_location" =
          signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym := by
      simpa [arm64_norm, cliIoErrnoLocationSym] using cliIoReadFile_errno2_pc
    refine SepWP.done (by simpa [arm64_norm] using herrno2_pc)
      (by simpa [arm64_norm] using hrun_e1')
      fun sm2 hcpu_20 hcl_2 hnsp_2 hsym_2 => ?_
    have hcpu_2 := hcpu_20.1
    have ⟨hacp_12, hvm_12⟩ :=
      vmPreserved_of_seg hcpu_e10 hcpu_20 hnsp_2 hsym_2
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_12 : P_pool se1 = P_pool sm2 := (hP_vm hvm_12.toVmMemPreserved).symm
    have hpc_2 : sm2.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
      hcpu_2.pc_eq.trans (by simpa [arm64_norm] using herrno2_pc)
    have hrun_2 : sm2.status = .Running := hcpu_2.status_eq.trans hrun_e1'
    have hsp_2_eq : sm2.sp = s0.sp - 8320#64 :=
      hcpu_2.sp_eq.trans ((by simp [arm64_norm] : _ = se1'.sp).trans (hcpu_e1.sp_eq.trans hsp_se1_eq))
    have hsp_2 : sm2.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_2_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hlr_2 : sm2.readReg64 .lr = cliIoPl03.base + 160#64 := by
      rw [hcpu_2.readReg64 .lr]; simp [arm64_norm]
    have hx24_2 : sm2.readReg64 (.gpr 24#5) = sret := by
      rw [hcpu_2.readReg64]; simp only [arm64_norm]; exact (hcpu_e1.readReg64 _).trans hx24_se1
    have htp_2 : sm2.tpidrEl0 = s0.tpidrEl0 := hacp_12.2.2.2.1.trans htp_se1
    have hvregs_2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 :=
      hcpu_2.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se1').trans
        (hcpu_e1.calleeSavedVRegs.trans hvregs_se1))
    let T_el2 : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗ P_pool sm2
    apply seqCodeLoaded hcl_2 (mid := cliIoPl03.base + 160#64)
    apply (SepWP.call_subroutine_frame herrno (F := T_el2) (x := ())
      hpc_2 hrun_2 hsp_2 hlr_2
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslErrnoLocationSpec, T_el2]; rw [emp_sepConj]
      rw [hpool_eq_1, hpool_eq_12] at hm'
      exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
    · intro se2 hpc_se2 hrun_se2 hsp_se2 hcs_2
      refine SepWP.done hpc_se2 hrun_se2 fun hcl_se2 => ?_
      wp_conv_pre =>
        dsimp only [muslErrnoLocationSpec, T_el2]
        rw [show vecHeader sret v0 v1 v2 =
          (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
        simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_se2, _, hstd_2⟩
      have hpool_eq_2 : P_pool sm2 = P_pool se2 :=
        (hP_vm (vmPreserved_of_stdState hstd_2).toVmMemPreserved).symm
      have hsp_se2_eq : se2.sp = s0.sp - 8320#64 := hsp_se2.trans hsp_2_eq
      have hx0_se2' : se2.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
        rw [hx0_se2, muslErrnoAddr_eq_stdErrnoAddr, htp_2]
      have hx24_se2 : se2.readReg64 (.gpr 24#5) = sret := hcs_2.2.2.2.2.2.1.trans hx24_2
      have htp_se2 : se2.tpidrEl0 = s0.tpidrEl0 := hstd_2.2.2.1.trans htp_2
      have hvregs_se2 : calleeSavedVRegs se2 = calleeSavedVRegs s0 :=
        (calleeSaved_vregs hcs_2).trans hvregs_2
      have hfs_se2 : se2.fs = s0.fs :=
        hstd_2.1.trans (hacp_12.1.trans (hstd_1.1.trans (hacp_o1.1.trans hfs_o)))
      have htr_se2 : se2.trace = s0.trace :=
        hstd_2.2.1.trans (hacp_12.2.1.trans (hstd_1.2.1.trans (hacp_o1.2.1.trans htr_o)))
      have hsig_se2 : se2.sigActions = s0.sigActions :=
        hstd_2.2.2.2.1.trans (hacp_12.2.2.1.trans (hstd_1.2.2.2.1.trans (hacp_o1.2.2.1.trans hsig_o)))
      have hbs_se2 : se2.brkStart = s0.brkStart :=
        hstd_2.2.2.2.2.2.1.trans (hacp_12.2.2.2.2.1.trans (hstd_1.2.2.2.2.2.1.trans (hacp_o1.2.2.2.2.1.trans hbs_o)))
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_se2
        (mid := cliIoPl03.base + 520#64)
      intro se2' hcpu_e20; have hcpu_e2 := hcpu_e20.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_e2' : se2'.pc = cliIoPl03.base + 160#64 := hcpu_e2.pc_eq.trans hpc_se2
      have hrun_e2' : se2'.status = .Running := hcpu_e2.status_eq.trans hrun_se2
      have hsp_e2' : se2'.spAligned = true := by
        rw [hcpu_e2.spAligned]; simp only [State.spAligned]; rw [hsp_se2_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx0_e2' : se2'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
        (hcpu_e2.readReg64 _).trans hx0_se2'
      have hx24_e2' : se2'.readReg64 (.gpr 24#5) = sret :=
        (hcpu_e2.readReg64 _).trans hx24_se2
      by_cases he2 : errno = 2
      · subst he2
        dsimp only [ev]
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e2')
          fun se_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
        have hcpu_r := hcpu_r0.1
        have ⟨hacp_2r, hvm_2r⟩ :=
          vmPreserved_of_seg hcpu_e20 hcpu_r0 hnsp_r hsym_r
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_2r : P_pool se2 = P_pool se_ret := (hP_vm hvm_2r.toVmMemPreserved).symm
        have hsp_r_eq : se_ret.sp = s0.sp - 8320#64 :=
          hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = se2'.sp).trans (hcpu_e2.sp_eq.trans hsp_se2_eq))
        have hvregs_r : calleeSavedVRegs se_ret = calleeSavedVRegs s0 :=
          hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se2').trans
            (hcpu_e2.calleeSavedVRegs.trans hvregs_se2))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue_vm hext3 hP_vm (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := ioVecAt R_alloc sret (if (2 : Nat) = 2 then .ok [] else .error ()) ∗
              StdErrnoCell s0.tpidrEl0)
            hlo hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_r.status_eq.trans hrun_e2') hsp0 hsp_r_eq hvregs_r
            fun sf hpc_f hrun_f hsp_f hcs_f _ hacp_rf {_Pre_f} hent =>
              hcont sf hpc_f hrun_f hsp_f hcs_f
                (hacp_rf.1.trans (hacp_2r.1.trans hfs_se2))
                (hacp_rf.2.1.trans (hacp_2r.2.1.trans htr_se2))
                (hacp_rf.2.2.1.trans (hacp_2r.2.2.1.trans hsig_se2))
                (hacp_rf.2.2.2.1.trans (hacp_2r.2.2.2.1.trans htp_se2))
                (hacp_rf.2.2.2.2.1.trans (hacp_2r.2.2.2.2.1.trans hbs_se2)) hent)
        simp only [↓reduceIte]; rw [hpool_eq_2, hpool_eq_2r]
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ 2#32) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right 2#32 (Entails.refl _)
        have hok_sret := vecHeader_empty_entails_ioVecAt_ok R_alloc sret
        let KeepE2 : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ P_pool se_ret
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hok_sret (sepConj_mono_left (Q := KeepE2) hev_cell))
            (by dsimp only [KeepE2]; sep_entail))
        dsimp only [KeepE2]; sep_entail
      · have hev_ne2 : (BitVec.setWidth 64 ev - 2#64 == 0#64) = false := by
          dsimp only [ev]
          rcases herr_cases with rfl | rfl | rfl
          · exact absurd rfl he2
          · decide
          · decide
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e2')
          fun se_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
        have hcpu_r := hcpu_r0.1
        have ⟨hacp_2r, hvm_2r⟩ :=
          vmPreserved_of_seg hcpu_e20 hcpu_r0 hnsp_r hsym_r
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_2r : P_pool se2 = P_pool se_ret := (hP_vm hvm_2r.toVmMemPreserved).symm
        have hsp_r_eq : se_ret.sp = s0.sp - 8320#64 :=
          hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = se2'.sp).trans (hcpu_e2.sp_eq.trans hsp_se2_eq))
        have hvregs_r : calleeSavedVRegs se_ret = calleeSavedVRegs s0 :=
          hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se2').trans
            (hcpu_e2.calleeSavedVRegs.trans hvregs_se2))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue_vm hext3 hP_vm (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := ioVecAt R_alloc sret (if errno = 2 then .ok [] else .error ()) ∗
              StdErrnoCell s0.tpidrEl0)
            hlo hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_r.status_eq.trans hrun_e2') hsp0 hsp_r_eq hvregs_r
            fun sf hpc_f hrun_f hsp_f hcs_f _ hacp_rf {_Pre_f} hent =>
              hcont sf hpc_f hrun_f hsp_f hcs_f
                (hacp_rf.1.trans (hacp_2r.1.trans hfs_se2))
                (hacp_rf.2.1.trans (hacp_2r.2.1.trans htr_se2))
                (hacp_rf.2.2.1.trans (hacp_2r.2.2.1.trans hsig_se2))
                (hacp_rf.2.2.2.1.trans (hacp_2r.2.2.2.1.trans htp_se2))
                (hacp_rf.2.2.2.2.1.trans (hacp_2r.2.2.2.2.1.trans hbs_se2)) hent)
        simp only [he2, ↓reduceIte]; rw [hpool_eq_2, hpool_eq_2r, ← ioResultErr_eq_cliIoVecAt_err R_alloc sret]
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right ev (Entails.refl _)
        have herr_sret :
            (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) ⊢
              (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16 :=
          vecHeader_to_err_sret sret v1 v2
        let KeepEn : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ P_pool se_ret
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono herr_sret (sepConj_mono_left (Q := KeepEn) hev_cell))
            (by dsimp only [KeepEn]; sep_entail))
        dsimp only [KeepEn]; sep_entail

theorem cliIoReadFile_dir_loop_vm [CliIoPlacement]
    (R_alloc : RustAlloc)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadDir32Spec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 sl : State} {fd count sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sl.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir) (hcanr : desc.accMode.canRead = true)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl03.base + 216#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 8320#64)
    (hw19 : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx21 : sl.readReg64 (.gpr 21#5) = 0#64)
    (hx23 : sl.readReg64 (.gpr 23#5) = count)
    (hx24 : sl.readReg64 (.gpr 24#5) = sret)
    (htp : sl.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.fs = sl.fs.setFd fd none →
      sf.trace = sl.trace → sf.sigActions = sl.sigActions →
      sf.tpidrEl0 = sl.tpidrEl0 → sf.brkStart = sl.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (ioVecAt R_alloc sret (.error ()) ∗ StdErrnoCell s0.tpidrEl0) ∗
          P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        P_pool sl)
      post oomProp := by
  have h32_le : 32 ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 h32_le hsb_hi]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro e0
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 8320#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = count := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadFile_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hvm_lrd⟩ :=
    vmPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : P_pool sl = P_pool sm_rd := (hP_vm hvm_lrd.toVmMemPreserved).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadFile_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 8320#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl03.base + 232#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : (sm_rd.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_rd.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_l.readReg64 (.gpr 19#5)]
    exact hw19
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp only [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = count := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfds_rd : sm_rd.fs.fds fd = some desc := by rw [hacp_lrd.1]; exact hfds
  have htp_rd : sm_rd.tpidrEl0 = s0.tpidrEl0 := hacp_lrd.2.2.2.1.trans htp
  let T_rd : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ P_pool sm_rd
  apply seqCodeLoaded hcl_rd (mid := cliIoPl03.base + 232#64)
  apply (SepWP.call_subroutine_frame hread_dir (F := T_rd)
    (x := (fd, s0.sp - 4224#64, count, desc, e0))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadDir32Spec, T_rd]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hfd_lt, hx1_rd, hx2_rd, hfds_rd, hkind, hcanr⟩, ?_⟩
    rw [hpool_eq_lrd] at hm'
    rw [hsp_rd_eq, muslErrnoAddr_eq_stdErrnoAddr, htp_rd]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadDir32Spec, T_rd]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, _, herr_ne4, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : P_pool sm_rd = P_pool sr :=
      (hP_vm (vmMemPreserved_of_syscallPreserved hsys_sr)).symm
    have hsp_sr_eq : sr.sp = s0.sp - 8320#64 := hsp_sr.trans hsp_rd_eq
    have htp_sr : sr.tpidrEl0 = s0.tpidrEl0 := hsys_sr.1.trans htp_rd
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_sr
      (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
    intro sr' hcpu_r0
    have hcpu_r := hcpu_r0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc_sr
    have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun_sr
    have hsp_r' : sr'.spAligned = true := by
      rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_sr_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx0_r' : sr'.readReg64 .x0 = -1#64 := (hcpu_r.readReg64 _).trans hx0_sr
    wp_sym_steps
    refine SepWP.done cliIoReadFile_errno3_pc (by simpa [arm64_norm] using hrun_r')
      fun sm_el hcpu_el0 hcl_el hnsp_el hsym_el => ?_
    have hcpu_el := hcpu_el0.1
    have ⟨hacp_rel, hvm_rel⟩ :=
      vmPreserved_of_seg hcpu_r0 hcpu_el0 hnsp_el hsym_el
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_rel : P_pool sr = P_pool sm_el := (hP_vm hvm_rel.toVmMemPreserved).symm
    have hpc_el : sm_el.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
      hcpu_el.pc_eq.trans cliIoReadFile_errno3_pc
    have hrun_el : sm_el.status = .Running := hcpu_el.status_eq.trans hrun_r'
    have hsp_el_eq : sm_el.sp = s0.sp - 8320#64 :=
      hcpu_el.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_sr_eq))
    have hsp_el : sm_el.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_el_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hlr_el : sm_el.readReg64 .lr = cliIoPl03.base + 244#64 := by
      rw [hcpu_el.readReg64 .lr]; simp [arm64_norm]
    have htp_el : sm_el.tpidrEl0 = s0.tpidrEl0 := hacp_rel.2.2.2.1.trans htp_sr
    let ev := dirReadErrno32 (s0.sp - 4224#64) count
    let T_el : SepProp :=
      stackAt sm_rd.sp 32 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗
        memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ P_pool sm_el
    apply seqCodeLoaded hcl_el (mid := cliIoPl03.base + 244#64)
    apply (SepWP.call_subroutine_frame herrno (F := T_el) (x := ())
      hpc_el hrun_el hsp_el hlr_el
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslErrnoLocationSpec, T_el]
      rw [emp_sepConj]
      rw [hpool_eq_sr, hpool_eq_rel, muslErrnoAddr_eq_stdErrnoAddr, htp_sr] at hm'
      exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
    · intro se0 hpc_se0 hrun_se0 hsp_se0 hcs_else0
      refine SepWP.done hpc_se0 hrun_se0 fun hcl_se0 => ?_
      wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el]; simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_se0, _, hstd_el⟩
      have hpool_eq_el : P_pool sm_el = P_pool se0 :=
        (hP_vm (vmPreserved_of_stdState hstd_el).toVmMemPreserved).symm
      have hsp_se0_eq : se0.sp = s0.sp - 8320#64 := hsp_se0.trans hsp_el_eq
      have hx0_se0' : se0.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
        rw [hx0_se0, muslErrnoAddr_eq_stdErrnoAddr, htp_el]
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_se0
        (mid := cliIoPl03.base + 468#64)
      intro sc' hcpu_c0
      have hcpu_c := hcpu_c0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_c' : sc'.pc = cliIoPl03.base + 244#64 := hcpu_c.pc_eq.trans hpc_se0
      have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun_se0
      have hsp_c' : sc'.spAligned = true := by
        rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_se0_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx0_c' : sc'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := (hcpu_c.readReg64 _).trans hx0_se0'
      have hev_zext_beq4 : (BitVec.setWidth 64 ev - 4#64 == 0#64) = false := by
        rcases dirReadErrno32_cases (s0.sp - 4224#64) count with h21 | h14
        · dsimp only [ev]; rw [h21]; decide
        · dsimp only [ev]; rw [h14]; decide
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_c')
        fun se_ep hcpu_ep0 hcl_ep hnsp_ep hsym_ep => ?_
      have hcpu_ep := hcpu_ep0.1
      have ⟨hacp_cep, hvm_cep⟩ :=
        vmPreserved_of_seg hcpu_c0 hcpu_ep0 hnsp_ep hsym_ep
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_cep : P_pool se0 = P_pool se_ep := (hP_vm hvm_cep.toVmMemPreserved).symm
      have hfs_ep : se_ep.fs = sl.fs :=
        hacp_cep.1.trans (hstd_el.1.trans (hacp_rel.1.trans (hfs_sr.trans hacp_lrd.1)))
      have htr_ep : se_ep.trace = sl.trace :=
        hacp_cep.2.1.trans (hstd_el.2.1.trans (hacp_rel.2.1.trans (htr_sr.trans hacp_lrd.2.1)))
      have hsig_ep : se_ep.sigActions = sl.sigActions :=
        hacp_cep.2.2.1.trans (hstd_el.2.2.2.1.trans (hacp_rel.2.2.1.trans (hsys_sr.2.1.trans hacp_lrd.2.2.1)))
      have htp_ep : se_ep.tpidrEl0 = sl.tpidrEl0 :=
        hacp_cep.2.2.2.1.trans (hstd_el.2.2.1.trans (hacp_rel.2.2.2.1.trans (hsys_sr.1.trans hacp_lrd.2.2.2.1)))
      have hbs_ep : se_ep.brkStart = sl.brkStart :=
        hacp_cep.2.2.2.2.1.trans (hstd_el.2.2.2.2.2.1.trans
          (hacp_rel.2.2.2.2.1.trans (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1)))
      have hw19_ep : (se_ep.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
        rw [readReg32_of_readReg64_eq (hcpu_ep.readReg64 (.gpr 19#5))]
        simp only [arm64_norm]
        rw [hcpu_c.readReg64 (.gpr 19#5), hcs_else0.readReg64_x19,
          hcpu_el.readReg64 (.gpr 19#5)]
        simp only [arm64_norm]
        rw [hcpu_r.readReg64 (.gpr 19#5), hcs_rdsr.readReg64_x19,
          hcpu_rd.readReg64 (.gpr 19#5)]
        simp only [arm64_norm]
        rw [hcpu_l.readReg64 (.gpr 19#5)]
        exact hw19
      have hx21_ep : se_ep.readReg64 (.gpr 21#5) = 0#64 := by
        rw [hcpu_ep.readReg64]; simp only [arm64_norm]
        rw [hcpu_c.readReg64, hcs_else0.readReg64_x21, hcpu_el.readReg64]; simp only [arm64_norm]
        rw [hcpu_r.readReg64, hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]
        exact (hcpu_l.readReg64 _).trans hx21
      have hx24_ep : se_ep.readReg64 (.gpr 24#5) = sret := by
        rw [hcpu_ep.readReg64]; simp only [arm64_norm]
        rw [hcpu_c.readReg64, hcs_else0.readReg64_x24, hcpu_el.readReg64]; simp only [arm64_norm]
        rw [hcpu_r.readReg64, hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]
        exact (hcpu_l.readReg64 _).trans hx24
      have hvregs_ep : calleeSavedVRegs se_ep = calleeSavedVRegs s0 :=
        hcpu_ep.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
          (hcpu_c.calleeSavedVRegs.trans (hcs_else0.vregs.trans
            (hcpu_el.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
              (hcpu_r.calleeSavedVRegs.trans (hcs_rdsr.vregs.trans
                (hcpu_rd.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans
                  (hcpu_l.calleeSavedVRegs.trans hvregs))))))))))
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_err_cap0_epilogue_vm hext3 hclose hP_vm
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (R_extra := StdErrnoCell s0.tpidrEl0)
          hlo hhi hfd_lt (by rw [hfs_ep]; exact hfds) (Or.inr hkind) hcl_ep
          (hcpu_ep.pc_eq.trans (by simp [arm64_norm])) (hcpu_ep.status_eq.trans hrun_c') hsp0
          (hcpu_ep.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans (hcpu_c.sp_eq.trans hsp_se0_eq)))
          hw19_ep hx21_ep hx24_ep hvregs_ep
          fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent =>
            hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
              (hfs_f.trans (congrArg (fun f => f.setFd fd none) hfs_ep))
              (htr_f.trans htr_ep) (hsig_f.trans hsig_ep) (htp_f.trans htp_ep) (hbs_f.trans hbs_ep)
              (by simpa only [ioResultErr_eq_cliIoVecAt_err R_alloc sret] using hent))
      rw [hpool_eq_el, hpool_eq_cep, hsp_rd_eq,
        stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 h32_le hsb_hi]
      have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
        Entails.sepExists_right ev (Entails.refl _)
      let Rest : SepProp :=
        stackAt (s0.sp - 8320#64) 32 ∗
          memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ P_pool se_ep
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_right (P := Rest) hev_cell) (by dsimp only [Rest]; sep_entail))
      dsimp only [Rest]; sep_entail

/-! ## Budget-Threaded Post-`open` `.ok` Branch (`+0x88 → +0xd8`) -/

theorem cliIoReadFile_open_ok_budget [CliIoPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 so : State} {fd sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {ev0 : BitVec 32} {pathBytes : List (BitVec 8)} {kind : FdKind}
    {stackBytes : Nat} {st : M.σ}
    {post : State → SepProp → Prop}
    (hlo : 8368 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (htp0 : s0.tpidrEl0 = tp) (hbs0 : s0.brkStart = brkStart)
    (hcl_ok : classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd kind)
    (hcl_o : signalSessionIoMultiLib.CodeLoaded cliIoMpl so.mem)
    (hpc_o : so.pc = cliIoPl03.base + 136#64) (hrun_o : so.status = .Running)
    (hsp_o : so.sp = s0.sp - 8320#64)
    (hw0_o : so.readReg32 .x0 = fd.truncate 32)
    (hx24_o : so.readReg64 (.gpr 24#5) = sret)
    (hx29_o : so.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htp_o : so.tpidrEl0 = s0.tpidrEl0)
    (hvregs_o : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_o : so.fs = s0.fs.setFd fd (some (cliIoOpenEntry pathBytes kind)))
    (htr_o : so.trace = s0.trace) (hsig_o : so.sigActions = s0.sigActions)
    (hbs_o : so.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          ioVecAt A.repAlloc sret (cliIo.rd s0.fs.files pathBytes) ∗
          A.pool lim (M.stepEvents (readFileBudgetEvents s0.fs.files pathBytes) st) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ S.core lim st so)
      post
      (fun sf_oom =>
        ⌜¬ FitsEvents M lim st (readFileBudgetEvents s0.fs.files pathBytes) ∧
          CliIoFilesOomPreserved s0 sf_oom⌝) := by
  obtain ⟨hb_none, _, _, hfd_max, hfds_none, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl_ok
  have hfd_lt31 : fd.toNat < 2 ^ 31 := Nat.lt_trans hfd_max (by decide)
  have hfd_lt32 : fd.toNat < 2 ^ 32 := Nat.lt_trans hfd_lt31 (by decide)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_o
    (mid := cliIoPl03.base + 216#64)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl03.base + 136#64 := hcpu_o.pc_eq.trans hpc_o
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_o
  have hsp_o' : so'.spAligned = true := by
    rw [hcpu_o.spAligned]; simp only [State.spAligned]; rw [hsp_o]
    exact s0.spAligned_sub 8320#64 hsp0
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = false := by
    rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_o]
    exact getLsbD_31_of_fd_lt hfd_lt31
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_o')
    fun sl hcpu_l0 hcl_l hnsp_l hsym_l => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨hacp_ol, hvm_ol⟩ :=
    vmPreserved_of_seg hcpu_o0 hcpu_l0 hnsp_l hsym_l
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hcore_eq_ol : S.core lim st so = S.core lim st sl :=
    (S.core_transport lim st hvm_ol.toVmMemPreserved).symm
  have hpc_l : sl.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl.status = .Running := hcpu_l.status_eq.trans hrun_o'
  have hsp_l : sl.sp = s0.sp - 8320#64 :=
    hcpu_l.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_o))
  have hw19_l : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    apply readReg32_zeroExtend_of_truncate ?_ hfd_lt32
    rw [readReg32_of_readReg64_eq (hcpu_l.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_o.readReg64 .x0]
    exact hw0_o
  have hx24_l : sl.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_l.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx24_o
  have hx29_l : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_l.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx29_o
  have hvregs_l : calleeSavedVRegs sl = calleeSavedVRegs s0 :=
    hcpu_l.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_o))
  have hfs_l : sl.fs = s0.fs.setFd fd (some (cliIoOpenEntry pathBytes kind)) :=
    hacp_ol.1.trans hfs_o
  have htr_l : sl.trace = s0.trace := hacp_ol.2.1.trans htr_o
  have hsig_l : sl.sigActions = s0.sigActions := hacp_ol.2.2.1.trans hsig_o
  have htp_l : sl.tpidrEl0 = s0.tpidrEl0 := hacp_ol.2.2.2.1.trans htp_o
  have hbs_l : sl.brkStart = s0.brkStart := hacp_ol.2.2.2.2.1.trans hbs_o
  have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ StdErrnoCell s0.tpidrEl0 :=
    Entails.sepExists_right ev0 (Entails.refl _)
  rcases hkind_cases with ⟨rfl, _⟩ | ⟨rfl, bs, hbs_file⟩
  · obtain ⟨hrd_dir, hevs_dir⟩ := classifyOpenRdonly_localDir_align hcl_ok
    have hfds_l : sl.fs.fds fd = some (cliIoOpenEntry pathBytes .localDir) := by
      rw [hfs_l]; simp [FsState.setFd]
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_dir_loop_vm A.repAlloc hext3 hread_dir herrno hclose
        (fun hvm => S.core_transport lim st hvm)
        (count := 4096#64) (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
        (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (by omega) hhi hfd_lt31 hfds_l rfl rfl
        hcl_l hpc_l hrun_l hsp0 hsp_l hw19_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        hx24_l htp_l hvregs_l
        fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent => ?_)
    · rw [hcore_eq_ol]
      let KeepDir : SepProp :=
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ S.core lim st sl
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_left (Q := KeepDir) hev_cell)
          (by dsimp only [KeepDir]; sep_entail))
      dsimp only [KeepDir]; sep_entail
    · have hfs_f' : sf.fs = s0.fs := by
        rw [hfs_f, hfs_l]; exact setFd_none_setFd_of_fds_none hfds_none
      have htp_sf : sf.tpidrEl0 = s0.tpidrEl0 := htp_f.trans htp_l
      have hbs_sf : sf.brkStart = s0.brkStart := hbs_f.trans hbs_l
      have hjoin_sf : S.core lim st sf ∗ StdErrnoCell s0.tpidrEl0 ⊢ A.pool lim st sf := by
        rw [htp0]
        exact S.pool_join lim st (htp_sf.trans htp0) (hbs_sf.trans hbs0)
      refine hcont sf hpc_f hrun_f hsp_f hcs_f hfs_f'
        (htr_f.trans htr_l) (hsig_f.trans hsig_l) htp_sf hbs_sf ?_
      rw [hrd_dir, hevs_dir]
      have hstep_nil : M.stepEvents [] st = st := rfl
      rw [hstep_nil]
      refine Entails.trans hent ?_
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right hjoin_sf))
      sep_entail
  · let d0 := cliIoOpenEntry pathBytes .localFile
    have hrem_bs : (s0.fs.fdBytes d0).drop d0.offset = bs := by
      dsimp only [d0, cliIoOpenEntry]; rw [fdBytes_open_localFile hbs_file]; rfl
    obtain ⟨hout_eq, hevs_eq⟩ := classifyOpenRdonly_localFile_align hb_none hbs_file
    rw [show (fun sf_oom =>
        ⌜¬ FitsEvents M lim st (readFileBudgetEvents s0.fs.files pathBytes) ∧
          CliIoFilesOomPreserved s0 sf_oom⌝) =
      (fun sf_oom =>
        ⌜¬ FitsEvents M lim st (cliIoFileLoopBudgetEvents ((s0.fs.fdBytes d0).drop d0.offset)) ∧
          CliIoFilesOomPreserved s0 sf_oom⌝) by
      funext sf_oom; rw [hrem_bs, hevs_eq]]
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_file_loop_budget A lim (fun st => S.pool_mem_transport lim st)
        hext3 hread_file hmemcpy hfg hdealloc hclose
        (d0 := d0) (fd := fd) (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
        hlo hhi hsp_lo hsp_va hsp0 hfd_lt31 hfds_none rfl rfl rfl
        (fun sf hpc_f hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f
            (by simpa only [hrem_bs, hout_eq, hevs_eq] using hent))
        (cliIoFileCap + 1) sl 1#64 st0 st1 st2 st3 0 0 st
        (Nat.le_refl _) (Nat.zero_le _) (fun _ => Nat.dvd_zero 4096) rfl rfl
        hcl_l hpc_l hrun_l hsp_l hw19_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm, wantBytes])
        hx24_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        hx29_l hvregs_l
        (by simpa only [d0, cliIoOpenEntry, Nat.zero_add] using hfs_l)
        htr_l hsig_l htp_l hbs_l)
    rw [hcore_eq_ol]
    have hjoin_sl : S.core lim st sl ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ A.pool lim st sl := by
      refine Entails.trans (sepConj_mono_right hev_cell) ?_
      rw [htp0]
      exact S.pool_join lim st (htp_l.trans htp0) (hbs_l.trans hbs0)
    have hvec0 : emp ⊢ cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64
        (((s0.fs.fdBytes d0).drop d0.offset).take 0) :=
      cliIoVecBuf_zero_intro A.repAlloc (ptr := 1#64) (by decide)
    let KeepFile : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2
    have hwith_vec :
        KeepFile ⊢ KeepFile ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64
            (((s0.fs.fdBytes d0).drop d0.offset).take 0) := by
      simpa only [sepConj_emp] using sepConj_mono_right (P := KeepFile) hvec0
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hwith_vec hjoin_sl)
        (by dsimp only [KeepFile]; sep_entail))
    dsimp only [KeepFile]; sep_entail


/-! ## Unified Strong Spec and `PoolErrnoSplit` Discharges -/

private theorem sepWP_frame_right {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P (fun sf Pf => post sf (Pf ∗ F)) oom) :
    SepWP prog target_pc s (P ∗ F) post oom := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono (h (F ∗ R) hm) ?_ (fun _ _ ho => Satisfies.drop_mid ho)
  rintro sf _ _ ⟨Pf, hmf, hpost⟩
  exact ⟨Pf ∗ F, by rw [sepConj_assoc]; exact hmf, hpost⟩

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

/-- Strong unified conditional-OOM budget-threaded contract for compiled
    `signal_session_io::read_file`: strengthens `readFileAnyBudgetCondSpec.post` with full
    `AllocCallPreserved s0 sf` so both `readFileAnyBudgetCondSpec` (`ro : Bool`) and
    `readFileBudgetCondSpec` (`ro = false`, `cliWrOk x.path`) follow as immediate corollaries. -/
def readFileAnyStrongBudgetCondSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (ReadFileCall × M.σ) :=
  { readFileAnyBudgetCondSpec A lim stk with
    post := fun (x, st) s0 sf =>
      let evs := readFileBudgetEvents s0.fs.files x.path
      ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
        ioVecAt A.repAlloc x.ret (cliIo.rd s0.fs.files x.path) ∗
        bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf }

theorem cliIoReadFileAnyStrongBudgetCond_withCodeLoaded_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readFileAnyStrongBudgetCondSpec A lim stk)) := by
  have hfg := cliIoFinishGrow_budget_ok_withCodeLoaded A lim hpl hext4 hshim halloc hrealloc
  let _ : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 3 cliIoReadFileSym cliIo3_lt cliIoReadFile_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
    readFileAnyBudgetCondSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, _hlt32, hpok, hallocFd⟩, hmem⟩
  have hstk_pos : 0 < stk := by omega
  have h8320 : 8320 ≤ stk := by omega
  have hhi : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (p := x.ret) (sp := s0.sp) (n := 24) (stk := stk)
      (R := bytesAt x.ro x.pathA x.path ∗ A.pool lim st s0 ∗ R)
      (by decide) hstk_pos (Satisfies.mono (by sep_entail) hmem)
  have ⟨hsp_lo, hsp_va⟩ : stk ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT :=
    stackAt_bounds_of_mapped hstk_pos hhi
      (fun _ hmap => S.pool_mapped_lt_userVa lim st hEnf
        (R := bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk ∗ R)
        (Satisfies.mono (by sep_entail) hmem) hmap)
      (R := bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ A.pool lim st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  have hpOk : PathOk (cPathOf x.path) = true := by
    rw [cPathOf_eq_pathStr]; exact hpok.1
  have hpMax : ((pathComps (cPathOf x.path)).all fun c => decide (c.length ≤ NAME_MAX)) = true := by
    rw [cPathOf_eq_pathStr]; exact hpok.2.1.2
  have hlt : x.path.length < 4096 := hpok.2.2
  have hnul : (0#8 : BitVec 8) ∉ x.path :=
    ReadFileBudgetPlaced.zero_not_mem_of_pathOk hpok.1
  have hmem1 : s0.mem ⊨ ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      ((stackAt s0.sp stk ∗ memcpySrc x.ro x.pathA x.path ∗
        memRegion x.ret 24 ∗ StdErrnoCell s0.tpidrEl0 ∗ S.core lim st s0) ∗ R) := by
    rw [← memcpySrc_eq_bytesAt x.ro x.pathA x.path] at hmem
    refine Satisfies.mono ?_ hmem
    let Keep0 : SepProp :=
      (memcpySrc x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk) ∗ R
    refine Entails.trans (by dsimp only [Keep0]; sep_entail)
      (Entails.trans (sepConj_mono_left (Q := Keep0) (S.pool_split lim st s0))
        (by dsimp only [Keep0]; sep_entail))
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨htp0, hbs0⟩, hmem_split⟩
  refine ⟨_, hmem_split, ?_⟩
  apply cliIo_sepWP_carry_oracle_symtab hsvc hext_os
  refine SepWP.weaken_pre (Entails.refl _)
    (cliIoReadFile_pre_open_valid_vm hext3
      (P_pool := S.core lim st) (fun hvm => S.core_transport lim st hvm)
      h8320 hhi hlt hnul hcl0 hpc hrun hsp0 hx0 hx1 hx8
      fun sm ev0 v0 v1 v2 st0 st1 st2 st3
          hcl_m hpc_m hrun_m hsp_m_eq hsp_m hlr_m hx0_m hw1_m hx24_m hx29_m hvregs_m hacp_0m => ?_)
  have h112_le : 112 ≤ stk - 8320 := by omega
  have hsb_hi : stk - 8320 ≤ 2 ^ 64 := by omega
  let PreOpenRest : SepProp :=
    stackAt (s0.sp - 8320#64) (stk - 8320) ∗
      ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf x.path)) ∗
      memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (x.path.length + 1))
        (4095 - x.path.length) ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      vecHeader x.ret v0 v1 v2 ∗
      (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗
      S.core lim st sm
  refine SepWP.weaken_pre
    (P' := PreOpenRest ∗ memcpySrc x.ro x.pathA x.path)
    (by dsimp only [PreOpenRest]; sep_entail) ?_
  apply sepWP_frame_right
  dsimp only [PreOpenRest]
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stk - 8320) 112 h112_le hsb_hi]
    simp only [sepConj_assoc]
  have hpath_len : (cPathOf x.path).toList.length < PATH_MAX := by
    rw [toList_cPathOf_length]; exact hlt
  have hpath_ascii : ∀ c ∈ (cPathOf x.path).toList, c.toNat < 256 :=
    fun _ hc => mem_toList_cPathOf_lt_256 hc
  let T_open : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stk - 8320)) (stk - 8320 - 112) ∗
      memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (x.path.length + 1))
        (4095 - x.path.length) ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader x.ret v0 v1 v2 ∗ S.core lim st sm
  apply seqCodeLoaded hcl_m (mid := cliIoPl03.base + 136#64)
  apply (SepWP.call_subroutine_frame hopen (F := T_open)
    (x := (s0.sp - 8320#64, cPathOf x.path, ev0))
    hpc_m hrun_m hsp_m hlr_m
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslOpenRdonlyDetSpec, T_open]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_m, hw1_m, hpOk, hpMax, hpath_len, hpath_ascii⟩, ?_⟩
    rw [hsp_m_eq, muslErrnoAddr_eq_stdErrnoAddr, hacp_0m.2.2.2.1]
    exact Satisfies.mono (by sep_frame) hm'
  · intro so hpc_so hrun_so hsp_so hcs_mo
    refine SepWP.done hpc_so hrun_so fun hcl_so => ?_
    have hsp_so_eq : so.sp = s0.sp - 8320#64 := hsp_so.trans hsp_m_eq
    have hx24_so : so.readReg64 (.gpr 24#5) = x.ret := (calleeSaved_x24 hcs_mo).trans hx24_m
    have hx29_so : so.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
      (calleeSaved_fp hcs_mo).trans hx29_m
    have hvregs_so : calleeSavedVRegs so = calleeSavedVRegs s0 :=
      (calleeSaved_vregs hcs_mo).trans hvregs_m
    have hstk_back :
        stackAt sm.sp 112 ∗
          memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stk - 8320)) (stk - 8320 - 112) ⊢
          stackAt (s0.sp - 8320#64) (stk - 8320) := by
      rw [hsp_m_eq, stackAt_shrink (s0.sp - 8320#64) (stk - 8320) 112 h112_le hsb_hi]
      sep_entail
    have hcstr_back := refold_cstr_buf4096 (s0.sp - 8320#64) x.path hlt
    wp_conv_pre => dsimp only [muslOpenRdonlyDetSpec, T_open]
    rw [hacp_0m.1]
    cases hcl_res : classifyOpenRdonly s0.fs (cPathOf x.path) with
    | err errno =>
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hw0_so, hfs_so, htr_so, hsys_so⟩
      have hcore_eq_mo : S.core lim st sm = S.core lim st so :=
        (S.core_transport lim st (vmMemPreserved_of_syscallPreserved hsys_so)).symm
      have htp_so : so.tpidrEl0 = s0.tpidrEl0 := hsys_so.1.trans hacp_0m.2.2.2.1
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_open_err_vm A.repAlloc hext3 herrno
          (P_pool := S.core lim st) (fun hvm => S.core_transport lim st hvm)
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          h8320 hhi hsp0
          (classifyOpenRdonly_err_cases hcl_res)
          hcl_so hpc_so hrun_so hsp_so_eq hw0_so hx24_so htp_so hvregs_so
          hfs_so (htr_so.trans hacp_0m.2.1)
          (hsys_so.2.1.trans hacp_0m.2.2.1) (hsys_so.2.2.brkStart_eq.trans hacp_0m.2.2.2.2.1)
          fun sf _hpc_f _hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent
              horc_f hsym_f => ?_)
      · rw [hcore_eq_mo, muslErrnoAddr_eq_stdErrnoAddr, htp_so]
        let KeepErr0 : SepProp :=
          memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader x.ret v0 v1 v2 ∗
            (stdErrnoAddr s0.tpidrEl0 ↦₃₂ BitVec.ofNat 32 errno) ∗ S.core lim st so
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hstk_back (sepConj_mono_left (Q := KeepErr0) hcstr_back))
            (by dsimp only [KeepErr0]; sep_entail))
        dsimp only [KeepErr0]; sep_entail
      · have hacp_f : AllocCallPreserved s0 sf :=
          ⟨hfs_f, htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
        have hjoin_sf : S.core lim st sf ∗ StdErrnoCell s0.tpidrEl0 ⊢ A.pool lim st sf := by
          rw [htp0]; exact S.pool_join lim st (htp_f.trans htp0) (hbs_f.trans hbs0)
        refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
        rw [memcpySrc_eq_bytesAt x.ro x.pathA x.path] at hm_out
        rw [pure_sepConj_of_true ⟨hacp_f, hfs_f⟩]
        by_cases he2 : errno = 2
        · subst he2
          obtain ⟨hrd2, hevs2⟩ := classifyOpenRdonly_err2_align hcl_res
          rw [hrd2, hevs2]
          have hstep_nil : M.stepEvents [] st = st := rfl
          rw [hstep_nil]
          have hent' : _Pre_f ⊢
              stackAt s0.sp stk ∗ ioVecAt A.repAlloc x.ret (.ok []) ∗ A.pool lim st sf := by
            refine Entails.trans (by simpa only [↓reduceIte] using hent) ?_
            refine Entails.trans ?_
              (sepConj_mono_right (P := stackAt s0.sp stk)
                (sepConj_mono_right (P := ioVecAt A.repAlloc x.ret (.ok [])) hjoin_sf))
            sep_entail
          exact Satisfies.mono
            (sepConj_mono_left (Entails.trans (sepConj_mono_left hent') (by sep_entail))) hm_out
        · obtain ⟨hrd_ne, hevs_ne⟩ := classifyOpenRdonly_errNe2_align hallocFd hcl_res he2
          rw [hrd_ne, hevs_ne]
          have hstep_nil : M.stepEvents [] st = st := rfl
          rw [hstep_nil]
          have hent' : _Pre_f ⊢
              stackAt s0.sp stk ∗ ioVecAt A.repAlloc x.ret (.error ()) ∗ A.pool lim st sf := by
            refine Entails.trans (by simpa only [he2, ↓reduceIte] using hent) ?_
            refine Entails.trans ?_
              (sepConj_mono_right (P := stackAt s0.sp stk)
                (sepConj_mono_right (P := ioVecAt A.repAlloc x.ret (.error ())) hjoin_sf))
            sep_entail
          exact Satisfies.mono
            (sepConj_mono_left (Entails.trans (sepConj_mono_left hent') (by sep_entail))) hm_out
    | ok fd kind =>
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hw0_so, hfs_so, htr_so, hsys_so⟩
      have hcore_eq_mo : S.core lim st sm = S.core lim st so :=
        (S.core_transport lim st (vmMemPreserved_of_syscallPreserved hsys_so)).symm
      have htp_so : so.tpidrEl0 = s0.tpidrEl0 := hsys_so.1.trans hacp_0m.2.2.2.1
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_open_ok_budget S lim hext3 herrno hread_dir hread_file
          hmemcpy hfg hdealloc hclose
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3) (ev0 := ev0)
          (by omega : 8368 + allocHookStack ≤ stk) hhi hsp_lo hsp_va hsp0 htp0 hbs0 hcl_res
          hcl_so hpc_so hrun_so hsp_so_eq hw0_so hx24_so hx29_so htp_so hvregs_so
          hfs_so (htr_so.trans hacp_0m.2.1)
          (hsys_so.2.1.trans hacp_0m.2.2.1) (hsys_so.2.2.brkStart_eq.trans hacp_0m.2.2.2.2.1)
          fun sf _hpc_f _hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent
              horc_f hsym_f => ?_)
      · rw [hcore_eq_mo, muslErrnoAddr_eq_stdErrnoAddr, htp_so]
        let KeepOk0 : SepProp :=
          memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader x.ret v0 v1 v2 ∗
            (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ S.core lim st so
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hstk_back (sepConj_mono_left (Q := KeepOk0) hcstr_back))
            (by dsimp only [KeepOk0]; sep_entail))
        dsimp only [KeepOk0]; sep_entail
      · have hacp_f : AllocCallPreserved s0 sf :=
          ⟨hfs_f, htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
        refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
        rw [memcpySrc_eq_bytesAt x.ro x.pathA x.path] at hm_out
        rw [pure_sepConj_of_true ⟨hacp_f, hfs_f⟩]
        exact Satisfies.mono
          (sepConj_mono_left (Entails.trans (sepConj_mono_left hent) (by sep_entail))) hm_out

end

theorem subroutine_ok_strip_withCodeLoaded {α : Type}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (h : subroutine_ok P entry (signalSessionIoMultiLib.withCodeLoaded mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' : s0.mem ⊨ (signalSessionIoMultiLib.withCodeLoaded mpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCode s0.mem hLP, hpre⟩
  exact subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

theorem subroutine_ok_readFileAnyBudgetCond_withCodeLoaded_of_strong
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readFileAnyStrongBudgetCondSpec A lim stk))) :
    subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readFileAnyBudgetCondSpec A lim stk)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
      readFileAnyBudgetCondSpec] at hpost ⊢
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left
        (Entails.pure_mono fun ⟨hacp, hfs⟩ => ⟨hacp.2.1, hfs⟩)))
      hpost
  · exact Or.inr hrest

theorem subroutine_ok_readFileBudgetCond_withCodeLoaded_of_strong
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readFileAnyStrongBudgetCondSpec A lim stk))) :
    subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (readFileBudgetCondSpec A lim stk)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  let y : ReadFileCall × M.σ := (⟨x.pathA, false, x.path, x.ret⟩, st)
  have hpreAny :
      s0.mem ⊨ (signalSessionIoMultiLib.withCodeLoaded mpl
        (readFileAnyStrongBudgetCondSpec A lim stk)).pre y s0 ∗ R := by
    have hEnt :
        (signalSessionIoMultiLib.withCodeLoaded mpl (readFileBudgetCondSpec A lim stk)).pre
            (x, st) s0 ∗ R ⊢
          (signalSessionIoMultiLib.withCodeLoaded mpl
            (readFileAnyStrongBudgetCondSpec A lim stk)).pre y s0 ∗ R := by
      dsimp only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y]
      rw [bytesAt_false]
      exact sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
        (Entails.pure_mono fun ⟨hx0, hx1, hx8, hlt32, hwrok, hallocFd⟩ =>
          ⟨hx0, hx1, hx8, hlt32, hwrok.1, hallocFd⟩)))
    exact Satisfies.mono hEnt hpre
  refine subroutine_ok.mono_outcome h y R s0 hpc hrun hpreAny hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
      readFileBudgetCondSpec, y] at hpost ⊢
    rwa [bytesAt_false] at hpost
  · exact Or.inr (Or.inl ⟨hp,
      by simpa only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y] using hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc,
      by simpa only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y] using hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho,
      by simpa only [MultiPlacedLib.withCodeLoaded, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y] using hoom⟩))

theorem cliIoReadFileAnyBudgetCond_withCodeLoaded_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (readFileAnyBudgetCondSpec A lim stk)) :=
  subroutine_ok_readFileAnyBudgetCond_withCodeLoaded_of_strong
    (cliIoReadFileAnyStrongBudgetCond_withCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

theorem cliIoReadFileBudgetCond_withCodeLoaded_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (readFileBudgetCondSpec A lim stk)) :=
  subroutine_ok_readFileBudgetCond_withCodeLoaded_of_strong
    (cliIoReadFileAnyStrongBudgetCond_withCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

theorem cliIoReadFileAnyBudgetCond_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileAnyBudgetCondSpec A lim stk) :=
  subroutine_ok_strip_withCodeLoaded hCode
    (cliIoReadFileAnyBudgetCond_withCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

theorem cliIoReadFileBudgetCond_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileBudgetCondSpec A lim stk) :=
  subroutine_ok_strip_withCodeLoaded hCode
    (cliIoReadFileBudgetCond_withCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

/-! ## `mallocng` `PoolErrnoSplit` Instances and `subroutine_ok` Corollaries -/

/-- Non-`errno` core of `mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s` (`I.CoreM` +
    `mallocngBudgetPoolInv` + `MallocngLibcCells`), invariant under `VmPreserved`. -/
noncomputable def mallocngCorePoolAt (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  (∃∗ staticIvs : List (BitVec 64 × Nat),
    ∃∗ ivs : List (BitVec 64 × Nat),
      ⌜mallocngBudgetPoolInv lim staticIvs ivs s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      I.CoreM γ mAddrs brkStart s.brk st ivs) ∗
    MallocngLibcCells mAddrs

theorem mallocngCorePoolAt_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) {s s' : State}
    (hvm : VmMemPreserved s s') :
    mallocngCorePoolAt M I γ mAddrs tp brkStart lim st s' =
      mallocngCorePoolAt M I γ mAddrs tp brkStart lim st s := by
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs s' = mallocngBudgetPoolInv lim staticIvs ivs s :=
    fun staticIvs ivs => mallocngBudgetPoolInv_transport_mem hvm
  rcases hvm with ⟨⟨hbs, hbrk, htp⟩, _, _⟩
  unfold mallocngCorePoolAt
  simp only [hinv, htp, hbs, hbrk]

noncomputable def mallocngPoolErrnoSplitAt {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64) :
    PoolErrnoSplit (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart) tp brkStart where
  core := mallocngCorePoolAt M I γ mAddrs tp brkStart
  core_transport lim st _ _ hvm :=
    mallocngCorePoolAt_transport M I γ mAddrs tp brkStart lim st hvm
  pool_mem_transport lim st _ _ hvm :=
    mallocngBudgetPoolAt_transport_mem M I γ mAddrs tp brkStart lim st hvm
  pool_split lim st s := by
    change mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s ⊢ _
    rw [mallocngBudgetPoolAt_split_runtime hS]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun staticIvs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ivs => ?_
    rw [mallocngRuntime_eq_stdErrnoCell_sep, sepConj_assoc]
    refine Entails.pure_left fun ⟨hinv, htp, hbs⟩ => ?_
    refine Entails.pure_right ⟨htp, hbs⟩ ?_
    rw [htp]
    unfold mallocngCorePoolAt
    have hcore_intro :
        I.CoreM γ mAddrs brkStart s.brk st ivs ⊢
          ∃∗ sIvs : List (BitVec 64 × Nat), ∃∗ ivs' : List (BitVec 64 × Nat),
            ⌜mallocngBudgetPoolInv lim sIvs ivs' s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
            I.CoreM γ mAddrs brkStart s.brk st ivs' :=
      Entails.sepExists_right staticIvs
        (Entails.sepExists_right ivs
          (Entails.pure_right ⟨hinv, htp, hbs⟩ (Entails.refl _)))
    exact Entails.trans (sepConj_mono_left hcore_intro) (by sep_entail)
  pool_join lim st {_s} _htp _hbs := by
    change mallocngCorePoolAt M I γ mAddrs tp brkStart lim st _s ∗ StdErrnoCell tp ⊢
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st _s
    rw [mallocngBudgetPoolAt_split_runtime hS, mallocngRuntime_eq_stdErrnoCell_sep]
    unfold mallocngCorePoolAt
    sep_entail
  pool_mapped_lt_userVa _ _ {_} {_} {_} henf hsat hmap :=
    mallocngBudgetPoolAt_mapped_lt_userVa hS henf hsat hmap

noncomputable def mallocngPoolErrnoSplit {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : MultiPlacement) (tp brkStart : BitVec 64) :
    PoolErrnoSplit (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) tp brkStart :=
  mallocngPoolErrnoSplitAt hS γ (mallocngAddrsOfPlacement mpl) tp brkStart

noncomputable def mallocngHookPoolErrnoSplit {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : MultiPlacement) (tp brkStart : BitVec 64) :
    PoolErrnoSplit (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) tp brkStart where
  core lim st s :=
    VerifiedLibraries.mallocngLib.codeRO mpl ∗
      (mallocngPoolErrnoSplit hS γ mpl tp brkStart).core lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝
  core_transport lim st _ _ hvm := by
    have hc := (mallocngPoolErrnoSplit hS γ mpl tp brkStart).core_transport lim st hvm
    have hrx := codeBlocksPermRX_of_perm_eq (mpl := mpl) hvm.2.2
    simp only [hc, hrx]
  pool_mem_transport lim st _ _ hvm :=
    mallocngHookBudgetPool_transport_mem M I γ mpl tp brkStart lim st hvm
  pool_split lim st s := by
    change mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ⊢ _
    unfold mallocngHookBudgetPool
    have hsp := (mallocngPoolErrnoSplit hS γ mpl tp brkStart).pool_split lim st s
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left hsp)) ?_
    have hEq :
        VerifiedLibraries.mallocngLib.codeRO mpl ∗
          (⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
            ((mallocngPoolErrnoSplit hS γ mpl tp brkStart).core lim st s ∗
              StdErrnoCell s.tpidrEl0)) ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝ =
        ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
          ((VerifiedLibraries.mallocngLib.codeRO mpl ∗
            (mallocngPoolErrnoSplit hS γ mpl tp brkStart).core lim st s ∗
            ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝) ∗
            StdErrnoCell s.tpidrEl0) := by
      sep_ac_rfl
    exact Entails.of_eq hEq
  pool_join lim st {s} htp hbs := by
    change _ ⊢ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s
    unfold mallocngHookBudgetPool
    have hjn := (mallocngPoolErrnoSplit hS γ mpl tp brkStart).pool_join lim st htp hbs
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_left hjn))
    sep_entail
  pool_mapped_lt_userVa _ _ {_} {_} {_} henf hsat hmap :=
    mallocngHookBudgetPool_mapped_lt_userVa hS henf hsat hmap

noncomputable def finePoolErrnoSplit (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolErrnoSplit (fineRustCliAllocBudget γ mpl tp brkStart) tp brkStart :=
  mallocngPoolErrnoSplit fineCostModelSound γ mpl tp brkStart

noncomputable def fineHookPoolErrnoSplit (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolErrnoSplit (fineHookRustCliAllocBudget γ mpl tp brkStart) tp brkStart :=
  mallocngHookPoolErrnoSplit fineCostModelSound γ mpl tp brkStart

/-- `RustCliAllocBudgetEntries` wrapper for `readFileAnyBudgetCondSpec` at any
`PoolErrnoSplit A tp brkStart`. -/
theorem cliIoReadFileAnyBudgetCond_ok_of_entries
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (hAlloc : RustCliAllocBudgetEntriesBase M A P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym })
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileAnyBudgetCondSpec A lim stk) :=
  cliIoReadFileAnyBudgetCond_ok_of_errnoSplit S lim hpl hCode hstk hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim
    (hAlloc.alloc lim) (hAlloc.realloc lim) (hAlloc.dealloc lim) hEnf

theorem cliIoReadFileBudgetCond_ok_of_entries
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (hAlloc : RustCliAllocBudgetEntriesBase M A P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym })
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileBudgetCondSpec A lim stk) :=
  cliIoReadFileBudgetCond_ok_of_errnoSplit S lim hpl hCode hstk hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim
    (hAlloc.alloc lim) (hAlloc.realloc lim) (hAlloc.dealloc lim) hEnf

/-! ## Read-Only Block Subset `{0, 3, 4}` (`CliIoReadsCodeLoaded`) Variants -/

section
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  cliIoReadsKeep CliIoReadsCodeLoaded sepWP_seg_cliIo_block_pure_reads
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget (
  cliIoFinishGrow_budget_ok_withReadsCodeLoaded
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoLoopBudget (
  cliIoReadFile_ret_epilogue_vm_reads cliIoReadFile_err_cap0_epilogue_vm_reads
  cliIoReadFile_file_loop_budget_reads
)
open VerifiedLibraries.RustStd (seqCodeLoadedWhere)

section
arm64_proof_prelude

theorem cliIoReadFile_pre_open_valid_vm_reads [CliIoPlacement]
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {ro : Bool} {s0 : State} {sret pathPtr : BitVec 64} {pathBytes : List (BitVec 8)}
    {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hlt : pathBytes.length < 4096) (hnul : 0#8 ∉ pathBytes)
    (hcl0 : CliIoReadsCodeLoaded cliIoMpl s0.mem)
    (hpc0 : s0.pc = cliIoPl03.base) (hrun0 : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = pathPtr)
    (hx1 : (s0.readReg64 .x1).toNat = pathBytes.length)
    (hx8 : s0.readReg64 .x8 = sret)
    (hat_open : ∀ (sm : State) (ev0 : BitVec 32) (v0 v1 v2 st0 st1 st2 st3 : BitVec 64),
      CliIoReadsCodeLoaded cliIoMpl sm.mem →
      sm.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym →
      sm.status = .Running →
      sm.sp = s0.sp - 8320#64 →
      sm.spAligned = true →
      sm.readReg64 .lr = cliIoPl03.base + 136#64 →
      sm.readReg64 .x0 = s0.sp - 8320#64 →
      sm.readReg32 .x1 = O_CLOEXEC_W32 →
      sm.readReg64 (.gpr 24#5) = sret →
      sm.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      AllocCallPreserved s0 sm →
      SepWP P (s0.readReg64 .lr) sm
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
          memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
            (4095 - pathBytes.length) ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
          ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          memcpySrc ro pathPtr pathBytes ∗
          vecHeader sret v0 v1 v2 ∗
          (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗
          P_pool sm)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗
        memRegion sret 24 ∗ StdErrnoCell s0.tpidrEl0 ∗ P_pool s0)
      post oomProp := by
  have hlen_lt64 : pathBytes.length < 2 ^ 64 := hx1 ▸ (s0.readReg64 .x1).isLt
  have hx1_bv : s0.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := by
    rw [← hx1]; simp
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [cliIoReadFile_stack_split s0.sp hlo hhi,
      memRegion24_eq_exists_vecHeader sret,
      memRegion4096_split_probe32 (s0.sp - 8320#64),
      memRegion4096_split_probe32 (s0.sp - 4224#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
  refine SepWP.exists_elim fun ev0 =>
    SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 =>
    SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 =>
    SepWP.exists_elim fun r4 => SepWP.exists_elim fun r5 =>
    SepWP.exists_elim fun r6 => SepWP.exists_elim fun r7 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r9 =>
    SepWP.exists_elim fun r10 => SepWP.exists_elim fun r11 =>
    SepWP.exists_elim fun wp4224 => SepWP.exists_elim fun wp8320 => ?_
  have hrefold8320 :
      memRegion (s0.sp - 8320#64) 32 ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 8280#64) 4056 ⊢ memRegion (s0.sp - 8320#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 8320#64) 0#64
  have hrefold4224 :
      memRegion (s0.sp - 4224#64) 32 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 4056 ⊢ memRegion (s0.sp - 4224#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 4224#64) 0#64
  have hule_t : BitVec.ule (BitVec.ofNat 64 pathBytes.length) 4095#64 = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hult_f : BitVec.ult 4095#64 (BitVec.ofNat 64 pathBytes.length) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl0
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym)
  intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = cliIoPl03.base := hcpu1.pc_eq.trans hpc0
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx0_1' : s1'.readReg64 .x0 = pathPtr := (hcpu1.readReg64 .x0).trans hx0
  have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := (hcpu1.readReg64 .x1).trans hx1_bv
  have hx8_1' : s1'.readReg64 .x8 = sret := (hcpu1.readReg64 .x8).trans hx8
  by_cases hnil : pathBytes = []
  · subst hnil
    have hnil_len : ([] : List (BitVec 8)).length = 0 := rfl
    rw [hnil_len] at hx1_1'
    apply rustSepWP_cut (mid := cliIoPl03.base + 112#64)
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1') ?_
    have hcarve8320 :
        memRegion (s0.sp - 8320#64) 4096 =
          ((∃∗ z0 : BitVec 8, (s0.sp - 8320#64) ↦₈ z0) ∗ memRegion (s0.sp - 8319#64) 4095) := by
      simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 8320#64) 0 4095 (by decide)
    let KeepEmpty0 : SepProp :=
      memcpySrc ro pathPtr [] ∗
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        (((s0.sp - 96#64) ↦₆₄ s1'.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s1'.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s1'.readReg64 (.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s1'.readReg64 (.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s1'.readReg64 (.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s1'.readReg64 (.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s1'.readReg64 (.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s1'.readReg64 (.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s1'.readReg64 (.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s1'.readReg64 (.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s1'.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s1'.readReg64 (.gpr 19#5))) ∗
        vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool s0
    refine SepWP.weaken_pre
      (P' := ((∃∗ z0 : BitVec 8, (s0.sp - 8320#64) ↦₈ z0) ∗ memRegion (s0.sp - 8319#64) 4095) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗ KeepEmpty0)
      (by rw [← hcarve8320]
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hrefold8320 (sepConj_mono_left (Q := KeepEmpty0) hrefold4224))
              (by dsimp only [KeepEmpty0]; sep_entail))
          dsimp only [KeepEmpty0]; sep_entail) ?_
    wp_conv_pre => dsimp only [KeepEmpty0]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro z0
    wp_sym_steps
    refine SepWP.done cliIoReadFile_open_pc (by simpa [arm64_norm] using hrun1')
      fun sm hcpu_m0 hcl_m hnsp_m hsym_m => ?_
    have hcpu_m := hcpu_m0.1
    have ⟨hacp_0m, hvm_0m⟩ :=
      vmPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m hsym_m
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq : P_pool s0 = P_pool sm := (hP_vm hvm_0m.toVmMemPreserved).symm
    have hsp_m_eq : sm.sp = s0.sp - 8320#64 := hcpu_m.sp_eq.trans (by simp [arm64_norm])
    have hsp_m : sm.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hw1_m : sm.readReg32 .x1 = O_CLOEXEC_W32 := by
      rw [State.readReg32, hcpu_m.readReg64 .x1]; simp [arm64_norm, O_CLOEXEC_W32]
    refine SepWP.weaken_pre ?_
      (hat_open sm ev0 v0 v1 v2 st0 st1 st2 st3
        hcl_m (hcpu_m.pc_eq.trans cliIoReadFile_open_pc) (hcpu_m.status_eq.trans hrun1')
        hsp_m_eq hsp_m
        (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
        (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
        hw1_m
        (by rw [hcpu_m.readReg64]; simp [arm64_norm])
        (by rw [hcpu_m.readReg64]; simp [arm64_norm])
        (hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
        hacp_0m)
    have hcstr_nil : cstrBytes (cPathOf []) = [0#8] := by rw [cstrBytes_cPathOf]; rfl
    rw [hcstr_nil, pointsToBytes_singleton, hpool_eq,
      hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
      hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
      hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
      hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
      hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
      hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
    dsimp only [cliIoSavedRegs12]; simp only [bv_lin_norm]
    sep_entail
  · have h1_pos : 1 ≤ pathBytes.length := List.length_pos_iff.mpr hnil
    have hnez_len : (BitVec.ofNat 64 pathBytes.length == 0#64) = false :=
      bv64_beq_ofNat_false (b := 0) (by omega) (by omega) (by decide)
    apply rustSepWP_cut (mid := cliIoPl03.base + 84#64)
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm])
      (by simpa [arm64_norm] using hrun1') ?_
    let F_ok : SepProp :=
      memRegion (s0.sp - 4223#64) 4095 ∗
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool s0
    have hcarve4224' :
        memRegion (s0.sp - 4224#64) 4096 ⊢
          (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095 := by
      rw [show memRegion (s0.sp - 4224#64) 4096 =
        ((∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095) by
          simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 4224#64) 0 4095 (by decide)]
      exact Entails.refl _
    refine SepWP.weaken_pre
      (P' := memcpySrc ro (pathPtr + 0#64) pathBytes ∗
        memRegion ((s0.sp - 8320#64) + 0#64) 4096 ∗
        (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ F_ok) ?_ ?_
    · rw [hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
        hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
        hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
        hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
        hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
        hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
      dsimp only [F_ok, cliIoSavedRegs12]; simp only [bv_lin_norm]
      let KeepOk0 : SepProp :=
        memcpySrc ro pathPtr pathBytes ∗
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
          vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool s0
      refine Entails.trans ?_
        (Entails.trans
          (sepConj_mono hrefold8320
            (sepConj_mono_left (Q := KeepOk0) (Entails.trans hrefold4224 hcarve4224')))
          (by dsimp only [KeepOk0]; simp only [bv_lin_norm]; sep_entail))
      dsimp only [KeepOk0]; simp only [bv_lin_norm]; sep_entail
    · wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro sc0
      wp_conv_pre => simp only [← sepConj_assoc]
      refine SepWP.weaken_pre (by sep_entail)
        (cliIoReadFile_nul_scan_loop_valid pathBytes (idx := 0) (n := pathBytes.length)
          (pathPtr := pathPtr) (dst := s0.sp - 8320#64) (scratchPtr := s0.sp - 4224#64)
          (F := F_ok) (sc0 := sc0)
          h1_pos (Nat.zero_add _) hlt hnul
          (by simp [arm64_norm])
          (by simpa [arm64_norm] using hrun1')
          (by simp only [State.spAligned, arm64_norm]; exact hsp0)
          (by simp [arm64_norm, hx0_1', bv_lin_norm])
          (by simp only [arm64_norm])
          (by simp [arm64_norm, bv_lin_norm])
          (by simp [arm64_norm])
          (fun sf_scan sc1 hpc_scan hpres_scan => ?_))
      dsimp only [F_ok]
      wp_conv_pre =>
        rw [show 4096 - pathBytes.length = (4095 - pathBytes.length) + 1 by omega,
          memRegion_succ_off (s0.sp - 8320#64) pathBytes.length (4095 - pathBytes.length) (by omega)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro z_nul
      have hx1_scan : sf_scan.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
        hpres_scan.x1_eq.trans (by simp [arm64_norm, hx1_1'])
      have hx8_scan : sf_scan.readReg64 .x8 = sret :=
        hpres_scan.x8_eq.trans (by simp [arm64_norm, hx8_1'])
      have hsp_scan_eq : sf_scan.sp = s0.sp - 8320#64 :=
        hpres_scan.sp_eq.trans (by simp [arm64_norm])
      have hrun_scan := hpres_scan.run_eq
      have hsp_scan := hpres_scan.spAligned_eq
      wp_sym_steps
      refine SepWP.done cliIoReadFile_open_pc (by simpa [arm64_norm] using hrun_scan)
        fun sm hcpu_m0 hcl_m hnsp_m hsym_m => ?_
      have hcpu_m := hcpu_m0.1
      have ⟨hacp_0m, hvm_0m⟩ :=
        vmPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m hsym_m
          ((by simp [arm64_norm] : _ = sf_scan.tpidrEl0).trans
            (hpres_scan.tp_eq.trans (by simp [arm64_norm])))
          ((by simp [arm64_norm] : _ = sf_scan.sigActions).trans
            (hpres_scan.sig_eq.trans (by simp [arm64_norm])))
          ((by simp [arm64_norm] : _ = sf_scan.oracle).trans
            (hpres_scan.oracle_eq.trans (by simp [arm64_norm])))
      have hpool_eq : P_pool s0 = P_pool sm := (hP_vm hvm_0m.toVmMemPreserved).symm
      have hsp_m_eq : sm.sp = s0.sp - 8320#64 :=
        hcpu_m.sp_eq.trans (by simp [arm64_norm, hsp_scan_eq])
      have hsp_m : sm.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 8320#64 hsp0
      have hw1_m : sm.readReg32 .x1 = O_CLOEXEC_W32 := by
        rw [State.readReg32, hcpu_m.readReg64 .x1]; simp [arm64_norm, O_CLOEXEC_W32]
      have hx29_m : sm.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_m.readReg64 (.gpr 29#5)]; simp only [arm64_norm]
        exact hpres_scan.x29_eq.trans (by simp [arm64_norm])
      have hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
        hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sf_scan).trans
          (hpres_scan.vregs_eq.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)))
      refine SepWP.weaken_pre ?_
        (hat_open sm ev0 v0 v1 v2 st0 st1 st2 st3
          hcl_m (hcpu_m.pc_eq.trans cliIoReadFile_open_pc) (hcpu_m.status_eq.trans hrun_scan)
          hsp_m_eq hsp_m
          (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
          (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
          hw1_m
          (by rw [hcpu_m.readReg64]; simp [arm64_norm])
          hx29_m hvregs_m hacp_0m)
      have hmerge4224 :
          ((s0.sp - 4224#64) ↦₈ sc1) ∗ memRegion (s0.sp - 4223#64) 4095 ⊢
            memRegion (s0.sp - 4224#64) 4096 := by
        simpa only [bv_lin_norm] using memRegion_byte_merge (s0.sp - 4224#64) sc1 4095 (by decide)
      have hcstr_eq :
          ((s0.sp - 8320#64) ↦ₛ pathBytes) ∗
            (((s0.sp - 8320#64) + BitVec.ofNat 64 pathBytes.length) ↦₈ 0#8) =
          ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) := by
        rw [cstrBytes_cPathOf, pointsToBytes_snoc]
      rw [hpool_eq]
      let KeepOk1 : SepProp :=
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
          memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
            (4095 - pathBytes.length) ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗
          memcpySrc ro pathPtr pathBytes ∗
          vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ P_pool sm
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_left (Q := KeepOk1) hmerge4224)
          (by dsimp only [KeepOk1]; simp only [bv_lin_norm]; sep_entail))
      dsimp only [KeepOk1]
      rw [← hcstr_eq]
      simp only [bv_lin_norm]
      sep_entail

/-! ## 3. Post-`open` `.err` and `.localDir` Paths Over `VmPreserved` Pool -/

theorem cliIoReadFile_open_err_vm_reads [CliIoPlacement]
    (R_alloc : RustAlloc)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 so : State} {sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {errno stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) (hsp0 : s0.spAligned = true)
    (herr_cases : errno = 2 ∨ errno = 20 ∨ errno = 24)
    (hcl_o : CliIoReadsCodeLoaded cliIoMpl so.mem)
    (hpc_o : so.pc = cliIoPl03.base + 136#64) (hrun_o : so.status = .Running)
    (hsp_o : so.sp = s0.sp - 8320#64)
    (hw0_o : so.readReg32 .x0 = 0xffffffff#32)
    (hx24_o : so.readReg64 (.gpr 24#5) = sret)
    (htp_o : so.tpidrEl0 = s0.tpidrEl0)
    (hvregs_o : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_o : so.fs = s0.fs) (htr_o : so.trace = s0.trace)
    (hsig_o : so.sigActions = s0.sigActions) (hbs_o : so.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (ioVecAt R_alloc sret (if errno = 2 then .ok [] else .error ()) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ BitVec.ofNat 32 errno) ∗ P_pool so)
      post oomProp := by
  let ev := BitVec.ofNat 32 errno
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_o
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl03.base + 136#64 := hcpu_o.pc_eq.trans hpc_o
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_o
  have hsp_o' : so'.spAligned = true := by
    rw [hcpu_o.spAligned]; simp only [State.spAligned]; rw [hsp_o]
    exact s0.spAligned_sub 8320#64 hsp0
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = true := by
    rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_o]; decide
  wp_sym_steps
  refine SepWP.done cliIoReadFile_errno1_pc (by simpa [arm64_norm] using hrun_o')
    fun sm1 hcpu_10 hcl_1 hnsp_1 hsym_1 => ?_
  have hcpu_1 := hcpu_10.1
  have ⟨hacp_o1, hvm_o1⟩ :=
    vmPreserved_of_seg hcpu_o0 hcpu_10 hnsp_1 hsym_1
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_o1 : P_pool so = P_pool sm1 := (hP_vm hvm_o1.toVmMemPreserved).symm
  have hpc_1 : sm1.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
    hcpu_1.pc_eq.trans cliIoReadFile_errno1_pc
  have hrun_1 : sm1.status = .Running := hcpu_1.status_eq.trans hrun_o'
  have hsp_1_eq : sm1.sp = s0.sp - 8320#64 :=
    hcpu_1.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_o))
  have hsp_1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_1_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_1 : sm1.readReg64 .lr = cliIoPl03.base + 144#64 := by
    rw [hcpu_1.readReg64 .lr]; simp [arm64_norm]
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_1.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx24_o
  have htp_1 : sm1.tpidrEl0 = s0.tpidrEl0 := hacp_o1.2.2.2.1.trans htp_o
  have hvregs_1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 :=
    hcpu_1.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_o))
  let T_el1 : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
      (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗ P_pool sm1
  apply seqCodeLoadedWhere hcl_1 (mid := cliIoPl03.base + 144#64)
  apply (SepWP.call_subroutine_frame herrno (F := T_el1) (x := ())
    hpc_1 hrun_1 hsp_1 hlr_1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslErrnoLocationSpec, T_el1]; rw [emp_sepConj]
    rw [hpool_eq_o1] at hm'
    exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
  · intro se1 hpc_se1 hrun_se1 hsp_se1 hcs_1
    refine SepWP.done hpc_se1 hrun_se1 fun hcl_se1 => ?_
    wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el1]
    apply SepWP.pure_elim; rintro ⟨hx0_se1, _, hstd_1⟩
    have hpool_eq_1 : P_pool sm1 = P_pool se1 :=
      (hP_vm (vmPreserved_of_stdState hstd_1).toVmMemPreserved).symm
    have hsp_se1_eq : se1.sp = s0.sp - 8320#64 := hsp_se1.trans hsp_1_eq
    have hx0_se1' : se1.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
      rw [hx0_se1, muslErrnoAddr_eq_stdErrnoAddr, htp_1]
    have hx24_se1 : se1.readReg64 (.gpr 24#5) = sret := (calleeSaved_x24 hcs_1).trans hx24_1
    have htp_se1 : se1.tpidrEl0 = s0.tpidrEl0 := hstd_1.2.2.1.trans htp_1
    have hvregs_se1 : calleeSavedVRegs se1 = calleeSavedVRegs s0 :=
      (calleeSaved_vregs hcs_1).trans hvregs_1
    apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_se1
      (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
    intro se1' hcpu_e10; have hcpu_e1 := hcpu_e10.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_e1' : se1'.pc = cliIoPl03.base + 144#64 := hcpu_e1.pc_eq.trans hpc_se1
    have hrun_e1' : se1'.status = .Running := hcpu_e1.status_eq.trans hrun_se1
    have hsp_e1' : se1'.spAligned = true := by
      rw [hcpu_e1.spAligned]; simp only [State.spAligned]; rw [hsp_se1_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx0_e1' : se1'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
      (hcpu_e1.readReg64 _).trans hx0_se1'
    have hev_ne4 : (BitVec.setWidth 64 ev - 4#64 == 0#64) = false := by
      dsimp only [ev]; rcases herr_cases with rfl | rfl | rfl <;> decide
    wp_sym_steps
    have herrno2_pc :
        cliIoPl03.ρ "__errno_location" =
          signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym := by
      simpa [arm64_norm, cliIoErrnoLocationSym] using cliIoReadFile_errno2_pc
    refine SepWP.done (by simpa [arm64_norm] using herrno2_pc)
      (by simpa [arm64_norm] using hrun_e1')
      fun sm2 hcpu_20 hcl_2 hnsp_2 hsym_2 => ?_
    have hcpu_2 := hcpu_20.1
    have ⟨hacp_12, hvm_12⟩ :=
      vmPreserved_of_seg hcpu_e10 hcpu_20 hnsp_2 hsym_2
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_12 : P_pool se1 = P_pool sm2 := (hP_vm hvm_12.toVmMemPreserved).symm
    have hpc_2 : sm2.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
      hcpu_2.pc_eq.trans (by simpa [arm64_norm] using herrno2_pc)
    have hrun_2 : sm2.status = .Running := hcpu_2.status_eq.trans hrun_e1'
    have hsp_2_eq : sm2.sp = s0.sp - 8320#64 :=
      hcpu_2.sp_eq.trans ((by simp [arm64_norm] : _ = se1'.sp).trans (hcpu_e1.sp_eq.trans hsp_se1_eq))
    have hsp_2 : sm2.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_2_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hlr_2 : sm2.readReg64 .lr = cliIoPl03.base + 160#64 := by
      rw [hcpu_2.readReg64 .lr]; simp [arm64_norm]
    have hx24_2 : sm2.readReg64 (.gpr 24#5) = sret := by
      rw [hcpu_2.readReg64]; simp only [arm64_norm]; exact (hcpu_e1.readReg64 _).trans hx24_se1
    have htp_2 : sm2.tpidrEl0 = s0.tpidrEl0 := hacp_12.2.2.2.1.trans htp_se1
    have hvregs_2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 :=
      hcpu_2.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se1').trans
        (hcpu_e1.calleeSavedVRegs.trans hvregs_se1))
    let T_el2 : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗ P_pool sm2
    apply seqCodeLoadedWhere hcl_2 (mid := cliIoPl03.base + 160#64)
    apply (SepWP.call_subroutine_frame herrno (F := T_el2) (x := ())
      hpc_2 hrun_2 hsp_2 hlr_2
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslErrnoLocationSpec, T_el2]; rw [emp_sepConj]
      rw [hpool_eq_1, hpool_eq_12] at hm'
      exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
    · intro se2 hpc_se2 hrun_se2 hsp_se2 hcs_2
      refine SepWP.done hpc_se2 hrun_se2 fun hcl_se2 => ?_
      wp_conv_pre =>
        dsimp only [muslErrnoLocationSpec, T_el2]
        rw [show vecHeader sret v0 v1 v2 =
          (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
        simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_se2, _, hstd_2⟩
      have hpool_eq_2 : P_pool sm2 = P_pool se2 :=
        (hP_vm (vmPreserved_of_stdState hstd_2).toVmMemPreserved).symm
      have hsp_se2_eq : se2.sp = s0.sp - 8320#64 := hsp_se2.trans hsp_2_eq
      have hx0_se2' : se2.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
        rw [hx0_se2, muslErrnoAddr_eq_stdErrnoAddr, htp_2]
      have hx24_se2 : se2.readReg64 (.gpr 24#5) = sret := hcs_2.2.2.2.2.2.1.trans hx24_2
      have htp_se2 : se2.tpidrEl0 = s0.tpidrEl0 := hstd_2.2.2.1.trans htp_2
      have hvregs_se2 : calleeSavedVRegs se2 = calleeSavedVRegs s0 :=
        (calleeSaved_vregs hcs_2).trans hvregs_2
      have hfs_se2 : se2.fs = s0.fs :=
        hstd_2.1.trans (hacp_12.1.trans (hstd_1.1.trans (hacp_o1.1.trans hfs_o)))
      have htr_se2 : se2.trace = s0.trace :=
        hstd_2.2.1.trans (hacp_12.2.1.trans (hstd_1.2.1.trans (hacp_o1.2.1.trans htr_o)))
      have hsig_se2 : se2.sigActions = s0.sigActions :=
        hstd_2.2.2.2.1.trans (hacp_12.2.2.1.trans (hstd_1.2.2.2.1.trans (hacp_o1.2.2.1.trans hsig_o)))
      have hbs_se2 : se2.brkStart = s0.brkStart :=
        hstd_2.2.2.2.2.2.1.trans (hacp_12.2.2.2.2.1.trans (hstd_1.2.2.2.2.2.1.trans (hacp_o1.2.2.2.2.1.trans hbs_o)))
      apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_se2
        (mid := cliIoPl03.base + 520#64)
      intro se2' hcpu_e20; have hcpu_e2 := hcpu_e20.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_e2' : se2'.pc = cliIoPl03.base + 160#64 := hcpu_e2.pc_eq.trans hpc_se2
      have hrun_e2' : se2'.status = .Running := hcpu_e2.status_eq.trans hrun_se2
      have hsp_e2' : se2'.spAligned = true := by
        rw [hcpu_e2.spAligned]; simp only [State.spAligned]; rw [hsp_se2_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx0_e2' : se2'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
        (hcpu_e2.readReg64 _).trans hx0_se2'
      have hx24_e2' : se2'.readReg64 (.gpr 24#5) = sret :=
        (hcpu_e2.readReg64 _).trans hx24_se2
      by_cases he2 : errno = 2
      · subst he2
        dsimp only [ev]
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e2')
          fun se_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
        have hcpu_r := hcpu_r0.1
        have ⟨hacp_2r, hvm_2r⟩ :=
          vmPreserved_of_seg hcpu_e20 hcpu_r0 hnsp_r hsym_r
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_2r : P_pool se2 = P_pool se_ret := (hP_vm hvm_2r.toVmMemPreserved).symm
        have hsp_r_eq : se_ret.sp = s0.sp - 8320#64 :=
          hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = se2'.sp).trans (hcpu_e2.sp_eq.trans hsp_se2_eq))
        have hvregs_r : calleeSavedVRegs se_ret = calleeSavedVRegs s0 :=
          hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se2').trans
            (hcpu_e2.calleeSavedVRegs.trans hvregs_se2))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue_vm_reads hext3 hP_vm (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := ioVecAt R_alloc sret (if (2 : Nat) = 2 then .ok [] else .error ()) ∗
              StdErrnoCell s0.tpidrEl0)
            hlo hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_r.status_eq.trans hrun_e2') hsp0 hsp_r_eq hvregs_r
            fun sf hpc_f hrun_f hsp_f hcs_f _ hacp_rf {_Pre_f} hent =>
              hcont sf hpc_f hrun_f hsp_f hcs_f
                (hacp_rf.1.trans (hacp_2r.1.trans hfs_se2))
                (hacp_rf.2.1.trans (hacp_2r.2.1.trans htr_se2))
                (hacp_rf.2.2.1.trans (hacp_2r.2.2.1.trans hsig_se2))
                (hacp_rf.2.2.2.1.trans (hacp_2r.2.2.2.1.trans htp_se2))
                (hacp_rf.2.2.2.2.1.trans (hacp_2r.2.2.2.2.1.trans hbs_se2)) hent)
        simp only [↓reduceIte]; rw [hpool_eq_2, hpool_eq_2r]
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ 2#32) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right 2#32 (Entails.refl _)
        have hok_sret := vecHeader_empty_entails_ioVecAt_ok R_alloc sret
        let KeepE2 : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ P_pool se_ret
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hok_sret (sepConj_mono_left (Q := KeepE2) hev_cell))
            (by dsimp only [KeepE2]; sep_entail))
        dsimp only [KeepE2]; sep_entail
      · have hev_ne2 : (BitVec.setWidth 64 ev - 2#64 == 0#64) = false := by
          dsimp only [ev]
          rcases herr_cases with rfl | rfl | rfl
          · exact absurd rfl he2
          · decide
          · decide
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e2')
          fun se_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
        have hcpu_r := hcpu_r0.1
        have ⟨hacp_2r, hvm_2r⟩ :=
          vmPreserved_of_seg hcpu_e20 hcpu_r0 hnsp_r hsym_r
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_2r : P_pool se2 = P_pool se_ret := (hP_vm hvm_2r.toVmMemPreserved).symm
        have hsp_r_eq : se_ret.sp = s0.sp - 8320#64 :=
          hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = se2'.sp).trans (hcpu_e2.sp_eq.trans hsp_se2_eq))
        have hvregs_r : calleeSavedVRegs se_ret = calleeSavedVRegs s0 :=
          hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se2').trans
            (hcpu_e2.calleeSavedVRegs.trans hvregs_se2))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue_vm_reads hext3 hP_vm (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := ioVecAt R_alloc sret (if errno = 2 then .ok [] else .error ()) ∗
              StdErrnoCell s0.tpidrEl0)
            hlo hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_r.status_eq.trans hrun_e2') hsp0 hsp_r_eq hvregs_r
            fun sf hpc_f hrun_f hsp_f hcs_f _ hacp_rf {_Pre_f} hent =>
              hcont sf hpc_f hrun_f hsp_f hcs_f
                (hacp_rf.1.trans (hacp_2r.1.trans hfs_se2))
                (hacp_rf.2.1.trans (hacp_2r.2.1.trans htr_se2))
                (hacp_rf.2.2.1.trans (hacp_2r.2.2.1.trans hsig_se2))
                (hacp_rf.2.2.2.1.trans (hacp_2r.2.2.2.1.trans htp_se2))
                (hacp_rf.2.2.2.2.1.trans (hacp_2r.2.2.2.2.1.trans hbs_se2)) hent)
        simp only [he2, ↓reduceIte]; rw [hpool_eq_2, hpool_eq_2r, ← ioResultErr_eq_cliIoVecAt_err R_alloc sret]
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right ev (Entails.refl _)
        have herr_sret :
            (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) ⊢
              (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16 :=
          vecHeader_to_err_sret sret v1 v2
        let KeepEn : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ P_pool se_ret
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono herr_sret (sepConj_mono_left (Q := KeepEn) hev_cell))
            (by dsimp only [KeepEn]; sep_entail))
        dsimp only [KeepEn]; sep_entail

theorem cliIoReadFile_dir_loop_vm_reads [CliIoPlacement]
    (R_alloc : RustAlloc)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadDir32Spec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {P_pool : State → SepProp}
    (hP_vm : ∀ {s s' : State}, VmMemPreserved s s' → P_pool s' = P_pool s)
    {s0 sl : State} {fd count sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {desc : FdEntry} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8368 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds : sl.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir) (hcanr : desc.accMode.canRead = true)
    (hcl : CliIoReadsCodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl03.base + 216#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 8320#64)
    (hw19 : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx21 : sl.readReg64 (.gpr 21#5) = 0#64)
    (hx23 : sl.readReg64 (.gpr 23#5) = count)
    (hx24 : sl.readReg64 (.gpr 24#5) = sret)
    (htp : sl.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      CliIoReadsCodeLoaded cliIoMpl sf.mem →
      sf.fs = sl.fs.setFd fd none →
      sf.trace = sl.trace → sf.sigActions = sl.sigActions →
      sf.tpidrEl0 = sl.tpidrEl0 → sf.brkStart = sl.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          (ioVecAt R_alloc sret (.error ()) ∗ StdErrnoCell s0.tpidrEl0) ∗
          P_pool sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        P_pool sl)
      post oomProp := by
  have h32_le : 32 ≤ stackBytes - 8320 := by omega
  have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 h32_le hsb_hi]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro e0
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 8320#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = count := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadFile_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hvm_lrd⟩ :=
    vmPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : P_pool sl = P_pool sm_rd := (hP_vm hvm_lrd.toVmMemPreserved).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadFile_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 8320#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl03.base + 232#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : (sm_rd.readReg32 .x0).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_rd.readReg64 .x0)]
    simp only [arm64_norm]
    rw [hcpu_l.readReg64 (.gpr 19#5)]
    exact hw19
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp only [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = count := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfds_rd : sm_rd.fs.fds fd = some desc := by rw [hacp_lrd.1]; exact hfds
  have htp_rd : sm_rd.tpidrEl0 = s0.tpidrEl0 := hacp_lrd.2.2.2.1.trans htp
  let T_rd : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ P_pool sm_rd
  apply seqCodeLoadedWhere hcl_rd (mid := cliIoPl03.base + 232#64)
  apply (SepWP.call_subroutine_frame hread_dir (F := T_rd)
    (x := (fd, s0.sp - 4224#64, count, desc, e0))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadDir32Spec, T_rd]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hfd_lt, hx1_rd, hx2_rd, hfds_rd, hkind, hcanr⟩, ?_⟩
    rw [hpool_eq_lrd] at hm'
    rw [hsp_rd_eq, muslErrnoAddr_eq_stdErrnoAddr, htp_rd]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadDir32Spec, T_rd]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, _, herr_ne4, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : P_pool sm_rd = P_pool sr :=
      (hP_vm (vmMemPreserved_of_syscallPreserved hsys_sr)).symm
    have hsp_sr_eq : sr.sp = s0.sp - 8320#64 := hsp_sr.trans hsp_rd_eq
    have htp_sr : sr.tpidrEl0 = s0.tpidrEl0 := hsys_sr.1.trans htp_rd
    apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_sr
      (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
    intro sr' hcpu_r0
    have hcpu_r := hcpu_r0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_r' : sr'.pc = cliIoPl03.base + 232#64 := hcpu_r.pc_eq.trans hpc_sr
    have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun_sr
    have hsp_r' : sr'.spAligned = true := by
      rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_sr_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx0_r' : sr'.readReg64 .x0 = -1#64 := (hcpu_r.readReg64 _).trans hx0_sr
    wp_sym_steps
    refine SepWP.done cliIoReadFile_errno3_pc (by simpa [arm64_norm] using hrun_r')
      fun sm_el hcpu_el0 hcl_el hnsp_el hsym_el => ?_
    have hcpu_el := hcpu_el0.1
    have ⟨hacp_rel, hvm_rel⟩ :=
      vmPreserved_of_seg hcpu_r0 hcpu_el0 hnsp_el hsym_el
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_rel : P_pool sr = P_pool sm_el := (hP_vm hvm_rel.toVmMemPreserved).symm
    have hpc_el : sm_el.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
      hcpu_el.pc_eq.trans cliIoReadFile_errno3_pc
    have hrun_el : sm_el.status = .Running := hcpu_el.status_eq.trans hrun_r'
    have hsp_el_eq : sm_el.sp = s0.sp - 8320#64 :=
      hcpu_el.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_sr_eq))
    have hsp_el : sm_el.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_el_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hlr_el : sm_el.readReg64 .lr = cliIoPl03.base + 244#64 := by
      rw [hcpu_el.readReg64 .lr]; simp [arm64_norm]
    have htp_el : sm_el.tpidrEl0 = s0.tpidrEl0 := hacp_rel.2.2.2.1.trans htp_sr
    let ev := dirReadErrno32 (s0.sp - 4224#64) count
    let T_el : SepProp :=
      stackAt sm_rd.sp 32 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗
        memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ P_pool sm_el
    apply seqCodeLoadedWhere hcl_el (mid := cliIoPl03.base + 244#64)
    apply (SepWP.call_subroutine_frame herrno (F := T_el) (x := ())
      hpc_el hrun_el hsp_el hlr_el
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslErrnoLocationSpec, T_el]
      rw [emp_sepConj]
      rw [hpool_eq_sr, hpool_eq_rel, muslErrnoAddr_eq_stdErrnoAddr, htp_sr] at hm'
      exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
    · intro se0 hpc_se0 hrun_se0 hsp_se0 hcs_else0
      refine SepWP.done hpc_se0 hrun_se0 fun hcl_se0 => ?_
      wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el]; simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_se0, _, hstd_el⟩
      have hpool_eq_el : P_pool sm_el = P_pool se0 :=
        (hP_vm (vmPreserved_of_stdState hstd_el).toVmMemPreserved).symm
      have hsp_se0_eq : se0.sp = s0.sp - 8320#64 := hsp_se0.trans hsp_el_eq
      have hx0_se0' : se0.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
        rw [hx0_se0, muslErrnoAddr_eq_stdErrnoAddr, htp_el]
      apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_se0
        (mid := cliIoPl03.base + 468#64)
      intro sc' hcpu_c0
      have hcpu_c := hcpu_c0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_c' : sc'.pc = cliIoPl03.base + 244#64 := hcpu_c.pc_eq.trans hpc_se0
      have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun_se0
      have hsp_c' : sc'.spAligned = true := by
        rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_se0_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx0_c' : sc'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := (hcpu_c.readReg64 _).trans hx0_se0'
      have hev_zext_beq4 : (BitVec.setWidth 64 ev - 4#64 == 0#64) = false := by
        rcases dirReadErrno32_cases (s0.sp - 4224#64) count with h21 | h14
        · dsimp only [ev]; rw [h21]; decide
        · dsimp only [ev]; rw [h14]; decide
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_c')
        fun se_ep hcpu_ep0 hcl_ep hnsp_ep hsym_ep => ?_
      have hcpu_ep := hcpu_ep0.1
      have ⟨hacp_cep, hvm_cep⟩ :=
        vmPreserved_of_seg hcpu_c0 hcpu_ep0 hnsp_ep hsym_ep
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_cep : P_pool se0 = P_pool se_ep := (hP_vm hvm_cep.toVmMemPreserved).symm
      have hfs_ep : se_ep.fs = sl.fs :=
        hacp_cep.1.trans (hstd_el.1.trans (hacp_rel.1.trans (hfs_sr.trans hacp_lrd.1)))
      have htr_ep : se_ep.trace = sl.trace :=
        hacp_cep.2.1.trans (hstd_el.2.1.trans (hacp_rel.2.1.trans (htr_sr.trans hacp_lrd.2.1)))
      have hsig_ep : se_ep.sigActions = sl.sigActions :=
        hacp_cep.2.2.1.trans (hstd_el.2.2.2.1.trans (hacp_rel.2.2.1.trans (hsys_sr.2.1.trans hacp_lrd.2.2.1)))
      have htp_ep : se_ep.tpidrEl0 = sl.tpidrEl0 :=
        hacp_cep.2.2.2.1.trans (hstd_el.2.2.1.trans (hacp_rel.2.2.2.1.trans (hsys_sr.1.trans hacp_lrd.2.2.2.1)))
      have hbs_ep : se_ep.brkStart = sl.brkStart :=
        hacp_cep.2.2.2.2.1.trans (hstd_el.2.2.2.2.2.1.trans
          (hacp_rel.2.2.2.2.1.trans (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1)))
      have hw19_ep : (se_ep.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
        rw [readReg32_of_readReg64_eq (hcpu_ep.readReg64 (.gpr 19#5))]
        simp only [arm64_norm]
        rw [hcpu_c.readReg64 (.gpr 19#5), hcs_else0.readReg64_x19,
          hcpu_el.readReg64 (.gpr 19#5)]
        simp only [arm64_norm]
        rw [hcpu_r.readReg64 (.gpr 19#5), hcs_rdsr.readReg64_x19,
          hcpu_rd.readReg64 (.gpr 19#5)]
        simp only [arm64_norm]
        rw [hcpu_l.readReg64 (.gpr 19#5)]
        exact hw19
      have hx21_ep : se_ep.readReg64 (.gpr 21#5) = 0#64 := by
        rw [hcpu_ep.readReg64]; simp only [arm64_norm]
        rw [hcpu_c.readReg64, hcs_else0.readReg64_x21, hcpu_el.readReg64]; simp only [arm64_norm]
        rw [hcpu_r.readReg64, hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]
        exact (hcpu_l.readReg64 _).trans hx21
      have hx24_ep : se_ep.readReg64 (.gpr 24#5) = sret := by
        rw [hcpu_ep.readReg64]; simp only [arm64_norm]
        rw [hcpu_c.readReg64, hcs_else0.readReg64_x24, hcpu_el.readReg64]; simp only [arm64_norm]
        rw [hcpu_r.readReg64, hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]
        exact (hcpu_l.readReg64 _).trans hx24
      have hvregs_ep : calleeSavedVRegs se_ep = calleeSavedVRegs s0 :=
        hcpu_ep.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
          (hcpu_c.calleeSavedVRegs.trans (hcs_else0.vregs.trans
            (hcpu_el.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
              (hcpu_r.calleeSavedVRegs.trans (hcs_rdsr.vregs.trans
                (hcpu_rd.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans
                  (hcpu_l.calleeSavedVRegs.trans hvregs))))))))))
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_err_cap0_epilogue_vm_reads hext3 hclose hP_vm
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (R_extra := StdErrnoCell s0.tpidrEl0)
          hlo hhi hfd_lt (by rw [hfs_ep]; exact hfds) (Or.inr hkind) hcl_ep
          (hcpu_ep.pc_eq.trans (by simp [arm64_norm])) (hcpu_ep.status_eq.trans hrun_c') hsp0
          (hcpu_ep.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans (hcpu_c.sp_eq.trans hsp_se0_eq)))
          hw19_ep hx21_ep hx24_ep hvregs_ep
          fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent =>
            hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
              (hfs_f.trans (congrArg (fun f => f.setFd fd none) hfs_ep))
              (htr_f.trans htr_ep) (hsig_f.trans hsig_ep) (htp_f.trans htp_ep) (hbs_f.trans hbs_ep)
              (by simpa only [ioResultErr_eq_cliIoVecAt_err R_alloc sret] using hent))
      rw [hpool_eq_el, hpool_eq_cep, hsp_rd_eq,
        stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 32 h32_le hsb_hi]
      have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
        Entails.sepExists_right ev (Entails.refl _)
      let Rest : SepProp :=
        stackAt (s0.sp - 8320#64) 32 ∗
          memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 32) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ P_pool se_ep
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_right (P := Rest) hev_cell) (by dsimp only [Rest]; sep_entail))
      dsimp only [Rest]; sep_entail

/-! ## 4. Budget-Threaded Post-`open` `.ok` Branch (`+0x88 → +0xd8`) -/

theorem cliIoReadFile_open_ok_budget_reads [CliIoPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 so : State} {fd sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {ev0 : BitVec 32} {pathBytes : List (BitVec 8)} {kind : FdKind}
    {stackBytes : Nat} {st : M.σ}
    {post : State → SepProp → Prop}
    (hlo : 8368 + allocHookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (htp0 : s0.tpidrEl0 = tp) (hbs0 : s0.brkStart = brkStart)
    (hcl_ok : classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd kind)
    (hcl_o : CliIoReadsCodeLoaded cliIoMpl so.mem)
    (hpc_o : so.pc = cliIoPl03.base + 136#64) (hrun_o : so.status = .Running)
    (hsp_o : so.sp = s0.sp - 8320#64)
    (hw0_o : so.readReg32 .x0 = fd.truncate 32)
    (hx24_o : so.readReg64 (.gpr 24#5) = sret)
    (hx29_o : so.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htp_o : so.tpidrEl0 = s0.tpidrEl0)
    (hvregs_o : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_o : so.fs = s0.fs.setFd fd (some (cliIoOpenEntry pathBytes kind)))
    (htr_o : so.trace = s0.trace) (hsig_o : so.sigActions = s0.sigActions)
    (hbs_o : so.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          ioVecAt A.repAlloc sret (cliIo.rd s0.fs.files pathBytes) ∗
          A.pool lim (M.stepEvents (readFileBudgetEvents s0.fs.files pathBytes) st) sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ S.core lim st so)
      post
      (fun sf_oom =>
        ⌜¬ FitsEvents M lim st (readFileBudgetEvents s0.fs.files pathBytes) ∧
          CliIoFilesOomPreserved s0 sf_oom⌝) := by
  obtain ⟨hb_none, _, _, hfd_max, hfds_none, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl_ok
  have hfd_lt31 : fd.toNat < 2 ^ 31 := Nat.lt_trans hfd_max (by decide)
  have hfd_lt32 : fd.toNat < 2 ^ 32 := Nat.lt_trans hfd_lt31 (by decide)
  apply sepWP_seg_cliIo_block_pure_reads 3 cliIo3_lt rfl hext3 cliIoBlockNoSvc0_03 hcl_o
    (mid := cliIoPl03.base + 216#64)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl03.base + 136#64 := hcpu_o.pc_eq.trans hpc_o
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_o
  have hsp_o' : so'.spAligned = true := by
    rw [hcpu_o.spAligned]; simp only [State.spAligned]; rw [hsp_o]
    exact s0.spAligned_sub 8320#64 hsp0
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = false := by
    rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_o]
    exact getLsbD_31_of_fd_lt hfd_lt31
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_o')
    fun sl hcpu_l0 hcl_l hnsp_l hsym_l => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨hacp_ol, hvm_ol⟩ :=
    vmPreserved_of_seg hcpu_o0 hcpu_l0 hnsp_l hsym_l
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hcore_eq_ol : S.core lim st so = S.core lim st sl :=
    (S.core_transport lim st hvm_ol.toVmMemPreserved).symm
  have hpc_l : sl.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl.status = .Running := hcpu_l.status_eq.trans hrun_o'
  have hsp_l : sl.sp = s0.sp - 8320#64 :=
    hcpu_l.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_o))
  have hw19_l : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    apply readReg32_zeroExtend_of_truncate ?_ hfd_lt32
    rw [readReg32_of_readReg64_eq (hcpu_l.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_o.readReg64 .x0]
    exact hw0_o
  have hx24_l : sl.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_l.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx24_o
  have hx29_l : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_l.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx29_o
  have hvregs_l : calleeSavedVRegs sl = calleeSavedVRegs s0 :=
    hcpu_l.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_o))
  have hfs_l : sl.fs = s0.fs.setFd fd (some (cliIoOpenEntry pathBytes kind)) :=
    hacp_ol.1.trans hfs_o
  have htr_l : sl.trace = s0.trace := hacp_ol.2.1.trans htr_o
  have hsig_l : sl.sigActions = s0.sigActions := hacp_ol.2.2.1.trans hsig_o
  have htp_l : sl.tpidrEl0 = s0.tpidrEl0 := hacp_ol.2.2.2.1.trans htp_o
  have hbs_l : sl.brkStart = s0.brkStart := hacp_ol.2.2.2.2.1.trans hbs_o
  have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ StdErrnoCell s0.tpidrEl0 :=
    Entails.sepExists_right ev0 (Entails.refl _)
  rcases hkind_cases with ⟨rfl, _⟩ | ⟨rfl, bs, hbs_file⟩
  · obtain ⟨hrd_dir, hevs_dir⟩ := classifyOpenRdonly_localDir_align hcl_ok
    have hfds_l : sl.fs.fds fd = some (cliIoOpenEntry pathBytes .localDir) := by
      rw [hfs_l]; simp [FsState.setFd]
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_dir_loop_vm_reads A.repAlloc hext3 hread_dir herrno hclose
        (fun hvm => S.core_transport lim st hvm)
        (count := 4096#64) (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
        (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (by omega) hhi hfd_lt31 hfds_l rfl rfl
        hcl_l hpc_l hrun_l hsp0 hsp_l hw19_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        hx24_l htp_l hvregs_l
        fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent => ?_)
    · rw [hcore_eq_ol]
      let KeepDir : SepProp :=
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ S.core lim st sl
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_left (Q := KeepDir) hev_cell)
          (by dsimp only [KeepDir]; sep_entail))
      dsimp only [KeepDir]; sep_entail
    · have hfs_f' : sf.fs = s0.fs := by
        rw [hfs_f, hfs_l]; exact setFd_none_setFd_of_fds_none hfds_none
      have htp_sf : sf.tpidrEl0 = s0.tpidrEl0 := htp_f.trans htp_l
      have hbs_sf : sf.brkStart = s0.brkStart := hbs_f.trans hbs_l
      have hjoin_sf : S.core lim st sf ∗ StdErrnoCell s0.tpidrEl0 ⊢ A.pool lim st sf := by
        rw [htp0]
        exact S.pool_join lim st (htp_sf.trans htp0) (hbs_sf.trans hbs0)
      refine hcont sf hpc_f hrun_f hsp_f hcs_f hfs_f'
        (htr_f.trans htr_l) (hsig_f.trans hsig_l) htp_sf hbs_sf ?_
      rw [hrd_dir, hevs_dir]
      have hstep_nil : M.stepEvents [] st = st := rfl
      rw [hstep_nil]
      refine Entails.trans hent ?_
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right hjoin_sf))
      sep_entail
  · let d0 := cliIoOpenEntry pathBytes .localFile
    have hrem_bs : (s0.fs.fdBytes d0).drop d0.offset = bs := by
      dsimp only [d0, cliIoOpenEntry]; rw [fdBytes_open_localFile hbs_file]; rfl
    obtain ⟨hout_eq, hevs_eq⟩ := classifyOpenRdonly_localFile_align hb_none hbs_file
    rw [show (fun sf_oom =>
        ⌜¬ FitsEvents M lim st (readFileBudgetEvents s0.fs.files pathBytes) ∧
          CliIoFilesOomPreserved s0 sf_oom⌝) =
      (fun sf_oom =>
        ⌜¬ FitsEvents M lim st (cliIoFileLoopBudgetEvents ((s0.fs.fdBytes d0).drop d0.offset)) ∧
          CliIoFilesOomPreserved s0 sf_oom⌝) by
      funext sf_oom; rw [hrem_bs, hevs_eq]]
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_file_loop_budget_reads A lim (fun st => S.pool_mem_transport lim st)
        hext3 hread_file hmemcpy hfg hdealloc hclose
        (d0 := d0) (fd := fd) (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
        hlo hhi hsp_lo hsp_va hsp0 hfd_lt31 hfds_none rfl rfl rfl
        (fun sf hpc_f hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f
            (by simpa only [hrem_bs, hout_eq, hevs_eq] using hent))
        (cliIoFileCap + 1) sl 1#64 st0 st1 st2 st3 0 0 st
        (Nat.le_refl _) (Nat.zero_le _) (fun _ => Nat.dvd_zero 4096) rfl rfl
        hcl_l hpc_l hrun_l hsp_l hw19_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm, wantBytes])
        hx24_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        hx29_l hvregs_l
        (by simpa only [d0, cliIoOpenEntry, Nat.zero_add] using hfs_l)
        htr_l hsig_l htp_l hbs_l)
    rw [hcore_eq_ol]
    have hjoin_sl : S.core lim st sl ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ A.pool lim st sl := by
      refine Entails.trans (sepConj_mono_right hev_cell) ?_
      rw [htp0]
      exact S.pool_join lim st (htp_l.trans htp0) (hbs_l.trans hbs0)
    have hvec0 : emp ⊢ cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64
        (((s0.fs.fdBytes d0).drop d0.offset).take 0) :=
      cliIoVecBuf_zero_intro A.repAlloc (ptr := 1#64) (by decide)
    let KeepFile : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2
    have hwith_vec :
        KeepFile ⊢ KeepFile ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 0) 1#64
            (((s0.fs.fdBytes d0).drop d0.offset).take 0) := by
      simpa only [sepConj_emp] using sepConj_mono_right (P := KeepFile) hvec0
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hwith_vec hjoin_sl)
        (by dsimp only [KeepFile]; sep_entail))
    dsimp only [KeepFile]; sep_entail


/-! ## 5. Layer 1: Unified Strong Spec & `PoolErrnoSplit` Discharges of `readFileAnyBudgetCondSpec` / `readFileBudgetCondSpec` -/

theorem cliIoReadFileAnyStrongBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readFileAnyStrongBudgetCondSpec A lim stk)) := by
  have hfg := cliIoFinishGrow_budget_ok_withReadsCodeLoaded A lim hpl hext4 hshim halloc hrealloc
  let _ : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 3 cliIoReadFileSym cliIo3_lt cliIoReadFile_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
    readFileAnyBudgetCondSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, _hlt32, hpok, hallocFd⟩, hmem⟩
  have hstk_pos : 0 < stk := by omega
  have h8320 : 8320 ≤ stk := by omega
  have hhi : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (p := x.ret) (sp := s0.sp) (n := 24) (stk := stk)
      (R := bytesAt x.ro x.pathA x.path ∗ A.pool lim st s0 ∗ R)
      (by decide) hstk_pos (Satisfies.mono (by sep_entail) hmem)
  have ⟨hsp_lo, hsp_va⟩ : stk ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT :=
    stackAt_bounds_of_mapped hstk_pos hhi
      (fun _ hmap => S.pool_mapped_lt_userVa lim st hEnf
        (R := bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk ∗ R)
        (Satisfies.mono (by sep_entail) hmem) hmap)
      (R := bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ A.pool lim st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  have hpOk : PathOk (cPathOf x.path) = true := by
    rw [cPathOf_eq_pathStr]; exact hpok.1
  have hpMax : ((pathComps (cPathOf x.path)).all fun c => decide (c.length ≤ NAME_MAX)) = true := by
    rw [cPathOf_eq_pathStr]; exact hpok.2.1.2
  have hlt : x.path.length < 4096 := hpok.2.2
  have hnul : (0#8 : BitVec 8) ∉ x.path :=
    ReadFileBudgetPlaced.zero_not_mem_of_pathOk hpok.1
  have hmem1 : s0.mem ⊨ ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      ((stackAt s0.sp stk ∗ memcpySrc x.ro x.pathA x.path ∗
        memRegion x.ret 24 ∗ StdErrnoCell s0.tpidrEl0 ∗ S.core lim st s0) ∗ R) := by
    rw [← memcpySrc_eq_bytesAt x.ro x.pathA x.path] at hmem
    refine Satisfies.mono ?_ hmem
    let Keep0 : SepProp :=
      (memcpySrc x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk) ∗ R
    refine Entails.trans (by dsimp only [Keep0]; sep_entail)
      (Entails.trans (sepConj_mono_left (Q := Keep0) (S.pool_split lim st s0))
        (by dsimp only [Keep0]; sep_entail))
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨htp0, hbs0⟩, hmem_split⟩
  refine ⟨_, hmem_split, ?_⟩
  apply cliIo_sepWP_carry_oracle_symtab hsvc hext_os
  refine SepWP.weaken_pre (Entails.refl _)
    (cliIoReadFile_pre_open_valid_vm_reads hext3
      (P_pool := S.core lim st) (fun hvm => S.core_transport lim st hvm)
      h8320 hhi hlt hnul hcl0 hpc hrun hsp0 hx0 hx1 hx8
      fun sm ev0 v0 v1 v2 st0 st1 st2 st3
          hcl_m hpc_m hrun_m hsp_m_eq hsp_m hlr_m hx0_m hw1_m hx24_m hx29_m hvregs_m hacp_0m => ?_)
  have h112_le : 112 ≤ stk - 8320 := by omega
  have hsb_hi : stk - 8320 ≤ 2 ^ 64 := by omega
  let PreOpenRest : SepProp :=
    stackAt (s0.sp - 8320#64) (stk - 8320) ∗
      ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf x.path)) ∗
      memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (x.path.length + 1))
        (4095 - x.path.length) ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
      ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗
      vecHeader x.ret v0 v1 v2 ∗
      (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗
      S.core lim st sm
  refine SepWP.weaken_pre
    (P' := PreOpenRest ∗ memcpySrc x.ro x.pathA x.path)
    (by dsimp only [PreOpenRest]; sep_entail) ?_
  apply sepWP_frame_right
  dsimp only [PreOpenRest]
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stk - 8320) 112 h112_le hsb_hi]
    simp only [sepConj_assoc]
  have hpath_len : (cPathOf x.path).toList.length < PATH_MAX := by
    rw [toList_cPathOf_length]; exact hlt
  have hpath_ascii : ∀ c ∈ (cPathOf x.path).toList, c.toNat < 256 :=
    fun _ hc => mem_toList_cPathOf_lt_256 hc
  let T_open : SepProp :=
    memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stk - 8320)) (stk - 8320 - 112) ∗
      memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (x.path.length + 1))
        (4095 - x.path.length) ∗
      memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader x.ret v0 v1 v2 ∗ S.core lim st sm
  apply seqCodeLoadedWhere hcl_m (mid := cliIoPl03.base + 136#64)
  apply (SepWP.call_subroutine_frame hopen (F := T_open)
    (x := (s0.sp - 8320#64, cPathOf x.path, ev0))
    hpc_m hrun_m hsp_m hlr_m
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslOpenRdonlyDetSpec, T_open]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_m, hw1_m, hpOk, hpMax, hpath_len, hpath_ascii⟩, ?_⟩
    rw [hsp_m_eq, muslErrnoAddr_eq_stdErrnoAddr, hacp_0m.2.2.2.1]
    exact Satisfies.mono (by sep_frame) hm'
  · intro so hpc_so hrun_so hsp_so hcs_mo
    refine SepWP.done hpc_so hrun_so fun hcl_so => ?_
    have hsp_so_eq : so.sp = s0.sp - 8320#64 := hsp_so.trans hsp_m_eq
    have hx24_so : so.readReg64 (.gpr 24#5) = x.ret := (calleeSaved_x24 hcs_mo).trans hx24_m
    have hx29_so : so.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
      (calleeSaved_fp hcs_mo).trans hx29_m
    have hvregs_so : calleeSavedVRegs so = calleeSavedVRegs s0 :=
      (calleeSaved_vregs hcs_mo).trans hvregs_m
    have hstk_back :
        stackAt sm.sp 112 ∗
          memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stk - 8320)) (stk - 8320 - 112) ⊢
          stackAt (s0.sp - 8320#64) (stk - 8320) := by
      rw [hsp_m_eq, stackAt_shrink (s0.sp - 8320#64) (stk - 8320) 112 h112_le hsb_hi]
      sep_entail
    have hcstr_back := refold_cstr_buf4096 (s0.sp - 8320#64) x.path hlt
    wp_conv_pre => dsimp only [muslOpenRdonlyDetSpec, T_open]
    rw [hacp_0m.1]
    cases hcl_res : classifyOpenRdonly s0.fs (cPathOf x.path) with
    | err errno =>
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hw0_so, hfs_so, htr_so, hsys_so⟩
      have hcore_eq_mo : S.core lim st sm = S.core lim st so :=
        (S.core_transport lim st (vmMemPreserved_of_syscallPreserved hsys_so)).symm
      have htp_so : so.tpidrEl0 = s0.tpidrEl0 := hsys_so.1.trans hacp_0m.2.2.2.1
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_open_err_vm_reads A.repAlloc hext3 herrno
          (P_pool := S.core lim st) (fun hvm => S.core_transport lim st hvm)
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          h8320 hhi hsp0
          (classifyOpenRdonly_err_cases hcl_res)
          hcl_so hpc_so hrun_so hsp_so_eq hw0_so hx24_so htp_so hvregs_so
          hfs_so (htr_so.trans hacp_0m.2.1)
          (hsys_so.2.1.trans hacp_0m.2.2.1) (hsys_so.2.2.brkStart_eq.trans hacp_0m.2.2.2.2.1)
          fun sf _hpc_f _hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent
              horc_f hsym_f => ?_)
      · rw [hcore_eq_mo, muslErrnoAddr_eq_stdErrnoAddr, htp_so]
        let KeepErr0 : SepProp :=
          memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader x.ret v0 v1 v2 ∗
            (stdErrnoAddr s0.tpidrEl0 ↦₃₂ BitVec.ofNat 32 errno) ∗ S.core lim st so
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hstk_back (sepConj_mono_left (Q := KeepErr0) hcstr_back))
            (by dsimp only [KeepErr0]; sep_entail))
        dsimp only [KeepErr0]; sep_entail
      · have hacp_f : AllocCallPreserved s0 sf :=
          ⟨hfs_f, htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
        have hjoin_sf : S.core lim st sf ∗ StdErrnoCell s0.tpidrEl0 ⊢ A.pool lim st sf := by
          rw [htp0]; exact S.pool_join lim st (htp_f.trans htp0) (hbs_f.trans hbs0)
        refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
        rw [memcpySrc_eq_bytesAt x.ro x.pathA x.path] at hm_out
        rw [pure_sepConj_of_true ⟨hacp_f, hfs_f⟩]
        by_cases he2 : errno = 2
        · subst he2
          obtain ⟨hrd2, hevs2⟩ := classifyOpenRdonly_err2_align hcl_res
          rw [hrd2, hevs2]
          have hstep_nil : M.stepEvents [] st = st := rfl
          rw [hstep_nil]
          have hent' : _Pre_f ⊢
              stackAt s0.sp stk ∗ ioVecAt A.repAlloc x.ret (.ok []) ∗ A.pool lim st sf := by
            refine Entails.trans (by simpa only [↓reduceIte] using hent) ?_
            refine Entails.trans ?_
              (sepConj_mono_right (P := stackAt s0.sp stk)
                (sepConj_mono_right (P := ioVecAt A.repAlloc x.ret (.ok [])) hjoin_sf))
            sep_entail
          exact Satisfies.mono
            (sepConj_mono_left (Entails.trans (sepConj_mono_left hent') (by sep_entail))) hm_out
        · obtain ⟨hrd_ne, hevs_ne⟩ := classifyOpenRdonly_errNe2_align hallocFd hcl_res he2
          rw [hrd_ne, hevs_ne]
          have hstep_nil : M.stepEvents [] st = st := rfl
          rw [hstep_nil]
          have hent' : _Pre_f ⊢
              stackAt s0.sp stk ∗ ioVecAt A.repAlloc x.ret (.error ()) ∗ A.pool lim st sf := by
            refine Entails.trans (by simpa only [he2, ↓reduceIte] using hent) ?_
            refine Entails.trans ?_
              (sepConj_mono_right (P := stackAt s0.sp stk)
                (sepConj_mono_right (P := ioVecAt A.repAlloc x.ret (.error ())) hjoin_sf))
            sep_entail
          exact Satisfies.mono
            (sepConj_mono_left (Entails.trans (sepConj_mono_left hent') (by sep_entail))) hm_out
    | ok fd kind =>
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hw0_so, hfs_so, htr_so, hsys_so⟩
      have hcore_eq_mo : S.core lim st sm = S.core lim st so :=
        (S.core_transport lim st (vmMemPreserved_of_syscallPreserved hsys_so)).symm
      have htp_so : so.tpidrEl0 = s0.tpidrEl0 := hsys_so.1.trans hacp_0m.2.2.2.1
      refine SepWP.weaken_pre ?_
        (cliIoReadFile_open_ok_budget_reads S lim hext3 herrno hread_dir hread_file
          hmemcpy hfg hdealloc hclose
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3) (ev0 := ev0)
          (by omega : 8368 + allocHookStack ≤ stk) hhi hsp_lo hsp_va hsp0 htp0 hbs0 hcl_res
          hcl_so hpc_so hrun_so hsp_so_eq hw0_so hx24_so hx29_so htp_so hvregs_so
          hfs_so (htr_so.trans hacp_0m.2.1)
          (hsys_so.2.1.trans hacp_0m.2.2.1) (hsys_so.2.2.brkStart_eq.trans hacp_0m.2.2.2.2.1)
          fun sf _hpc_f _hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent
              horc_f hsym_f => ?_)
      · rw [hcore_eq_mo, muslErrnoAddr_eq_stdErrnoAddr, htp_so]
        let KeepOk0 : SepProp :=
          memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ vecHeader x.ret v0 v1 v2 ∗
            (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ S.core lim st so
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hstk_back (sepConj_mono_left (Q := KeepOk0) hcstr_back))
            (by dsimp only [KeepOk0]; sep_entail))
        dsimp only [KeepOk0]; sep_entail
      · have hacp_f : AllocCallPreserved s0 sf :=
          ⟨hfs_f, htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
        refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
        rw [memcpySrc_eq_bytesAt x.ro x.pathA x.path] at hm_out
        rw [pure_sepConj_of_true ⟨hacp_f, hfs_f⟩]
        exact Satisfies.mono
          (sepConj_mono_left (Entails.trans (sepConj_mono_left hent) (by sep_entail))) hm_out


end

theorem subroutine_ok_strip_withReadsCodeLoaded {α : Type}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hCode : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m)
    (h : subroutine_ok P entry (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' : s0.mem ⊨ (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere]
    rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCode s0.mem hLP, hpre⟩
  exact subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

theorem subroutine_ok_readFileAnyBudgetCond_withReadsCodeLoaded_of_strong
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readFileAnyStrongBudgetCondSpec A lim stk))) :
    subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readFileAnyBudgetCondSpec A lim stk)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
      readFileAnyBudgetCondSpec] at hpost ⊢
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left
        (Entails.pure_mono fun ⟨hacp, hfs⟩ => ⟨hacp.2.1, hfs⟩)))
      hpost
  · exact Or.inr hrest

theorem subroutine_ok_readFileBudgetCond_withReadsCodeLoaded_of_strong
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readFileAnyStrongBudgetCondSpec A lim stk))) :
    subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readFileBudgetCondSpec A lim stk)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  let y : ReadFileCall × M.σ := (⟨x.pathA, false, x.path, x.ret⟩, st)
  have hpreAny :
      s0.mem ⊨ (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
        (readFileAnyStrongBudgetCondSpec A lim stk)).pre y s0 ∗ R := by
    have hEnt :
        (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl (readFileBudgetCondSpec A lim stk)).pre
            (x, st) s0 ∗ R ⊢
          (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl
            (readFileAnyStrongBudgetCondSpec A lim stk)).pre y s0 ∗ R := by
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y]
      rw [bytesAt_false]
      exact sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
        (Entails.pure_mono fun ⟨hx0, hx1, hx8, hlt32, hwrok, hallocFd⟩ =>
          ⟨hx0, hx1, hx8, hlt32, hwrok.1, hallocFd⟩)))
    exact Satisfies.mono hEnt hpre
  refine subroutine_ok.mono_outcome h y R s0 hpc hrun hpreAny hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
      readFileBudgetCondSpec, y] at hpost ⊢
    rwa [bytesAt_false] at hpost
  · exact Or.inr (Or.inl ⟨hp,
      by simpa only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y] using hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc,
      by simpa only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y] using hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho,
      by simpa only [MultiPlacedLib.withCodeLoadedWhere, readFileAnyStrongBudgetCondSpec,
        readFileAnyBudgetCondSpec, readFileBudgetCondSpec, y] using hoom⟩))

theorem cliIoReadFileAnyBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl (readFileAnyBudgetCondSpec A lim stk)) :=
  subroutine_ok_readFileAnyBudgetCond_withReadsCodeLoaded_of_strong
    (cliIoReadFileAnyStrongBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

theorem cliIoReadFileBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl (readFileBudgetCondSpec A lim stk)) :=
  subroutine_ok_readFileBudgetCond_withReadsCodeLoaded_of_strong
    (cliIoReadFileAnyStrongBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

theorem cliIoReadFileAnyBudgetCond_ok_of_errnoSplit_of_readsCodeLoaded
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileAnyBudgetCondSpec A lim stk) :=
  subroutine_ok_strip_withReadsCodeLoaded hCode
    (cliIoReadFileAnyBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)

theorem cliIoReadFileBudgetCond_ok_of_errnoSplit_of_readsCodeLoaded
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileBudgetCondSpec A lim stk) :=
  subroutine_ok_strip_withReadsCodeLoaded hCode
    (cliIoReadFileBudgetCond_withReadsCodeLoaded_ok_of_errnoSplit S lim hpl hstk hsvc hext_os
      hext3 hext4 hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc
      hEnf)


/-- Direct `RustCliAllocBudgetEntries` bundle wrapper for `readFileAnyBudgetCondSpec` at any
    `PoolErrnoSplit A tp brkStart` (covering `mallocngPoolErrnoSplitAt`, `mallocngPoolErrnoSplit`,
    `mallocngHookPoolErrnoSplit`, `finePoolErrnoSplit`, and `fineHookPoolErrnoSplit`). -/
theorem cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (hAlloc : RustCliAllocBudgetEntriesBase M A P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym })
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileAnyBudgetCondSpec A lim stk) :=
  cliIoReadFileAnyBudgetCond_ok_of_errnoSplit_of_readsCodeLoaded S lim hpl hCode hstk hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim
    (hAlloc.alloc lim) (hAlloc.realloc lim) (hAlloc.dealloc lim) hEnf

/-- Direct `RustCliAllocBudgetEntries` bundle wrapper for `readFileBudgetCondSpec` (`ro = false`)
    at any `PoolErrnoSplit A tp brkStart`. -/
theorem cliIoReadFileBudgetCond_ok_of_entries_of_readsCodeLoaded
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → CliIoReadsCodeLoaded mpl m)
    (hstk : 8432 + allocHookStack ≤ stk := by decide)
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.rustAllocShimVmSpec)
    (hAlloc : RustCliAllocBudgetEntriesBase M A P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym })
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (readFileBudgetCondSpec A lim stk) :=
  cliIoReadFileBudgetCond_ok_of_errnoSplit_of_readsCodeLoaded S lim hpl hCode hstk hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim
    (hAlloc.alloc lim) (hAlloc.realloc lim) (hAlloc.dealloc lim) hEnf


end

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
