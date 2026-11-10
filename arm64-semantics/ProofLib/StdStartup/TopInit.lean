/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.MuslStage1
public import ProofLib.StdStartup.MuslTls
public import ProofLib.StdStartup.StdDetect
public import ProofLib.StdStartup.LangStartPre
public import ProofLib.StdStartup.CleanupAndExit
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
public import ProofLib.MallocngIface

/-!
# `StdStartup` Code Bundle, `userMain` Entry State, and `mallocng` Initialization

Bundles the instruction and `WordTree` checks for `StdStartup` (`StdStartupCode`,
`checkStdStartupCode`), extracts alignment and bounds facts from `MatchesImage`
(`LayoutImageFacts`), and defines the `userMain` entry state, precondition, cleanup frame,
and `stdInitMallocngHeap`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection StdBinaryLayout

/-! ## Combined `StdStartupCode` bundle and `WordTree` validator -/

/-- Code chunks for stage-1 `musl` startup, static TLS, `std_detect`, and outline atomics. -/
def stdStartupExtraChunks (L : StdBinaryLayout) : List CodeChunk :=
  [ .instrs0 L.startAddr (startInstrs L),
    .instrs0 L.startCAddr (startCInstrs L),
    .instrs0 L.libcStartMainAddr (libcStartMainInstrs L),
    .instrs0 L.initLibcAddr (initLibcInstrs L),
    .words L.dummy1Addr dummy1Words,
    .instrs0 L.staticInitTlsAddr (staticInitTlsInstrs L),
    .instrs0 L.copyTlsAddr (copyTlsInstrs L),
    .instrs0 L.initTpAddr (initTpInstrs L),
    .words L.setThreadAreaAddr setThreadAreaWords,
    .instrs0 L.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs L),
    .instrs0 L.libcStartInitAddr (libcStartInitInstrs L),
    .words L.initFnAddr initFnWords,
    .instrs0 L.doInitAddr (doInitInstrs L),
    .instrs0 L.getauxvalAddr (getauxvalInstrs L),
    .instrs0 L.detectAndInitializeAddr (detectInitFastInstrs L),
    .instrs0 L.initLseAddr (initLseInstrs L),
    .instrs0 L.rustEnableLseAddr (rustEnableLseInstrs L),
    .instrs0 L.cas8RelaxAddr (cas8RelaxInstrs L),
    .instrs0 L.cas4AcqAddr (cas4AcqInstrs L),
    .instrs0 L.cas8AcqAddr (cas8AcqInstrs L),
    .instrs0 L.swp4RelAddr (swp4RelInstrs L) ]

/-- Full instruction, memory-primitive, and syscall configuration for `StdStartup` on `P`. -/
structure StdStartupCode (P : Program) (L : StdBinaryLayout) : Prop where
  no_hooks    : P.NoHooks
  svc_eq      : P.svc = Syscall.standard
  ne_memset   : L.initLibcAddr + 0x28#64 ≠ L.memsetAddr
  ne_tls      : L.initLibcAddr + 0x108#64 ≠ L.staticInitTlsAddr
  ne_stage2   : L.libcStartMainAddr + 0x50#64 ≠ L.libcStartMainStage2Addr
  extra       : CodeChunks P (stdStartupExtraChunks L)
  langStart   : LangStartPreCode P L
  cleanup     : StdCleanupCode P L
  memOps      : StdMemOps P L.memcpyAddr L.memsetAddr
  memOpsNonVm : StdMemOps (P.withSvc nonVmSvc) L.memcpyAddr L.memsetAddr

/-- $O(k \log N)$ boolean validator discharging all instruction/word chunks of `StdStartupCode`. -/
def checkStdStartupCode (L : StdBinaryLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (L.initLibcAddr + 0x28#64 != L.memsetAddr) &&
  (L.initLibcAddr + 0x108#64 != L.staticInitTlsAddr) &&
  (L.libcStartMainAddr + 0x50#64 != L.libcStartMainStage2Addr) &&
  (stdStartupExtraChunks L).all (checkCodeChunk base t) &&
  checkLangStartPreCode L base t &&
  checkCleanupCode L base t

private theorem codeChunks_of_all_startup {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, codeChunks_of_all_startup hc h.2⟩

/-- Construct `StdStartupCode P L` from `checkStdStartupCode L P.base t = true` and `StdMemOps`. -/
theorem stdStartupCode_of_wordTree {P : Program} {L : StdBinaryLayout} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hmem : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hmemNonVm : StdMemOps (P.withSvc nonVmSvc) L.memcpyAddr L.memsetAddr)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkStdStartupCode L P.base t = true) : StdStartupCode P L := by
  have hno_hooks : P.NoHooks := Program.NoHooks.of_eq_none
    (funext fun s => Option.isNone_iff_eq_none.mp (hext s))
    (funext fun s => Option.isNone_iff_eq_none.mp (hovr s))
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkStdStartupCode at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  rcases hok with ⟨⟨⟨⟨⟨hne1, hne2⟩, hne3⟩, hextra⟩, hlang⟩, hclean⟩
  exact ⟨hno_hooks, hsvc, hne1, hne2, hne3, codeChunks_of_all_startup hc hextra,
    langStartPreCode_of_wordTree n hcode hwf hsvc hstubs hsyms hext hovr hlang,
    stdCleanupCode_of_wordTree n hcode hwf hstubs hsyms hext hovr hclean, hmem, hmemNonVm⟩

/-! ## `MatchesImage` alignment and bounds extraction -/

private theorem isAligned_w32_of_mod4 {a : BitVec 64} (h : a.toNat % 4 = 0) :
    MemWidth.isAligned .W32 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 3 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; exact h

private theorem isAligned_x64_of_mod8 {a : BitVec 64} (h : a.toNat % 8 = 0) :
    MemWidth.isAligned .X64 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 7 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 3]; exact h

/-- Alignment, non-null, and table-bounds facts derived from `L.MatchesImage img = true`. -/
structure LayoutImageFacts (L : StdBinaryLayout) : Prop where
  checkPhdr      : L.checkPhdrTable = true
  phdr_end       : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64
  builtinTls_al  : L.builtinTlsAddr.toNat % 8 = 0
  mainTls_nz     : L.mainTlsAddr ≠ 0#64
  initArray_bnd  : L.initArrayAddr.toNat + 16 < 2 ^ 64
  finiArray_bnd  : L.finiArrayAddr.toNat + 8 < 2 ^ 64
  al_tid         : MemWidth.isAligned .X64 L.threadIdCounterAddr = true
  al_clean       : MemWidth.isAligned .W32 L.cleanupOnceAddr = true
  al_outOnce     : MemWidth.isAligned .W32 (L.stdoutGlobalAddr + 0x38#64) = true
  al_exiting     : MemWidth.isAligned .X64 L.exitingThreadIdAddr = true
  al_got         : MemWidth.isAligned .X64 L.gotAddr = true
  al_fini        : MemWidth.isAligned .X64 L.finiArrayAddr = true
  al_ofl         : MemWidth.isAligned .X64 L.oflHeadAddr = true
  al_stdin       : MemWidth.isAligned .X64 L.stdinUsedAddr = true
  al_stdout      : MemWidth.isAligned .X64 L.stdoutUsedAddr = true
  al_stderrUsed  : MemWidth.isAligned .X64 L.stderrUsedAddr = true
  al_stderrFile  : MemWidth.isAligned .X64 L.stderrFileAddr = true
  stderrFile_nz  : L.stderrFileAddr ≠ 0#64
  tp_bounds      : 0xa4 ≤ (L.builtinTlsAddr + 0xc8#64).toNat ∧
                     (L.builtinTlsAddr + 0xc8#64).toNat ≤ 2 ^ 48

theorem extractLayoutImageFacts {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (hmatch : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0) :
    LayoutImageFacts L := by
  obtain ⟨hwf, _, _, _, _, _, phdrSeg, _, _, rwSeg, hphdrSeg, _, _, hrwSeg,
    _, _, _, hphdr, hphdrSlice, _, hrwChk⟩ := MatchesImage.segments hmatch
  have ⟨_, _, hphdr_hi⟩ := MatchesImage.holdsBytes_ro_slice hmatch hload (Or.inr hphdrSeg) hphdrSlice
  have hplen : L.phdrBytes.length = L.phnum * 56 := by
    unfold StdBinaryLayout.checkPhdrTable at hphdr
    simp only [Bool.and_eq_true, beq_iff_eq] at hphdr; exact hphdr.1.1.1.1.1.2
  have ⟨_, _, _, _, hseg_bnds⟩ := wellFormed_segments_bounds hwf
  have ⟨hrw_lo, _, _⟩ := hseg_bnds rwSeg (List.mem_of_getElem? hrwSeg)
  unfold StdBinaryLayout.checkRwSegment at hrwChk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hrwChk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hbtls⟩, _⟩, _⟩, _⟩, hstderr_al⟩, _⟩, hfini_al⟩, hgot_al⟩,
    hstderr_lo⟩, _⟩, hall_rw⟩, _⟩, _⟩ := hrwChk
  have atomProps : ∀ {x : RwAtom}, x ∈ L.allRwAtoms →
      x.addr.toNat % x.align = 0 ∧ Obj.pageSize ≤ x.addr.toNat ∧
        x.addr.toNat + x.rawBytes.length ≤ 2 ^ 48 := fun hx => by
    have ⟨hal, hsl⟩ := hall_rw _ hx
    have ⟨_, hlo, hhi⟩ := MatchesImage.holdsBytes_rw_slice hmatch hload hrwSeg hsl
    exact ⟨hal, hlo, hhi⟩
  have memStd : ∀ {x : RwAtom}, x ∈ L.stdRwAtoms → x ∈ L.allRwAtoms :=
    fun hx => List.mem_append_left _ hx
  have h_init0 := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.initFiniAtoms] :
    RwAtom.u64 L.initArrayAddr L.initLseAddr ∈ L.stdRwAtoms))
  have h_fini0 := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.initFiniAtoms] :
    RwAtom.u64 L.finiArrayAddr L.doFiniAddr ∈ L.stdRwAtoms))
  have h_mtls := atomProps (memStd (by
    simp only [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.tlsAtoms,
      List.mem_append, List.mem_cons, true_or, or_true] :
    RwAtom.u64 L.mainTlsAddr 0#64 ∈ L.stdRwAtoms))
  have h_clean := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.dataNoStderrAtoms] :
    RwAtom.u32 L.cleanupOnceAddr 3#32 ∈ L.stdRwAtoms))
  have h_outOnce := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.dataNoStderrAtoms] :
    RwAtom.u32 (L.stdoutGlobalAddr + 0x38#64) 3#32 ∈ L.stdRwAtoms))
  have h_stderrU := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.dataNoStderrAtoms] :
    RwAtom.u64 L.stderrUsedAddr L.stderrFileAddr ∈ L.stdRwAtoms))
  have h_tid := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.bssAtoms] :
    RwAtom.u64 L.threadIdCounterAddr 0#64 ∈ L.stdRwAtoms))
  have h_exit := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.bssAtoms] :
    RwAtom.u64 L.exitingThreadIdAddr 0#64 ∈ L.stdRwAtoms))
  have h_stdin := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.bssAtoms] :
    RwAtom.u64 L.stdinUsedAddr 0#64 ∈ L.stdRwAtoms))
  have h_ofl := atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.bssAtoms] :
    RwAtom.u64 L.oflHeadAddr 0#64 ∈ L.stdRwAtoms))
  have h_stdout_al : L.stdoutUsedAddr.toNat % 8 = 0 := by
    by_cases heq : L.stdoutUsedAddr == L.stdinUsedAddr
    · rw [beq_iff_eq.mp heq]; exact h_stdin.1
    · exact (atomProps (memStd (by simp [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.bssAtoms, heq] :
        RwAtom.u64 L.stdoutUsedAddr 0#64 ∈ L.stdRwAtoms))).1
  have h_btls := atomProps (memStd (by
    simp only [StdBinaryLayout.stdRwAtoms, StdBinaryLayout.tlsAtoms,
      List.mem_append, List.mem_cons, true_or, or_true] :
    RwAtom.bytes L.builtinTlsAddr (List.replicate 0x150 0#8) ∈ L.stdRwAtoms))
  have dPage : Obj.pageSize = 4096 := rfl
  refine ⟨hphdr, by omega, hbtls, ?_, ?_, ?_,
    isAligned_x64_of_mod8 h_tid.1, isAligned_w32_of_mod4 h_clean.1,
    isAligned_w32_of_mod4 h_outOnce.1, isAligned_x64_of_mod8 h_exit.1,
    isAligned_x64_of_mod8 hgot_al, isAligned_x64_of_mod8 hfini_al,
    isAligned_x64_of_mod8 h_ofl.1, isAligned_x64_of_mod8 h_stdin.1,
    isAligned_x64_of_mod8 h_stdout_al, isAligned_x64_of_mod8 h_stderrU.1,
    isAligned_x64_of_mod8 hstderr_al, ?_, ?_⟩
  · intro hz; dsimp only [RwAtom.addr] at h_mtls; rw [hz, dPage] at h_mtls; simp at h_mtls
  · dsimp only [RwAtom.addr, RwAtom.rawBytes] at h_init0; rw [unpack64_length] at h_init0; omega
  · dsimp only [RwAtom.addr, RwAtom.rawBytes] at h_fini0; rw [unpack64_length] at h_fini0; omega
  · intro hz; rw [hz] at hstderr_lo; simp at hstderr_lo; omega
  · dsimp only [RwAtom.addr, RwAtom.rawBytes] at h_btls
    rw [List.length_replicate, dPage] at h_btls
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩

/-! ## `userMain` entry invariant, precondition bundle, and `mallocng` initialization -/

/-- Machine-state properties established at entry to `L.userMainAddr`. -/
structure StdUserMainState (P : Program) (L : StdBinaryLayout) (img : ElfImage)
    (inputs : ProcessInputs) (s0 s_main : State) : Prop where
  initInfo        : InitialStackInfo img inputs s0
  pc_eq           : s_main.pc = L.userMainAddr
  status_eq       : s_main.status = .Running
  sp_eq           : s_main.sp = (StackLayout.of img inputs).sp0 - 0xa0#64
  spAligned_eq    : s_main.spAligned = true
  sp_headroom     : 261984 ≤ s_main.sp.toNat
  lr_eq           : s_main.readReg64 .lr = L.beginShortBacktraceAddr + 0x0c#64
  tpidr_eq        : s_main.tpidrEl0 = L.builtinTlsAddr + 0xc8#64
  fs_eq           : s_main.fs = initFsState inputs
  trace_eq        : s_main.trace = []
  brk_eq          : s_main.brk = L.brkStart
  brkStart_eq     : s_main.brkStart = L.brkStart
  physMemAvail_eq : s_main.physMemAvail = inputs.init.physMemAvail
  perm_eq         : ∀ a, s_main.mem.perm a = s0.mem.perm a
  codeLoaded      : P.CodeLoaded s_main.mem

/-- Separation-logic resources handed to `userMain` at `s_main` (with `261984` B of stack scratch,
    initialized TLS `errno` and `ThreadId = 1`, frozen `have_lse_atomics`, initialized `libc`
    `need_locks`/`auxv`/`page_size` fields, initialized `ARGC`/`ARGV`/`PAGE_SIZE`/`environ`,
    initial stack tables/strings, and binary-specific `StdExtraRo` / `StdExtraRw` globals). -/
def StdUserMainPre (L : StdBinaryLayout) (img : ElfImage) (inputs : ProcessInputs)
    (s_main : State) : SepProp :=
  let sl := StackLayout.of img inputs
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  stackAt s_main.sp 261984 ∗
  ((s_main.tpidrEl0 - 0xa4#64) ↦₃₂ 0#32) ∗
  ((s_main.tpidrEl0 + 0x10#64) ↦₆₄ 1#64) ∗
  (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
  ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
  ((L.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
  ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
  (if L.hasArgcGlobal then L.argcGlobalAddr ↦₆₄ BitVec.ofNat 64 inputs.argv.length else emp) ∗
  (L.argvGlobalAddr ↦₆₄ sl.argvTableAddr) ∗
  (L.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
  (L.environAddr ↦₆₄ sl.envpTableAddr) ∗
  (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
  (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
  (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
  (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
  (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
  (sl.platformAddr ↦ᵣ platformCStringBytes) ∗
  (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗
  (L.emptyCStrAddr ↦₈ᵣ 0#8) ∗
  (L.devNullStdAddr ↦ᵣ devNullBytes) ∗
  (L.devNullLibcAddr ↦ᵣ devNullBytes) ∗
  StdExtraRo L ∗
  StdExtraRw L

/-- `StdMuslExitGlobals` minus `libc.need_locks` (`(L.libcAddr + 3#64) ↦₈ 0#8`), which stays
    available to `userMain` (and any heap allocator) and is frozen at `userMain` return. -/
abbrev StdMuslExitGlobalsNoNeedLocks (L : StdBinaryLayout) (finalized : BitVec 8) : SepProp :=
  (L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗
  ((L.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x60#64) ↦₆₄ (L.finiArrayAddr + 0x08#64)) ∗
  ((L.gotAddr + 0x68#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ finalized) ∗
  (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
  (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗
  (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L

/-- Post-`main` cleanup frame held aside across `userMain` for `cMain_post_*_wp` and `muslExit_to_svc_wp`. -/
def StdPostMainCleanup (L : StdBinaryLayout) (haveLse : BitVec 8) (sp_cmain saved_fp : BitVec 64) : SepProp :=
  let ret_cmain := if L.hasArgcGlobal then L.cMainAddr + 0x208#64 else L.cMainAddr + 0x1f4#64
  ((sp_cmain - 0x10#64) ↦₆₄ (sp_cmain + 0x20#64)) ∗
  ((sp_cmain - 0x08#64) ↦₆₄ ret_cmain) ∗
  stackAt (sp_cmain + 0x20#64) 32 ∗
  ((sp_cmain + 0x20#64) ↦₆₄ saved_fp) ∗
  ((sp_cmain + 0x28#64) ↦₆₄ (L.libcStartMainStage2Addr + 0x38#64)) ∗
  stackAt (sp_cmain + 0x60#64) 48 ∗
  StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗
  (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗
  StdMuslExitGlobalsNoNeedLocks L 0#8

/-- Duplicate a read-only slice `(a, bs) ∈ xs` out of `roSliceListSep xs`. -/
theorem roSliceListSep_dup_mem {a : BitVec 64} {bs : List (BitVec 8)} :
    ∀ {xs : List (BitVec 64 × List (BitVec 8))},
      (a, bs) ∈ xs → roSliceListSep xs ⊢ (a ↦ᵣ bs) ∗ roSliceListSep xs
  | [], h => nomatch h
  | [(a', bs')], h => by
    simp only [List.mem_singleton, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
    rw [roSliceListSep, pointsToBytesRO_dup]; exact Entails.refl _
  | (a1, bs1) :: x2 :: xs, h => by
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq
      change ((a ↦ᵣ bs) ∗ roSliceListSep (x2 :: xs)) ⊢
        (a ↦ᵣ bs) ∗ ((a ↦ᵣ bs) ∗ roSliceListSep (x2 :: xs))
      rw [← sepConj_assoc, pointsToBytesRO_dup]; exact Entails.refl _
    · change ((a1 ↦ᵣ bs1) ∗ roSliceListSep (x2 :: xs)) ⊢
        (a ↦ᵣ bs) ∗ ((a1 ↦ᵣ bs1) ∗ roSliceListSep (x2 :: xs))
      exact Entails.trans (sepConj_mono_right (roSliceListSep_dup_mem hmem)) (by sep_entail)

/-- Initialize an empty `mallocng` heap (`M.Heap γ 0 0 s_main`) at `userMain` entry from
    `MallocngInitialBss addrs` and the startup resources in `StdUserMainPre`, returning the
    thread-local `errno` slot, `StdExtraRo L`, the lower 8 bytes of `AT_RANDOM`, and frame `R`. -/
theorem stdInitMallocngHeap {P : Program} {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 s_main : State} {addrs : MallocngAddrs}
    {lim : MallocngLimits} (M : MallocngCoreIface P addrs lim)
    {e0 : BitVec 32} {R : SepProp}
    (hmatch : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0)
    (hvalid : inputs.Valid)
    (hs : StdUserMainState P L img inputs s0 s_main)
    (hphys : lim.CorePhysMem ≤ inputs.init.physMemAvail)
    (hro_mem : (addrs.roTablesAddr, mallocngRoTablesBytes) ∈ L.extraRoSlices)
    (hbrkBase : addrs.brkBase = L.brkStart := by rfl)
    (hneed : addrs.libcNeedLocksAddr = L.libcAddr + 3#64 := by rfl)
    (hauxv : addrs.libcAuxvAddr = L.libcAddr + 0x08#64 := by rfl)
    (hpage : addrs.libcPageSizeAddr = L.libcAddr + 0x30#64 := by rfl)
    (hm : s_main.mem ⊨ MallocngInitialBss addrs ∗ StdExtraRo L ∗
      ((s_main.tpidrEl0 - 0xa4#64) ↦₃₂ e0) ∗
      ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ (StackLayout.of img inputs).auxvTableAddr) ∗
      ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
      ((StackLayout.of img inputs).auxvTableAddr ↦ₛ
        encodeAuxvBytes (StackLayout.of img inputs).auxvEntries) ∗
      ((StackLayout.of img inputs).randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗ R) :
    ∃ (γ : GhostName) (e1 : BitVec 32),
      s_main.mem ⊨ M.Heap γ 0 0 s_main ∗
        ((s_main.tpidrEl0 - 0xa4#64) ↦₃₂ e1) ∗
        StdExtraRo L ∗
        ((StackLayout.of img inputs).randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) ∗ R := by
  let sl := StackLayout.of img inputs
  have lf := extractLayoutImageFacts hmatch hload
  have hbrkMin := MatchesImage.brkStart_ge_mmapMin hmatch
  obtain ⟨hwf, _, _, _, hbrk_eq, hbrk1G, _, _, roSeg, _, _, _, hroSeg, _, _, _, _, _, _, hroChk, _⟩ :=
    MatchesImage.segments hmatch
  unfold StdBinaryLayout.checkRoSegment at hroChk
  simp only [Bool.and_eq_true, List.all_eq_true] at hroChk
  have hro_slice := hroChk.2 (addrs.roTablesAddr, mallocngRoTablesBytes) hro_mem
  have ⟨hro_holds, _, _⟩ := MatchesImage.holdsBytes_ro_slice hmatch hload (Or.inl hroSeg) hro_slice
  have hro_len : mallocngRoTablesBytes.length = 200 := by decide +kernel
  have hfrozen : ∀ i < 200, s_main.mem.Frozen (addrs.roTablesAddr + BitVec.ofNat 64 i) := by
    intro i hi
    have hp := (hro_holds i (hro_len ▸ hi)).2
    simp only [Memory.Frozen, hs.perm_eq, hp]; rfl
  have hsize_le : inputs.init.stackSize ≤ inputs.init.stackTop.toNat := by
    have hfl := hs.initInfo.stackBase_floor; unfold STACK_BASE_MIN at hfl; omega
  have hstackCeil : inputs.init.stackSize ≤ 128 * 2 ^ 20 := by
    have hle := hvalid.stackSize_le; unfold STACK_SIZE_MAX at hle; omega
  have hmemWf0 := hs.initInfo.mallocngInitialMemWf (hbrkBase.trans hbrk_eq.symm)
    (hbrk_eq ▸ hbrkMin) (hbrk_eq ▸ hbrk1G.2) hsize_le hstackCeil hwf
  have hmemWf := MallocngInitialMemWf.transport hmemWf0
    (hs.brk_eq.trans (hbrk_eq ▸ hs.initInfo.s0_brk.symm))
    (hs.brkStart_eq.trans (hbrk_eq ▸ hs.initInfo.s0_brkStart.symm))
    (fun a ha => by rwa [hs.perm_eq a] at ha)
  have hrand16 := hvalid.auxv.random16
  have hsp16 := hs.initInfo.sp0_align16
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hs.initInfo.stackTop_align.2.2
  have han := hs.initInfo.addrs_nat; dsimp only at han
  obtain ⟨_, _, haux_nat, haux_le, hplat_nat, hargvB_nat, _, _, hupper_top⟩ := han
  obtain ⟨prePairs, sufPairs, hsplit_eq, _, hps_le, hpre_no, hsuf_no⟩ :=
    mkAuxvEntries_split_random img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  dsimp only [sl] at hsplit_eq ⊢
  have hauxE_split : (StackLayout.of img inputs).auxvEntries =
      prePairs ++ [(AuxvTag.random, (StackLayout.of img inputs).randomAddr)] ++ sufPairs :=
    hs.initInfo.auxvEntries_eq.trans hsplit_eq
  have hauxE_len : (StackLayout.of img inputs).auxvEntries.length =
      prePairs.length + sufPairs.length + 1 := by
    rw [hauxE_split]; simp; omega
  rw [hauxE_len] at haux_le
  have htp_bnds : 0xa4 ≤ s_main.tpidrEl0.toNat ∧ s_main.tpidrEl0.toNat ≤ 2 ^ 48 := by
    rw [hs.tpidr_eq]; exact lf.tp_bounds
  have hsh_pure :
      (inputs.init.auxv.randomBytes.drop 8).length = 8 ∧
      0xa4 ≤ s_main.tpidrEl0.toNat ∧
      s_main.tpidrEl0.toNat ≤ 2 ^ 48 ∧
      prePairs.length + sufPairs.length ≤ 64 ∧
      (StackLayout.of img inputs).auxvTableAddr.toNat % 8 = 0 ∧
      (StackLayout.of img inputs).auxvTableAddr.toNat +
        16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧
      (StackLayout.of img inputs).randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
      (∀ e ∈ prePairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) ∧
      (∀ e ∈ sufPairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) :=
    ⟨by simp [hrand16], htp_bnds.1, htp_bnds.2, hps_le, by omega,
     by omega, by omega, hpre_no, hsuf_no⟩
  have hdup_ro : StdExtraRo L ⊢ (addrs.roTablesAddr ↦ᵣ mallocngRoTablesBytes) ∗ StdExtraRo L :=
    roSliceListSep_dup_mem hro_mem
  have hm_split := hm
  rw [split_random_hi8 (StackLayout.of img inputs).randomAddr hrand16, hauxE_split] at hm_split
  have hm_init : s_main.mem ⊨ MallocngInitialBss addrs ∗
      MallocngStartupInputs addrs (StackLayout.of img inputs).auxvTableAddr
        (StackLayout.of img inputs).randomAddr prePairs sufPairs
        (inputs.init.auxv.randomBytes.drop 8) e0 s_main ∗
      (StdExtraRo L ∗
        ((StackLayout.of img inputs).randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) ∗ R) := by
    refine Satisfies.mono ?_ hm_split
    unfold MallocngStartupInputs muslErrnoAddr
    rw [pure_sepConj_of_true hsh_pure, hneed, hauxv, hpage]
    refine sepConj_mono_right ?_
    refine Entails.trans (sepConj_mono_left hdup_ro) (by sep_entail)
  obtain ⟨γ, e1, hγ⟩ := M.init_heap hs.codeLoaded hfrozen hmemWf
    (hs.physMemAvail_eq.symm ▸ hphys) hm_init
  exact ⟨γ, e1, by simpa [muslErrnoAddr, sepConj_assoc] using hγ⟩

end ProofLib.StdStartup
