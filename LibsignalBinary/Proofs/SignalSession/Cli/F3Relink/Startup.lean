/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
public import ProofLib.StdStartup.TopInit
public import ProofLib.StdStartup.StartupCompose
public import ProofLib.StdStartup.CleanupAndExit
public import VerifiedLibraries.Musl.Proofs.MemOps
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.InitStack
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.HarnessSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero

/-!
# Re-Linked `musl` Startup, Exit, and `fineCostModel` Heap Initialization

Layout-parametric whole-process `musl` v1.2.5 startup (`_start` → `__libc_start_main` →
`__init_libc` → `static_init_tls` `0/0/0/0` → `__init_tp` → `__libc_start_main_stage2` →
`RUST_LSE_INIT` → `cMainAddr`) and `exit` (`exit` → `__libc_exit_fini` → `__stdio_exit_needed` →
`_Exit` `SYS_exit_group`) harnesses, `WordTree` startup code validation, and `fineCostModel` /
`mallocng` heap initialization at `cMainAddr`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Mallocng (
  MallocngAuxvAt MallocngBrkStartWf MallocngRoTablesAt MallocngRuntime
  MallocngStartupResources mallocngAddrsOfPlacement
)
open VerifiedLibraries.Musl (memcpySymWords memsetWordsSym stdMemOps_of_muslWords)
open VerifiedLibraries.RustStd (
  StdErrnoCell mallocngRustCliAlloc mallocngRustCliPool_of_init_resources
)
open CryptoVerification.SignalSession (
  Inputs cliProcessInputs processInputs PrintableAsciiArg ArgvFitsInitialStack LoadablePath
)
open CryptoVerification.SignalSession.Cli (
  cliInputs CliInputsOk InputsLoadable ElfStaticOk
)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.InitStack (
  cliStackSize cliStrs loadState_cli_layout sp0 stackBase toNat_sp0
)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (
  CliElfMallocngLayout StartupVmPreserved cliElf_fineBudgetPool_of_init
  fineCostModel fineRustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.HarnessSpec (
  MuslHarnessNeedLocksN
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero (
  F3RoConstants F3DataGlobals F3BssGlobals F3InitGlobals F3TlsState F3LayoutImageFacts
  f3DataNoStderrAtoms f3BssAtoms f3MatchesImage f3MatchesImage_segments f3MatchesImage_codeLoaded
  f3MatchesImage_satisfies_roConstants f3MatchesImage_supportedOn_initGlobals_below_brk
  extractF3LayoutImageFacts f3SetTidOnlySvc f3StaticInitTlsSpec f3StaticInitTls_setTidOnly_ok
)

/-! ## `F3StartupCode` Bundle and `WordTree` Validator -/

/-- The 17 `seg[5]` startup, static-TLS, and `RUST_LSE_INIT` instruction/word chunks for F3
    (excluding unused `std::rt` outline atomics and `lang_start_internal` / `cleanup`). -/
def f3StartupExtraChunks (L : StdBinaryLayout) : List CodeChunk :=
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
    .instrs0 L.rustEnableLseAddr (rustEnableLseInstrs L) ]

/-- Full `seg[5]` code, `musl` exit, and `memcpy`/`memset` bundle for F3 startup/exit. -/
structure F3StartupCode (P : Program) (L : StdBinaryLayout) : Prop where
  no_hooks     : P.NoHooks
  svc_eq       : P.svc = Syscall.standard
  ne_memset    : L.initLibcAddr + 40#64 ≠ L.memsetAddr
  ne_tls       : L.initLibcAddr + 264#64 ≠ L.staticInitTlsAddr
  ne_stage2    : L.libcStartMainAddr + 80#64 ≠ L.libcStartMainStage2Addr
  extra        : CodeChunks P (f3StartupExtraChunks L)
  muslExit     : MuslExitCode P L
  memOps       : StdMemOps P L.memcpyAddr L.memsetAddr
  memOpsSetTid : StdMemOps (P.withSvc f3SetTidOnlySvc) L.memcpyAddr L.memsetAddr

/-- $O(k \log N)$ boolean validator discharging all chunks and `StdMemOps` of `F3StartupCode`. -/
def checkF3StartupCode (L : StdBinaryLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (L.initLibcAddr + 40#64 != L.memsetAddr) &&
  (L.initLibcAddr + 264#64 != L.staticInitTlsAddr) &&
  (L.libcStartMainAddr + 80#64 != L.libcStartMainStage2Addr) &&
  (f3StartupExtraChunks L).all (checkCodeChunk base t) &&
  (muslExitChunks L).all (checkCodeChunk base t) &&
  checkCodeChunk base t (.words L.memcpyAddr memcpySymWords) &&
  checkCodeChunk base t (.words L.memsetAddr memsetWordsSym)

private theorem codeChunks_of_all_f3 {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, codeChunks_of_all_f3 hc h.2⟩

private theorem unpack_f3_extra_chunks {P : Program} {L : StdBinaryLayout}
    (h : CodeChunks P (f3StartupExtraChunks L)) :
    hasInstrs P L.startAddr (startInstrs L) ∧
    hasInstrs P L.startCAddr (startCInstrs L) ∧
    hasInstrs P L.libcStartMainAddr (libcStartMainInstrs L) ∧
    hasInstrs P L.initLibcAddr (initLibcInstrs L) ∧
    P.hasWords L.dummy1Addr dummy1Words ∧
    hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L) ∧
    hasInstrs P L.copyTlsAddr (copyTlsInstrs L) ∧
    hasInstrs P L.initTpAddr (initTpInstrs L) ∧
    P.hasWords L.setThreadAreaAddr setThreadAreaWords ∧
    hasInstrs P L.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs L) ∧
    hasInstrs P L.libcStartInitAddr (libcStartInitInstrs L) ∧
    P.hasWords L.initFnAddr initFnWords ∧
    hasInstrs P L.doInitAddr (doInitInstrs L) ∧
    hasInstrs P L.getauxvalAddr (getauxvalInstrs L) ∧
    hasInstrs P L.detectAndInitializeAddr (detectInitFastInstrs L) ∧
    hasInstrs P L.initLseAddr (initLseInstrs L) ∧
    hasInstrs P L.rustEnableLseAddr (rustEnableLseInstrs L) := by
  dsimp only [f3StartupExtraChunks, CodeChunks, CodeChunk.holds] at h
  exact h

private theorem hasInstrs_withSvc_f3 {P : Program} {svc : State → State}
    {base : BitVec 64} {is : List Instr} (h : hasInstrs P base is) :
    hasInstrs (P.withSvc svc) base is :=
  h

private theorem hasWords_withSvc_f3 {P : Program} {svc : State → State}
    {addr : BitVec 64} {ws : List (BitVec 32)} (h : P.hasWords addr ws) :
    (P.withSvc svc).hasWords addr ws :=
  h

private theorem hasCode_withSvc_f3 {P : Program} {svc : State → State}
    {addr : BitVec 64} {ws : List (BitVec 32)} (h : P.hasCode addr ws) :
    (P.withSvc svc).hasCode addr ws :=
  h

theorem f3StartupCode_of_wordTree {P : Program} {L : StdBinaryLayout} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkF3StartupCode L P.base t = true) : F3StartupCode P L := by
  have hno_hooks : P.NoHooks := Program.NoHooks.of_eq_none
    (funext fun s => Option.isNone_iff_eq_none.mp (hext s))
    (funext fun s => Option.isNone_iff_eq_none.mp (hovr s))
  have hno_ext : ∀ pc, P.externAt? pc = none := hno_hooks
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkF3StartupCode at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨hne1, hne2⟩, hne3⟩, hextra⟩, hexit⟩, hmc⟩, hms⟩
  have hw_mc : P.hasWords L.memcpyAddr memcpySymWords := hc hmc
  have hw_ms : P.hasWords L.memsetAddr memsetWordsSym := hc hms
  exact {
    no_hooks := hno_hooks
    svc_eq := hsvc
    ne_memset := hne1
    ne_tls := hne2
    ne_stage2 := hne3
    extra := codeChunks_of_all_f3 hc hextra
    muslExit := codeChunks_of_all_f3 hc hexit
    memOps := stdMemOps_of_muslWords P L.memcpyAddr L.memsetAddr hno_ext hw_mc hw_ms
    memOpsSetTid := stdMemOps_of_muslWords (P.withSvc f3SetTidOnlySvc) L.memcpyAddr L.memsetAddr
      (fun pc => by rw [externAt?_withSvc]; exact hno_ext pc)
      (hasWords_withSvc_f3 hw_mc) (hasWords_withSvc_f3 hw_ms)
  }

/-! ## `stripS (progKeep P_rx)` and `setFs` Trace Lifting -/

private theorem codeLoaded_withSvc_iff {P : Program} {svc : State → State} {m : Memory} :
    (P.withSvc svc).CodeLoaded m ↔ P.CodeLoaded m := by
  simp [Program.codeLoaded_iff, Program.withSvc]

private theorem strip_codeLoaded_f3 {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    simp only [progKeep, decide_eq_true_eq, hsub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hi
  rw [strip_read8, strip_perm_of_keep hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem holdsBytes_rw_strip (keep : BitVec 64 → Bool) {m : Memory}
    {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : Obj.HoldsBytes m addr bs (fun _ => Perm.rw)) :
    Obj.HoldsBytes (stripExecOutside keep m) addr bs (fun _ => Perm.rw) := by
  intro i hi
  obtain ⟨hr, hp, hlf⟩ := h i hi
  exact ⟨by rw [strip_read8]; exact hr, (strip_perm_props keep m _).2.2.2.mpr hp,
    by rw [strip_isLazyFree]; exact hlf⟩

private theorem initialStackInfo_strip (keep : BitVec 64 → Bool)
    {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : InitialStackInfo img inputs s0) :
    InitialStackInfo img inputs (stripS keep s0) where
  s0_regs := by dsimp [stripS]; exact h.s0_regs
  s0_vregs := by dsimp [stripS]; exact h.s0_vregs
  s0_sp := by dsimp [stripS]; exact h.s0_sp
  s0_pc := by dsimp [stripS]; exact h.s0_pc
  s0_pstate := by dsimp [stripS]; exact h.s0_pstate
  s0_status := by dsimp [stripS]; exact h.s0_status
  s0_tpidrEl0 := by dsimp [stripS]; exact h.s0_tpidrEl0
  s0_brk := by dsimp [stripS]; exact h.s0_brk
  s0_brkStart := by dsimp [stripS]; exact h.s0_brkStart
  s0_fs := by dsimp [stripS]; exact h.s0_fs
  s0_trace := by dsimp [stripS]; exact h.s0_trace
  s0_oracle := by dsimp [stripS]; exact h.s0_oracle
  s0_oracleIdx := by dsimp [stripS]; exact h.s0_oracleIdx
  s0_exclFails := by dsimp [stripS]; exact h.s0_exclFails
  s0_sigActions := by dsimp [stripS]; exact h.s0_sigActions
  s0_sigAltStack := by dsimp [stripS]; exact h.s0_sigAltStack
  s0_physMemAvail := by dsimp [stripS]; exact h.s0_physMemAvail
  sp0_align16 := h.sp0_align16
  random_align16 := h.random_align16
  stackTop_align := h.stackTop_align
  stackBase_floor := h.stackBase_floor
  sp0_headroom := h.sp0_headroom
  argc_bounds := h.argc_bounds
  argvAddrs_eq := h.argvAddrs_eq
  envpAddrs_eq := h.envpAddrs_eq
  upperStr_eq := h.upperStr_eq
  auxvEntries_eq := h.auxvEntries_eq
  addrs_nat := h.addrs_nat
  s0_perm_rw_below_sp0 := fun a h1 h2 => by
    dsimp [stripS, State.setMem]
    exact (strip_perm_props keep s0.mem a).2.2.2.mpr (h.s0_perm_rw_below_sp0 a h1 h2)
  s0_isLazyFree := fun a => by
    dsimp [stripS, State.setMem]; rw [strip_isLazyFree]; exact h.s0_isLazyFree a
  s0_unmapped_heap := fun a h1 h2 => by
    dsimp [stripS, State.setMem]; rw [strip_perm, h.s0_unmapped_heap a h1 h2]; rfl
  s0_mapped_iff := fun a hm => by
    dsimp [stripS, State.setMem] at hm
    change ((stripExecOutside keep s0.mem).perm a).mapped = true at hm
    rw [(strip_perm_props keep s0.mem a).2.2.1] at hm
    exact h.s0_mapped_iff a hm
  holds_argc := holdsBytes_rw_strip keep h.holds_argc
  holds_argv := holdsBytes_rw_strip keep h.holds_argv
  holds_envp := holdsBytes_rw_strip keep h.holds_envp
  holds_auxv := holdsBytes_rw_strip keep h.holds_auxv
  holds_random := holdsBytes_rw_strip keep h.holds_random
  holds_platform := holdsBytes_rw_strip keep h.holds_platform
  holds_upperStr := holdsBytes_rw_strip keep h.holds_upperStr

private theorem evalInst_not_isSvc0 {prog : Program} {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    prog.evalInst inst s = execInst inst s := by
  cases inst with
  | system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm
        subst heq; simp [Instr.isSvc0] at h
      · simp [Program.evalInst, execInst, execInstWithSvc, himm]
    · rfl
  | _ => rfl

/-- Lift `Steps (P_rx.withSvc f3SetTidOnlySvc)` reaching a `.Running` state from
    `stripS (progKeep P_rx) (s1.setFs fs0)` to any `Syscall.standard` `Program` `P` that has no
    hooks inside `progKeep P_rx`, preserving `fs`, `physMemAvail`, and `mem.perm` on `P`. -/
theorem steps_lift_setTidOnly {P_rx P : Program}
    (hNoExtRx : ∀ pc, P_rx.externAt? pc = none)
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep P_rx pc = true → (P.externAt? pc).isNone = true)
    {sa' sf' : State}
    (hsteps : Steps (P_rx.withSvc f3SetTidOnlySvc) sa' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State) (fs0 : FsState),
      sa' = stripS (progKeep P_rx) (s1.setFs fs0) →
      ∃ sf, Steps P s1 sf ∧
        sf' = stripS (progKeep P_rx) (sf.setFs fs0) ∧
        sf.fs = s1.fs ∧
        sf.physMemAvail = s1.physMemAvail ∧
        (∀ a, sf.mem.perm a = s1.mem.perm a) := by
  induction hsteps with
  | refl _ =>
    intro s1 fs0 hs1
    exact ⟨s1, Steps.refl s1, hs1, rfl, rfl, fun _ => rfl⟩
  | @step s1' s2' _ h1 hrest ih =>
    intro s1 fs0 hsa
    have hrun2' : s2'.status = .Running := by
      cases hrest with
      | refl => exact hrun_f
      | step hs2 _ => exact hs2.running_of_step
    cases h1 with
    | halt_unmapped _ _ _ => cases hrun2'
    | extern _ hex _ _ => rw [externAt?_withSvc, hNoExtRx] at hex; cases hex
    | extern_fault _ hex _ => rw [externAt?_withSvc, hNoExtRx] at hex; cases hex
    | @exec inst hrun1' hfm' =>
      have hrun1 : s1.status = .Running := by
        rw [hsa] at hrun1'; dsimp [stripS] at hrun1'; simpa using hrun1'
      have hpc_eq : s1'.pc = s1.pc := by rw [hsa]; rfl
      have hmem_eq : s1'.mem = stripExecOutside (progKeep P_rx) s1.mem := by rw [hsa]; rfl
      have hkeep_and_fm : progKeep P_rx s1.pc = true ∧ P.fetchMem s1.mem s1.pc = some inst := by
        rw [hpc_eq, hmem_eq] at hfm'
        unfold Program.fetchMem at hfm' ⊢
        rw [externAt?_withSvc, hNoExtRx s1.pc] at hfm'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm' ⊢
          split at hfm'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            unfold Memory.canExec at hce'
            rw [Memory.allPerm_iff] at hce'
            have hx0 := hce' 0 (by decide)
            rw [BitVec.add_zero] at hx0
            have hkeep : progKeep P_rx s1.pc = true := (strip_perm_x_imp hx0).2
            have hextP : (P.externAt? s1.pc).isSome = false := by
              rw [Bool.eq_false_iff]; intro hs
              have hn := hHookFree s1.pc hkeep
              cases hq : P.externAt? s1.pc <;> simp_all
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec; rw [Memory.allPerm_iff]
              intro k hk; exact (strip_perm_x_imp (hce' k hk)).1
            have hr32 : (stripExecOutside (progKeep P_rx) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by
              simp [Memory.read32, strip_read8]
            rw [hr32] at hfm'
            refine ⟨hkeep, ?_⟩
            simp only [hextP, Bool.false_eq_true, ↓reduceIte, hce, Bool.not_true]
            exact hfm'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfm'
          contradiction
      let s2 := P.evalInst inst s1
      have hstepP : Step P s1 s2 := Step.exec hrun1 hkeep_and_fm.2
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst_eq : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rename_i isHalt imm
          cases isHalt <;> simp at hsvc0
          exact congrArg (Instr.system false) hsvc0
        subst hinst_eq
        have hx8_eq : s1'.readReg64 .x8 = s1.readReg64 .x8 := by
          rw [hsa]; cases s1; rfl
        by_cases h96 : s1.readReg64 .x8 == 96#64
        · have hnum : s1.readReg64 .x8 = 96#64 := beq_iff_eq.mp h96
          have hnum' : s1'.readReg64 .x8 = 96#64 := hx8_eq.trans hnum
          have hev_tid : ∀ (f : State → State) (st : State),
              f st = execSetTidAddress st → evalSvc f st = execSetTidAddress st := by
            intro f st hf; dsimp only [evalSvc]; rw [hf]
            cases st; rename_i regs vregs pc sp pstate status mem tpidrEl0 brk brkStart fs oracle oracleIdx exclFails exclWillFail trace symtab fpsr sigActions
            cases mem
            simp [execSetTidAddress, State.writeReg64, State.advancePC]
          have hs2'_eq : (P_rx.withSvc f3SetTidOnlySvc).evalInst (.system false 0#16) s1' =
              execSetTidAddress s1' := by
            dsimp only [Program.evalInst, Program.withSvc, execInstWithSvc]
            exact hev_tid _ s1' (by simp [f3SetTidOnlySvc, hnum'])
          have hs2_eq : s2 = execSetTidAddress s1 := by
            dsimp only [s2, Program.evalInst, execInstWithSvc]
            rw [hsvc]
            refine hev_tid _ s1 ?_
            dsimp only [Syscall.standard, Syscall.dispatch]
            rw [hnum]
            change (match Syscall.standardTable.find? (·.1 == 96#64) with
              | some (_, h) => h s1
              | none => s1.setStatus (.Exception "unmodeled syscall (svc)")) = execSetTidAddress s1
            rw [show Syscall.standardTable.find? (·.1 == 96#64) = some (96#64, execSetTidAddress) from rfl]
          have hcomm : execSetTidAddress s1' = stripS (progKeep P_rx) ((execSetTidAddress s1).setFs fs0) := by
            rw [hsa]; cases s1; rfl
          have hs2'_rel : (P_rx.withSvc f3SetTidOnlySvc).evalInst (.system false 0#16) s1' =
              stripS (progKeep P_rx) (s2.setFs fs0) := by
            rw [hs2'_eq, hs2_eq]; exact hcomm
          have hfs12 : s2.fs = s1.fs := by rw [hs2_eq]; rfl
          have hphys12 : s2.physMemAvail = s1.physMemAvail := by rw [hs2_eq]; rfl
          have hperm12 : ∀ a, s2.mem.perm a = s1.mem.perm a := by
            intro a; rw [hs2_eq]; rfl
          obtain ⟨sf, hstepsP, hsf_eq, hfs2f, hphys2f, hperm2f⟩ := ih hrun_f s2 fs0 hs2'_rel
          exact ⟨sf, Steps.step hstepP hstepsP, hsf_eq, hfs2f.trans hfs12,
            hphys2f.trans hphys12, fun a => (hperm2f a).trans (hperm12 a)⟩
        · have h96' : (s1'.readReg64 .x8 == 96#64) = false := by
            rw [hx8_eq]; exact Bool.eq_false_iff.mpr h96
          have hf3_bad : f3SetTidOnlySvc s1' =
              s1'.setStatus (.Exception "unexpected syscall in F3 startup") := by
            simp [f3SetTidOnlySvc, h96']
          have hbad : ((P_rx.withSvc f3SetTidOnlySvc).evalInst (.system false 0#16) s1').status =
              .Exception "unexpected syscall in F3 startup" := by
            dsimp only [Program.evalInst, Program.withSvc, execInstWithSvc, evalSvc]
            rw [hf3_bad]; rfl
          rw [hbad] at hrun2'; cases hrun2'
      · have hnot0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hne_svc0 : inst ≠ .system false 0#16 := by
          rintro rfl; simp [Instr.isSvc0] at hnot0
        have hs2_eq : s2 = execInst inst s1 := evalInst_not_isSvc0 hnot0 s1
        have hs2'_eq : (P_rx.withSvc f3SetTidOnlySvc).evalInst inst s1' =
            stripS (progKeep P_rx) (s2.setFs fs0) := by
          rw [evalInst_not_isSvc0 hnot0, hsa, execInst_stripS hnot0,
            Process.execInst_setFs_of_isNonFs inst s1 fs0 (isNonFs_of_ne_svc0 inst s1 hne_svc0),
            ← hs2_eq]
        have hnsp := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnot0 s1
        have hfs12 : s2.fs = s1.fs := by rw [hs2_eq]; exact hnsp.2.2.2.2.2.2
        have hphys12 : s2.physMemAvail = s1.physMemAvail := by rw [hs2_eq]; exact hnsp.2.2.2.2.1
        have hperm12 : ∀ a, s2.mem.perm a = s1.mem.perm a := by
          intro a; rw [hs2_eq, hnsp.2.1]
        obtain ⟨sf, hstepsP, hsf_eq, hfs2f, hphys2f, hperm2f⟩ := ih hrun_f s2 fs0 hs2'_eq
        exact ⟨sf, Steps.step hstepP hstepsP, hsf_eq, hfs2f.trans hfs12,
          hphys2f.trans hphys12, fun a => (hperm2f a).trans (hperm12 a)⟩

/-! ## Read-Only `argvAtRO` and `MuslHarnessN` -/

/-- Read-only NUL-terminated bytes of `s` at `p`. -/
def cStrAtRO (p : BitVec 64) (s : List (BitVec 8)) : SepProp :=
  p ↦ᵣ (s ++ [0#8])

/-- Read-only C `argv` pointer table at `a` (as frozen by `ProofLib.StdStartup` on initial stack). -/
def argvAtRO : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ᵣ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ᵣ p) ∗ cStrAtRO p s ∗ argvAtRO (a + 8#64) ss

/-- Generalized `MuslHarness` requiring `n` bytes of stack below `sm.sp` on `main` return
    (`n = 80` for real `musl` v1.2.5 `exit` → `__libc_exit_fini` → `__stdio_exit_needed`). -/
def MuslHarnessN (n : Nat) (elf : ElfImage) (P : Program) (mainPc : BitVec 64) (Fr : SepProp)
    (Ok : Inputs → Prop) (MainPre : Inputs → State → SepProp) : Prop :=
  ElfStaticOk elf → ∀ i, Ok i → ∃ s0 sm,
    elf.loadState (cliInputs i) = .ok s0 ∧ Steps P s0 sm ∧
    sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
    sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
    (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    (sm.mem ⊨ MainPre i sm ∗ Fr) ∧
    ∀ sr, Steps P sm sr → Returned sm sr → (sr.mem ⊨ stackAt sm.sp n ∗ Fr ∗ anyHeap) →
      ∃ sx, Steps P sr sx ∧
        sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
        sx.fs = sr.fs ∧ sx.trace = sr.trace

theorem exit_frame_n {m : Memory} {sp : BitVec 64} {n stk : Nat} {Fr : SepProp}
    (hstk : n ≤ stk) (_hstk' : stk ≤ 2 ^ 64) (h : m ⊨ (stackAt sp stk ∗ anyHeap) ∗ Fr) :
    m ⊨ stackAt sp n ∗ Fr ∗ anyHeap := by
  have hsplit := stackAt_split_bottom sp n (stk - n) (by omega)
  rw [show n + (stk - n) = stk by omega] at hsplit
  rw [hsplit] at h
  refine Satisfies.mono ?_ h
  have e : ((memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ stackAt sp n) ∗ anyHeap) ∗ Fr =
      stackAt sp n ∗ Fr ∗ (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ anyHeap) := by
    sep_ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _))

/-! ## `MuslHarnessNeedLocksN 80`, `MuslHarnessN 80`, and `f3InitFineBudgetPool` -/

/-- Auxiliary input bundle for initial stack/TLS validation: zeroes `stdin`, `files`, and `dirs`
    so `ProcessInputs.Valid` holds under `CliInputsOk i` alone (while `buildInitialStack` and
    `StackLayout.of` remain definitionally identical to `cliInputs i`). -/
private def f3EmptyFsInputs (i : Inputs) : ProcessInputs :=
  { cliInputs i with stdin := [], files := [], dirs := [] }

private theorem bytesOfString_length (s : String) : (bytesOfString s).length = s.length := by
  simp [bytesOfString, String.length_toList]

private theorem zero_not_mem_bytesOfString {s : String}
    (h : ∀ c ∈ s.toList, 0 < c.toNat ∧ c.toNat < 128) :
    0#8 ∉ bytesOfString s := by
  intro hm
  simp only [bytesOfString, List.mem_map] at hm
  obtain ⟨c, hc, h0⟩ := hm
  have ⟨hpos, hlt⟩ := h c hc
  have htn := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.toNat < 256)] at htn
  omega

private theorem foldl_argv_len_le_sum (xs : List String) (acc : Nat) :
    (xs.map bytesOfString).foldl (fun n s => n + (s.length + 1)) acc + 8 * xs.length =
      acc + (xs.map fun a => a.length + 1 + 8).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons, List.length_cons, List.sum_cons,
      bytesOfString_length]
    have := ih (acc + (x.length + 1))
    omega

private theorem le_sum_of_mem_nat {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp only [List.sum_cons]; omega
    · simp only [List.sum_cons]; have := ih hm; omega

private theorem argv_elem_len_le {a : String} {argv : List String}
    (hmem : a ∈ argv) (hfit : ArgvFitsInitialStack argv) :
    a.length + 1 + 8 ≤ 16384 := by
  unfold ArgvFitsInitialStack at hfit
  have hle : a.length + 1 + 8 ≤ (argv.map fun x => x.length + 1 + 8).sum :=
    le_sum_of_mem_nat (List.mem_map_of_mem hmem)
  omega

private theorem f3EmptyFsInputs_valid {i : Inputs} (hi : CliInputsOk i) :
    (f3EmptyFsInputs i).Valid := by
  obtain ⟨hprint, hfit⟩ := hi
  have hinit : (f3EmptyFsInputs i).init.Valid :=
    show ({ stackSize := 8388608 } : ProcessInit).Valid from
      (ProcessInit.check_iff_valid _).mp (by decide)
  have hfs : FsValid (f3EmptyFsInputs i) :=
    (FsValid.check_iff (f3EmptyFsInputs i)).mp rfl
  have hargs : ArgsValid (f3EmptyFsInputs i) := by
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [f3EmptyFsInputs, cliInputs, processInputs]
    · intro s hs
      simp only [f3EmptyFsInputs, cliInputs, processInputs,
        List.map_cons, List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | hmem
      · exact of_decide_eq_true (by decide)
      · obtain ⟨a, ⟨ha, rfl⟩⟩ := hmem
        exact zero_not_mem_bytesOfString (hprint a ha).2
    · intro s hs
      simp [f3EmptyFsInputs, cliInputs, processInputs] at hs
    · simp [f3EmptyFsInputs, cliInputs, processInputs]
    · intro s hs
      simp only [f3EmptyFsInputs, cliInputs, processInputs, List.append_nil,
        List.map_cons, List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | hmem
      · exact of_decide_eq_true (by decide)
      · obtain ⟨a, ⟨ha, rfl⟩⟩ := hmem
        rw [bytesOfString_length]
        have := argv_elem_len_le ha hfit
        unfold MAX_ARG_STRLEN Obj.pageSize; omega
    · simp only [f3EmptyFsInputs, cliInputs, processInputs]
      decide
    · unfold argBytes argLimit STK_LIM ARG_MAX
      simp only [f3EmptyFsInputs, cliInputs, processInputs, List.map_cons,
        List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      have hbin : (bytesOfString "libsignal-cli").length = 13 := by decide
      rw [hbin]
      have hfold := foldl_argv_len_le_sum i.argv (0 + (13 + 1))
      unfold ArgvFitsInitialStack at hfit
      have hlen_map : (List.map bytesOfString i.argv).length = i.argv.length := List.length_map _
      rw [hlen_map]
      omega
  exact ⟨hargs, hinit, hfs⟩

private theorem loadState_f3CliInputs_of_empty {elf : ElfImage} {i : Inputs} {s0_0 : State}
    (hl : InputsLoadable i)
    (hload0 : elf.loadState (f3EmptyFsInputs i) = .ok s0_0) :
    ∃ s0 : State,
      elf.loadState (cliInputs i) = .ok s0 ∧
      s0_0 = s0.setFs (initFsState (f3EmptyFsInputs i)) ∧
      s0.fs = initFsState (cliInputs i) ∧
      s0.trace = [] ∧
      s0.mem = s0_0.mem ∧
      s0.brk = s0_0.brk ∧
      s0.brkStart = s0_0.brkStart ∧
      s0.physMemAvail = s0_0.physMemAvail := by
  have hd_any : (cliInputs i).dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := by
    rw [List.any_eq_false]
    intro d hd
    have ⟨h1, h2⟩ := hl.1 d hd
    simp [h1, h2]
  have hf_any : (cliInputs i).files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := by
    rw [List.any_eq_false]
    rintro ⟨p, bs⟩ hp
    have ⟨⟨h1, h2⟩, h3⟩ := hl.2 (p, bs) hp
    simp [h1, h2, h3]
  have hb_eq : buildInitialStack elf (cliInputs i) = buildInitialStack elf (f3EmptyFsInputs i) := rfl
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at hload0 ⊢
  have hd0 : (f3EmptyFsInputs i).dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := rfl
  have hf0 : (f3EmptyFsInputs i).files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := rfl
  rw [hd0, hf0] at hload0
  rw [hd_any, hf_any, hb_eq]
  cases hwf : (!elf.WellFormed) <;> simp only [hwf, Bool.false_eq_true, ↓reduceIte] at hload0 ⊢
  · generalize hbis : buildInitialStack elf (f3EmptyFsInputs i) = r at hload0 ⊢
    cases r with
    | error _ => contradiction
    | ok pr =>
      obtain ⟨sp, stackRegion⟩ := pr
      dsimp only at hload0 ⊢
      cases hload0
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · contradiction

private theorem rwAtomListSep_f3BssAtoms (L : StdBinaryLayout) :
    F3BssGlobals L =
      (L.threadListLockAddr ↦₃₂ 0#32) ∗ (L.sysinfoAddr ↦₆₄ 0#64) ∗ (L.hwcapAddr ↦₆₄ 0#64) ∗
      (L.finalizedAddr ↦₈ 0#8) ∗ (L.initializedAddr ↦₈ 0#8) ∗
      (L.stdDetectCacheAddr ↦₆₄ 0#64) ∗ (L.environAddr ↦₆₄ 0#64) ∗
      (L.prognameAddr ↦₆₄ 0#64) ∗ (L.prognameFullAddr ↦₆₄ 0#64) ∗
      (L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
      (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗
      (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.oflLockAddr ↦₃₂ 0#32) := by
  unfold F3BssGlobals f3BssAtoms
  cases (L.stdoutUsedAddr == L.stdinUsedAddr) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.cons_append, rwAtomListSep, RwAtom.toSepProp]
  | true =>
    simp only [↓reduceIte,
      List.nil_append, List.cons_append, rwAtomListSep, RwAtom.toSepProp]
    sep_ac_rfl

private def f3PreTlsSep (L : StdBinaryLayout) (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 544#64) 96 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ StdTlsGlobals L ∗
    (L.libcAddr ↦₈ 0#8) ∗ StdLibcTlsZero L

private def f3PostTlsSep (L : StdBinaryLayout) (sp0 sysinfoVal : BitVec 64) : SepProp :=
  ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗ (L.libcAddr ↦₈ 1#8) ∗
    memRegion (sp0 - 544#64) 96 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F3TlsState L sysinfoVal

private def f3InitAllSep (L : StdBinaryLayout) (img : ElfImage) (inputs : ProcessInputs) : SepProp :=
  let sl := StackLayout.of img inputs
  F3RoConstants L ∗ StdExtraRo L ∗ F3InitGlobals L ∗ StdExtraRw L ∗
    memRegion (sl.sp0 - 8371824#64) 8371824 ∗
    (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
    (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
    (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
    (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
    (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
    (sl.platformAddr ↦ᵣ platformCStringBytes) ∗
    (sl.argvBase ↦ᵣ sl.upperStrBytes)

private theorem scratch_supportedOn_of_headroom {img : ElfImage} {inputs : ProcessInputs}
    {s0 : State} (h : InitialStackInfo img inputs s0) {K : Nat}
    (hK : inputs.init.stackTop.toNat - inputs.init.stackSize + K ≤
      (StackLayout.of img inputs).sp0.toNat) :
    let L := StackLayout.of img inputs
    SupportedOn 0#64 (fun k => L.sp0.toNat - K ≤ k ∧ k < L.sp0.toNat) s0.mem
      (memRegion (L.sp0 - BitVec.ofNat 64 K) K) := by
  have hperm := h.s0_perm_rw_below_sp0
  have hnolf := h.s0_isLazyFree
  clear h; dsimp only
  generalize hsp : (StackLayout.of img inputs).sp0 = sp0 at *; clear hsp
  have hlt := sp0.isLt
  have hbase : (sp0 - BitVec.ofNat 64 K).toNat = sp0.toNat - K := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsup := SupportedOn.of_memRegion_rw0 (addr := sp0 - BitVec.ofNat 64 K) (len := K)
    (m := s0.mem) (by rw [hbase]; omega)
    (fun a ha => by
      unfold InRegion at ha; have := a.isLt
      rw [BitVec.toNat_sub, hbase] at ha
      exact hperm a (by omega) (by omega))
    (fun a _ => hnolf a)
  rwa [hbase, show sp0.toNat - K + K = sp0.toNat by omega] at hsup

private theorem s0_satisfies_f3InitAllSep {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (hmatch : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0)
    (hinfo : InitialStackInfo img inputs s0) (hvalid : inputs.Valid)
    (hhr8 : inputs.init.stackTop.toNat - inputs.init.stackSize + 8371824 ≤
      (StackLayout.of img inputs).sp0.toNat) :
    s0.mem ⊨ f3InitAllSep L img inputs := by
  have hseg := f3MatchesImage_segments hmatch
  have hbrk_eq := hseg.2.2.2.2.1
  have hbrk_le := hseg.2.2.2.2.2.1.2
  have hfl := hinfo.stackBase_floor
  unfold STACK_BASE_MIN at hfl
  have htop_pos : (StackLayout.of img inputs).sp0.toNat ≤ inputs.init.stackTop.toNat := by
    have := hinfo.addrs_nat; omega
  have h1 := SupportedOn.bupd_intro (f3MatchesImage_supportedOn_initGlobals_below_brk hmatch hload)
  have h2_sc := SupportedOn.bupd_intro (scratch_supportedOn_of_headroom hinfo hhr8)
  have h2_0 := hinfo.stack_supportedOn_bupd hvalid.auxv.random16 (K := 0) (Nat.zero_le _)
  have h2 := SupportedOn.sepConj_bupd_interval
    (lo := (StackLayout.of img inputs).sp0.toNat - 8371824)
    (hi := inputs.init.stackTop.toNat) h2_sc h2_0 (by omega) (by omega) (by omega)
  have h12 := SupportedOn.sepConj_bupd_interval
    (lo := 0) (hi := inputs.init.stackTop.toNat) h1 h2 (by omega) (by omega) (by omega)
  have hsat := f3MatchesImage_satisfies_roConstants hmatch hload (SupportedOn.satisfies_bupd h12)
  have hmr0 : memRegion ((StackLayout.of img inputs).sp0 - 8371824#64) 8371824 ∗
      memRegion ((StackLayout.of img inputs).sp0 - 0#64) 0 =
      memRegion ((StackLayout.of img inputs).sp0 - 8371824#64) 8371824 := by
    have hs := memRegion_split_le ((StackLayout.of img inputs).sp0 - 8371824#64)
      8371824 8371824 (by decide) (by decide)
    rw [show (StackLayout.of img inputs).sp0 - 8371824#64 + BitVec.ofNat 64 8371824 =
      (StackLayout.of img inputs).sp0 - 0#64 by bv_lin] at hs
    exact hs.symm
  refine Satisfies.mono ?_ hsat
  dsimp only [f3InitAllSep]
  rw [← sepConj_assoc (memRegion ((StackLayout.of img inputs).sp0 - 8371824#64) 8371824)
    (memRegion ((StackLayout.of img inputs).sp0 - 0#64) 0), hmr0]
  sep_entail

private theorem absorb_ro_pad {U C Pad : SepProp}
    (hdup : (U ∗ (C ∗ Pad)) = U) (hc : (C ∗ C) = C) :
    U ⊢ C ∗ U := by
  refine Entails.trans (Entails.of_eq hdup.symm) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hc.symm))) ?_
  refine Entails.trans (Q := C ∗ (U ∗ (C ∗ Pad))) (by sep_entail) ?_
  exact sepConj_mono_right (Entails.of_eq hdup)

private theorem argvTable_dup_argvAtRO {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hinfo : InitialStackInfo img inputs s0) (hargs : ArgsValid inputs) :
    let sl := StackLayout.of img inputs
    ((sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes)) ⊢
      argvAtRO sl.argvTableAddr inputs.argv ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
  dsimp only
  let sl := StackLayout.of img inputs
  have hlen : sl.argvAddrs.length = inputs.argv.length := hinfo.argvAddrs_length
  suffices hgen : ∀ (k : Nat), k ≤ inputs.argv.length →
      (((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (sl.argvAddrs.drop k ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes)) ⊢
      argvAtRO (sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) (inputs.argv.drop k) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (sl.argvAddrs.drop k ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) by
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.drop_zero] using
      hgen 0 (Nat.zero_le _)
  intro k hk
  induction hd : inputs.argv.length - k generalizing k with
  | zero =>
    have hk_eq : k = inputs.argv.length := by omega
    subst hk_eq
    have hd1 : sl.argvAddrs.drop inputs.argv.length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.drop_length, List.nil_append]
    simp only [argvAtRO, pointsToWords64RO_cons, pointsToWords64RO_nil, sepConj_emp]
    refine Entails.trans (sepConj_mono_left (Entails.of_eq (pointsTo64RO_dup _ _).symm)) (by sep_entail)
  | succ rem ih =>
    have hk_lt : k < inputs.argv.length := by omega
    have hk_lt' : k < sl.argvAddrs.length := by omega
    have hd_a : sl.argvAddrs.drop k = sl.argvAddrs[k] :: sl.argvAddrs.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt'
    have hd_v : inputs.argv.drop k = inputs.argv[k] :: inputs.argv.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hd_a, hd_v, List.cons_append]
    simp only [argvAtRO, pointsToWords64RO_cons]
    have hstep_addr : (sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) + 8#64 =
        sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      exact congrArg (sl.argvTableAddr + BitVec.ofNat 64 ·) (by omega)
    rw [hstep_addr]
    obtain ⟨pad, _, _, _, _, hdup_str⟩ := hinfo.dup_argv_cstr_padded hargs hk_lt
    have habs_str : (sl.argvBase ↦ᵣ sl.upperStrBytes) ⊢
        (sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
      have hdup_str' : ((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗
          ((sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗
            ((sl.argvAddrs[k] + BitVec.ofNat 64 (inputs.argv[k] ++ [0#8]).length) ↦ᵣ pad))) =
          (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
        dsimp only [sl]; rw [← pointsToBytesRO_append]; exact hdup_str
      exact absorb_ro_pad hdup_str' (pointsToBytesRO_dup _ _)
    have hih := ih (k + 1) (by omega) (by omega)
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.sepExists_right sl.argvAddrs[k] (Entails.refl _)))
    dsimp only [cStrAtRO]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_left (Entails.of_eq (pointsTo64RO_dup _ _).symm))) ?_
    refine Entails.trans
      (Q := ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (((sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1))) ↦₆₄ᵣ*
          (sl.argvAddrs.drop (k + 1) ++ [0#64])) ∗
          ((sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗
            (sl.argvBase ↦ᵣ sl.upperStrBytes))))
      (Entails.trans (by sep_entail)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          habs_str))))
      ?_
    refine Entails.trans
      (Q := ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (((sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1))) ↦₆₄ᵣ*
          (sl.argvAddrs.drop (k + 1) ++ [0#64])) ∗
          (sl.argvBase ↦ᵣ sl.upperStrBytes)))
      (by sep_entail)
      ?_
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hih)))
      (by sep_entail)

private theorem pointsToBytes_flatMap_u64 {a : BitVec 64} (ws : List (BitVec 64))
    (hal : a.toNat % 8 = 0) (hbnd : a.toNat + 8 * ws.length ≤ 2 ^ 48) :
    (a ↦ₛ (ws.flatMap fun w => List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8))) ⊢
      (a ↦₆₄* ws) := by
  induction ws generalizing a with
  | nil =>
    simp only [List.flatMap_nil, pointsToBytes_nil, pointsToWords64_nil]
    exact Entails.refl _
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_cons] at hbnd ⊢
    have hlen8 : (List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)).length = 8 := by simp
    rw [pointsToBytes_append a (List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)) _, hlen8]
    have ha8_nat : (a + 8#64).toNat = a.toNat + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hw : (a ↦ₛ List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)) ⊢ (a ↦₆₄ w) := by
      rw [pointsTo64_eq_pointsToBytes]
      exact Entails.refl _
    rw [pointsToWords64_cons]
    exact sepConj_mono hw (ih (by omega) (by omega))

private theorem auxv_entails_mallocngAuxvAt {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hinfo : InitialStackInfo img inputs s0) (hvalid : inputs.Valid) :
    let sl := StackLayout.of img inputs
    ((sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
      (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes)) ⊢
      MallocngAuxvAt sl.auxvTableAddr ∗
        (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) := by
  dsimp only
  have hrand16 := hvalid.auxv.random16
  have han := hinfo.addrs_nat; dsimp only at han
  obtain ⟨_, _, haux_nat, haux_le, hplat_nat, hargvB_nat, _, _, hupper_top⟩ := han
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  have hsp16 := hinfo.sp0_align16
  obtain ⟨prePairs, sufPairs, hsplit_eq, _, hps_le, hpre_no, hsuf_no⟩ :=
    mkAuxvEntries_split_random img hvalid.auxv
      (StackLayout.of img inputs).platformAddr
      (StackLayout.of img inputs).randomAddr
      (StackLayout.of img inputs).execfnAddr
  have hauxE_split : (StackLayout.of img inputs).auxvEntries =
      prePairs ++ [(AuxvTag.random, (StackLayout.of img inputs).randomAddr)] ++ sufPairs :=
    hinfo.auxvEntries_eq.trans hsplit_eq
  have hauxE_len : (StackLayout.of img inputs).auxvEntries.length =
      prePairs.length + sufPairs.length + 1 := by
    rw [hauxE_split]; simp; omega
  rw [hauxE_len] at haux_le
  let ws := ((prePairs ++ [(25#64, (StackLayout.of img inputs).randomAddr)] ++
    sufPairs ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])
  have hws_len : ws.length = 2 * (prePairs.length + sufPairs.length + 2) := by
    have hfl : ∀ xs : List (BitVec 64 × BitVec 64),
        (xs.flatMap fun (t, v) => [t, v]).length = 2 * xs.length := by
      intro xs; induction xs with
      | nil => simp
      | cons _ tl ih => simp [ih]; omega
    rw [hfl]; simp; omega
  have henc_eq : encodeAuxvBytes (StackLayout.of img inputs).auxvEntries =
      ws.flatMap (fun w => List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)) := by
    rw [hauxE_split]; rfl
  rw [henc_eq, split_random_hi8 (StackLayout.of img inputs).randomAddr hrand16]
  have hpure :
      (∀ e ∈ prePairs, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      (∀ e ∈ sufPairs, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      prePairs.length + sufPairs.length ≤ 64 ∧
      (StackLayout.of img inputs).auxvTableAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧
      (StackLayout.of img inputs).randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
      (inputs.init.auxv.randomBytes.drop 8).length = 8 :=
    ⟨hpre_no, hsuf_no, hps_le, by omega, by omega, by simp [hrand16]⟩
  have hwords := pointsToBytes_flatMap_u64 (a := (StackLayout.of img inputs).auxvTableAddr) ws
    (by omega) (by rw [hws_len]; omega)
  refine Entails.trans (sepConj_mono_left hwords) ?_
  refine Entails.trans
    (Q := (((StackLayout.of img inputs).auxvTableAddr ↦₆₄* ws) ∗
        (((StackLayout.of img inputs).randomAddr + 8#64) ↦ₛ inputs.init.auxv.randomBytes.drop 8)) ∗
      ((StackLayout.of img inputs).randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8))
    (by sep_entail) ?_
  unfold MallocngAuxvAt
  exact sepConj_mono_left
    (Entails.sepExists_right prePairs
      (Entails.sepExists_right sufPairs
        (Entails.sepExists_right (StackLayout.of img inputs).randomAddr
          (Entails.sepExists_right 0#64
            (Entails.sepExists_right (inputs.init.auxv.randomBytes.drop 8)
              (by dsimp only [ws]; rw [pure_sepConj_of_true hpure]; sep_entail))))))

/-- Residual startup resources held alongside the core `cMainAddr` entry frame in
    `f3StartupMainPre` (framing the stage-2 saved frame at `[sp0 - 48, sp0)`, TLS state,
    `libc` globals, and read-only stack tables without requiring `|==>` drops). -/
def f3StartupResidual (_L : StdBinaryLayout) (_elf : ElfImage) (_i : Inputs) : SepProp :=
  ∃∗ R_unused : SepProp, R_unused

/-- Separation-logic precondition handed to `main` (`L.cMainAddr`) by `f3MuslHarness80_of_layout`
    (with `libc.need_locks` frozen inside `StdMuslExitGlobals L 0#8`). Includes
    `∃ sLoad, elf.loadState (cliProcessInputs i) = .ok sLoad ∧ StartupVmPreserved sLoad sm` so
    `ElfInitFine.cliElf_fineBudgetPool_of_init` discharges directly. -/
def f3StartupMainPre (L : StdBinaryLayout) (elf : ElfImage) (i : Inputs) (sm : State) : SepProp :=
  let sl := StackLayout.of elf (cliInputs i)
  ⌜(L.rxProgram elf).CodeLoaded sm.mem ∧
    (∃ sLoad, elf.loadState (cliProcessInputs i) = .ok sLoad ∧ StartupVmPreserved sLoad sm) ∧
    cliMainStk ≤ sm.sp.toNat ∧
    sm.sp = sl.sp0 - 48#64 ∧
    sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 ∧
    sm.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧
    164 ≤ sm.tpidrEl0.toNat ∧
    sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
    MallocngBrkStartWf sm.brkStart ∧
    sm.brk = sm.brkStart ∧
    sm.brkStart = L.brkStart⌝ ∗
  argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
  stackAt sm.sp cliMainStk ∗
  StdExtraRo L ∗
  StdExtraRw L ∗
  ((sm.tpidrEl0 - 164#64) ↦₃₂ 0#32) ∗
  ((L.libcAddr + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
  ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
  MallocngAuxvAt sl.auxvTableAddr ∗
  f3StartupResidual L elf i

/-- Separation-logic precondition handed to `main` (`L.cMainAddr`) by
    `f3MuslHarnessNeedLocks80_of_layout`: extends `f3StartupMainPre` with writable
    `((L.libcAddr + 3#64) ↦₈ 0#8)` (`__libc.need_locks = 0`) for single-threaded `mallocng`. -/
def f3StartupMainPreNeedLocks (L : StdBinaryLayout) (elf : ElfImage) (i : Inputs) (sm : State) :
    SepProp :=
  ((L.libcAddr + 3#64) ↦₈ 0#8) ∗ f3StartupMainPre L elf i sm

/-- Initialize `(fineRustCliAllocBudget γ mpl sm.tpidrEl0 sm.brkStart).pool lim fineCostModel.init sm`
    at `cMainAddr` entry directly from `f3StartupMainPreNeedLocks L elf i sm` and
    `CliElfMallocngLayout elf lim` via `ElfInitFine.cliElf_fineBudgetPool_of_init`, keeping
    `argvAtRO`, the `8,371,776` B `stackAt sm.sp cliMainStk` stack region, and `ExtraRest`. -/
theorem f3InitFineBudgetPool {L : StdBinaryLayout} {elf : ElfImage} {mpl : Obj.MultiPlacement}
    {lim : BudgetLimits} {i : Inputs} {sm : State} {ExtraRest R : SepProp}
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mpl).libc = L.libcAddr)
    (hdata : StdExtraRo L ∗ StdExtraRw L ⊢ VerifiedLibraries.mallocngLib.dataInit mpl ∗ ExtraRest)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks L elf i sm ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl sm.tpidrEl0 sm.brkStart
      sm.mem ⊨
        (A.pool lim fineCostModel.init sm ∗
          ⌜(L.rxProgram elf).CodeLoaded sm.mem ∧
            cliMainStk ≤ sm.sp.toNat ∧
            sm.sp = (StackLayout.of elf (cliInputs i)).sp0 - 48#64 ∧
            sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 ∧
            sm.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧
            MallocngBrkStartWf sm.brkStart ∧
            sm.brk = sm.brkStart ∧
            sm.brkStart = L.brkStart⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗
          ExtraRest ∗
          f3StartupResidual L elf i) ∗ R := by
  unfold f3StartupMainPreNeedLocks f3StartupMainPre at hm
  dsimp only at hm
  simp only [sepConj_left_comm ((L.libcAddr + 3#64) ↦₈ 0#8), sepConj_assoc,
    satisfies_pure_sepConj] at hm
  obtain ⟨⟨hCL, ⟨sLoad, hLoad, hVm⟩, hsp_ge, hsp_eq, hlr_eq, htp_eq, htpLo, htpHi,
    hbrkWf, hbrk, hbrkS⟩, hm⟩ := hm
  let mAddrs := mallocngAddrsOfPlacement mpl
  let auxvPtr := (StackLayout.of elf (cliInputs i)).auxvTableAddr
  have hm_init : sm.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime mAddrs sm.tpidrEl0 ∗
        ((mAddrs.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗
        ((argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗ ExtraRest ∗ f3StartupResidual L elf i) ∗ R) := by
    refine Satisfies.mono ?_ hm
    refine Entails.trans
      (Q := (((StdExtraRo L ∗ StdExtraRw L) ∗
          ((sm.tpidrEl0 - 164#64) ↦₃₂ 0#32) ∗
          ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
          ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
          ((L.libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
          MallocngAuxvAt auxvPtr) ∗
        (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗ f3StartupResidual L elf i ∗ R)))
      (by sep_entail) ?_
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left hdata)) ?_
    have herr0 : ((sm.tpidrEl0 - 164#64) ↦₃₂ 0#32) ⊢
        (∃∗ errnoVal : BitVec 32, (sm.tpidrEl0 - 164#64) ↦₃₂ errnoVal) :=
      Entails.sepExists_right 0#32 (Entails.refl _)
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left herr0))) ?_
    unfold MallocngRuntime
    dsimp only [mAddrs]
    rw [hlibc]
    sep_entail
  obtain ⟨γ, hPool⟩ := cliElf_fineBudgetPool_of_init hLayout hLoad hVm htpLo htpHi hm_init
  refine ⟨γ, Satisfies.mono ?_ hPool⟩
  rw [pure_sepConj_of_true ⟨hCL, hsp_ge, hsp_eq, hlr_eq, htp_eq, hbrkWf, hbrk, hbrkS⟩]
  sep_entail

/-- Initialize unbudgeted `(mallocngRustCliAlloc γ mAddrs).pool 0 0 sm ∗ StdErrnoCell sm.tpidrEl0`
    at `cMainAddr` entry directly from `f3StartupMainPreNeedLocks L elf i sm`. -/
theorem f3InitMallocngHeap {L : StdBinaryLayout} {elf : ElfImage} {i : Inputs} {sm : State}
    {mAddrs : VerifiedLibraries.Mallocng.MallocngAddrs} {ExtraRest R : SepProp}
    (hlibc : mAddrs.libc = L.libcAddr)
    (hdata : StdExtraRo L ∗ StdExtraRw L ⊢
      MallocngRoTablesAt mAddrs ∗
      (mAddrs.ctx ↦ₛ List.replicate 928 0#8) ∗
      (mAddrs.lock ↦₃₂ 0#32) ∗
      (mAddrs.replaced ↦₃₂ 0#32) ∗
      (mAddrs.aaReplaced ↦₃₂ 0#32) ∗
      ExtraRest)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks L elf i sm ∗ R) :
    ∃ γ : GhostName,
      sm.mem ⊨
        ((mallocngRustCliAlloc γ mAddrs).pool 0 0 sm ∗
          StdErrnoCell sm.tpidrEl0 ∗
          ⌜(L.rxProgram elf).CodeLoaded sm.mem ∧
            cliMainStk ≤ sm.sp.toNat ∧
            sm.sp = (StackLayout.of elf (cliInputs i)).sp0 - 48#64 ∧
            sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 ∧
            sm.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧
            MallocngBrkStartWf sm.brkStart ∧
            sm.brk = sm.brkStart ∧
            sm.brkStart = L.brkStart⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗
          ExtraRest ∗
          f3StartupResidual L elf i) ∗ R := by
  unfold f3StartupMainPreNeedLocks f3StartupMainPre at hm
  dsimp only at hm
  simp only [sepConj_left_comm ((L.libcAddr + 3#64) ↦₈ 0#8), sepConj_assoc,
    satisfies_pure_sepConj] at hm
  obtain ⟨⟨hCL, _, hsp_ge, hsp_eq, hlr_eq, htp_eq, htpLo, htpHi, hbrkWf, hbrk, hbrkS⟩, hm⟩ := hm
  have hm_res : sm.mem ⊨ MallocngStartupResources mAddrs sm.tpidrEl0 ∗
      (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
        stackAt sm.sp cliMainStk ∗ ExtraRest ∗ f3StartupResidual L elf i ∗ R) := by
    refine Satisfies.mono ?_ hm
    refine Entails.trans
      (Q := (((StdExtraRo L ∗ StdExtraRw L) ∗
          ((sm.tpidrEl0 - 164#64) ↦₃₂ 0#32) ∗
          ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
          ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
          ((L.libcAddr + 8#64) ↦₆₄ (StackLayout.of elf (cliInputs i)).auxvTableAddr) ∗
          MallocngAuxvAt (StackLayout.of elf (cliInputs i)).auxvTableAddr) ∗
        (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗ f3StartupResidual L elf i ∗ R)))
      (by sep_entail) ?_
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left hdata)) ?_
    have herr0 : ((sm.tpidrEl0 - 164#64) ↦₃₂ 0#32) ⊢
        (∃∗ errnoVal : BitVec 32, (sm.tpidrEl0 - 164#64) ↦₃₂ errnoVal) :=
      Entails.sepExists_right 0#32 (Entails.refl _)
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left herr0))) ?_
    unfold MallocngStartupResources
    refine Entails.trans ?_
      (sepConj_mono_left
        (Entails.sepExists_right (StackLayout.of elf (cliInputs i)).auxvTableAddr (Entails.refl _)))
    unfold MallocngRuntime
    rw [hlibc]
    sep_entail
  obtain ⟨γ, hγ⟩ := mallocngRustCliPool_of_init_resources mAddrs _ sm htpLo htpHi hbrkWf hbrk hm_res
  refine ⟨γ, Satisfies.mono ?_ hγ⟩
  rw [pure_sepConj_of_true ⟨hCL, hsp_ge, hsp_eq, hlr_eq, htp_eq, hbrkWf, hbrk, hbrkS⟩]
  sep_entail

private theorem codeLoaded_unstrip_f3 {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded (stripExecOutside (progKeep prog) m)) :
    prog.CodeLoaded m := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    simp only [progKeep, decide_eq_true_eq, hsub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hi
  have hb := hL.byte_eq i hi
  have hp := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [strip_read8] at hb
  rw [strip_perm_of_keep hin] at hp
  rw [strip_isLazyFree] at hlf
  exact ⟨hb, hp, hlf⟩

private theorem codeLoaded_steps_any {prog P : Program} {s1 s2 : State}
    (hsteps : Steps P s1 s2) (hL : prog.CodeLoaded s1.mem) :
    prog.CodeLoaded s2.mem :=
  hL.of_keepsFrozen hsteps.keepsFrozen

private theorem f3Exit80_of_layout {L : StdBinaryLayout} {elf : ElfImage} {P : Program}
    (lf : F3LayoutImageFacts L)
    (hc : F3StartupCode (L.rxProgram elf) L)
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep (L.rxProgram elf) pc = true → (P.externAt? pc).isNone = true)
    (fs0 : FsState)
    {sm sr : State}
    (hL_rx : (L.rxProgram elf).CodeLoaded sr.mem)
    (hlr_sm : sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64)
    (hal_sm : sm.spAligned = true)
    (hret : Returned sm sr)
    (hm_sr : sr.mem ⊨ stackAt sm.sp 80 ∗ StdMuslExitGlobals L 0#8 ∗ anyHeap) :
    ∃ sx : State, Steps P sr sx ∧
      sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
      sx.fs = sr.fs ∧ sx.trace = sr.trace := by
  let P_rx := L.rxProgram elf
  let P_st := P_rx.withSvc f3SetTidOnlySvc
  obtain ⟨hpc_sr, hsp_sr, hrun_sr⟩ := hret
  have hal_sr : sr.spAligned = true := by
    simp only [State.spAligned, hsp_sr] at hal_sm ⊢; exact hal_sm
  rw [hlr_sm] at hpc_sr
  have hm_sr' : (sr.setFs fs0).mem ⊨
      (StdMuslExitGlobals L 0#8 ∗ stackAt sm.sp 80) ∗ anyHeap := by
    exact Satisfies.mono (by sep_entail) hm_sr
  obtain ⟨R_view, hstrip_sat, _⟩ := strip_frame (progKeep P_rx) hm_sr'
  let sr' := stripS (progKeep P_rx) (sr.setFs fs0)
  have hwp_exit : SepWP P_st (L.sysExitAddr + 12#64) sr'
      ((StdMuslExitGlobals L 0#8 ∗ stackAt sm.sp 80) ∗ emp)
      (fun sf' _ => sf'.pc = L.sysExitAddr + 12#64 ∧ sf'.status = .Running ∧
        sf'.readReg64 .x8 = 94#64 ∧
        sf'.readReg64 .x0 = (sr'.readReg32 .x0).signExtend 64 ∧
        sf'.trace = sr'.trace) := by
    rw [sepConj_assoc]
    refine muslExit_to_svc_wp (P := P_st) (L := L) (F := emp)
      hc.muslExit
      (show sr'.pc = L.libcStartMainStage2Addr + 56#64 from hpc_sr)
      (show sr'.status = .Running from hrun_sr)
      (show sr'.sp = sm.sp from hsp_sr)
      (show sr'.spAligned = true from hal_sr)
      lf.finiArray_bnd lf.al_got lf.al_fini lf.al_ofl lf.al_stdin lf.al_stdout
      lf.al_stderrUsed lf.al_stderrFile lf.stderrFile_nz
      fun sf' hpc' hrun' _ _ hx8' hx0' hstd' => ?_
    apply SepWP.done hpc' hrun'
    exact ⟨hpc', hrun', hx8', hx0', hstd'.2.1⟩
  have hL_st : P_st.CodeLoaded sr'.mem := codeLoaded_withSvc_iff.mpr (strip_codeLoaded_f3 hL_rx)
  have hsat_exit : sr'.mem ⊨ ((StdMuslExitGlobals L 0#8 ∗ stackAt sm.sp 80) ∗ emp) ∗ R_view := by
    dsimp only [sr', stripS, State.setMem, State.setFs]
    exact Satisfies.mono (by sep_entail) hstrip_sat
  obtain ⟨s_svc', hsteps_st, ⟨hpc_svc', hrun_svc', _, _, ⟨_, _, hx8_svc', hx0_svc', htr_svc'⟩⟩ | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp_exit hsat_exit hL_st
  · obtain ⟨s_svc, hsteps_P, hs_svc_eq, hfs_svc, _, _⟩ :=
      steps_lift_setTidOnly hc.no_hooks hsvc hHookFree hsteps_st hrun_svc' sr fs0 rfl
    have hpc_svc : s_svc.pc = L.sysExitAddr + 12#64 := by
      have := congrArg State.pc hs_svc_eq
      simpa [stripS, State.setFs] using this.symm.trans hpc_svc'
    have hrun_svc : s_svc.status = .Running := by
      have := congrArg State.status hs_svc_eq
      simpa [stripS, State.setFs] using this.symm.trans hrun_svc'
    have hx8_svc : s_svc.readReg64 .x8 = 94#64 := by
      have : s_svc'.readReg64 .x8 = s_svc.readReg64 .x8 := by rw [hs_svc_eq]; rfl
      exact this.symm.trans hx8_svc'
    have hx0_svc : s_svc.readReg64 .x0 = ((sr.readReg64 .x0).setWidth 32).signExtend 64 := by
      have h1 : s_svc'.readReg64 .x0 = s_svc.readReg64 .x0 := by rw [hs_svc_eq]; rfl
      have h2 : sr'.readReg32 .x0 = (sr.readReg64 .x0).setWidth 32 := rfl
      rw [← h1, hx0_svc', h2]
    have htr_svc : s_svc.trace = sr.trace := by
      have h1 : s_svc'.trace = s_svc.trace := by rw [hs_svc_eq]; rfl
      have h2 : sr'.trace = sr.trace := rfl
      exact h1.symm.trans (htr_svc'.trans h2)
    have hL_svc_st : P_rx.CodeLoaded s_svc'.mem := codeLoaded_withSvc_iff.mp (hsteps_st.codeLoaded hL_st)
    have hL_svc_rx : P_rx.CodeLoaded s_svc.mem := by
      rw [hs_svc_eq] at hL_svc_st
      exact codeLoaded_unstrip_f3 hL_svc_st
    have hfetch_rx : P_rx.fetch (L.sysExitAddr + 12#64) = some (.system false 0#16) :=
      MuslExitCode.fetch_sysExit_svc hc.muslExit
    have hfm_rx : P_rx.fetchMem s_svc.mem (L.sysExitAddr + 12#64) =
        some (.system false 0#16) :=
      Program.fetchMem_of_fetch hL_svc_rx hfetch_rx
    have hkeep_sys : progKeep P_rx (L.sysExitAddr + 12#64) = true := by
      unfold Program.fetch Program.readWordOff at hfetch_rx
      rw [hc.no_hooks (L.sysExitAddr + 12#64)] at hfetch_rx
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfetch_rx
      split at hfetch_rx
      · simp at hfetch_rx
      · generalize hd : P_rx.code.drop (L.sysExitAddr + 12#64 - P_rx.base).toNat = bs at hfetch_rx
        match bs with
        | b0 :: b1 :: b2 :: b3 :: rest =>
          have hlen := congrArg List.length hd
          simp only [List.length_drop, List.length_cons] at hlen
          simp only [progKeep, decide_eq_true_eq]
          omega
        | [] | [_] | [_, _] | [_, _, _] => simp at hfetch_rx
    have hfm_P : P.fetchMem s_svc.mem s_svc.pc = some (.system false 0#16) := by
      rw [hpc_svc]
      have hext_P : P.externAt? (L.sysExitAddr + 12#64) = none :=
        Option.isNone_iff_eq_none.mp (hHookFree _ hkeep_sys)
      have hext_rx : P_rx.externAt? (L.sysExitAddr + 12#64) = none :=
        hc.no_hooks _
      simp only [Program.fetchMem, hext_P, hext_rx] at hfm_rx ⊢
      exact hfm_rx
    let sx := P.evalInst (.system false 0#16) s_svc
    have hstep1 : Step P s_svc sx := Step.exec hrun_svc hfm_P
    have hsvc_exit : P.svc s_svc = execExit s_svc := by
      rw [hsvc]
      dsimp only [Syscall.standard, Syscall.dispatch]
      rw [hx8_svc]
      change (match Syscall.standardTable.find? (·.1 == 94#64) with
        | some (_, h) => h s_svc
        | none => s_svc.setStatus (.Exception "unmodeled syscall (svc)")) = execExit s_svc
      rw [show Syscall.standardTable.find? (·.1 == 94#64) = some (94#64, execExit) from rfl]
    refine ⟨sx, hsteps_P.trans (Steps.step hstep1 (Steps.refl _)), ?_, ?_, ?_⟩
    · simp only [sx, Program.evalInst, execInstWithSvc, evalSvc,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rw [hsvc_exit]
      dsimp only [execExit, State.setStatus]
      rw [hx0_svc]
    · simp only [sx, Program.evalInst, execInstWithSvc, evalSvc,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rw [hsvc_exit]; exact hfs_svc
    · simp only [sx, Program.evalInst, execInstWithSvc, evalSvc,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rw [hsvc_exit]; exact htr_svc
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Construct `HarnessSpec.MuslHarnessNeedLocksN 80 L.libcAddr` on `elf` for any `Syscall.standard`
    program `P` that has no hooks inside `seg[5]` (`progKeep (L.rxProgram elf)`). -/
theorem f3MuslHarnessNeedLocks80_of_layout {L : StdBinaryLayout} {elf : ElfImage} {P : Program}
    (hmatch : f3MatchesImage L elf = true)
    (hc : F3StartupCode (L.rxProgram elf) L)
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep (L.rxProgram elf) pc = true → (P.externAt? pc).isNone = true) :
    MuslHarnessNeedLocksN 80 L.libcAddr elf P L.cMainAddr
      (StdMuslExitGlobalsNoNeedLocks L 0#8)
      (fun i => CliInputsOk i ∧ InputsLoadable i)
      (f3StartupMainPreNeedLocks L elf) := by
  intro _hE i ⟨hi, hl⟩
  let inputs0 := f3EmptyFsInputs i
  have hvalid0 : inputs0.Valid := f3EmptyFsInputs_valid hi
  obtain ⟨hwf, hentry_eq, hphdr_eq, hphnum_eq, hbrk_eq, ⟨hbrk_lo, hbrk_hi⟩, _⟩ :=
    f3MatchesImage_segments hmatch
  have hbrk_sbm : elf.brkStart.toNat ≤ STACK_BASE_MIN := by
    rw [hbrk_eq]; unfold STACK_BASE_MIN; omega
  obtain ⟨s0_0, hload0, hinfo0⟩ := loadState_ok_initialStackInfo elf hwf hvalid0 hbrk_sbm
  obtain ⟨s0, hload, hs0_0_eq, hfs0, htr0, hmem0, hbrk0, hbrkS0, hphys0⟩ :=
    loadState_f3CliInputs_of_empty hl hload0
  let P_rx := L.rxProgram elf
  let P_st := P_rx.withSvc f3SetTidOnlySvc
  let s0' := stripS (progKeep P_rx) s0_0
  have hinfo' : InitialStackInfo elf inputs0 s0' := initialStackInfo_strip (progKeep P_rx) hinfo0
  have hL0_rx : P_rx.CodeLoaded s0_0.mem := f3MatchesImage_codeLoaded hmatch hload0
  have hL0_st : P_st.CodeLoaded s0'.mem := codeLoaded_withSvc_iff.mpr (strip_codeLoaded_f3 hL0_rx)
  have lf : F3LayoutImageFacts L := extractF3LayoutImageFacts hmatch hload0
  obtain ⟨hc_start, hc_startC, hc_lsm, hc_init, hdummy1, hc_stls, hc_ctls, hc_itp, hset_tp,
    hc_st2, hc_lsi, hinitFn, hc_doInit, hc_getaux, hc_det, hc_ilse, hc_enlse⟩ :=
    unpack_f3_extra_chunks hc.extra
  let sl := StackLayout.of elf inputs0
  have hinp0_eq : inputs0 = processInputs ("libsignal-cli" :: i.argv) [] [] [] := rfl
  have hlay := loadState_cli_layout elf i.argv [] [] [] hwf
    (by
      have hbf := hvalid0.stack.base_floor
      have hsb_eq : inputs0.init.stackTop.toNat - inputs0.init.stackSize =
          defaultStackTop.toNat - cliStackSize := rfl
      omega)
    (fun a ha => (hi.1 a ha).2) hi.2 (by simp) (by simp)
  have hs0_raw : s0_0 = elf.rawState inputs0 := by
    have hlay1 : elf.loadState inputs0 = .ok (elf.rawState inputs0) := hinp0_eq ▸ hlay.1
    exact Except.ok.inj (hload0.symm.trans hlay1)
  have hsp0_init : sl.sp0.toNat = sp0 (cliStrs i.argv) := by
    have hsp_bv : sl.sp0 = BitVec.ofNat 64 (sp0 (cliStrs i.argv)) := by
      rw [← hinfo0.s0_sp, hs0_raw]; exact hinp0_eq ▸ hlay.2.1
    rw [hsp_bv, toNat_sp0]
  have hhr8 : inputs0.init.stackTop.toNat - inputs0.init.stackSize + 8371824 ≤ sl.sp0.toNat := by
    have hlo : stackBase + 8371824 ≤ sp0 (cliStrs i.argv) := hlay.2.2.2.1
    have hsb_eq : inputs0.init.stackTop.toNat - inputs0.init.stackSize = stackBase := by
      unfold stackBase cliStackSize; rfl
    omega
  have hsp0_16 := hinfo'.sp0_align16
  have hsp0_ge : 8371824 ≤ sl.sp0.toNat := by
    omega
  have hscan := auxvScan38_mkAuxvEntries elf hvalid0.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo'.auxvEntries_eq] at hscan
  have hwf_aux := mkAuxvEntries_wf elf hvalid0.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo'.auxvEntries_eq] at hwf_aux
  have hfind_aux := mkAuxvEntries_find? elf hvalid0.auxv sl.platformAddr sl.randomAddr sl.execfnAddr []
  rw [List.append_nil, ← hinfo'.auxvEntries_eq] at hfind_aux
  have hphent_eq := (wellFormed_segments_bounds hwf).1
  have hbrk_mod : elf.brkStart.toNat % 4096 = 0 := (wellFormed_segments_bounds hwf).2.1
  have hTlsSpec : subroutine_ok P_st L.staticInitTlsAddr (f3StaticInitTlsSpec L) :=
    f3StaticInitTls_setTidOnly_ok
      (hasInstrs_withSvc_f3 hc_stls) (hasInstrs_withSvc_f3 hc_ctls)
      (hasInstrs_withSvc_f3 hc_itp) (hasCode_withSvc_f3 hset_tp)
      hc.memOpsSetTid rfl lf.checkPhdr lf.phdr_end lf.builtinTls_al lf.mainTls_nz
  let sysinfoVal := (auxvScan38 sl.auxvEntries).getD 32 0#64
  have hTls : ∀ (st : State) (FTls : SepProp), st.pc = L.staticInitTlsAddr → st.status = .Running →
      st.sp = sl.sp0 - 448#64 → st.readReg64 .x0 = sl.sp0 - 352#64 →
      st.readReg64 .lr = L.initLibcAddr + 268#64 → StdStatePreserved s0' st →
      SepWP P_st (L.initLibcAddr + 268#64) st
        ((((sl.sp0 - 352#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
          (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ f3PreTlsSep L sl.sp0) ∗ FTls)
        (fun st' Q => st'.pc = L.initLibcAddr + 268#64 ∧ st'.status = .Running ∧
          st'.sp = sl.sp0 - 448#64 ∧
          (st'.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧ StdTlsFieldsPreserved st st') ∧
          (Q ⊢ (((sl.sp0 - 352#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
            (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ f3PostTlsSep L sl.sp0 sysinfoVal) ∗ FTls)) := by
    intro st FTls hpct hrunt hspt hx0t hlrt _
    have hsp_al_t : st.spAligned = true := by
      simp only [State.spAligned, hspt, beq_iff_eq]
      have hb : sl.sp0 &&& 15#64 = 0#64 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]; change sl.sp0.toNat &&& 15 = 0
        rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; exact hsp0_16
      bv_bits
    have hsp_60 : st.sp - 96#64 = sl.sp0 - 544#64 := by rw [hspt]; bv_lin
    refine SepWP.call_subroutine_frame (ret_pc := L.initLibcAddr + 268#64) hTlsSpec
      (x := (sl.sp0 - 352#64, auxvScan38 sl.auxvEntries, 0#8, sysinfoVal)) (F := FTls)
      hpct hrunt hsp_al_t hlrt ?_
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      fun st' hpct' hrunt' hspt' _ => ?_
    · dsimp only [f3StaticInitTlsSpec, f3PreTlsSep]
      rw [hsp_60, pure_sepConj_of_true ⟨hx0t, hphdr_eq ▸ hscan.2.1,
        hphent_eq ▸ hscan.2.2.1, hphnum_eq ▸ hscan.2.2.2.1⟩]
      sep_entail
    · dsimp only [f3StaticInitTlsSpec]
      rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨htp', htls'⟩
      have hspt'' : st'.sp = sl.sp0 - 448#64 := hspt'.trans hspt
      have hsp'_60 : st'.sp - 96#64 = sl.sp0 - 544#64 := by rw [hspt'']; bv_lin
      apply SepWP.done hpct' hrunt'
      refine ⟨hpct', hrunt', hspt'', ⟨htp', htls'⟩, ?_⟩
      dsimp only [f3PostTlsSep]; rw [htp', hsp'_60]; sep_entail
  have hLsiSpec : subroutine_ok P_st L.libcStartInitAddr (stdLibcStartInitSpec L) :=
    libcStartInit_ok P_st L (hasInstrs_withSvc_f3 hc_lsi)
      (initFn_ok P_st L.initFnAddr (hasWords_withSvc_f3 hinitFn))
      (initLse_ok P_st L (hasInstrs_withSvc_f3 hc_ilse)
        (detectAndInitialize_ok P_st L (hasInstrs_withSvc_f3 hc_det)
          (getauxval_found_ok P_st L (hasInstrs_withSvc_f3 hc_getaux)))
        (rustEnableLse_ok P_st L (hasInstrs_withSvc_f3 hc_enlse)))
      (doInit_ok P_st L (hasInstrs_withSvc_f3 hc_doInit))
  have hmr_init : memRegion (sl.sp0 - 8371824#64) 8371824 =
      memRegion (sl.sp0 - 8371824#64) 8371280 ∗ memRegion (sl.sp0 - 544#64) 96 ∗
      memRegion (sl.sp0 - 448#64) 448 := by
    have s1 := memRegion_split_le (sl.sp0 - 8371824#64) 8371280 8371824 (by decide) (by decide)
    have s2 := memRegion_split_le (sl.sp0 - 544#64) 96 544 (by decide) (by decide)
    rw [show sl.sp0 - 8371824#64 + BitVec.ofNat 64 8371280 = sl.sp0 - 544#64 by bv_lin] at s1
    rw [show sl.sp0 - 544#64 + BitVec.ofNat 64 96 = sl.sp0 - 448#64 by bv_lin] at s2
    rw [s1, show (8371824 - 8371280 : Nat) = 544 from rfl, s2, show (544 - 96 : Nat) = 448 from rfl]
  have hmr_st2 : memRegion (sl.sp0 - 8371824#64) 8371280 ∗ memRegion (sl.sp0 - 544#64) 96 ∗
      memRegion (sl.sp0 - 448#64) 448 =
      stackAt (sl.sp0 - 304#64) 8371520 ∗ stackFrameAt sl.sp0 304 := by
    rw [← hmr_init, ← stackAt_eq_stackFrameAt sl.sp0 304]
    have s1 := memRegion_split_le (sl.sp0 - 8371824#64) 8371520 8371824 (by decide) (by decide)
    have e1 : sl.sp0 - 8371824#64 + BitVec.ofNat 64 8371520 = sl.sp0 - 304#64 := by bv_lin
    have e2 : (sl.sp0 - 304#64) - BitVec.ofNat 64 8371520 = sl.sp0 - 8371824#64 := by bv_lin
    dsimp only [stackAt]; rw [e1] at s1; rw [e2]; exact s1
  have hwp_startup : SepWP P_st L.cMainAddr s0' (f3InitAllSep L elf inputs0)
      (fun s_cm P_out =>
        (s_cm.sp = sl.sp0 - 48#64 ∧ s_cm.spAligned = true ∧
          cliMainStk ≤ s_cm.sp.toNat ∧
          s_cm.readReg64 .x30 = L.libcStartMainStage2Addr + 56#64 ∧
          s_cm.readReg64 .x0 = BitVec.ofNat 64 inputs0.argv.length ∧
          s_cm.readReg64 .x1 = sl.argvTableAddr ∧
          s_cm.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧
          StdTlsFieldsPreserved s0' s_cm) ∧
        (P_out ⊢ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
          argvAtRO sl.argvTableAddr inputs0.argv ∗
          stackAt (sl.sp0 - 48#64) cliMainStk ∗
          StdExtraRo L ∗ StdExtraRw L ∗
          ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗
          ((L.libcAddr + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
          ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
          MallocngAuxvAt sl.auxvTableAddr ∗
          f3StartupResidual L elf i ∗
          StdMuslExitGlobalsNoNeedLocks L 0#8)) := by
    apply SepWP.cut (mid := L.libcStartMainStage2Addr)
    refine SepWP.weaken_pre (P' := (memRegion (sl.sp0 - 448#64) 448 ∗ Stage1GlobalsPre L ∗
        StdGotGlobals L ∗ (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs0.argv.length) ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ f3PreTlsSep L sl.sp0) ∗ _) (by
      rw [f3InitAllSep]
      dsimp only [f3PreTlsSep, F3RoConstants, F3InitGlobals, Stage1GlobalsPre,
        StdLibcGlobals, F3DataGlobals, StdLibcTlsZero,
        StdBinaryLayout.libcAtoms, f3DataNoStderrAtoms, rwAtomListSep, RwAtom.toSepProp]
      rw [rwAtomListSep_f3BssAtoms L, hmr_init]
      sep_frame) ?_
    apply SepWP.mono
    case h =>
      exact muslStage1 hinfo' hvalid0
        (hasInstrs_withSvc_f3 hc_start) (hasInstrs_withSvc_f3 hc_startC)
        (hasInstrs_withSvc_f3 hc_lsm) (hasInstrs_withSvc_f3 hc_init)
        (hasWords_withSvc_f3 hdummy1) hc.memOpsSetTid hTls
        hentry_eq hc.ne_memset hc.ne_tls hc.ne_stage2
    case hoom => exact fun _ _ _ ho => ho
    case himp =>
    rintro s_st2 _ hpc_st2 hrun_st2 ⟨⟨hsp_st2, hx0_st2, hx1_st2, hx2_st2,
      st, st', hstd0t, ⟨htp_t', htlst⟩, hstdtf⟩, hent_st2⟩
    apply SepWP.weaken_pre hent_st2
    have hsp_al_st2 : s_st2.spAligned = true := by
      simp only [State.spAligned, hsp_st2, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]; change sl.sp0.toNat &&& 15 = 0
      rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; exact hsp0_16
    have htp_st2 : s_st2.tpidrEl0 = L.builtinTlsAddr + 200#64 := hstdtf.2.2.1.trans htp_t'
    have htlf_0_st2 : StdTlsFieldsPreserved s0' s_st2 :=
      (hstd0t.toTlsFields.trans htlst).trans hstdtf.toTlsFields
    have hm_st2 : memRegion (sl.sp0 - 448#64) 448 ∗ memRegion (sl.sp0 - 544#64) 96 ∗
        memRegion (sl.sp0 - 8371824#64) 8371280 =
        stackAt (sl.sp0 - 304#64) 8371520 ∗ stackFrameAt sl.sp0 304 := by
      rw [← hmr_st2]; sep_ac_rfl
    refine SepWP.weaken_pre (P' := (stdInitGlobalsPre L sl.auxvTableAddr sl.auxvEntries ∗
        stackFrameAt sl.sp0 304) ∗ _) (by
      dsimp only [f3PostTlsSep, Stage1GlobalsPost, StdGotGlobals, StdInitFiniGlobals,
        stdInitGlobalsPre, StdBinaryLayout.gotAtoms, StdBinaryLayout.initFiniAtoms,
        rwAtomListSep, RwAtom.toSepProp]
      refine Entails.trans (Q := (memRegion (sl.sp0 - 448#64) 448 ∗
        memRegion (sl.sp0 - 544#64) 96 ∗ memRegion (sl.sp0 - 8371824#64) 8371280) ∗ _)
        (by sep_frame) ?_
      rw [hm_st2]; sep_frame) ?_
    refine stage2_to_cMain P_st L (hasInstrs_withSvc_f3 hc_st2) hLsiSpec
      hpc_st2 hrun_st2 hsp_st2 hsp_al_st2
      hx0_st2 hx1_st2 hx2_st2 hinfo'.argc_bounds.2.1 hvalid0.auxv.hwcap_fp_asimd
      (fun t v hm => (hwf_aux.2.2 t v hm).1) hfind_aux.2.2.2.2.2.2.2.2.2.2.1
      hfind_aux.2.2.2.2.2.2.2.2.2.2.2.2.2.1 lf.initArray_bnd
      fun s_cm hpc_cm hrun_cm hsp_cm hsp_al_cm hlr_cm hx0_cm hx1_cm _ hstd_cm => ?_
    dsimp only [stdInitGlobalsPost]
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro cacheVal
    have hstk_cm : stackAt (sl.sp0 - 304#64) 8371520 ∗ stackFrameAt (sl.sp0 - 48#64) 256 =
        stackAt (sl.sp0 - 48#64) cliMainStk := by
      rw [← stackAt_eq_stackFrameAt (sl.sp0 - 48#64) 256]
      have c1 := memRegion_split_le (sl.sp0 - 8371824#64) 8371520 cliMainStk (by decide) (by decide)
      rw [show sl.sp0 - 8371824#64 + BitVec.ofNat 64 8371520 = sl.sp0 - 304#64 by bv_lin] at c1
      dsimp only [stackAt, cliMainStk]
      rw [show (sl.sp0 - 304#64) - 8371520#64 = sl.sp0 - 8371824#64 by bv_lin,
        show (sl.sp0 - 48#64) - 256#64 = sl.sp0 - 304#64 by bv_lin,
        show (sl.sp0 - 48#64) - 8371776#64 = sl.sp0 - 8371824#64 by bv_lin]
      exact c1.symm
    have htp_cm : s_cm.tpidrEl0 = L.builtinTlsAddr + 200#64 := hstd_cm.2.2.1.trans htp_st2
    have htlf_0_cm : StdTlsFieldsPreserved s0' s_cm := htlf_0_st2.trans hstd_cm.toTlsFields
    have hsp_cm_ge : cliMainStk ≤ s_cm.sp.toNat := by
      rw [hsp_cm, BitVec.toNat_sub_of_le (by change 48 ≤ sl.sp0.toNat; omega)]
      change 8371776 ≤ sl.sp0.toNat - 48; omega
    have hargv_dup := argvTable_dup_argvAtRO hinfo0 hvalid0.args
    have hauxv_ent := auxv_entails_mallocngAuxvAt hinfo0 hvalid0
    apply SepWP.done hpc_cm hrun_cm
    refine ⟨⟨hsp_cm, hsp_al_cm, hsp_cm_ge, hlr_cm, hx0_cm, hx1_cm, htp_cm, htlf_0_cm⟩, ?_⟩
    dsimp only [StdMuslExitGlobalsNoNeedLocks]
    refine Entails.trans (Q := ((stackAt (sl.sp0 - 304#64) 8371520 ∗
        stackFrameAt (sl.sp0 - 48#64) 256) ∗
      ((sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes)) ∗
      ((sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.randomAddr ↦ₛ inputs0.init.auxv.randomBytes)) ∗ _))
      (by sep_frame) ?_
    rw [hstk_cm]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono hargv_dup (sepConj_mono_left hauxv_ent))) ?_
    unfold f3StartupResidual
    refine Entails.trans (Q := ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
        argvAtRO sl.argvTableAddr inputs0.argv ∗
        stackAt (sl.sp0 - 48#64) cliMainStk ∗
        StdExtraRo L ∗ StdExtraRw L ∗
        ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗
        ((L.libcAddr + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
        MallocngAuxvAt sl.auxvTableAddr ∗
        ((L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 32#64) ↦₆₄ 0#64) ∗
          ((L.gotAddr + 40#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 96#64) ↦₆₄ (L.finiArrayAddr + 8#64)) ∗
          ((L.gotAddr + 104#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ 0#8) ∗
          (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
          (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗
          (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L) ∗ _)
      (by sep_frame) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (Entails.sepExists_right (Q := fun R_unused => R_unused) _ (Entails.refl _)))))))))))) ?_
    sep_entail
  have hm0_0 : s0_0.mem ⊨ f3InitAllSep L elf inputs0 ∗ emp := by
    rw [sepConj_emp]; exact s0_satisfies_f3InitAllSep hmatch hload0 hinfo0 hvalid0 hhr8
  obtain ⟨R_view, hs0'_sat, hunstrip⟩ := strip_frame (progKeep P_rx) hm0_0
  obtain ⟨s_cm', hsteps_st, ⟨hpc_cm', hrun_cm', P_out, hm_out',
    ⟨hsp_cm', hsp_al_cm', hsp_ge_cm', hlr_cm', hx0_cm', hx1_cm', htp_cm', htlf_cm'⟩,
    hent_out⟩ | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp_startup hs0'_sat hL0_st
  · obtain ⟨sm, hsteps_P, hsm_eq, hfs_sm, hphys_sm, hperm_sm⟩ :=
      steps_lift_setTidOnly hc.no_hooks hsvc hHookFree hsteps_st hrun_cm' s0 (initFsState inputs0)
        (congrArg (stripS (progKeep P_rx)) hs0_0_eq)
    have hpc_sm : sm.pc = L.cMainAddr := by
      have := congrArg State.pc hsm_eq; simpa [stripS, State.setFs] using this.symm.trans hpc_cm'
    have hrun_sm : sm.status = .Running := by
      have := congrArg State.status hsm_eq
      simpa [stripS, State.setFs] using this.symm.trans hrun_cm'
    have hsp_sm : sm.sp = sl.sp0 - 48#64 := by
      have := congrArg State.sp hsm_eq; simpa [stripS, State.setFs] using this.symm.trans hsp_cm'
    have hal_sm : sm.spAligned = true := by
      simp only [State.spAligned, hsp_sm] at hsp_al_cm' ⊢
      rwa [← hsp_cm']
    have hlr_sm : sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 := by
      have : s_cm'.readReg64 .lr = sm.readReg64 .lr := by rw [hsm_eq]; rfl
      exact this.symm.trans hlr_cm'
    have hx0_sm64 : sm.readReg64 .x0 = BitVec.ofNat 64 inputs0.argv.length := by
      have : s_cm'.readReg64 .x0 = sm.readReg64 .x0 := by rw [hsm_eq]; rfl
      exact this.symm.trans hx0_cm'
    have hx0_sm32 : (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) := by
      rw [hx0_sm64]
      have hlen_argv : inputs0.argv.length = i.argv.length + 1 := by
        simp [inputs0, f3EmptyFsInputs, cliInputs, processInputs]
      rw [hlen_argv]
      apply BitVec.eq_of_toNat_eq; simp
    have hx1_sm : sm.readReg64 .x1 = sl.argvTableAddr := by
      have : s_cm'.readReg64 .x1 = sm.readReg64 .x1 := by rw [hsm_eq]; rfl
      exact this.symm.trans hx1_cm'
    have htp_sm : sm.tpidrEl0 = L.builtinTlsAddr + 200#64 := by
      have := congrArg State.tpidrEl0 hsm_eq
      simpa [stripS, State.setFs] using this.symm.trans htp_cm'
    have htr_sm : sm.trace = s0.trace := by
      have h1 : s_cm'.trace = sm.trace := by rw [hsm_eq]; rfl
      have h2 : s0'.trace = s0.trace := by simp [s0', stripS, hs0_0_eq, State.setFs]
      exact h1.symm.trans (htlf_cm'.2.1.trans h2)
    have hbrk_sm : sm.brk = L.brkStart := by
      have h1 : s_cm'.brk = sm.brk := by rw [hsm_eq]; rfl
      exact h1.symm.trans (htlf_cm'.2.2.2.1.trans (hinfo'.s0_brk.trans hbrk_eq))
    have hbrkS_sm : sm.brkStart = L.brkStart := by
      have h1 : s_cm'.brkStart = sm.brkStart := by rw [hsm_eq]; rfl
      exact h1.symm.trans (htlf_cm'.2.2.2.2.1.trans (hinfo'.s0_brkStart.trans hbrk_eq))
    have hbrk_s0 : s0.brk = L.brkStart := hbrk0.trans (hinfo0.s0_brk.trans hbrk_eq)
    have hbrkS_s0 : s0.brkStart = L.brkStart := hbrkS0.trans (hinfo0.s0_brkStart.trans hbrk_eq)
    have hvm_sm : StartupVmPreserved s0 sm :=
      ⟨hbrkS_sm.trans hbrkS_s0.symm, hbrk_sm.trans hbrk_s0.symm, hphys_sm, hperm_sm⟩
    have hL_sm_st : P_rx.CodeLoaded s_cm'.mem := codeLoaded_withSvc_iff.mp (hsteps_st.codeLoaded hL0_st)
    have hL_sm_rx : P_rx.CodeLoaded sm.mem := by
      rw [hsm_eq] at hL_sm_st
      exact codeLoaded_unstrip_f3 hL_sm_st
    have hm_sm_stripped : stripExecOutside (progKeep P_rx) sm.mem ⊨ P_out ∗ R_view := by
      have hmem_eq : s_cm'.mem = stripExecOutside (progKeep P_rx) sm.mem := by rw [hsm_eq]; rfl
      rwa [← hmem_eq]
    have hm_sm_unstripped : sm.mem ⊨ P_out ∗ emp :=
      hunstrip (fun a => (hperm_sm a).trans (by rw [hmem0])) hm_sm_stripped
    rw [sepConj_emp] at hm_sm_unstripped
    have hm_sm_post := Satisfies.mono hent_out hm_sm_unstripped
    have hbrkWf_sm : MallocngBrkStartWf sm.brkStart := by
      unfold MallocngBrkStartWf MMAP_MIN_ADDR PAGE_SIZE
      rw [hbrkS_sm, ← hbrk_eq]
      exact ⟨by rw [hbrk_eq]; exact hbrk_lo, hbrk_mod, by rw [hbrk_eq]; omega⟩
    have hsl_eq : StackLayout.of elf (cliInputs i) = sl := rfl
    have hargv_eq : inputs0.argv = ("libsignal-cli" :: i.argv).map bytesOfString := rfl
    have hm_sm_pre : sm.mem ⊨ f3StartupMainPreNeedLocks L elf i sm ∗
        StdMuslExitGlobalsNoNeedLocks L 0#8 := by
      unfold f3StartupMainPreNeedLocks f3StartupMainPre
      rw [hsl_eq, hx1_sm, htp_sm]
      rw [← hargv_eq] at *
      have hpure_sm :
          P_rx.CodeLoaded sm.mem ∧
          (∃ sLoad, elf.loadState (cliProcessInputs i) = .ok sLoad ∧ StartupVmPreserved sLoad sm) ∧
          cliMainStk ≤ sm.sp.toNat ∧
          sm.sp = sl.sp0 - 48#64 ∧
          sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 ∧
          L.builtinTlsAddr + 200#64 = L.builtinTlsAddr + 200#64 ∧
          164 ≤ (L.builtinTlsAddr + 200#64).toNat ∧
          (L.builtinTlsAddr + 200#64).toNat ≤ 2 ^ 48 ∧
          MallocngBrkStartWf sm.brkStart ∧
          sm.brk = sm.brkStart ∧
          sm.brkStart = L.brkStart :=
        ⟨hL_sm_rx, ⟨s0, hload, hvm_sm⟩, hsp_sm ▸ hsp_cm' ▸ hsp_ge_cm', hsp_sm, hlr_sm, rfl,
          lf.tp_bounds.1, lf.tp_bounds.2, hbrkWf_sm, hbrk_sm.trans hbrkS_sm.symm, hbrkS_sm⟩
      rw [pure_sepConj_of_true hpure_sm, hsp_sm]
      exact Satisfies.mono (by sep_entail) hm_sm_post
    refine ⟨s0, sm, hload, hsteps_P, hpc_sm, hrun_sm, hal_sm, hfs_sm, htr_sm, hx0_sm32, hm_sm_pre,
      fun sr hsteps1 hret hm_sr => ?_⟩
    have hm_reord : sr.mem ⊨ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
        (stackAt sm.sp 80 ∗ StdMuslExitGlobalsNoNeedLocks L 0#8 ∗ anyHeap) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_sr
    have hm_frz := Satisfies.of_bupd_frame_left (pointsTo8_freeze_ro (L.libcAddr + 3#64) 0#8) hm_reord
    have hm_exit : sr.mem ⊨ stackAt sm.sp 80 ∗ StdMuslExitGlobals L 0#8 ∗ anyHeap := by
      refine Satisfies.mono ?_ hm_frz
      dsimp only [StdMuslExitGlobalsNoNeedLocks, StdMuslExitGlobals]
      sep_entail
    exact f3Exit80_of_layout lf hc hsvc hHookFree (initFsState inputs0)
      (codeLoaded_steps_any hsteps1 hL_sm_rx) hlr_sm hal_sm hret hm_exit
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Construct `MuslHarnessN 80` on `elf` (with `libc.need_locks` pre-frozen inside
    `StdMuslExitGlobals L 0#8`) from `f3MuslHarnessNeedLocks80_of_layout`. -/
theorem f3MuslHarness80_of_layout {L : StdBinaryLayout} {elf : ElfImage} {P : Program}
    (hmatch : f3MatchesImage L elf = true)
    (hc : F3StartupCode (L.rxProgram elf) L)
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep (L.rxProgram elf) pc = true → (P.externAt? pc).isNone = true) :
    MuslHarnessN 80 elf P L.cMainAddr
      (StdMuslExitGlobals L 0#8)
      (fun i => CliInputsOk i ∧ InputsLoadable i)
      (f3StartupMainPre L elf) := by
  intro hE i hok
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hm_nl, _⟩ :=
    f3MuslHarnessNeedLocks80_of_layout hmatch hc hsvc hHookFree hE i hok
  unfold f3StartupMainPreNeedLocks at hm_nl
  rw [sepConj_assoc] at hm_nl
  have hm_reord : sm.mem ⊨ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
      (f3StartupMainPre L elf i sm ∗ StdMuslExitGlobalsNoNeedLocks L 0#8) := hm_nl
  have hm_frz := Satisfies.of_bupd_frame_left (pointsTo8_freeze_ro (L.libcAddr + 3#64) 0#8) hm_reord
  have hm_pre : sm.mem ⊨ f3StartupMainPre L elf i sm ∗ StdMuslExitGlobals L 0#8 := by
    refine Satisfies.mono ?_ hm_frz
    dsimp only [StdMuslExitGlobalsNoNeedLocks, StdMuslExitGlobals]
    sep_entail
  have lf : F3LayoutImageFacts L := extractF3LayoutImageFacts hmatch hload
  have hpure := hm_pre
  unfold f3StartupMainPre at hpure
  dsimp only at hpure
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpure
  have hL_sm_rx : (L.rxProgram elf).CodeLoaded sm.mem := hpure.1.1
  have hlr_sm : sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 := hpure.1.2.2.2.2.1
  refine ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hm_pre,
    fun sr hsteps1 hret hm_sr => ?_⟩
  have hm_exit : sr.mem ⊨ stackAt sm.sp 80 ∗ StdMuslExitGlobals L 0#8 ∗ anyHeap :=
    Satisfies.mono (by sep_entail) hm_sr
  exact f3Exit80_of_layout lf hc hsvc hHookFree (initFsState (f3EmptyFsInputs i))
    (codeLoaded_steps_any hsteps1 hL_sm_rx) hlr_sm hal hret hm_exit

end LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup
