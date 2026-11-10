/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.SignalSessionIoPlacedObj
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.FinishGrow
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic Fetch and Pure-Segment Infrastructure for `signal-session-io`

Placement typeclass (`CliIoPlacement`), symbol constants (`cliIo*Sym`), block-scoped pure-segment
lifter (`sepWP_seg_cliIo_block_pure`), `cliIoWithCodeLoaded` wrappers, and generated instruction
fetches for blocks `0..4` of `CryptoVerification.signalSessionIoMultiLib`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.Sym

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  SameCpuState blockProgram_rebase_allInstrs_not_isSvc0
)
open VerifiedLibraries.RustStd.Io (SameCpuOracleState)

/-! ## 1. Placement Typeclass & Symbol Constants -/

/-- Placement typeclass for `CryptoVerification.signalSessionIoMultiLib`. -/
class CliIoPlacement where
  mpl : MultiPlacement
  placeable : signalSessionIoMultiLib.Placeable mpl

abbrev cliIoMpl [CliIoPlacement] : MultiPlacement := CliIoPlacement.mpl

/-- `P` installs no extern hooks inside code block `j` of `signalSessionIoMultiLib`. -/
def CliIoBlockNoExtern (mpl : MultiPlacement) (P : Program) (j : Nat) : Prop :=
  ∀ off : Nat, off < (signalSessionIoMultiLib.blockLib j).text.code.length →
    P.externAt? (mpl.base j + BitVec.ofNat 64 off) = none

theorem CliIoBlockNoExtern.of_no_extern {mpl : MultiPlacement} {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (j : Nat) :
    CliIoBlockNoExtern mpl P j :=
  fun _ _ => hext _

/-- Block `0` export (`436` B / `109` insns): `signal_session_io::read_stdin`. -/
abbrev cliIoReadStdinSym : String := "libsignal_cli_io::read_stdin"

/-- Block `1` export (`304` B / `76` insns): `signal_session_io::write_file`. -/
abbrev cliIoWriteFileSym : String := "libsignal_cli_io::write_file"

/-- Block `2` export (`184` B / `46` insns): `signal_session_io::write_stdout`. -/
abbrev cliIoWriteStdoutSym : String := "libsignal_cli_io::write_stdout"

/-- Block `3` export (`572` B / `143` insns): `signal_session_io::read_file`. -/
abbrev cliIoReadFileSym : String := "libsignal_cli_io::read_file"

/-- Block `4` internal helper (`168` B / `42` insns): `<alloc::raw_vec::RawVecInner>::finish_grow`. -/
abbrev cliIoFinishGrowSym : String := "<alloc::raw_vec::RawVecInner>::finish_grow"

abbrev cliIoRustAllocSym : String := "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev cliIoRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev cliIoRustReallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"

abbrev cliIoRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev cliIoHandleErrorSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

abbrev cliIoErrnoLocationSym : String := "__errno_location"

abbrev cliIoCloseSym : String := "close"

abbrev cliIoMemcpySym : String := "memcpy"

abbrev cliIoOpenSym : String := "open"

abbrev cliIoReadSym : String := "read"

abbrev cliIoWriteSym : String := "write"

theorem cliIoResolve_eq_base {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    (j : Nat) (sym : String) (hj : j < signalSessionIoMultiLib.blocks.length)
    (hl : lookup sym signalSessionIoMultiLib.blocks[j].symbols = some 0) :
    signalSessionIoMultiLib.resolve mpl sym = mpl.base j := by
  have hblk := lookupBlockSym_of_lookup hj hpl.symbols_nodup hl
  simp [MultiPlacedLib.resolve, hblk]

/-! ## 2. Block-Scoped Pure-Segment Lifter for `signalSessionIoMultiLib` -/

private theorem strip_codeLoaded_cliIo {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_cliIo (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_cliIo {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_cliIo_block {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_cliIo hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_cliIo hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_cliIo R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              have hk := (ProofLib.strip_perm_x_imp hx0).2
              simpa using hk
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest⟩

/-- Run a pure (non-syscall) segment of `signalSessionIoMultiLib` block `j` up to `mid` from any
    `P : Program` with `CliIoBlockNoExtern mpl P j`, refreshing `CodeLoaded` and supplying
    `SameCpuOracleState`, `NonSyscallPreserved`, and `sm.symtab = s.symtab`. -/
theorem sepWP_seg_cliIo_block_pure {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < signalSessionIoMultiLib.blocks.length)
    (hext_blk : CliIoBlockNoExtern mpl P j)
    (hchk : VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib j).text = true)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoaded mpl s.mem)
    (hseg : ∀ s' : State, SameCpuOracleState s' s →
      SepWP ((signalSessionIoMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none))
        mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuOracleState sm sm' → signalSessionIoMultiLib.CodeLoaded mpl sm.mem →
            ProofLib.NonSyscallPreserved s sm → sm.symtab = s.symtab →
            SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_j := (signalSessionIoMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keep := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by
    intro pc; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 signalSessionIoMultiLib mpl j hchk
  have hext_R_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    have hlen : R_j.code.length ≤ (signalSessionIoMultiLib.blockLib j).text.code.length := by
      change ((signalSessionIoMultiLib.blockLib j).text.patched
        (signalSessionIoMultiLib.blockPlacement mpl j)).length ≤ _
      rw [Obj.CodeBlock.length_patched]
      omega
    exact hext_blk off (Nat.lt_of_lt_of_le hoff hlen)
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuOracleState (ProofLib.stripS keep s) s :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp [ProofLib.stripS]⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_cliIo hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      steps_rebase_lift_cliIo_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : signalSessionIoMultiLib.CodeLoaded mpl sm.mem :=
      fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hcpu_out : SameCpuOracleState sm sm' :=
      ⟨SameCpuState.of_stripS_left hsm_eq, by rw [hsm_eq]; simp [ProofLib.stripS]⟩
    have hwp_cont := hcont sm hcpu_out hcl_m hnsp hsteps_P.symtab_eq
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

/-- Wrap `spec` with `signalSessionIoMultiLib.CodeLoaded mpl` in both `pre` and `post`. -/
def cliIoWithCodeLoaded {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { signalSessionIoMultiLib.withCodeLoaded mpl spec with
    post := fun x s0 sf => ⌜signalSessionIoMultiLib.CodeLoaded mpl sf.mem⌝ ∗ spec.post x s0 sf }

/-- Drop the postcondition `CodeLoaded` witness from `cliIoWithCodeLoaded` to `withCodeLoaded`. -/
theorem subroutine_ok_of_cliIoWithCodeLoaded {α : Type}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (cliIoWithCodeLoaded mpl spec)) :
    subroutine_ok P entry (signalSessionIoMultiLib.withCodeLoaded mpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cliIoWithCodeLoaded] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

/-! ## 3. Fast Symbol Lookup Witnesses (`rfl_kernel`) -/

theorem cliIoBlocks_len : signalSessionIoMultiLib.blocks.length = 5 := by rfl_kernel

theorem cliIo00_symbols_list :
    signalSessionIoMultiLib.blocks[0].symbols = [(cliIoReadStdinSym, 0)] := by
  rfl_kernel

theorem cliIoReadStdin_lookup :
    lookup cliIoReadStdinSym signalSessionIoMultiLib.blocks[0].symbols = some 0 := by
  rw [cliIo00_symbols_list]; simp [lookup]

theorem cliIo01_symbols_list :
    signalSessionIoMultiLib.blocks[1].symbols = [(cliIoWriteFileSym, 0)] := by
  rfl_kernel

theorem cliIoWriteFile_lookup :
    lookup cliIoWriteFileSym signalSessionIoMultiLib.blocks[1].symbols = some 0 := by
  rw [cliIo01_symbols_list]; simp [lookup]

theorem cliIo02_symbols_list :
    signalSessionIoMultiLib.blocks[2].symbols = [(cliIoWriteStdoutSym, 0)] := by
  rfl_kernel

theorem cliIoWriteStdout_lookup :
    lookup cliIoWriteStdoutSym signalSessionIoMultiLib.blocks[2].symbols = some 0 := by
  rw [cliIo02_symbols_list]; simp [lookup]

theorem cliIo03_symbols_list :
    signalSessionIoMultiLib.blocks[3].symbols = [(cliIoReadFileSym, 0)] := by
  rfl_kernel

theorem cliIoReadFile_lookup :
    lookup cliIoReadFileSym signalSessionIoMultiLib.blocks[3].symbols = some 0 := by
  rw [cliIo03_symbols_list]; simp [lookup]

theorem cliIo04_symbols_list :
    signalSessionIoMultiLib.blocks[4].symbols = [(cliIoFinishGrowSym, 0)] := by
  rfl_kernel

theorem cliIoFinishGrow_lookup :
    lookup cliIoFinishGrowSym signalSessionIoMultiLib.blocks[4].symbols = some 0 := by
  rw [cliIo04_symbols_list]; simp [lookup]

/-! ## 4. Per-Block Placement Projections & Fetch Generation (`0..4`) -/

-- Block 0: `signal_session_io::read_stdin` (`436` B / `109` insns, `[0x0 → 0x1b0]`)
def cliIoLib00 : PlacedLib := signalSessionIoMultiLib.blockLib 0
def cliIoPl00 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 0
theorem cliIoPlaceable00 [CliIoPlacement] : cliIoLib00.Placeable cliIoPl00 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
def cliIoPC00 [CliIoPlacement] : Program := cliIoLib00.program cliIoPl00

def cliIoProg00 : Program := { code := cliIoLib00.text.code, symbols := cliIoLib00.text.symbols }
def cliIoTree00 : WordTree := word_tree_of% cliIoProg00
theorem cliIo00_code_eq : cliIoLib00.text.code = cliIoTree00.toBytes := by rfl_kernel
theorem cliIo00_tree_size : cliIoTree00.checkSize? = some 109 := by rfl_kernel
def cliIoSymChars00 : List (List Char × Nat) := sym_chars_of% cliIoProg00
theorem cliIo00_symbols_eq : cliIoLib00.text.symbols = toStringSymbols cliIoSymChars00 := by rfl_kernel
theorem cliIo00_symbols_fresh : allFreshCharSymbols cliIoSymChars00 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC00 cliIoLib00 cliIoTree00 cliIo00_code_eq cliIo00_tree_size
  via_placement cliIoPl00 cliIoPlaceable00 [0x0 → 0x1b0]
gen_placed_fnOffs cliIoPC00 cliIoLib00 cliIoSymChars00 cliIo00_symbols_eq cliIo00_symbols_fresh
end

theorem cliIoBlockNoSvc0_00 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib 0).text = true := by
  rfl_kernel

-- Block 1: `signal_session_io::write_file` (`304` B / `76` insns, `[0x0 → 0x12c]`)
def cliIoLib01 : PlacedLib := signalSessionIoMultiLib.blockLib 1
def cliIoPl01 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 1
theorem cliIoPlaceable01 [CliIoPlacement] : cliIoLib01.Placeable cliIoPl01 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
def cliIoPC01 [CliIoPlacement] : Program := cliIoLib01.program cliIoPl01

def cliIoProg01 : Program := { code := cliIoLib01.text.code, symbols := cliIoLib01.text.symbols }
def cliIoTree01 : WordTree := word_tree_of% cliIoProg01
theorem cliIo01_code_eq : cliIoLib01.text.code = cliIoTree01.toBytes := by rfl_kernel
theorem cliIo01_tree_size : cliIoTree01.checkSize? = some 76 := by rfl_kernel
def cliIoSymChars01 : List (List Char × Nat) := sym_chars_of% cliIoProg01
theorem cliIo01_symbols_eq : cliIoLib01.text.symbols = toStringSymbols cliIoSymChars01 := by rfl_kernel
theorem cliIo01_symbols_fresh : allFreshCharSymbols cliIoSymChars01 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC01 cliIoLib01 cliIoTree01 cliIo01_code_eq cliIo01_tree_size
  via_placement cliIoPl01 cliIoPlaceable01 [0x0 → 0x12c]
gen_placed_fnOffs cliIoPC01 cliIoLib01 cliIoSymChars01 cliIo01_symbols_eq cliIo01_symbols_fresh
end

theorem cliIoBlockNoSvc0_01 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib 1).text = true := by
  rfl_kernel

-- Block 2: `signal_session_io::write_stdout` (`184` B / `46` insns, `[0x0 → 0xb4]`)
def cliIoLib02 : PlacedLib := signalSessionIoMultiLib.blockLib 2
def cliIoPl02 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 2
theorem cliIoPlaceable02 [CliIoPlacement] : cliIoLib02.Placeable cliIoPl02 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
def cliIoPC02 [CliIoPlacement] : Program := cliIoLib02.program cliIoPl02

def cliIoProg02 : Program := { code := cliIoLib02.text.code, symbols := cliIoLib02.text.symbols }
def cliIoTree02 : WordTree := word_tree_of% cliIoProg02
theorem cliIo02_code_eq : cliIoLib02.text.code = cliIoTree02.toBytes := by rfl_kernel
theorem cliIo02_tree_size : cliIoTree02.checkSize? = some 46 := by rfl_kernel
def cliIoSymChars02 : List (List Char × Nat) := sym_chars_of% cliIoProg02
theorem cliIo02_symbols_eq : cliIoLib02.text.symbols = toStringSymbols cliIoSymChars02 := by rfl_kernel
theorem cliIo02_symbols_fresh : allFreshCharSymbols cliIoSymChars02 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC02 cliIoLib02 cliIoTree02 cliIo02_code_eq cliIo02_tree_size
  via_placement cliIoPl02 cliIoPlaceable02 [0x0 → 0xb4]
gen_placed_fnOffs cliIoPC02 cliIoLib02 cliIoSymChars02 cliIo02_symbols_eq cliIo02_symbols_fresh
end

theorem cliIoBlockNoSvc0_02 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib 2).text = true := by
  rfl_kernel

-- Block 3: `signal_session_io::read_file` (`572` B / `143` insns, `[0x0 → 0x238]`)
def cliIoLib03 : PlacedLib := signalSessionIoMultiLib.blockLib 3
def cliIoPl03 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 3
theorem cliIoPlaceable03 [CliIoPlacement] : cliIoLib03.Placeable cliIoPl03 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
def cliIoPC03 [CliIoPlacement] : Program := cliIoLib03.program cliIoPl03

def cliIoProg03 : Program := { code := cliIoLib03.text.code, symbols := cliIoLib03.text.symbols }
def cliIoTree03 : WordTree := word_tree_of% cliIoProg03
theorem cliIo03_code_eq : cliIoLib03.text.code = cliIoTree03.toBytes := by rfl_kernel
theorem cliIo03_tree_size : cliIoTree03.checkSize? = some 143 := by rfl_kernel
def cliIoSymChars03 : List (List Char × Nat) := sym_chars_of% cliIoProg03
theorem cliIo03_symbols_eq : cliIoLib03.text.symbols = toStringSymbols cliIoSymChars03 := by rfl_kernel
theorem cliIo03_symbols_fresh : allFreshCharSymbols cliIoSymChars03 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC03 cliIoLib03 cliIoTree03 cliIo03_code_eq cliIo03_tree_size
  via_placement cliIoPl03 cliIoPlaceable03 [0x0 → 0x238]
gen_placed_fnOffs cliIoPC03 cliIoLib03 cliIoSymChars03 cliIo03_symbols_eq cliIo03_symbols_fresh
end

theorem cliIoBlockNoSvc0_03 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib 3).text = true := by
  rfl_kernel

-- Block 4: `<alloc::raw_vec::RawVecInner>::finish_grow` (`168` B / `42` insns, `[0x0 → 0xa4]`)
def cliIoLib04 : PlacedLib := signalSessionIoMultiLib.blockLib 4
def cliIoPl04 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 4
theorem cliIoPlaceable04 [CliIoPlacement] : cliIoLib04.Placeable cliIoPl04 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
def cliIoPC04 [CliIoPlacement] : Program := cliIoLib04.program cliIoPl04

def cliIoProg04 : Program := { code := cliIoLib04.text.code, symbols := cliIoLib04.text.symbols }
def cliIoTree04 : WordTree := word_tree_of% cliIoProg04
theorem cliIo04_code_eq : cliIoLib04.text.code = cliIoTree04.toBytes := by rfl_kernel
theorem cliIo04_tree_size : cliIoTree04.checkSize? = some 42 := by rfl_kernel
def cliIoSymChars04 : List (List Char × Nat) := sym_chars_of% cliIoProg04
theorem cliIo04_symbols_eq : cliIoLib04.text.symbols = toStringSymbols cliIoSymChars04 := by rfl_kernel
theorem cliIo04_symbols_fresh : allFreshCharSymbols cliIoSymChars04 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC04 cliIoLib04 cliIoTree04 cliIo04_code_eq cliIo04_tree_size
  via_placement cliIoPl04 cliIoPlaceable04 [0x0 → 0xa4]
gen_placed_fnOffs cliIoPC04 cliIoLib04 cliIoSymChars04 cliIo04_symbols_eq cliIo04_symbols_fresh
end

theorem cliIoBlockNoSvc0_04 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib 4).text = true := by
  rfl_kernel

/-! ## 5. Read-Only Block Subset `{0, 3, 4}` (`CliIoReadsCodeLoaded`) -/

/-- Block selector for the 3 unhooked `signalSessionIoMultiLib` read blocks (`read_stdin` `0`,
    `read_file` `3`, and `<alloc::raw_vec::RawVecInner>::finish_grow` `4`). -/
def cliIoReadsKeep (i : Nat) : Bool :=
  i == 0 || i == 3 || i == 4

/-- Block-subset `CodeLoaded` for `signalSessionIoMultiLib` on `{0, 3, 4}`
    (`MultiPlacedLib.CodeLoadedWhere cliIoReadsKeep`). -/
abbrev CliIoReadsCodeLoaded (mpl : MultiPlacement) (m : Memory) : Prop :=
  signalSessionIoMultiLib.CodeLoadedWhere cliIoReadsKeep mpl m

/-- Assemble `CliIoReadsCodeLoaded mpl m` from individual `Program.CodeLoaded` witnesses for
    blocks `0`, `3`, and `4`. -/
theorem cliIoReadsCodeLoaded_of_blocks {mpl : MultiPlacement} {m : Memory}
    (h0 : (signalSessionIoMultiLib.blockProgram mpl 0).CodeLoaded m)
    (h3 : (signalSessionIoMultiLib.blockProgram mpl 3).CodeLoaded m)
    (h4 : (signalSessionIoMultiLib.blockProgram mpl 4).CodeLoaded m) :
    CliIoReadsCodeLoaded mpl m := by
  intro i hi hk
  rw [cliIoBlocks_len] at hi
  match i with
  | 0 => exact h0
  | 1 => cases hk
  | 2 => cases hk
  | 3 => exact h3
  | 4 => exact h4
  | n + 5 => omega

/-- Run a pure (non-syscall) segment of `signalSessionIoMultiLib` read block `j`
    (`cliIoReadsKeep j = true`) up to `mid` from any `P : Program` with `CliIoBlockNoExtern mpl P j`,
    refreshing `CliIoReadsCodeLoaded` and supplying `SameCpuOracleState`, `NonSyscallPreserved`,
    and `sm.symtab = s.symtab`. -/
theorem sepWP_seg_cliIo_block_pure_reads {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < signalSessionIoMultiLib.blocks.length)
    (hk : cliIoReadsKeep j = true)
    (hext_blk : CliIoBlockNoExtern mpl P j)
    (hchk : VerifiedLibraries.RustStd.checkBlockNoSvc0 (signalSessionIoMultiLib.blockLib j).text = true)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : CliIoReadsCodeLoaded mpl s.mem)
    (hseg : ∀ s' : State, SameCpuOracleState s' s →
      SepWP ((signalSessionIoMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none))
        mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuOracleState sm sm' → CliIoReadsCodeLoaded mpl sm.mem →
            ProofLib.NonSyscallPreserved s sm → sm.symtab = s.symtab →
            SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_j := (signalSessionIoMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keep := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj hk).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by
    intro pc; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 signalSessionIoMultiLib mpl j hchk
  have hext_R_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    have hlen : R_j.code.length ≤ (signalSessionIoMultiLib.blockLib j).text.code.length := by
      change ((signalSessionIoMultiLib.blockLib j).text.patched
        (signalSessionIoMultiLib.blockPlacement mpl j)).length ≤ _
      rw [Obj.CodeBlock.length_patched]
      omega
    exact hext_blk off (Nat.lt_of_lt_of_le hoff hlen)
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuOracleState (ProofLib.stripS keep s) s :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp [ProofLib.stripS]⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_cliIo hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      steps_rebase_lift_cliIo_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : CliIoReadsCodeLoaded mpl sm.mem :=
      fun k hk_lt hk_keep => hsteps_P.codeLoaded (hcl k hk_lt hk_keep)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hcpu_out : SameCpuOracleState sm sm' :=
      ⟨SameCpuState.of_stripS_left hsm_eq, by rw [hsm_eq]; simp [ProofLib.stripS]⟩
    have hwp_cont := hcont sm hcpu_out hcl_m hnsp hsteps_P.symtab_eq
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

/-- Wrap `spec` with `CliIoReadsCodeLoaded mpl` in both `pre` and `post`. -/
def cliIoWithReadsCodeLoaded {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl spec with
    post := fun x s0 sf => ⌜CliIoReadsCodeLoaded mpl sf.mem⌝ ∗ spec.post x s0 sf }

/-- Drop the postcondition `CliIoReadsCodeLoaded` witness from `cliIoWithReadsCodeLoaded` to
    `withCodeLoadedWhere cliIoReadsKeep`. -/
theorem subroutine_ok_of_cliIoWithReadsCodeLoaded {α : Type}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (cliIoWithReadsCodeLoaded mpl spec)) :
    subroutine_ok P entry
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cliIoWithReadsCodeLoaded] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

end LibsignalBinary.Proofs.SignalSession.CliIo.Sym
