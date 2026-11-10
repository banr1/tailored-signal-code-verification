/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Spec.Hoare
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.ProgramReflection
public import LibsignalBinary.Heap.IfaceBudgetBaseBridges
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf

/-!
# Real-Run First-Stop Instances for `alloc` and `allocZeroed`

**Checked by Lean.**

Proves real-run first-stop obligations, `ActiveRealRun` (`f3AllocFallback` deadness), and
visited-PC bounds on `f3TrialRxProg` (`seg[5]`, `[0x49c000, 0x4a2000)`) for `__rust_alloc`
(`f3RdlAddrs.alloc`) and `__rust_alloc_zeroed` (`f3RdlAzAddr`) from `mallocngLib` `subroutine_ok`
theorems and `AllocGhostLinkTransfer.real_subroutine_run_of_stripS`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng ProgContainsMultiLib)
open VerifiedLibraries.RustStd (mallocngPlacedCAddrs)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap
  (RustCliAllocBudgetEntries rustCliAllocBudgetSpec subroutine_ok_rustCliAllocBudget_of_base)
open LibsignalBinary.Heap.Fine
  (f3MallocngMpl f3RdlAddrs f3RdlAzAddr f3RxWordCount f3StdLayout fineCostModel
   fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRdlAllocZeroed_budget_placed_ok fineHookRustCliAllocBudgetEntries)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen real_subroutine_run_of_stripS specPreservesFsTrace_alloc)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook specStripSInvariant_fine_alloc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_linkedAt_unique f3TrialElf
   f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_svc
   f3TrialRxWordTree_eq f3TrialRxWordTree_size f3Trial_allocMemcpyVm_ok f3Trial_allocMemsetVm_ok
   f3Trial_progContainsMallocng f3Trial_seg5ShimBundle)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_ghFixed hole2_keep hole2_keepSub)

/-- `(γ, tp)`-indexed fine-budget `rustCliAllocBudgetSpec` family guarding
    `f3AllocGhostHookFine` (`zeroed = false`) and `f3AllocZeroedGhostHookFine` (`zeroed = true`)
    in `hole2_ghFixed`. -/
noncomputable def h2fsalloc_spec [LibsignalPlacement] (mmpl : MultiPlacement) (zeroed : Bool)
    (γ : GhostName) (tp : BitVec 64) : Spec (Nat × Nat × fineCostModel.σ) :=
  rustCliAllocBudgetSpec fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
    cliBudgetLimits zeroed

/-- `seg[5]` entry target for `alloc` (`zeroed = false`) and `allocZeroed` (`zeroed = true`). -/
def h2fsalloc_target (zeroed : Bool) : BitVec 64 :=
  if zeroed then f3RdlAzAddr else f3RdlAddrs.alloc

theorem h2fsalloc_mng_placeable (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

theorem h2fsalloc_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem h2fsalloc_toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

/-- Every `mallocngLib` code byte in `cliElfBytes` lies inside `hole2_keepSub` (`[0x469000, 0x46f000)`). -/
theorem h2fsalloc_keepSub_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((h2fsalloc_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (h2fsalloc_mng_placeable mmpl hMm) (h2fsalloc_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hlo : 0x469000 ≤ f3MngCodeLo := by decide
    have hhi : f3MngCodeHi ≤ 0x46f000 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat :=
      h2fsalloc_toNat_add_ofNat_of_lt (by omega)
    rw [heq_a] at ht
    unfold hole2_keepSub
    exact decide_eq_true ⟨by omega, by omega⟩

/-- `hole2_keepSub` (`[0x469000, 0x46f000)`) is a subset of `hole2_keep`. -/
theorem h2fsalloc_keep_of_keepSub {a : BitVec 64} (h : hole2_keepSub a = true) :
    hole2_keep a = true := by
  unfold hole2_keepSub at h
  unfold hole2_keep
  have h' : 0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000 := of_decide_eq_true h
  exact decide_eq_true (Or.inr h')

/-- Contrapositive: `hole2_keep a = false → hole2_keepSub a = false`. -/
theorem h2fsalloc_keepSub_false_of_keep_false {a : BitVec 64} (h : hole2_keep a = false) :
    hole2_keepSub a = false := by
  cases hs : hole2_keepSub a with
  | false => rfl
  | true =>
    have hk := h2fsalloc_keep_of_keepSub hs
    rw [h] at hk
    cases hk

/-- Every `mallocngLib` code byte in `cliElfBytes` also lies inside `hole2_keep`. -/
theorem h2fsalloc_keep_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keep a = true :=
  fun a hsome => h2fsalloc_keep_of_keepSub (h2fsalloc_keepSub_mallocng mmpl hMm a hsome)

/-- `f3TrialRxProg` (`seg[2]`, `[0x469000, 0x46f000)`) has identical `CodeLoaded` under
    `stripExecOutside hole2_keepSub` and `stripExecOutside hole2_keep`. -/
theorem h2fsalloc_rxProg_codeLoaded_keepSub_iff_keep (m : Memory) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) ↔
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep m) := by
  have hbase : f3TrialRxProg.base = f3RxSegBase := f3TrialRxProg_base
  have hbase_nat : f3RxSegBase.toNat = 0x469000 := by decide
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hwc : f3RxWordCount = 6144 := rfl
  have hinSub : ∀ i, i < f3TrialRxProg.code.length →
      hole2_keepSub (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
    intro i hi
    have ht : (f3TrialRxProg.base + BitVec.ofNat 64 i).toNat =
        f3TrialRxProg.base.toNat + i := by
      apply h2fsalloc_toNat_add_ofNat_of_lt
      rw [hbase, hbase_nat]
      rw [hlen, hwc] at hi
      omega
    unfold hole2_keepSub
    refine decide_eq_true ⟨?_, ?_⟩ <;> (rw [ht, hbase, hbase_nat]; rw [hlen, hwc] at hi; omega)
  constructor <;> intro hL
  · refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
    have hs := hinSub i hi
    have hk := h2fsalloc_keep_of_keepSub hs
    have hb := hL.byte_eq i hi
    have hp := hL.perm_eq i hi
    have hlf := hL.isLazyFree_eq i hi
    rw [ProofLib.strip_read8] at hb ⊢
    rw [ProofLib.strip_perm_of_keep hs] at hp
    rw [ProofLib.strip_perm_of_keep hk]
    rw [ProofLib.strip_isLazyFree] at hlf ⊢
    exact ⟨hb, hp, hlf⟩
  · refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
    have hs := hinSub i hi
    have hk := h2fsalloc_keep_of_keepSub hs
    have hb := hL.byte_eq i hi
    have hp := hL.perm_eq i hi
    have hlf := hL.isLazyFree_eq i hi
    rw [ProofLib.strip_read8] at hb ⊢
    rw [ProofLib.strip_perm_of_keep hk] at hp
    rw [ProofLib.strip_perm_of_keep hs]
    rw [ProofLib.strip_isLazyFree] at hlf ⊢
    exact ⟨hb, hp, hlf⟩

theorem h2fsalloc_mng_fnAddr_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (name : String) :
    mallocngLib.fnAddr mmpl name = mallocngLib.fnAddr f3MallocngMpl name := by
  unfold MultiPlacedLib.fnAddr
  cases hlk : lookupBlockSym name mallocngLib.blocks with
  | none =>
    exact (f3CliElf_mallocng_linkedAt_unique hMm).1 0 (Nat.zero_lt_succ 23)
  | some p =>
    rcases p with ⟨i, _⟩
    dsimp only
    rw [(f3CliElf_mallocng_linkedAt_unique hMm).1 i (lookupBlockSym_lt hlk)]

theorem h2fsalloc_mng_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  unfold mallocngPlacedCAddrs
  simp only [h2fsalloc_mng_fnAddr_eq mmpl hMm]

theorem h2fsalloc_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hPl1 := h2fsalloc_mng_placeable mmpl hMm
  have hIn1 := h2fsalloc_mng_inElf mmpl hMm
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
  have hlen2 : (mallocngLib.blocks[i].patched
      (mallocngLib.blockPlacement f3MallocngMpl i)).length =
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

theorem h2fsalloc_rdlEntries [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntries fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      f3TrialRxProg f3RdlAddrs := by
  have hShims := f3Trial_seg5ShimBundle.rdlShims
  rw [← h2fsalloc_mng_cAddrs_eq mmpl hMm] at hShims
  exact (fineHookRustCliAllocBudgetEntries
    (h2fsalloc_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hShims
    f3Trial_allocMemcpyVm_ok).toPlaced

/-- Compiled `f3TrialRxProg` `subroutine_ok` for `__rust_alloc` (`f3RdlAddrs.alloc`). -/
theorem h2fsalloc_rdlAlloc_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg f3RdlAddrs.alloc (h2fsalloc_spec mmpl false γ tp) :=
  (h2fsalloc_rdlEntries mmpl hMm γ tp).alloc cliBudgetLimits

/-- Compiled `f3TrialRxProg` `subroutine_ok` for `__rust_alloc_zeroed` (`f3RdlAzAddr`). -/
theorem h2fsalloc_rdlAllocZeroed_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg f3RdlAzAddr (h2fsalloc_spec mmpl true γ tp) := by
  have hZero := f3Trial_seg5ShimBundle.allocZeroedInstrs
  rw [← h2fsalloc_mng_fnAddr_eq mmpl hMm "calloc", ← h2fsalloc_mng_cAddrs_eq mmpl hMm] at hZero
  exact subroutine_ok_rustCliAllocBudget_of_base
    (fineHookRdlAllocZeroed_budget_placed_ok
      (h2fsalloc_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart
      f3RdlAzAddr f3StdLayout.memsetAddr cliBudgetLimits
      hZero f3Trial_allocMemsetVm_ok)

/-- Unified `subroutine_ok` over `f3TrialRxProg` for `zeroed : Bool` (`alloc` / `allocZeroed`). -/
theorem h2fsalloc_rdl_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (zeroed : Bool) (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg (h2fsalloc_target zeroed) (h2fsalloc_spec mmpl zeroed γ tp) := by
  cases zeroed
  · exact h2fsalloc_rdlAlloc_ok mmpl hMm γ tp
  · exact h2fsalloc_rdlAllocZeroed_ok mmpl hMm γ tp

private theorem h2fsalloc_prePC [LibsignalPlacement] (mmpl : MultiPlacement) (zeroed : Bool)
    (γ : GhostName) (tp : BitVec 64)
    (x : Nat × Nat × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (h2fsalloc_spec mmpl zeroed γ tp).pre x (s.setPC pc) =
      (h2fsalloc_spec mmpl zeroed γ tp).pre x s := by
  cases s; rfl

private theorem h2fsalloc_outPC [LibsignalPlacement] (mmpl : MultiPlacement) (zeroed : Bool)
    (γ : GhostName) (tp : BitVec 64)
    (x : Nat × Nat × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome (h2fsalloc_spec mmpl zeroed γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (h2fsalloc_spec mmpl zeroed γ tp) x R s0 sf := by
  cases s0; exact id

/-- Parametric `keep` / `P` real-run first-stop theorem for `alloc` (`zeroed = false`) and
`allocZeroed` (`zeroed = true`) via `h2fsalloc_rdl_ok` and `real_subroutine_run_of_stripS`. -/
theorem h2fsalloc_firstStop_of_keep [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (zeroed : Bool)
    {keep : BitVec 64 → Bool}
    (hKeepMallocng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl zeroed) s0)
    (hLr : keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC (h2fsalloc_target zeroed)) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS hsvc f3TrialRxProg_svc hno_ext f3TrialRxProg_no_ext
      (h2fsalloc_rdl_ok mmpl hMm zeroed γ tp)
      (specStripSInvariant_fine_alloc γ mmpl tp cliElfImage.brkStart hKeepMallocng
        cliBudgetLimits zeroed)
      (specPreservesFsTrace_alloc _ cliBudgetLimits zeroed)
      (h2fsalloc_prePC mmpl zeroed γ tp)
      (h2fsalloc_outPC mmpl zeroed γ tp)
      hRun hSp hSat hFr hLr hCode
  exact ⟨sf, huntil, hstop, hfs, hfst, hfr_sf⟩

/-- Real-run first-stop instance for `alloc` (`f3RdlAddrs.alloc`, `hole2_keep`). -/
theorem h2fsalloc_alloc_firstStop [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keep pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl false) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAddrs.alloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsalloc_firstStop_of_keep mmpl hMm false (h2fsalloc_keep_mallocng mmpl hMm)
    hsvc hno_ext hPre hLr hFr hCode

/-- Real-run first-stop instance for `allocZeroed` (`f3RdlAzAddr`, `hole2_keep`). -/
theorem h2fsalloc_allocZeroed_firstStop [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keep pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl true) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAzAddr) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsalloc_firstStop_of_keep mmpl hMm true (h2fsalloc_keep_mallocng mmpl hMm)
    hsvc hno_ext hPre hLr hFr hCode

/-- Real-run first-stop instance for `alloc` (`f3RdlAddrs.alloc`, `hole2_keepSub`). -/
theorem h2fsalloc_alloc_firstStop_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl false) s0)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAddrs.alloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsalloc_firstStop_of_keep mmpl hMm false (h2fsalloc_keepSub_mallocng mmpl hMm)
    hsvc hno_ext hPre hLr hFr hCode

/-- Real-run first-stop instance for `allocZeroed` (`f3RdlAzAddr`, `hole2_keepSub`). -/
theorem h2fsalloc_allocZeroed_firstStop_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl true) s0)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAzAddr) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsalloc_firstStop_of_keep mmpl hMm true (h2fsalloc_keepSub_mallocng mmpl hMm)
    hsvc hno_ext hPre hLr hFr hCode

/-- Under `ActiveF3CallPre`, `hole2_keep lr = false`, `ExecFrozen s0.mem`, and
`f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)`, `ActiveRealRun` holds for `alloc`
on `(hole2_keepSub, hole2_emptyProg)` (making `f3AllocFallback mmpl false` unreachable). -/
theorem h2fsalloc_alloc_activeRealRun [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl false) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.alloc s0 := by
  have hLrSub : hole2_keepSub (s0.readReg64 .lr) = false :=
    h2fsalloc_keepSub_false_of_keep_false hLr
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) :=
    (h2fsalloc_rxProg_codeLoaded_keepSub_iff_keep s0.mem).mpr hCode
  exact ⟨hFr, hLrSub, hCodeSub,
    h2fsalloc_alloc_firstStop_keepSub mmpl hMm rfl (fun _ _ => rfl) hPre hLrSub hFr hCodeSub⟩

/-- `ActiveRealRun` for `allocZeroed` on `(hole2_keepSub, hole2_emptyProg)` under `hole2_keep`
premises. -/
theorem h2fsalloc_allocZeroed_activeRealRun [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl true) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAzAddr s0 := by
  have hLrSub : hole2_keepSub (s0.readReg64 .lr) = false :=
    h2fsalloc_keepSub_false_of_keep_false hLr
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) :=
    (h2fsalloc_rxProg_codeLoaded_keepSub_iff_keep s0.mem).mpr hCode
  exact ⟨hFr, hLrSub, hCodeSub,
    h2fsalloc_allocZeroed_firstStop_keepSub mmpl hMm rfl (fun _ _ => rfl) hPre hLrSub hFr hCodeSub⟩

/-- Direct `StepsUntil hole2_emptyProg` evaluation of `(hole2_ghFixed mpl mmpl).alloc s0`
    under `ActiveF3CallPre` and `hole2_keep (s0.readReg64 .lr) = false` (Branch (c) dead). -/
theorem h2fsalloc_ghFixed_alloc_firstStop [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl false) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    let sf := (hole2_ghFixed mpl mmpl).alloc s0
    StepsUntil hole2_emptyProg (SubroutineStop s0) (s0.setPC f3RdlAddrs.alloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  classical
  have hReal : ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.alloc s0 :=
    h2fsalloc_alloc_activeRealRun mmpl hMm hPre hLr hFr hCode
  have heq : (hole2_ghFixed mpl mmpl).alloc s0 = Classical.choose hReal.2.2.2 := by
    change f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.alloc
      (h2fsalloc_spec mmpl false) _ s0 = _
    unfold f3LinkedCallHook
    simp [hPre, hReal]
  dsimp only
  rw [heq]
  exact Classical.choose_spec hReal.2.2.2

/-- Direct `StepsUntil hole2_emptyProg` evaluation of `(hole2_ghFixed mpl mmpl).allocZeroed s0`
    under `ActiveF3CallPre` and `hole2_keep (s0.readReg64 .lr) = false` (Branch (c) dead). -/
theorem h2fsalloc_ghFixed_allocZeroed_firstStop [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl true) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    let sf := (hole2_ghFixed mpl mmpl).allocZeroed s0
    StepsUntil hole2_emptyProg (SubroutineStop s0) (s0.setPC f3RdlAzAddr) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  classical
  have hReal : ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAzAddr s0 :=
    h2fsalloc_allocZeroed_activeRealRun mmpl hMm hPre hLr hFr hCode
  have heq : (hole2_ghFixed mpl mmpl).allocZeroed s0 = Classical.choose hReal.2.2.2 := by
    change f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAzAddr
      (h2fsalloc_spec mmpl true) _ s0 = _
    unfold f3LinkedCallHook
    simp [hPre, hReal]
  dsimp only
  rw [heq]
  exact Classical.choose_spec hReal.2.2.2

/-- `ActiveRealRun` for `alloc` (`f3RdlAddrs.alloc`) directly under `hole2_keepSub` premises. -/
theorem h2fsalloc_alloc_activeRealRun_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl false) s0)
    (hFr : ExecFrozen s0.mem)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.alloc s0 :=
  ⟨hFr, hLr, hCode,
    h2fsalloc_alloc_firstStop_keepSub mmpl hMm rfl (fun _ _ => rfl) hPre hLr hFr hCode⟩

/-- `ActiveRealRun` for `allocZeroed` (`f3RdlAzAddr`) directly under `hole2_keepSub` premises. -/
theorem h2fsalloc_allocZeroed_activeRealRun_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl true) s0)
    (hFr : ExecFrozen s0.mem)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAzAddr s0 :=
  ⟨hFr, hLr, hCode,
    h2fsalloc_allocZeroed_firstStop_keepSub mmpl hMm rfl (fun _ _ => rfl) hPre hLr hFr hCode⟩

/-! ### Visited-PCs-in-`hole2_keepSub` & Scoped `StepsUntil` / `Steps` Lift -/

/-- First-stop execution `StepsUntil prog stop s1 sf` in which every pre-step state `u` satisfies
    `keep u.pc = true` (exporting the visited-PCs invariant for scoped `Steps` / `StepsUntil` lift). -/
inductive h2fsalloc_StepsUntilInKeep (prog : Program) (keep : BitVec 64 → Bool)
    (stop : State → Prop) : State → State → Prop where
  | refl (s : State) : h2fsalloc_StepsUntilInKeep prog keep stop s s
  | step {s1 s2 s3 : State}
      (h_cont : ¬ stop s1)
      (h_keep : keep s1.pc = true)
      (h_step : Step prog s1 s2)
      (h_rest : h2fsalloc_StepsUntilInKeep prog keep stop s2 s3) :
      h2fsalloc_StepsUntilInKeep prog keep stop s1 s3

theorem h2fsalloc_StepsUntilInKeep.toStepsUntil {prog : Program} {keep : BitVec 64 → Bool}
    {stop : State → Prop} {s1 sf : State}
    (h : h2fsalloc_StepsUntilInKeep prog keep stop s1 sf) :
    StepsUntil prog stop s1 sf := by
  induction h with
  | refl s => exact StepsUntil.refl s
  | step hc _ hs _ ih => exact StepsUntil.step hc hs ih

theorem h2fsalloc_StepsUntilInKeep.toSteps {prog : Program} {keep : BitVec 64 → Bool}
    {stop : State → Prop} {s1 sf : State}
    (h : h2fsalloc_StepsUntilInKeep prog keep stop s1 sf) :
    Steps prog s1 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ _ hs _ ih => exact Steps.step hs ih

theorem h2fsalloc_StepsUntilInKeep.snoc {prog : Program} {keep : BitVec 64 → Bool}
    {stop : State → Prop} {s1 s2 s3 : State}
    (h12 : h2fsalloc_StepsUntilInKeep prog keep stop s1 s2)
    (h_cont : ¬ stop s2)
    (h_keep : keep s2.pc = true)
    (h_step : Step prog s2 s3) :
    h2fsalloc_StepsUntilInKeep prog keep stop s1 s3 := by
  induction h12 with
  | refl _ =>
    exact h2fsalloc_StepsUntilInKeep.step h_cont h_keep h_step
      (h2fsalloc_StepsUntilInKeep.refl s3)
  | step hc hk hs _ ih =>
    exact h2fsalloc_StepsUntilInKeep.step hc hk hs (ih h_cont h_keep h_step)

private theorem h2fsalloc_step_det {P : Program} {s s1 s2 : State}
    (h1 : Step P s s1) (h2 : Step P s s2) : s1 = s2 := by
  cases h1 with
  | exec _ hf1 =>
    cases h2 with
    | exec _ hf2 => cases hf1.symm.trans hf2; rfl
    | halt_unmapped _ hf2 _ => rw [hf1] at hf2; cases hf2
    | extern _ he2 _ _ => unfold Program.fetchMem at hf1; simp [he2] at hf1
    | extern_fault _ he2 _ => unfold Program.fetchMem at hf1; simp [he2] at hf1
  | halt_unmapped _ hf1 he1 =>
    cases h2 with
    | exec _ hf2 => rw [hf1] at hf2; cases hf2
    | halt_unmapped _ _ _ => rfl
    | extern _ he2 _ _ => rw [he1] at he2; cases he2
    | extern_fault _ he2 _ => rw [he1] at he2; cases he2
  | extern _ he1 hk1 hs1 =>
    cases h2 with
    | exec _ hf2 => unfold Program.fetchMem at hf2; simp [he1] at hf2
    | halt_unmapped _ _ he2 => rw [he1] at he2; cases he2
    | extern _ he2 _ _ => cases he1.symm.trans he2; rfl
    | extern_fault _ he2 hnk2 =>
      cases he1.symm.trans he2
      exact False.elim (hnk2 ⟨hk1, hs1⟩)
  | extern_fault _ he1 hnk1 =>
    cases h2 with
    | exec _ hf2 => unfold Program.fetchMem at hf2; simp [he1] at hf2
    | halt_unmapped _ _ he2 => rw [he1] at he2; cases he2
    | extern _ he2 hk2 hs2 =>
      cases he1.symm.trans he2
      exact False.elim (hnk1 ⟨hk2, hs2⟩)
    | extern_fault _ _ _ => rfl

private theorem h2fsalloc_step_of_agree {P Q : Program} {s s' : State}
    (hsvc : P.svc = Q.svc)
    (heP : P.externAt? s.pc = none)
    (heQ : Q.externAt? s.pc = none)
    (h : Step P s s') : Step Q s s' := by
  have hfm_eq : Q.fetchMem s.mem s.pc = P.fetchMem s.mem s.pc := by
    unfold Program.fetchMem; rw [heQ, heP]
  cases h with
  | exec hr hfm =>
    have hev : ∀ i, P.evalInst i s = Q.evalInst i s := by
      intro i; unfold Program.evalInst; rw [hsvc]
    rw [hev]
    exact Step.exec hr (hfm_eq.trans hfm)
  | halt_unmapped hr hfm _ =>
    exact Step.halt_unmapped hr (hfm_eq.trans hfm) heQ
  | extern _ he _ _ => rw [heP] at he; cases he
  | extern_fault _ he _ => rw [heP] at he; cases he

/-- Lift `h2fsalloc_StepsUntilInKeep P keep stop s1 sf` to any `Q` agreeing on `svc` and extern-free
    on `keep`. -/
theorem h2fsalloc_StepsUntilInKeep.liftProg {P Q : Program} {keep : BitVec 64 → Bool}
    {stop : State → Prop} {s1 sf : State}
    (hsvc : P.svc = Q.svc)
    (heP : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    (heQ : ∀ pc : BitVec 64, keep pc = true → Q.externAt? pc = none)
    (h : h2fsalloc_StepsUntilInKeep P keep stop s1 sf) :
    h2fsalloc_StepsUntilInKeep Q keep stop s1 sf := by
  induction h with
  | refl s => exact h2fsalloc_StepsUntilInKeep.refl s
  | step hc hk hs _ ih =>
    exact h2fsalloc_StepsUntilInKeep.step hc hk
      (h2fsalloc_step_of_agree hsvc (heP _ hk) (heQ _ hk) hs) ih

/-- Pure `Arm64` visited-PCs extraction: every state `u` reached before `stop` along `P` satisfies
    `keep u.pc = true`. -/
theorem h2fsalloc_StepsUntilInKeep.visited_pcs {P : Program} {keep : BitVec 64 → Bool}
    {stop : State → Prop} {s1 sf : State}
    (h : h2fsalloc_StepsUntilInKeep P keep stop s1 sf)
    (hStop : stop sf) :
    ∀ u : State,
      StepsUntil P (fun x => stop x ∨ x = u) s1 u →
      ¬ stop u →
      keep u.pc = true := by
  induction h with
  | refl s =>
    intro u hReach hNu
    cases hReach with
    | refl _ => exact False.elim (hNu hStop)
    | step hcont _ _ => exact False.elim (hcont (Or.inl hStop))
  | step _ hk hs _ ih =>
    intro u hReach hNu
    cases hReach with
    | refl _ => exact hk
    | step _ hs' hrest' =>
      cases h2fsalloc_step_det hs hs'
      exact ih hStop u hrest' hNu

private def h2fsalloc_probeProg (badPc : BitVec 64) : Program where
  base := 0#64
  code := []
  externs sym := if sym == "__probe_halt" then some (fun s => { s with status := .Halted }) else none
  stubs := [("__probe_halt", badPc.toNat)]
  svc := Syscall.standard

private theorem h2fsalloc_probeProg_externAt_self (badPc : BitVec 64) :
    (h2fsalloc_probeProg badPc).externAt? badPc =
      some (fun s => { s with status := .Halted }) := by
  unfold h2fsalloc_probeProg Program.externAt? Program.hookAtOff?
  simp [BitVec.sub_zero]

private theorem h2fsalloc_probeProg_externAt_ne {badPc pc : BitVec 64} (hne : pc ≠ badPc) :
    (h2fsalloc_probeProg badPc).externAt? pc = none := by
  unfold h2fsalloc_probeProg Program.externAt? Program.hookAtOff?
  simp only [BitVec.sub_zero, List.findSome?_cons, List.findSome?_nil, Option.or_none]
  have hnat : (badPc.toNat == pc.toNat) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    exact hne (BitVec.eq_of_toNat_eq heq.symm)
  simp [hnat]

private theorem h2fsalloc_steps_eq_of_not_running {P : Program} {u v : State}
    (hnr : u.status ≠ .Running) (h : Steps P u v) : u = v := by
  cases h with
  | refl _ => rfl
  | step h1 _ =>
    have hr : u.status = .Running := by cases h1 <;> assumption
    exact False.elim (hnr hr)

private theorem h2fsalloc_stepsUntil_toSteps {P : Program} {stop : State → Prop} {u v : State}
    (h : StepsUntil P stop u v) : Steps P u v := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ hs _ ih => exact Steps.step hs ih

private theorem h2fsalloc_not_subroutineStop_of_halted {s0 sf : State}
    (h : sf.status = .Halted) : ¬ SubroutineStop s0 sf := by
  rintro (⟨_, _, hr⟩ | hp | ⟨_, hex⟩ | ho) <;> rw [h] at * <;> contradiction

private theorem h2fsalloc_not_subroutineStop_of_exception {s0 sf : State} {msg : String}
    (h : sf.status = .Exception msg) : ¬ SubroutineStop s0 sf := by
  rintro (⟨_, _, hr⟩ | hp | ⟨_, hex⟩ | ho) <;> rw [h] at * <;> contradiction

private theorem h2fsalloc_replay_prefix {keep : BitVec 64 → Bool} {stop : State → Prop}
    {P : Program} {a b sf : State}
    (hsvc : P.svc = Syscall.standard)
    (hno : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    (hPref : h2fsalloc_StepsUntilInKeep hole2_emptyProg keep stop a b)
    (hU : StepsUntil P stop a sf)
    (hStop : stop sf) :
    StepsUntil P stop b sf := by
  induction hPref with
  | refl _ => exact hU
  | step hc hk hs _ ih =>
    cases hU with
    | refl _ => exact False.elim (hc hStop)
    | step _ hsP hrestP =>
      have hsP' : Step P _ _ :=
        h2fsalloc_step_of_agree (P := hole2_emptyProg) (Q := P) hsvc.symm rfl (hno _ hk) hs
      cases h2fsalloc_step_det hsP' hsP
      exact ih hrestP

private theorem h2fsalloc_stepsUntilInKeep_aux {keep : BitVec 64 → Bool}
    {s0 sStart s1 sf0 : State}
    (hAllP : ∀ (P : Program), P.svc = Syscall.standard →
      (∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none) →
      ∃ sf : State, StepsUntil P (SubroutineStop s0) sStart sf ∧ SubroutineStop s0 sf)
    (hU0 : StepsUntil hole2_emptyProg (SubroutineStop s0) s1 sf0) :
    h2fsalloc_StepsUntilInKeep hole2_emptyProg keep (SubroutineStop s0) sStart s1 →
    h2fsalloc_StepsUntilInKeep hole2_emptyProg keep (SubroutineStop s0) s1 sf0 := by
  induction hU0 with
  | refl s =>
    intro _
    exact h2fsalloc_StepsUntilInKeep.refl s
  | @step u v _ hcont hstep _ ih =>
    intro hPref
    have hkeep : keep u.pc = true := by
      by_cases hk : keep u.pc = true
      · exact hk
      · have hkf : keep u.pc = false := Bool.eq_false_iff.mpr hk
        have hno_probe : ∀ pc : BitVec 64, keep pc = true →
            (h2fsalloc_probeProg u.pc).externAt? pc = none := by
          intro pc hpc
          refine h2fsalloc_probeProg_externAt_ne (fun heq => ?_)
          rw [heq, hkf] at hpc
          cases hpc
        obtain ⟨sfBad, hUBad0, hStopBad⟩ := hAllP (h2fsalloc_probeProg u.pc) rfl hno_probe
        have hUBad : StepsUntil (h2fsalloc_probeProg u.pc) (SubroutineStop s0) u sfBad :=
          h2fsalloc_replay_prefix rfl hno_probe hPref hUBad0 hStopBad
        cases hUBad with
        | refl _ => exact False.elim (hcont hStopBad)
        | @step _ w _ _ hstepBad hrestBad =>
          have heSelf := h2fsalloc_probeProg_externAt_self u.pc
          cases hstepBad with
          | exec _ hfm =>
            unfold Program.fetchMem at hfm
            simp [heSelf] at hfm
          | halt_unmapped _ _ hext =>
            rw [heSelf] at hext; cases hext
          | extern _ hext _ _ =>
            cases heSelf.symm.trans hext
            have hw_eq : ({ u with status := .Halted } : State) = sfBad :=
              h2fsalloc_steps_eq_of_not_running (by simp)
                (h2fsalloc_stepsUntil_toSteps hrestBad)
            have hsf_halt : sfBad.status = .Halted := hw_eq ▸ rfl
            exact False.elim
              (h2fsalloc_not_subroutineStop_of_halted hsf_halt hStopBad)
          | extern_fault _ _ _ =>
            have hw_eq :=
              h2fsalloc_steps_eq_of_not_running (by simp)
                (h2fsalloc_stepsUntil_toSteps hrestBad)
            have hsf_ex : sfBad.status =
                .Exception "extern hook modified read-only memory or symbol table" :=
              hw_eq ▸ rfl
            exact False.elim
              (h2fsalloc_not_subroutineStop_of_exception hsf_ex hStopBad)
    exact h2fsalloc_StepsUntilInKeep.step hcont hkeep hstep
      (ih (hPref.snoc hcont hkeep hstep))

/-- Upgrade `StepsUntil hole2_emptyProg (SubroutineStop s0) sStart sf0` to
    `h2fsalloc_StepsUntilInKeep` whenever `StepsUntil P` reaches `SubroutineStop s0` for every
    `P` agreeing with `Syscall.standard` and extern-free on `keep`. -/
theorem h2fsalloc_stepsUntilInKeep_of_allProg {keep : BitVec 64 → Bool}
    {s0 sStart sf0 : State}
    (hAllP : ∀ (P : Program), P.svc = Syscall.standard →
      (∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none) →
      ∃ sf : State, StepsUntil P (SubroutineStop s0) sStart sf ∧ SubroutineStop s0 sf)
    (hU0 : StepsUntil hole2_emptyProg (SubroutineStop s0) sStart sf0) :
    h2fsalloc_StepsUntilInKeep hole2_emptyProg keep (SubroutineStop s0) sStart sf0 :=
  h2fsalloc_stepsUntilInKeep_aux hAllP hU0 (h2fsalloc_StepsUntilInKeep.refl sStart)


end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
