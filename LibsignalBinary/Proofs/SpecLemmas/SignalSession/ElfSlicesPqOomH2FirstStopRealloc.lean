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
# Real-Run First-Stop Instance for `realloc`

**Checked by Lean.**

Follows the SR3 `(R)` pure-composition recipe (`08:28Z` / `P4-lead 08:31Z`) over
`hole2_keepSub` (`[0x469000, 0x46f000)` = `seg[2]` = `f3TrialRxProg`) for `__rust_realloc`
(target `f3RdlAddrs.realloc`):
1. **`h2fsrealloc_activeRealRun`:** from `ActiveF3CallPre (h2fsrealloc_spec mmpl) s0`,
   `ExecFrozen s0.mem`, `hole2_keepSub (s0.readReg64 .lr) = false`, and
   `f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)`, proves
   `ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.realloc s0`
   (killing Branch `(c)` `f3ReallocFallback mmpl` on `(hole2_ghFixed mpl mmpl).realloc`).
2. **Visited PCs in `hole2_keepSub` & scoped program lift:** proves
   `h2fsrealloc_StepsUntilIn hole2_keepSub hole2_emptyProg (SubroutineStop s0)
   (s0.setPC f3RdlAddrs.realloc) ((hole2_ghFixed mpl mmpl).realloc s0)`, pointwise
   `h2fsrealloc_ghFixed_visited_pcs_in_keepSub` (`∀ u` before `SubroutineStop s0`,
   `hole2_keepSub u.pc = true`), and `h2fsrealloc_ghFixed_firstStop_of_prog` /
   `h2fsrealloc_ghFixed_steps_of_call` lifting the exact hook output state
   `(hole2_ghFixed mpl mmpl).realloc s0` to any `Syscall.standard` program `P` with no extern
   hooks inside `hole2_keepSub` (`0` `sorry`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopRealloc

open Arm64 ProofLib
open Arm64.Obj (CodeBlock MultiPlacedLib MultiPlacement PlacedLib lookupBlockSym)
open ProofLib.ProgramReflection (WordTree)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng ProgContainsMultiLib)
open VerifiedLibraries.RustStd (mallocngPlacedCAddrs)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (RustCliAllocBudgetEntries rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.Fine
  (f3MallocngMpl f3RdlAddrs f3RxWordCount fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (fineHookRustCliAllocBudgetEntries)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen StubReachesTarget real_subroutine_run_of_stripS
   specPreservesFsTrace_realloc)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook specStripSInvariant_fine_realloc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_linkedAt_unique f3TrialElf
   f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_svc
   f3TrialRxWordTree_eq f3TrialRxWordTree_size f3Trial_allocMemcpyVm_ok f3Trial_progContainsMallocng
   f3Trial_seg5ShimBundle)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_ghFixed hole2_keep hole2_keepSub)

/-- `(γ, tp)`-indexed fine-budget `rustCliReallocBudgetSpec` family guarding
    `f3ReallocGhostHookFine` in `hole2_ghFixed`. -/
noncomputable def h2fsrealloc_spec [LibsignalPlacement] (mmpl : MultiPlacement)
    (γ : GhostName) (tp : BitVec 64) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × fineCostModel.σ) :=
  rustCliReallocBudgetSpec fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
    cliBudgetLimits

/-- `StepsUntil` refinement witnessing that every intermediate (pre-`stop`) executed state `s1`
    satisfies `keep s1.pc = true`. -/
inductive h2fsrealloc_StepsUntilIn (keep : BitVec 64 → Bool) (prog : Program)
    (stop : State → Prop) : State → State → Prop where
  | refl (s : State) : h2fsrealloc_StepsUntilIn keep prog stop s s
  | step {s1 s2 s3 : State}
      (h_cont : ¬ stop s1)
      (h_in : keep s1.pc = true)
      (h_step : Step prog s1 s2)
      (h_rest : h2fsrealloc_StepsUntilIn keep prog stop s2 s3) :
      h2fsrealloc_StepsUntilIn keep prog stop s1 s3

theorem h2fsrealloc_StepsUntilIn.toStepsUntil {keep : BitVec 64 → Bool} {prog : Program}
    {stop : State → Prop} {s1 s2 : State}
    (h : h2fsrealloc_StepsUntilIn keep prog stop s1 s2) :
    StepsUntil prog stop s1 s2 := by
  induction h with
  | refl s => exact StepsUntil.refl s
  | step hcont _ hstep _ ih => exact StepsUntil.step hcont hstep ih

theorem h2fsrealloc_StepsUntilIn.toSteps {keep : BitVec 64 → Bool} {prog : Program}
    {stop : State → Prop} {s1 s2 : State}
    (h : h2fsrealloc_StepsUntilIn keep prog stop s1 s2) :
    Steps prog s1 s2 :=
  h.toStepsUntil.toSteps

/-- Every state `u` reached before `stop` along a `h2fsrealloc_StepsUntilIn keep prog stop a sf`
    trace (with `stop sf`) has `keep u.pc = true`. -/
theorem h2fsrealloc_StepsUntilIn.visited_pc_keep {keep : BitVec 64 → Bool} {prog : Program}
    {stop : State → Prop} {a sf u : State}
    (hin : h2fsrealloc_StepsUntilIn keep prog stop a sf)
    (hstop : stop sf)
    (hu : Steps prog a u)
    (hbefore : ∀ w : State, Steps prog a w → Steps prog w u → ¬ stop w) :
    keep u.pc = true := by
  induction hin with
  | refl s =>
    exact False.elim (hbefore s (Steps.refl s) hu hstop)
  | @step s1 s2 s3 _ hk1 hstep12 _ ih =>
    cases hu with
    | refl _ => exact hk1
    | step hstep1b hbu =>
      cases Step.deterministic hstep12 hstep1b
      exact ih hstop hbu (fun w h2w hwu => hbefore w (Steps.step hstep12 h2w) hwu)

/-- Lift a `h2fsrealloc_StepsUntilIn keep P₁ stop` trace to any program `P₂` with the same `svc`
    and no extern hooks on `keep` (when `P₁` also has no extern hooks on `keep`). -/
theorem h2fsrealloc_StepsUntilIn.liftProg {keep : BitVec 64 → Bool} {P₁ P₂ : Program}
    {stop : State → Prop} {a sf : State}
    (hsvc₁ : P₁.svc = Syscall.standard)
    (hsvc₂ : P₂.svc = Syscall.standard)
    (hno₁ : ∀ pc : BitVec 64, keep pc = true → P₁.externAt? pc = none)
    (hno₂ : ∀ pc : BitVec 64, keep pc = true → P₂.externAt? pc = none)
    (h : h2fsrealloc_StepsUntilIn keep P₁ stop a sf) :
    h2fsrealloc_StepsUntilIn keep P₂ stop a sf := by
  induction h with
  | refl s => exact .refl s
  | @step s1 s2 s3 hcont hk hstep _ ih =>
    have he₁ : P₁.externAt? s1.pc = none := hno₁ s1.pc hk
    have he₂ : P₂.externAt? s1.pc = none := hno₂ s1.pc hk
    have hfm_eq : P₂.fetchMem s1.mem s1.pc = P₁.fetchMem s1.mem s1.pc := by
      unfold Program.fetchMem
      rw [he₁, he₂]
    have hstep₂ : Step P₂ s1 s2 := by
      cases hstep with
      | @exec inst hrun hfm =>
        have hev : P₂.evalInst inst s1 = P₁.evalInst inst s1 := by
          unfold Program.evalInst
          rw [hsvc₁, hsvc₂]
        rw [← hev]
        exact Step.exec hrun (hfm_eq.trans hfm)
      | halt_unmapped hrun hfm _ =>
        exact Step.halt_unmapped hrun (hfm_eq.trans hfm) he₂
      | extern _ he _ _ =>
        rw [he₁] at he; cases he
      | extern_fault _ he _ =>
        rw [he₁] at he; cases he
    exact .step hcont hk hstep₂ ih

private def h2fsrealloc_probeEx (s : State) : State :=
  { s with status := .Exception "h2fsrealloc_probe" }

private def h2fsrealloc_probeProg (pc₀ : BitVec 64) : Program where
  base := 0#64
  code := []
  stubs := [("__probe", pc₀.toNat)]
  externs sym := if sym == "__probe" then some h2fsrealloc_probeEx else none
  svc := Syscall.standard

private theorem h2fsrealloc_probeProg_svc (pc₀ : BitVec 64) :
    (h2fsrealloc_probeProg pc₀).svc = Syscall.standard := rfl

private theorem h2fsrealloc_probeProg_externAt_self (pc₀ : BitVec 64) :
    (h2fsrealloc_probeProg pc₀).externAt? pc₀ = some h2fsrealloc_probeEx := by
  unfold Program.externAt? Program.hookAtOff? h2fsrealloc_probeProg
  rw [BitVec.sub_zero]
  simp

private theorem h2fsrealloc_probeProg_externAt_of_ne {pc₀ pc : BitVec 64} (hne : pc ≠ pc₀) :
    (h2fsrealloc_probeProg pc₀).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? h2fsrealloc_probeProg
  rw [BitVec.sub_zero]
  have hne_nat : pc₀.toNat ≠ pc.toNat := fun h => hne (BitVec.eq_of_toNat_eq h.symm)
  simp [hne_nat]

private theorem h2fsrealloc_subroutineStop_not_exception {s0 sf : State}
    (h : SubroutineStop s0 sf) (msg : String) :
    sf.status ≠ .Exception msg := by
  rcases h with ⟨_, _, hr⟩ | hp | ⟨_, he⟩ | ho
  · rw [hr]; nofun
  · rw [hp]; nofun
  · rw [he]; nofun
  · rw [ho]; nofun

private theorem h2fsrealloc_stepsUntil_preserves_exception {P : Program} {stop : State → Prop}
    {a sf : State} {msg : String}
    (h : StepsUntil P stop a sf) (ha : a.status = .Exception msg) :
    sf.status = .Exception msg := by
  cases h with
  | refl _ => exact ha
  | step _ h1 _ =>
    have hrun : a.status = .Running := Arm64.Step.status_running h1
    rw [ha] at hrun
    cases hrun

private theorem h2fsrealloc_emptyProg_externAt (pc : BitVec 64) :
    hole2_emptyProg.externAt? pc = none := rfl

private theorem h2fsrealloc_step_empty_to_probe {pc₀ : BitVec 64} {s1 s2 : State}
    (h : Step hole2_emptyProg s1 s2) (hne : s1.pc ≠ pc₀) :
    Step (h2fsrealloc_probeProg pc₀) s1 s2 := by
  have he0 : hole2_emptyProg.externAt? s1.pc = none := rfl
  have hep : (h2fsrealloc_probeProg pc₀).externAt? s1.pc = none :=
    h2fsrealloc_probeProg_externAt_of_ne hne
  have hfm_eq : (h2fsrealloc_probeProg pc₀).fetchMem s1.mem s1.pc =
      hole2_emptyProg.fetchMem s1.mem s1.pc := by
    unfold Program.fetchMem
    rw [he0, hep]
  cases h with
  | @exec inst hrun hfm =>
    exact Step.exec hrun (hfm_eq.trans hfm)
  | halt_unmapped hrun hfm _ =>
    exact Step.halt_unmapped hrun (hfm_eq.trans hfm) hep
  | extern _ he _ _ =>
    rw [he0] at he; cases he
  | extern_fault _ he _ =>
    rw [he0] at he; cases he

private theorem h2fsrealloc_stepsUntilIn_of_probes {keep : BitVec 64 → Bool} {s0 a sf : State}
    (h0 : StepsUntil hole2_emptyProg (SubroutineStop s0) a sf)
    (hProbes : ∀ pc₀ : BitVec 64, keep pc₀ = false →
      ∃ sf_p : State,
        StepsUntil (h2fsrealloc_probeProg pc₀) (SubroutineStop s0) a sf_p ∧
        SubroutineStop s0 sf_p) :
    h2fsrealloc_StepsUntilIn keep hole2_emptyProg (SubroutineStop s0) a sf := by
  induction h0 with
  | refl s => exact .refl s
  | @step s1 s2 s3 hcont hstep0 _ ih =>
    have hin : keep s1.pc = true := by
      cases hk : keep s1.pc with
      | true => rfl
      | false =>
        obtain ⟨sf_p, huntilP, hstopP⟩ := hProbes s1.pc hk
        cases huntilP with
        | refl _ => exact False.elim (hcont hstopP)
        | step _ hstepP hrestP =>
          have hself := h2fsrealloc_probeProg_externAt_self s1.pc
          cases hstepP with
          | exec _ hfm =>
            unfold Program.fetchMem at hfm
            rw [hself] at hfm
            simp at hfm
          | halt_unmapped _ _ hext =>
            rw [hself] at hext; cases hext
          | extern _ hext _ _ =>
            have hf := Option.some.inj (hext.symm.trans hself)
            subst hf
            have hex := h2fsrealloc_stepsUntil_preserves_exception hrestP rfl
            exact False.elim (h2fsrealloc_subroutineStop_not_exception hstopP _ hex)
          | extern_fault _ _ _ =>
            have hex := h2fsrealloc_stepsUntil_preserves_exception hrestP rfl
            exact False.elim (h2fsrealloc_subroutineStop_not_exception hstopP _ hex)
    refine .step hcont hin hstep0 (ih fun pc₀ hpc₀ => ?_)
    have hne : s1.pc ≠ pc₀ := fun heq => by rw [heq, hpc₀] at hin; cases hin
    have hstepP0 := h2fsrealloc_step_empty_to_probe hstep0 hne
    obtain ⟨sf_p, huntilP, hstopP⟩ := hProbes pc₀ hpc₀
    cases huntilP with
    | refl _ => exact False.elim (hcont hstopP)
    | step _ hstepP' hrestP =>
      cases Step.deterministic hstepP0 hstepP'
      exact ⟨sf_p, hrestP, hstopP⟩

private theorem h2fsrealloc_mng_placeable (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

private theorem h2fsrealloc_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem h2fsrealloc_toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

/-- Every `mallocngLib` code byte in `cliElfBytes` lies inside `hole2_keepSub` (`[0x469000, 0x46f000)`). -/
theorem h2fsrealloc_keepSub_mallocng (mmpl : MultiPlacement)
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
        ((h2fsrealloc_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (h2fsrealloc_mng_placeable mmpl hMm) (h2fsrealloc_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hlo : 0x469000 ≤ f3MngCodeLo := by decide
    have hhi : f3MngCodeHi ≤ 0x46f000 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat :=
      h2fsrealloc_toNat_add_ofNat_of_lt (by omega)
    rw [heq_a] at ht
    unfold hole2_keepSub
    exact decide_eq_true ⟨by omega, by omega⟩

/-- `hole2_keepSub` (`[0x469000, 0x46f000)`) is a subset of `hole2_keep`. -/
theorem h2fsrealloc_keep_of_keepSub {a : BitVec 64} (h : hole2_keepSub a = true) :
    hole2_keep a = true := by
  unfold hole2_keepSub at h
  unfold hole2_keep
  have h' : 0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000 := of_decide_eq_true h
  exact decide_eq_true (Or.inr h')

/-- Contrapositive: `hole2_keep a = false → hole2_keepSub a = false`. -/
theorem h2fsrealloc_keepSub_false_of_keep_false {a : BitVec 64} (h : hole2_keep a = false) :
    hole2_keepSub a = false := by
  cases hs : hole2_keepSub a with
  | false => rfl
  | true =>
    have hk := h2fsrealloc_keep_of_keepSub hs
    rw [h] at hk
    cases hk

/-- Every `mallocngLib` code byte in `cliElfBytes` also lies inside `hole2_keep`. -/
theorem h2fsrealloc_keep_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keep a = true :=
  fun a hsome => h2fsrealloc_keep_of_keepSub (h2fsrealloc_keepSub_mallocng mmpl hMm a hsome)

/-- `f3TrialRxProg` (`seg[2]`, `[0x469000, 0x46f000)`) has identical `CodeLoaded` under
    `stripExecOutside hole2_keepSub` and `stripExecOutside hole2_keep`. -/
theorem h2fsrealloc_rxProg_codeLoaded_keepSub_iff_keep (m : Memory) :
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
      apply h2fsrealloc_toNat_add_ofNat_of_lt
      rw [hbase, hbase_nat]
      rw [hlen, hwc] at hi
      omega
    unfold hole2_keepSub
    refine decide_eq_true ⟨?_, ?_⟩ <;> (rw [ht, hbase, hbase_nat]; rw [hlen, hwc] at hi; omega)
  constructor <;> intro hL
  · refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
    have hs := hinSub i hi
    have hk := h2fsrealloc_keep_of_keepSub hs
    have hb := hL.byte_eq i hi
    have hp := hL.perm_eq i hi
    have hlf := hL.isLazyFree_eq i hi
    rw [strip_read8] at hb ⊢
    rw [strip_perm_of_keep hs] at hp
    rw [strip_perm_of_keep hk]
    rw [strip_isLazyFree] at hlf ⊢
    exact ⟨hb, hp, hlf⟩
  · refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
    have hs := hinSub i hi
    have hk := h2fsrealloc_keep_of_keepSub hs
    have hb := hL.byte_eq i hi
    have hp := hL.perm_eq i hi
    have hlf := hL.isLazyFree_eq i hi
    rw [strip_read8] at hb ⊢
    rw [strip_perm_of_keep hk] at hp
    rw [strip_perm_of_keep hs]
    rw [strip_isLazyFree] at hlf ⊢
    exact ⟨hb, hp, hlf⟩

private theorem h2fsrealloc_mng_fnAddr_eq (mmpl : MultiPlacement)
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

private theorem h2fsrealloc_mng_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  unfold mallocngPlacedCAddrs
  simp only [h2fsrealloc_mng_fnAddr_eq mmpl hMm]

private theorem h2fsrealloc_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hPl1 := h2fsrealloc_mng_placeable mmpl hMm
  have hIn1 := h2fsrealloc_mng_inElf mmpl hMm
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

/-- `RustCliAllocBudgetEntries` bundle over `f3TrialRxProg` (`seg[5]`) at `f3RdlAddrs`. -/
theorem h2fsrealloc_rdlEntries [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntries fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      f3TrialRxProg f3RdlAddrs := by
  have hShims := f3Trial_seg5ShimBundle.rdlShims
  rw [← h2fsrealloc_mng_cAddrs_eq mmpl hMm] at hShims
  exact (fineHookRustCliAllocBudgetEntries
    (h2fsrealloc_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hShims
    f3Trial_allocMemcpyVm_ok).toPlaced

/-- Compiled `f3TrialRxProg` `subroutine_ok` for `__rust_realloc` (`f3RdlAddrs.realloc`). -/
theorem h2fsrealloc_rdlRealloc_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg f3RdlAddrs.realloc (h2fsrealloc_spec mmpl γ tp) :=
  (h2fsrealloc_rdlEntries mmpl hMm γ tp).realloc cliBudgetLimits

private theorem h2fsrealloc_prePC [LibsignalPlacement] (mmpl : MultiPlacement)
    (γ : GhostName) (tp : BitVec 64)
    (x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × fineCostModel.σ)
    (s : State) (pc : BitVec 64) :
    (h2fsrealloc_spec mmpl γ tp).pre x (s.setPC pc) =
      (h2fsrealloc_spec mmpl γ tp).pre x s := by
  cases s; rfl

private theorem h2fsrealloc_outPC [LibsignalPlacement] (mmpl : MultiPlacement)
    (γ : GhostName) (tp : BitVec 64)
    (x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × fineCostModel.σ)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome (h2fsrealloc_spec mmpl γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (h2fsrealloc_spec mmpl γ tp) x R s0 sf := by
  cases s0; exact id

/-- Parametric `keep` / `P` real-run first-stop theorem for `realloc` (`f3RdlAddrs.realloc`)
via `h2fsrealloc_rdlRealloc_ok` and `real_subroutine_run_of_stripS`. -/
theorem h2fsrealloc_firstStop_of_keep [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {keep : BitVec 64 → Bool}
    (hKeepMallocng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsrealloc_spec mmpl) s0)
    (hFr : ExecFrozen s0.mem)
    (hLr : keep (s0.readReg64 .lr) = false)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAddrs.realloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS hsvc f3TrialRxProg_svc hno_ext f3TrialRxProg_no_ext
      (h2fsrealloc_rdlRealloc_ok mmpl hMm γ tp)
      (specStripSInvariant_fine_realloc γ mmpl tp cliElfImage.brkStart hKeepMallocng
        cliBudgetLimits)
      (specPreservesFsTrace_realloc _ cliBudgetLimits)
      (h2fsrealloc_prePC mmpl γ tp)
      (h2fsrealloc_outPC mmpl γ tp)
      hRun hSp hSat hFr hLr hCode
  exact ⟨sf, huntil, hstop, hfs, hfst, hfr_sf⟩

/-- `ActiveRealRun` for `realloc` (`f3RdlAddrs.realloc`) under `hole2_keepSub` (`[0x469000, 0x46f000)`) premises
(making `f3ReallocFallback mmpl` unreachable). -/
theorem h2fsrealloc_activeRealRun [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsrealloc_spec mmpl) s0)
    (hFr : ExecFrozen s0.mem)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.realloc s0 :=
  ⟨hFr, hLr, hCode,
    h2fsrealloc_firstStop_of_keep mmpl hMm (h2fsrealloc_keepSub_mallocng mmpl hMm)
      rfl (fun _ _ => rfl) hPre hFr hLr hCode⟩


end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopRealloc
