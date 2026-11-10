/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Proofs.StdCli.StartupPreTop
import CaseStudies.Hashbrown.Proofs.StdCli.StartupPost
import CaseStudies.Hashbrown.Proofs.StdCli.StartupPostCleanup
import CaseStudies.Hashbrown.Proofs.StdCli.StartupPostExit
import CaseStudies.Hashbrown.Proofs.StdCli.MainReadAndScan

/-!
# Layout-Generic Startup and Post-`main` Exit

Composes `_start` through `userMain` (including `mallocng` heap initialization) with post-`userMain`
`std::rt::cleanup` and `exit_group` over an arbitrary `ElfImage` matching `HbCliLayout`.
-/

set_option autoImplicit false

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup

/-- Startup state witness threaded across `userMain` into `hbPostMain_to_exit`. -/
structure HbPostMainFrame (P : Program) (C : HbCliLayout) (S : HbStartupLayout) (img : ElfImage)
    (inputs : ProcessInputs) (s0 s_main : State) (haveLse : BitVec 8) (R_frame : SepProp) : Prop where
  load_eq       : img.loadState inputs = .ok s0
  steps_to_main : Steps P s0 s_main
  codeLoaded_s0 : P.CodeLoaded s0.mem
  no_hooks      : P.NoHooks
  svc_eq        : P.svc = Syscall.standard
  mainState     : HbUserMainState P C.std img inputs s0 s_main

/-- Whole-`ElfImage` `Program.pureMem` execution theorem composing `_start` to `userMain`
    (with `mallocng` heap initialization) and post-`userMain` teardown to `exit_group`. -/
theorem hbElfImage_runsTo {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {img : ElfImage} {mpl : Obj.MultiPlacement}
    {inputs : ProcessInputs} {post : ProcessOutcome → Prop} {oom : State → Prop}
    (cPre : HbPreMainCode P C S) (cPost : HbPostMainCode P C S)
    (hv : C.Valid) (hS : S.Valid C) (hmatch : HbMatchesImage C S img = true)
    (hMpl : HbMallocngPlaced P C mpl)
    (hvalid : inputs.Valid) (hbudget : HashbrownStdinBudget inputs)
    (hrx : C.std.rxProgram img = P := by rfl)
    (hMain : ∀ (s0 s_main : State) (γ : GhostName) (e_init : BitVec 32) (R_frame : SepProp),
      let M := hbMallocngIface hMpl hbudget.1
      let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
      HbPostMainFrame P C S img inputs s0 s_main haveLse R_frame →
      ∃ oomSep : State → SepProp,
        (∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ oomSep sf ∗ R_frame) → oom sf) ∧
        SepWP P (C.std.beginShortBacktraceAddr + 0x0c#64) s_main
          (hbRodata C.hbPl ∗ M.Heap γ 0 0 s_main ∗ HbStdoutInv C M.toMallocngCoreIface γ false ∗
           HbStdinUninit C ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
           HbCliRoData C ∗ (muslErrnoAddr s_main ↦₃₂ e_init) ∗
           HbThreadIdInv C s_main.tpidrEl0 ∗
           (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ stackAt s_main.sp 261984)
          (fun s_ret Pf =>
            s_ret.sp = s_main.sp ∧
            post (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret) ∧
            ∃ (init : Bool) (lc_leak blk_leak : Nat) (e_ret : BitVec 32) (R_ret : SepProp),
              Pf ⊢ M.Heap γ (lc_leak + hbStdoutCost init) (blk_leak + hbStdoutBlocks init) s_ret ∗
                HbStdoutInv C M.toMallocngCoreIface γ init ∗
                (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗
                HbThreadIdInv C s_ret.tpidrEl0 ∗
                stackAt s_ret.sp 4304 ∗ R_ret)
          oomSep) :
    ElfImageRunsTo img inputs post oom := by
  let sl := StackLayout.of img inputs
  let M := hbMallocngIface hMpl hbudget.1
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  obtain ⟨s0, s_main, altBase, γ, e_init, hload, hcode0, hst1, hms,
    _halt4k, _haltAl, _haltFit, hnonull, hbnd_req, hm_main⟩ :=
    hbStartup_to_userMain cPre hv hS hmatch hMpl hvalid hbudget hrx
  let altOpt : Option (BitVec 64 × Nat) := some (altBase, hbExpectedAltRawSz sl.auxvEntries)
  let R_frame : SepProp :=
    (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
      HbCallerFrames C sl.sp0 ∗ HbPostMainGlobals C S ∗
      HbAltstackInv4k C S altOpt ∗
      HbAltstackMappedPre altOpt ∗
      HbAuxvTicket γ sl.auxvTableAddr sl.auxvEntries ∗
      stackAt (s_main.sp - 261984#64) 261936 ∗ ∃∗ R_unused : SepProp, R_unused
  have hf : HbPostMainFrame P C S img inputs s0 s_main haveLse R_frame :=
    ⟨hload, hst1, hcode0, cPre.no_hooks, cPre.svc_eq, hms⟩
  obtain ⟨oomSep, hoom_imp, hwp_main⟩ := hMain s0 s_main γ e_init R_frame hf
  obtain ⟨s_ret, hst2,
      ⟨hpc_r, hrun_r, Pf, hm_ret, hsp_r, hpost_r, init, lc_leak, blk_leak, e_ret, R_ret, hent_ret⟩ |
      ⟨hoom_st, hoom_sat⟩⟩ :=
    SepWP.to_reaches_pc hwp_main hm_main hms.codeLoaded
  · have hsp_ret : s_ret.sp = sl.sp0 - 0x170#64 := hsp_r.trans hms.sp_eq
    have hal_ret : s_ret.spAligned = true := by
      unfold State.spAligned
      rw [hsp_r]
      exact hms.spAligned_eq
    have hsp_lo_ret : 4304 ≤ s_ret.sp.toNat :=
      Nat.le_trans (by decide : 4304 ≤ 261984) (hsp_r ▸ hms.sp_headroom)
    have hraw : ∀ b sz, altOpt = some (b, sz) →
        sz = Arm64.pageAlignUp (hbAltstackReqSz sl.auxvEntries) := by
      intro _ _ h
      dsimp only [altOpt] at h
      cases h
      rfl
    have htear : ∀ s_t,
        M.toMallocngCoreIface.Heap γ lc_leak blk_leak s_t ∗
          HbAuxvTicket γ sl.auxvTableAddr sl.auxvEntries ⊢
        (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ sl.auxvTableAddr) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        ∃∗ R_dead : SepProp, R_dead :=
      fun s_t => hbHeap_teardown hMpl hbudget.1 γ lc_leak blk_leak sl.auxvTableAddr sl.auxvEntries s_t
    have hm_ret' := Satisfies.mono (sepConj_mono_left hent_ret) hm_ret
    have hm_exit : s_ret.mem ⊨
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
          HbCallerFrames C sl.sp0 ∗
          HbPostMainGlobals C S ∗
          HbAltstackInv4k C S altOpt ∗ HbAltstackMapped altOpt ∗
          HbStdoutInv C M.toMallocngCoreIface γ init ∗
          HbThreadIdInv C s_ret.tpidrEl0 ∗
          M.toMallocngCoreIface.Heap γ (lc_leak + hbStdoutCost init) (blk_leak + hbStdoutBlocks init) s_ret ∗
          HbAuxvTicket γ sl.auxvTableAddr sl.auxvEntries ∗
          (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗
          stackAt s_ret.sp 4304) ∗
        (R_ret ∗ stackAt (s_main.sp - 261984#64) 261936 ∗ ∃∗ R_unused : SepProp, R_unused) := by
      refine Satisfies.mono ?_ hm_ret'
      dsimp only [R_frame, altOpt, HbAltstackMappedPre, HbAltstackMapped, M]
      sep_entail
    exact hbPostMain_to_exit cPost hv hS htear hraw hnonull hbnd_req hload hcode0
      (hst1.trans hst2) hpc_r hrun_r hsp_ret hal_ret hsp_lo_ret hpost_r hm_exit
  · exact ElfImageRunsTo.of_oom hload ((hst1.trans hst2).to_pureMem cPre.no_hooks cPre.svc_eq)
      hoom_st (hoom_imp s_ret hoom_st hoom_sat)

end CaseStudies.Hashbrown.Proofs.StdCli
