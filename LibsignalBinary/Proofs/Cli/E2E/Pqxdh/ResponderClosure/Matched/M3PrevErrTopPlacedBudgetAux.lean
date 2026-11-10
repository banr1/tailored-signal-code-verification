/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Helpers and Block-`518` Error Steppers for `Matched.M3PrevErrTopPlacedBudget`

`FromVPostTdEnv` / `FreeOnlyEvs` envelope lemmas, `SepWPp` sequencing helpers, Block-`511`
`drop_spe2_placed_ok_at_of_dealloc`, and Block-`518` pool-synchronizing Substage P3.5 error and
epilogue basic-block steppers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal2Spec growOneSpeSpec
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (dpClosureEntryM3Placed prevSessionsEmptyAt)
open CryptoVerification.CliHandshake.RespClosurePlaced CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalTripleRatchet.Getters hiding dropSpeSpec
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  PoolPreserved RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWP_lscro_steps_m3_placed
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromFEnv FromMEnv FromVPostTdEnv SegTailEnv
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## `FreeOnlyEvs` and `FromVPostTdEnv` envelope lemmas -/

theorem freeOnlyEvs_nil : FreeOnlyEvs [] := by
  intro _ h; cases h

theorem freeOnlyEvs_dealloc (sz al : Nat) : FreeOnlyEvs (rustDeallocEvents sz al) := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  exact ⟨al, sz, hev⟩

theorem freeOnlyEvs_append {e1 e2 : List AllocEvent}
    (h1 : FreeOnlyEvs e1) (h2 : FreeOnlyEvs e2) : FreeOnlyEvs (e1 ++ e2) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

theorem growOneSpeEnv_zero_192 : GrowOneSpeEnv 0#64 (rustAllocEvents 192 8) := by
  unfold GrowOneSpeEnv
  exact Or.inl ⟨rfl, rfl⟩

theorem segTailEnv_alloc17 : SegTailEnv (rustAllocEvents 17 1) :=
  Or.inr ⟨[], rustAllocEvents 17 1, rfl, freeOnlyEvs_nil, rfl⟩

theorem fitsEnv_growOneSpe_of_fromVPostTd {M : AllocCostModel} {lim : BudgetLimits} {st_b : M.σ}
    (hfits : FitsEnv M lim st_b FromVPostTdEnv) :
    FitsEnv M lim st_b (GrowOneSpeEnv 0#64) :=
  fun evs hg => hfits evs (Or.inr (Or.inl hg))

theorem fitsEvents_alloc17_of_fromVPostTd {M : AllocCostModel} {lim : BudgetLimits} {st_b : M.σ}
    (hfits : FitsEnv M lim st_b FromVPostTdEnv) :
    FitsEvents M lim (M.stepEvents (rustAllocEvents 192 8) st_b) (rustAllocEvents 17 1) := by
  have hmem : FromVPostTdEnv (rustAllocEvents 192 8 ++ rustAllocEvents 17 1) :=
    Or.inr (Or.inr ⟨rustAllocEvents 192 8, rustAllocEvents 17 1, rfl,
      growOneSpeEnv_zero_192, Or.inl segTailEnv_alloc17⟩)
  exact ((fitsEvents_append M lim (rustAllocEvents 192 8) (rustAllocEvents 17 1) st_b).mp
    (hfits _ hmem)).2

theorem fromVPostTdEnv_of_nondup {evs_drop1 evs_tail : List AllocEvent}
    (hd1 : FreeOnlyEvs evs_drop1) (htl : FreeOnlyEvs evs_tail) :
    FromVPostTdEnv (rustAllocEvents 192 8 ++ (rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail))) :=
  Or.inr (Or.inr ⟨rustAllocEvents 192 8, rustAllocEvents 17 1 ++ (evs_drop1 ++ evs_tail), rfl,
    growOneSpeEnv_zero_192,
    Or.inr ⟨rustAllocEvents 17 1, evs_drop1 ++ evs_tail, rfl,
      segTailEnv_alloc17, freeOnlyEvs_append hd1 htl⟩⟩)

/-! ## `SepWPp` sequencing, call, and read-only string helpers -/

theorem bind_sepWP_lscro_frame_err [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_lscro_steps_m3_placed hcro hstep hP
    (fun sm _ hpcm hrunm hcrom hregs => hnext sm hpcm hrunm hcrom hregs)

theorem call_raw_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, _⟩ := hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right
  · rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hcro.of_keepsFrozen hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

theorem call_lscl_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  call_raw_nopanic_err (spec := withLsCodeLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalCodeLoaded lsmpl s.mem) (T := T) (F := F) hcro hcall hpc hrun hsp hlr
    (by dsimp only [withLsCodeLoaded]; rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure])
    ⟨hφ, hcro.1⟩ hP hpan_false hexit_false hnext hoom_false

theorem call_lscl_ro_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (withLsRoLoaded lsmpl spec).pre x s = (⌜φ ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [withLsRoLoaded]; rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_lscl_nopanic_err (spec := withLsRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcro.2⟩ hP hpan_false hexit_false hnext hoom_false

private def decryptionFailedBytes : List (BitVec 8) :=
  [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8] ++
  ([0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8] ++ [0x64#8])

private theorem pointsToBytesRO_decryptionFailed_err (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedBytes) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  dsimp only [decryptionFailedBytes]
  rw [pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO_cons,
    pointsToBytesRO_nil, sepConj_emp, show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  simp only [BitVec.reduceAppend, sepConj_assoc]

theorem intro_lsro_decryptionFailed_err [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hro0 : s.mem ⊨ ((lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedBytes) ∗ (P ∗ R) :=
    lsro_intro_chk hcro.2 (by decide +kernel) hm
  change s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedBytes) ∗ (P ∗ R) at hro0
  rw [pointsToBytesRO_decryptionFailed_err] at hro0
  have hro1 : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hro0
  exact SepWPp.drop_frame (P_drop := (lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8)
    (by sep_ac_rfl) hwp R hro1 hL

/-! ## Block-`511` budget-threaded `drop_spe2_placed_ok_at_of_dealloc` -/

open DropGlueFacts in
private theorem spe2JumpTable_placed_byte' (base : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails (base ↦ᵣ speJumpTable) ((base + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h : (base ↦ᵣ speJumpTable) = (base ↦ᵣ speJumpTable.take i) ∗
      (((base + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗ ((base + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]; exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem spe2_false_elim' {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP; intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm; exact False.elim hm.1

private theorem sepWP_bind_lscl [LibsignalPlacement] {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun s1 P1 => LibsignalCodeLoaded lsmpl s1.mem → SepWP prog target_pc s1 P1 post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm hL; rcases h.elim hm hL with ⟨s1, hsteps, ⟨-, -, P1, hm1, hnext⟩ | ⟨hoom, hf⟩⟩
  · have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := ⟨hcl, hro⟩
    rcases (hnext (hcro.of_keepsFrozen hsteps.keepsFrozen).1).elim hm1 (hsteps.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps2, Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps2, Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨s1, hsteps, Or.inr ⟨hoom, hf⟩⟩

private theorem freeOnlyPool_nil' {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sf : State) :
    A.pool lim st sf ⊢
      ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf :=
  Entails.sepExists_right [] (Entails.pure_right freeOnlyEvs_nil (Entails.refl _))

private theorem freeOnlyPool_dealloc' {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sz al : Nat) (sf : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) st) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf :=
  Entails.sepExists_right (rustDeallocEvents sz al)
    (Entails.pure_right (freeOnlyEvs_dealloc sz al) (Entails.refl _))

open DropGlueFacts in
private theorem spe_str_cap0_budget' (pool : SepProp) (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro ∗ stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStack) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (spe_str_cap0_pre_weaken_full a w cap ptr sp fp lr x20 x19 ro pool)

open DropGlueFacts in
private theorem spe_noop_budget' (pool : SepProp) (a w sp fp lr x20 x19 : BitVec 64)
    (ro : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStack) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (spe_noop_pre_weaken_full a w sp fp lr x20 x19 ro pool)

private theorem spe_tail_dealloc_budget' (pool : SepProp)
    (a w cap ptr sp fp lr x20 x19 : BitVec 64) (ro live1 live2 : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro ∗ live1 ∗ live2 ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 4128#64) 32 ∗
        stackAt sp allocHookStack ∗ live1 ∗ live2) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (SatEntails.trans (spe_tail_dealloc_pre_weaken a w cap ptr sp fp lr x20 x19 ro (live1 ∗ live2) pool)
      (SatEntails.of_eq (by sep_ac_rfl)))

set_option maxHeartbeats 1600000 in
open DropGlueFacts in
theorem drop_spe2_placed_ok_at_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) := by
  have hd511_cl : subroutine_ok ((CliHandshake.Placed.blkPC_511).rebase (CliHandshake.Placed.blkPl_511).base ext)
      (lsρ Getters.lsRustDeallocSym) (withLsCodeLoaded lsmpl (rustCliDeallocBudgetSpec M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := (CliHandshake.Placed.blkPC_511).rebase (CliHandshake.Placed.blkPl_511).base ext)
      (subroutine_ok_withLsCodeLoaded_of_plain hdealloc) (by decide)
  have h511 : subroutine_ok ((CliHandshake.Placed.blkPC_511).rebase (CliHandshake.Placed.blkPl_511).base ext) (CliHandshake.Placed.blkPl_511).base
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) := by
    simp only [withLsCodeLoaded, withLsRoLoaded, dropSpeSpec, pure_sepConj_pure_assoc]
    simp only [withLsCodeLoaded, rustCliDeallocBudgetSpec, pure_sepConj_pure_assoc] at hd511_cl
    wp_init x s0; rcases x with ⟨⟨a, fnName, e⟩, st⟩; dsimp only at *
    have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
    subst hx0
    have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
    have hro : LibsignalRoLoaded lsmpl s0.mem := by assumption
    have h_intro_jt : ∀ {P : SepProp} {post : State → SepProp → Prop},
        SepWP ((CliHandshake.Placed.blkPC_511).rebase (CliHandshake.Placed.blkPl_511).base ext) (s0.readReg64 (Reg.gpr 30#5)) s0
          (((lsρ spe2JumpTableSym) ↦ᵣ speJumpTable) ∗ P) post →
        SepWP ((CliHandshake.Placed.blkPC_511).rebase (CliHandshake.Placed.blkPl_511).base ext) (s0.readReg64 (Reg.gpr 30#5)) s0 P post := by
      intro P post h; unfold SepWP at h ⊢; intro R hm; have hR := h R; rw [sepConj_assoc] at hR
      exact hR (lsro_intro_chk hro (by decide +kernel) hm)
    refine h_intro_jt ?_
    nth_rw 1 [stackAt_dropSpe_split s0.sp]; cells_unfold; wp_pull_exists
    cases e with
    | panic => simp only [speAt]; exact spe2_false_elim'
    | invalidState =>
      refine Getters.SepWP.weaken_pre_sat (spe_str_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_expose A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
      wp_pull_exists; rename_i cap ptr
      by_cases hcap : cap = 0#64
      · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
        simp only [State.setMem_setMem]
        refine Getters.SepWP.weaken_pre_sat (spe_str_cap0_budget' _ _ _ _ _ s0.sp _ _ _ _ _) ?_
        apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
      · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
        refine sepWP_bind_lscl hcl hro (mid := lsρ Getters.lsRustDeallocSym) ?_
        wp_steps_sync_pool (lsρ Getters.lsRustDeallocSym)
        simp only [State.setMem_setMem]
        refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
        refine Getters.SepWP.weaken_pre_sat (spe_tail_dealloc_budget' _ (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp _ _ _ _ _ _ _) ?_
        wp_call hd511_cl (ptr, cap.toNat, 1, st)
        have htr_d : sf.trace = s0.trace := ‹AllocCallPreserved _ sf›.2.1
        refine SepWP.weaken_pre (spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) (A.pool lim _ sf) s0.sp) ?_
        apply SepWP.fold (freeOnlyPool_dealloc' A lim st cap.toNat 1 sf) (by sep_focus); wp_done
    | invalidMessage t r =>
      refine Getters.SepWP.weaken_pre_sat (spe_str_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_expose A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
      wp_pull_exists; rename_i cap ptr
      by_cases hcap : cap = 0#64
      · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
        simp only [State.setMem_setMem]
        refine Getters.SepWP.weaken_pre_sat (spe_str_cap0_budget' _ _ _ _ _ s0.sp _ _ _ _ _) ?_
        apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
      · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
        refine sepWP_bind_lscl hcl hro (mid := lsρ Getters.lsRustDeallocSym) ?_
        wp_steps_sync_pool (lsρ Getters.lsRustDeallocSym)
        simp only [State.setMem_setMem]
        refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
        refine Getters.SepWP.weaken_pre_sat (spe_tail_dealloc_budget' _ (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp _ _ _ _ _ _ _) ?_
        wp_call hd511_cl (ptr, cap.toNat, 1, st)
        have htr_d : sf.trace = s0.trace := ‹AllocCallPreserved _ sf›.2.1
        refine SepWP.weaken_pre (spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) (A.pool lim _ sf) s0.sp) ?_
        apply SepWP.fold (freeOnlyPool_dealloc' A lim st cap.toNat 1 sf) (by sep_focus); wp_done
    | invalidProtobufEncoding =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 2 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | ciphertextMessageTooShort n =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | legacyCiphertextVersion v =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | unrecognizedCiphertextVersion v =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | noKeyTypeIdentifier =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 7 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | badKeyType t =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | badKeyLength n =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | invalidKeyAgreement =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 10 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | invalidSessionStructure r =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
    | duplicatedMessage idx c =>
      refine Getters.SepWP.weaken_pre_sat (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl (spe2JumpTable_placed_byte' (lsρ spe2JumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5)); simp only [State.setMem_setMem]
      refine Getters.SepWP.weaken_pre_sat (spe_noop_budget' _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil' A lim st _) (by sep_focus); wp_done
  exact ls_subroutine_ok_of_block (callerProg := lsProg_518 ext) h511 (by decide)

/-! ## Block-`518` pool-synchronizing Substage P3.5 error steppers -/

private def sessionShimNormSpec : Spec Unit where
  pre := fun _ _ => ⌜True⌝ ∗ emp
  post := fun _ s0 sf => ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗ emp

private theorem subroutine_ok_sessionShimNorm {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry sessionShimBudgetSpec) :
    subroutine_ok prog entry sessionShimNormSpec := by
  refine subroutine_ok.of_codeLoaded fun u R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [sessionShimNormSpec] at hpre
  rw [sepConj_assoc, emp_sepConj, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome u R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimSpec]
    rw [emp_sepConj]; exact hpre.2
  · rcases hout with ⟨hret, hcs, hpost⟩ | hp | he | ho
    · left; refine ⟨hret, hcs, ?_⟩
      dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
      dsimp only [sessionShimNormSpec]
      rw [sepConj_assoc, emp_sepConj, satisfies_pure_sepConj]
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩
    · right; left; exact hp
    · right; right; left; exact he
    · right; right; right; exact ho

theorem p3_err_dup_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p3_err_nondup_a_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag e1 e2 e3 e4 e5 u930 u938 u940 u948 u950 u958 : BitVec 64)
    (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64) (herr_ne_dup : errTag ≠ 0x8000000000000017#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 519) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗ ((s.sp + 0x950#64) ↦₆₄ u950) ∗
       ((s.sp + 0x958#64) ↦₆₄ u958) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((s.sp + 0x930#64) ↦₆₄ errTag) ∗ ((s.sp + 0x938#64) ↦₆₄ e1) ∗
          ((s.sp + 0x940#64) ↦₆₄ e2) ∗ ((s.sp + 0x948#64) ↦₆₄ e3) ∗ ((s.sp + 0x950#64) ↦₆₄ e4) ∗
          ((s.sp + 0x958#64) ↦₆₄ e5) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x2 = 7#64 ∧ s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x930#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2d9c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ok := cond_ne_adds64_of_ne_neg2 herr_ne_ok
  have hcond_dup := cond_eq_subs64_of_ne_dup herr_ne_dup
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 519)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p3_err_nondup_b_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2d9c#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 42) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2db4#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 42)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p3_err_nondup_c_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimBudgetSpec)
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2db4#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (lsProg_518 ext) (dpClosureEntryM3Placed + 0x2eac#64) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗ ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((s.sp + 0x270#64) ↦₆₄ errTag) ∗ ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗ ((s.sp + 0x288#64) ↦₆₄ e3) ∗ ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗ ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim' := subroutine_ok_sessionShimNorm hshim
  dsimp only [sessionShimNormSpec] at hshim'
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have herr0 : 0#64 * 0x30#64 + errsPtr = errsPtr := by bv_arith
  dsimp only [dpClosureEntryM3Placed, lsLogFilterAddr] at hpc ⊢
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  wp_call hshim' ()
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2eac#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p3_alloc_2eac_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (st : M.σ) (s : State) (F : SepProp)
    (hfits17 : FitsEvents M lim st (rustAllocEvents 17 1))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2eac#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x2eb0#64) s
      ((A.pool lim st s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool lim (M.stepEvents (rustAllocEvents 17 1) st) s2 ∗
                stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (fun _ _ => False) := by
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  have hbl : SepWP (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s
      (A.pool lim st s)
      (fun s1 P_f => (P_f ⊢ A.pool lim st s1) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2eb0#64) := by
    dsimp only [dpClosureEntryM3Placed] at hpc ⊢
    wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm])
      ⟨Entails.of_eq (sepConj_emp _),
        by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
        by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
        ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
         by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
         by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
         by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
         by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
         by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩,
        by simp_all [wp_norm, arm64_norm]⟩
  refine bind_sepWP_lscro_frame_err (F := stackAt s.sp allocHookStack ∗ F) hcro hbl (by sep_ac_rfl)
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hlay17 : RustLayoutOk 17 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧
      RustLayoutOk 17 1 ∧ FitsEvents M lim st (rustAllocEvents 17 1) ∧
      LsRetAddr624 (s1.readReg64 .lr) :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, hlay17, hfits17, by
      change LsRetAddr624 (s1.readReg64 .x30)
      rw [hlr1]
      exact lsRetAddr624_blockPlacement_base_add 518 0x2eb0#64 (by decide) (by decide)⟩
  refine call_raw_nopanic_err (spec := rustCliAllocNoOomSpec M A lim false) (x := (17, 1, st))
    (T := A.pool lim st s1 ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc_nooom hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1]) hφ (by sep_ac_rfl)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, hsp1, sepConj_assoc]
  exact SepWPp.pure_elim fun ⟨hacp, hoom, _⟩ =>
    SepWPp.done hpc2 hrun2 ⟨Entails.of_eq (by sep_ac_rfl), hoom, hsp2, hacp.2.1.trans htr1, hcs, hcro2⟩

theorem p3_err_nondup_d_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr dfPtr ro0 ro1 u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8) (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2eb0#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗ ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗ ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗ ((s.sp + 0x278#64) ↦₆₄ u_278) ∗ ((s.sp + 0x280#64) ↦₆₄ u_280) ∗
       ((s.sp + 0x288#64) ↦₆₄ u_288) ∗ ((s.sp + 0x290#64) ↦₈ u_290) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗ ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗ ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗ ((s.sp + 0x290#64) ↦₈ 3#8) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed, lsρ] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem p3_err_tail_dup_a_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr ssCap v_27c v_284 v_290 v_298 u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32) (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗ ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x384#64) ↦₆₄ v_290) ∗ ((s.sp + 0x38c#64) ↦₆₄ v_298) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x359c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000017#64 := hx28
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p3_err_tail_nondup_a1_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 511) s
      (((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x34f4#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 511)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem p3_err_tail_nondup_a2_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr errsPtr ssCap v_27c v_284 v_290 v_298 u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32) (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34f4#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr) (hx22 : s.readReg64 .x22 = errsPtr)
    (hx23 : s.readReg64 .x23 = 1#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗ ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗ ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗ ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 192 8) st) s1 ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x384#64) ↦₆₄ v_290) ∗ ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x359c#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (errsPtr, 192, 8, st)
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## Epilogue steppers (`+0x359c → retAddr`) -/

theorem p3_err_tail_prev_zero_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool lim st s ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool lim st s1 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [dpClosureEntryM3Placed] at hpc
  wp_steps_sync_518 ext retAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

private theorem mul24_eq_m3err_placed {prevCap : BitVec 64} (_h : prevCap.toNat * 24 < 2 ^ 63) :
    24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    (24#64 * prevCap).toNat = prevCap.toNat * 24 ∧
    (prevCap * 24#64).toNat = prevCap.toNat * 24 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem p3_err_tail_prev_dealloc_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  obtain ⟨hmul1, hmul2, hmul1_nat, hmul2_nat⟩ := mul24_eq_m3err_placed hcap_lt
  have hmul24' : (prevCap + (prevCap <<< 1)) <<< 3 = prevCap * 24#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; exact hmul2_nat
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; exact hmul2_nat
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [dpClosureEntryM3Placed] at hpc
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, st)
  wp_steps_sync_518 ext retAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by simp only [BitVec.add_zero]; sep_frame,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` helpers -/

theorem lscro_of_frozen [LibsignalPlacement] {m : Memory}
    (hfr : LibsignalFrozen lsmpl m) :
    StoreKit.LibsignalCodeRoLoaded lsmpl m :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.lscro_of_frozen hfr

theorem pqxdh_log_closure_frozen_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok
      ((blkPC_519).rebase (blkPl_519).base H)
      (lsmpl.base 519)
      (withLsFrozen lsmpl
        LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdhLogClosurePlacedSpec) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdh_log_closure_frozen_placed_ok H

theorem pqxdh_log_closure_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 519)
      (withLsFrozen lsmpl
        LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdhLogClosurePlacedSpec) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdh_log_closure_frozen_placed_ok_of_block

theorem bind_sepWP_lsfr_frame_err [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalFrozen lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen) hregs
      R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_lsfr_nopanic_err [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsFrozen lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalFrozen lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsFrozen lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsFrozen]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalFrozen lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hfr, hm⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h1
  obtain ⟨sm, hsteps, hout, _⟩ := hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right
  · dsimp only [withLsFrozen] at hoom_post
    rw [hoom_false] at hoom_post
    exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsFrozen] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsFrozen] at hpost
    rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsFrozen] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux
