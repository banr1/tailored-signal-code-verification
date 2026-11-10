/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Entry and Allocation Steppers for `<PolyDecoder as Decoder>::decoded_message`

Auxiliary `RustCliAllocBudget`-threaded and `VmPreserved` prologue, `points_vecs` allocation,
`Option<Poly>` cache initialization, and output-buffer allocation steppers for Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsρ)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Poly (polyDecoderPtsNeededOff vecHeaderBytes)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  CalleeSavedGprsPreserved
  bv64_and15_ofNat bv64_lsl1_norm bv64_lsr4_ofNat bv64_ne0_of_pos_le
  collectPointsVecsTotal collectedSlices decodedMessageStack
  memRegion24_eq_exists_three memRegion96_eq_exists_twelve
  memRegion_entails_rawOptPolySlots
  optPolyCacheListAt optPolyCacheSlotAt optVecU8Of
  rawOptPolySlots savedRegsAt sp672_aligned traceVRegs
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  DecodedMessageEnv DecodedMessageLoopEnv
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlacedBudget (
  decodedMessage_epilogue_ret_placed_sepWP
)
open scoped CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff rustAllocEvents
attribute [local wp_norm ↓, local arm64_norm ↓] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local wp_norm, local arm64_norm]
private theorem bv64_lsl1_norm_proof (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) :=
  bv64_lsl1_norm n

/-! ## Budget Envelope Bridges -/

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem freeOnlyEvs_append {e₁ e₂ : List AllocEvent}
    (h1 : FreeOnlyEvs e₁) (h2 : FreeOnlyEvs e₂) : FreeOnlyEvs (e₁ ++ e₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

theorem freeOnlyEvs_dealloc256 : FreeOnlyEvs (rustDeallocEvents 256 8) := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  exact ⟨8, 256, hev⟩

theorem decodedMessageEnv_of_isComplete_true {dec : PolyDecoder} (h : dec.isComplete = true) :
    DecodedMessageEnv dec [] := by
  unfold DecodedMessageEnv; simp [h]

theorem fitsAllocPv_of_isComplete_false {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {dec : PolyDecoder} (hcomp : dec.isComplete = false)
    (hfit : FitsEnv M lim st (DecodedMessageEnv dec)) :
    FitsEvents M lim st (rustAllocEvents 256 8) := by
  unfold DecodedMessageEnv at hfit
  simp only [hcomp, Bool.false_eq_true, ↓reduceIte] at hfit
  split at hfit
  · exact FitsEnv.eq_iff.mp hfit.seq_left
  · exact ((fitsEvents_append M lim _ _ st).mp (FitsEnv.eq_iff.mp hfit.seq_left)).1

theorem fitsAfterCollect_of_collect_false {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {dec : PolyDecoder} (hcomp : dec.isComplete = false)
    (hcol : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (hfit : FitsEnv M lim st (DecodedMessageEnv dec)) :
    dec.ptsNeeded ≠ 0 →
      FitsEvents M lim (M.stepEvents (rustAllocEvents 256 8) st)
        (rustAllocEvents (2 * dec.ptsNeeded) 1) ∧
      FitsEnv M lim
        (M.stepEvents (rustAllocEvents (2 * dec.ptsNeeded) 1)
          (M.stepEvents (rustAllocEvents 256 8) st))
        (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
          (List.replicate 16 none)) := by
  intro hne0
  have hdec0 : decide (dec.ptsNeeded = 0) = false := decide_eq_false hne0
  unfold DecodedMessageEnv at hfit
  simp only [hcomp, hcol, hdec0, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hfit
  have hpre : FitsEvents M lim st
      (rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1) :=
    FitsEnv.eq_iff.mp hfit.seq_left
  have hloop : FitsEnv M lim
      (M.stepEvents (rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1) st)
      (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
        (List.replicate 16 none)) :=
    (hfit.seq_right rfl).seq_left
  rw [M.stepEvents_append] at hloop
  exact ⟨((fitsEvents_append M lim _ _ st).mp hpre).2, hloop⟩

theorem decodedMessageEnv_of_collect_true {dec : PolyDecoder}
    (hcomp : dec.isComplete = false)
    (hcol : (collectPointsVecsTotal dec 0 16 false []).1 = true) :
    DecodedMessageEnv dec (rustAllocEvents 256 8 ++ rustDeallocEvents 256 8) := by
  unfold DecodedMessageEnv
  simp only [hcomp, hcol, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
  exact SeqEnv.append rfl freeOnlyEvs_dealloc256

theorem decodedMessageEnv_of_ptsNeeded_zero {dec : PolyDecoder} {evs : List AllocEvent}
    (hcomp : dec.isComplete = false)
    (hcol : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (hzero : dec.ptsNeeded = 0) (hfree : FreeOnlyEvs evs) :
    DecodedMessageEnv dec (rustAllocEvents 256 8 ++ evs) := by
  unfold DecodedMessageEnv
  simp only [hcomp, hcol, hzero, decide_true, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
  exact SeqEnv.append rfl hfree

theorem decodedMessageEnv_of_ptsNeeded_pos {dec : PolyDecoder}
    {evsLoop evsFree : List AllocEvent}
    (hcomp : dec.isComplete = false)
    (hcol : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (hne0 : dec.ptsNeeded ≠ 0)
    (hloop : DecodedMessageLoopEnv dec (collectedSlices dec 0 16) 0 dec.ptsNeeded
      (List.replicate 16 none) evsLoop)
    (hfree : FreeOnlyEvs evsFree) :
    DecodedMessageEnv dec
      (rustAllocEvents 256 8 ++ (rustAllocEvents (2 * dec.ptsNeeded) 1 ++ (evsLoop ++ evsFree))) := by
  have hdec0 : decide (dec.ptsNeeded = 0) = false := decide_eq_false hne0
  have hseq : DecodedMessageEnv dec
      ((rustAllocEvents 256 8 ++ rustAllocEvents (2 * dec.ptsNeeded) 1) ++
        (evsLoop ++ evsFree)) := by
    unfold DecodedMessageEnv
    simp only [hcomp, hcol, hdec0, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    exact SeqEnv.append rfl (SeqEnv.append hloop hfree)
  simpa only [List.append_assoc] using hseq

/-! ## Initialization of `polys: [Option<Poly>; 16]` (`+352..+424`) -/

/-- VM-preserving symbolic execution of `entry + 352#64` to `entry + 424#64` (18 instructions, `[LibsignalPlacement]`). -/
theorem initOptPolyCache_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 w648 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 352#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 424#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x24 = w648 → sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 648#64) ↦₆₄ w648) ∗ optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((sp0 - 648#64) ↦₆₄ w648) ∗ memRegion (sp0 - 600#64) 384 ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp672_aligned sp0 hsp0
  refine seq_vm_clean (mid := (blkPl_418).base + 424#64)
    (P_mid := ((sp0 - 648#64) ↦₆₄ w648) ∗ optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗ P)
    (Q := fun sf => sf.sp = sp0 - 672#64 ∧ traceVRegs sf = traceVRegs s ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x24 = w648 ∧ sf.readReg64 .x29 = s.readReg64 .x29)
    ?_ ?_
  · by_vm_steps (
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
        (memRegion_entails_rawOptPolySlots 16 (sp0 - 600#64) (by decide)))) ?_
      dsimp only [rawOptPolySlots]
      simp only [wp_norm, arm64_norm, sepConj_emp, sepConj_assoc]
      wp_pull_exists
      wp_steps 18
      refine SepWP.weaken_pre
        (show _ ⊢ ((sp0 - 648#64) ↦₆₄ w648) ∗ optPolyCacheListAt A (sp0 - 600#64) (List.replicate 16 none) ∗ P by
          dsimp only [List.replicate, optPolyCacheListAt, arrayAt, optPolyCacheSlotAt, vecHeaderBytes, noneCap]
          simp only [wp_norm, arm64_norm, sepConj_emp, sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩)
  · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hx20_f, hx24_f, hx29_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f hx20_f hx24_f hx29_f

/-! ## Output Buffer Allocation (`+424..+548`) -/

/-- VM-preserving zero-length output path (`dec.ptsNeeded = 0`) from `entry + 424#64` to `entry + 1460#64` (`[LibsignalPlacement]`). -/
theorem allocOut_zero_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 : BitVec 64) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 424#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hx24 : s.readReg64 .x24 = 0#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1460#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      VmPreserved s sf → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 1#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion (sp0 - 216#64) 24 ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  refine seq_vm_clean (mid := (blkPl_418).base + 1460#64)
    (P_mid := ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 1#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗ P)
    (Q := fun sf => sf.sp = sp0 - 672#64 ∧ traceVRegs sf = traceVRegs s ∧ sf.readReg64 .x29 = sp0 - 96#64)
    ?_ ?_
  · by_vm_steps (
      rw [memRegion24_eq_exists_three (sp0 - 216#64)]
      wp_conv_pre => simp only [wp_norm, arm64_norm, sepConj_assoc]
      wp_pull_exists
      wp_steps 8
      exact SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp,
         by rfl,
         by simpa [wp_norm, arm64_norm] using hx29⟩)
  · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hx29_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f hx29_f

/-- VM-preserving post-allocation setup (`+488..+548`, 8 instructions, `[LibsignalPlacement]`). -/
theorem allocOut_pos_setup_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 out_ptr : BitVec 64) (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 488#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (hx0 : s.readReg64 .x0 = out_ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (2 * ptsNeeded))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 548#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = 0#64 → sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ 0#64) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion (sp0 - 216#64) 24 ∗ P) post := by
  have hne0_pts : (BitVec.ofNat 64 ptsNeeded == 0#64) = false := bv64_ne0_of_pos_le hge1 (by omega)
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  refine seq_vm_clean (mid := (blkPl_418).base + 548#64)
    (P_mid := ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
      ((sp0 - 200#64) ↦₆₄ 0#64) ∗ P)
    (Q := fun sf => sf.sp = sp0 - 672#64 ∧ traceVRegs sf = traceVRegs s ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x22 = 0#64 ∧ sf.readReg64 .x23 = 0#64 ∧
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded ∧ sf.readReg64 .x25 = 24#64 ∧
      sf.readReg64 .x26 = sp0 - 600#64 ∧ sf.readReg64 .x29 = sp0 - 96#64)
    ?_ ?_
  · by_vm_steps (
      rw [memRegion24_eq_exists_three (sp0 - 216#64)]
      wp_conv_pre => simp only [wp_norm, arm64_norm, sepConj_assoc]
      wp_pull_exists
      wp_steps 8
      exact SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp,
         by rfl,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simpa [wp_norm, arm64_norm] using hx24,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hsp],
         by simpa [wp_norm, arm64_norm] using hx29⟩)
  · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx29_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f hx20_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f

/-- Budget-threaded positive-length output path (`1 ≤ ptsNeeded ≤ 16 * 65536`) from `entry + 424#64`
    to `entry + 548#64` (`[LibsignalPlacement]`, `SepWP`). -/
theorem allocOut_pos_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * ptsNeeded) 1))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 424#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (out_ptr : BitVec 64) (sf : State),
      out_ptr ≠ 0#64 → sf.pc = (blkPl_418).base + 548#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = 0#64 → sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ 0#64) ∗ A.live out_ptr (2 * ptsNeeded) 1 ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗ memRegion out_ptr (2 * ptsNeeded) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * ptsNeeded) 1) st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ F) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (memRegion (sp0 - 216#64) 24 ∗ A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F)
      post := by
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) (withVmPreserved sessionShimSpec) :=
    spqr_hook_ok_of_mem hshim_sat
  simp only [withVmPreserved, sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem halloc_sat)
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  have hne0_pts : (BitVec.ofNat 64 ptsNeeded == 0#64) = false := bv64_ne0_of_pos_le hge1 (by omega)
  have hne0_2pts : (BitVec.ofNat 64 (2 * ptsNeeded) == 0#64) = false :=
    bv64_ne0_of_pos_le (by omega) (by omega)
  have htoNat_2pts : (BitVec.ofNat 64 (2 * ptsNeeded)).toNat = 2 * ptsNeeded := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow1 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
  have hlay1 : RustLayoutOk (2 * ptsNeeded) 1 := ⟨⟨by omega, hpow1, by omega⟩, by decide⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpc hnext ⊢
  wp_steps 5
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption : VmPreserved _ sf) (hnext := ?_)
  have hsp_shim : sf.sp = sp0 - 672#64 :=
    (by assumption : sf.sp = _).trans (by simpa [wp_norm, arm64_norm] using hsp)
  wp_steps 4
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  wp_conv_pre => rw [← hsp_shim]
  wp_call halloc ⟨2 * ptsNeeded, 1, st⟩
  have hsp_alloc : sf_1.sp = sp0 - 672#64 := (by assumption : sf_1.sp = sf.sp).trans hsp_shim
  have htr_alloc : sf_1.trace = _ := (by assumption : AllocCallPreserved _ sf_1).2.1
  have hptr0_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hcbnz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0_ne
  wp_steps 1
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  refine SepWP.weaken_pre
    (show _ ⊢
      memRegion (sp0 - 216#64) 24 ∗
        (A.live (sf_1.readReg64 (Reg.gpr 0#5)) (2 * ptsNeeded) 1 ∗
          ((sf_1.readReg64 (Reg.gpr 0#5)) ↦ₛ ([] : List (BitVec 8))) ∗
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * ptsNeeded) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * ptsNeeded) 1) st) _ ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ F) by
      simp only [pointsToBytes_nil, sepConj_emp]; rw [hsp_shim]
      exact Entails.of_eq (by sep_ac_rfl))
    (allocOut_pos_setup_placed_sepWP (ext := ext) sp0 (sf_1.readReg64 (Reg.gpr 0#5)) ptsNeeded hge1 hle _ _ post
      (by simp [wp_norm, arm64_norm, hcbnz])
      (by simp [wp_norm, arm64_norm, hrun_sf_1])
      (by simp [wp_norm, arm64_norm, hsp_alloc])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (fun sf_2 hpc2 hstat2 hsp2 htr2 hvm2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
  refine SepWP.transport_budgetPool hvm2 (hnext := ?_)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext (sf_1.readReg64 (Reg.gpr 0#5)) sf_2 hptr0_ne hpc2 hstat2 hsp2
      (by rw [htr2]; simp [traceVRegs, wp_norm, arm64_norm, *])
      (by rw [hx20_2]; simp [wp_norm, arm64_norm, *])
      hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2)

theorem allocOut_pos_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * ptsNeeded) 1))
    (s0 s : State) (F : SepProp) (Q Qp : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 424#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (out_ptr : BitVec 64) (sf : State),
      out_ptr ≠ 0#64 → sf.pc = (blkPl_418).base + 548#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = 0#64 → sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = BitVec.ofNat 64 ptsNeeded → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗ ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ 0#64) ∗ A.live out_ptr (2 * ptsNeeded) 1 ∗
          (out_ptr ↦ₛ ([] : List (BitVec 8))) ∗ memRegion out_ptr (2 * ptsNeeded) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * ptsNeeded) 1) st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ F) Q Qp) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (memRegion (sp0 - 216#64) 24 ∗ A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F)
      Q Qp := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 548#64)
  refine allocOut_pos_placed_sepWP hshim_sat halloc_sat sp0 hsp0 ptsNeeded hge1 hle st hfit s0 s F _
    hpc hstat hsp htr hx24 hx29
    (fun out_ptr sf hout hpc_f hstat_f hsp_f htr_f hx20_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f => ?_)
  exact SepWP.done hpc_f hstat_f
    (hnext out_ptr sf hout hpc_f hstat_f hsp_f htr_f hx20_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f)

/-! ## Prologue, `points_vecs` Allocation, and `isComplete = true` Fast Path -/

/-- VM-preserving prologue (`+0..+32`, 8 instructions, `[LibsignalPlacement]`). -/
theorem decodedMessage_prologue_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (s0 : State) (P : SepProp) (post : State → SepProp → Prop) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s0.pc = (blkPl_418).base) (hstat : s0.status = .Running)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 32#64 →
      sf.status = .Running → sf.sp = s0.sp - 672#64 → traceVRegs sf = traceVRegs s0 →
      VmPreserved s0 sf →
      sf.readReg64 .x0 = s0.readReg64 .x0 → sf.readReg64 .x8 = s0.readReg64 .x8 →
      sf.readReg64 .x29 = s0.sp - 96#64 → sf.readReg64 .x30 = s0.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (savedRegsAt s0.sp s0 ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s0
      (memRegion (s0.sp - 96#64) 96 ∗ P) post := by
  have hsp672_al : (s0.sp - 672#64) &&& 15#64 = 0#64 := sp672_aligned s0.sp hsp0
  have hsp96_al : (s0.sp - 96#64) &&& 15#64 = 0#64 := by
    have h : (s0.sp - 96#64) &&& 15#64 = s0.sp &&& 15#64 := by bv_bits
    rw [h, hsp0]
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  refine seq_vm_clean (mid := (blkPl_418).base + 32#64)
    (P_mid := savedRegsAt s0.sp s0 ∗ P)
    (Q := fun sf => sf.sp = s0.sp - 672#64 ∧ traceVRegs sf = traceVRegs s0 ∧
      sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.readReg64 .x8 = s0.readReg64 .x8 ∧
      sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x30 = s0.readReg64 .x30)
    ?_ ?_
  · by_vm_steps (
      rw [memRegion96_eq_exists_twelve s0.sp]
      wp_conv_pre => simp only [wp_norm, arm64_norm, sepConj_assoc]
      wp_pull_exists
      wp_steps 8
      refine SepWP.weaken_pre
        (show _ ⊢ savedRegsAt s0.sp s0 ∗ P by unfold savedRegsAt; exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
         by simp [wp_norm, arm64_norm],
         by rfl,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩)
  · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hx0_f, hx8_f, hx29_f, hx30_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f hx0_f hx8_f hx29_f hx30_f

/-- Budget-threaded `points_vecs` allocation (`+32..+80`, `[LibsignalPlacement]`, `SepWP`)
    when `dec.isComplete = false`. -/
theorem decodedMessage_allocPv_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (sp0 decA out_sret : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents 256 8))
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 32#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = decA) (hx8 : s.readReg64 .x8 = out_sret)
    (hcont : ∀ (pv_ptr : BitVec 64) (sf : State),
      pv_ptr ≠ 0#64 → sf.pc = (blkPl_418).base + 80#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      sf.readReg64 .x0 = pv_ptr → sf.readReg64 .x20 = decA → sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((decA + 392#64) ↦₈ 0#8) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          A.live pv_ptr 256 8 ∗ memRegion pv_ptr 256 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((decA + 392#64) ↦₈ 0#8) ∗ (∃∗ w632 : BitVec 64, (sp0 - 632#64) ↦₆₄ w632) ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) (withVmPreserved sessionShimSpec) :=
    spqr_hook_ok_of_mem hshim_sat
  simp only [withVmPreserved, sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem halloc_sat)
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  have hpow8 : ∃ m, 8 = 2 ^ m := ⟨3, rfl⟩
  have hlay8 : RustLayoutOk 256 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hsp_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp672_aligned sp0 hsp0
  try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpc hcont ⊢
  refine seq_vm_clean (mid := lsρ spqrRustNoAllocShimSym)
    (P_mid := A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
      ((decA + 392#64) ↦₈ 0#8) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P)
    (Q := fun s1 => s1.sp = sp0 - 672#64 ∧ traceVRegs s1 = traceVRegs s ∧
      s1.readReg64 .x20 = decA ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
      s1.readReg64 .x30 = (blkPl_418).base + 64#64)
    ?_ ?_
  · by_vm_steps (
      wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists
      wp_steps 5
      exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm],
         by simpa [wp_norm, arm64_norm] using hx0,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, htr1, hx20_1, hx29_1, hx30_1⟩
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1, sp672_aligned sp0 hsp0]; rfl
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    wp_call hshim ()
    refine SepWP.transport_budgetPool (by assumption : VmPreserved s1 sf) (hnext := ?_)
    have hsp_shim : sf.sp = sp0 - 672#64 := (by assumption : sf.sp = s1.sp).trans hsp1
    wp_steps 3
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    wp_conv_pre => rw [← hsp_shim]
    wp_call halloc ⟨256, 8, st⟩
    have hsp_alloc : sf_1.sp = sp0 - 672#64 := (by assumption : sf_1.sp = sf.sp).trans hsp_shim
    have htr_alloc : sf_1.trace = _ := (by assumption : AllocCallPreserved _ sf_1).2.1
    have hptr0_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0_ne
    wp_steps 1
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    refine SepWP.weaken_pre
      (show _ ⊢
        ((decA + 392#64) ↦₈ 0#8) ∗ ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          A.live (sf_1.readReg64 (Reg.gpr 0#5)) 256 8 ∗
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 256 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 256 8) st) _ ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P by
        rw [hsp_shim]; exact Entails.of_eq (by sep_ac_rfl))
      (hcont (sf_1.readReg64 (Reg.gpr 0#5)) _ hptr0_ne
        (by simp [wp_norm, arm64_norm, hcbz])
        (by simp [wp_norm, arm64_norm, hrun_sf_1])
        (by simp [wp_norm, arm64_norm, hsp_alloc])
        (by
          rcases Prod.mk.inj htr1 with ⟨htr1_tr, htr1_vr⟩
          simp [traceVRegs, wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))

/-- VM-preserving post-`pv_ptr`-allocation setup (`+80..+128`, 12 instructions, `[LibsignalPlacement]`). -/
theorem decodedMessage_allocPv_setup_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (dec : PolyDecoder) (sp0 decA pv_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hneed : dec.ptsNeeded < 2 ^ 64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 80#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = pv_ptr) (hx20 : s.readReg64 .x20 = decA)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 128#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x0 = pv_ptr → sf.readReg64 .x20 = decA → sf.readReg64 .x21 = 0#64 →
      sf.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) →
      sf.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) →
      sf.readReg64 .x24 = decA + 40#64 → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = 0#64 → sf.readReg64 .x27 = 0#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 → sf.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 0#64) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (((decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (∃∗ w648 : BitVec 64, (sp0 - 648#64) ↦₆₄ w648) ∗
        (∃∗ w624 : BitVec 64, (sp0 - 624#64) ↦₆₄ w624) ∗
        (∃∗ w616 : BitVec 64, (sp0 - 616#64) ↦₆₄ w616) ∗
        (∃∗ w608 : BitVec 64, (sp0 - 608#64) ↦₆₄ w608) ∗ P) post := by
  have hsp_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp672_aligned sp0 hsp0
  have hlsr := bv64_lsr4_ofNat hneed
  try dsimp only [polyDecoderPtsNeededOff, BitVec.ofNat_eq_ofNat] at *
  refine seq_vm_clean (mid := (blkPl_418).base + 128#64)
    (P_mid := ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((sp0 - 624#64) ↦₆₄ 16#64) ∗ ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
      ((sp0 - 608#64) ↦₆₄ 0#64) ∗ P)
    (Q := fun sf => sf.sp = sp0 - 672#64 ∧ traceVRegs sf = traceVRegs s ∧
      sf.readReg64 .x0 = pv_ptr ∧ sf.readReg64 .x20 = decA ∧ sf.readReg64 .x21 = 0#64 ∧
      sf.readReg64 .x22 = BitVec.ofNat 64 (dec.ptsNeeded / 16) ∧
      sf.readReg64 .x23 = BitVec.ofNat 64 (dec.ptsNeeded % 16) ∧
      sf.readReg64 .x24 = decA + 40#64 ∧ sf.readReg64 .x25 = 24#64 ∧
      sf.readReg64 .x26 = 0#64 ∧ sf.readReg64 .x27 = 0#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = s.readReg64 .x30)
    ?_ ?_
  · by_vm_steps (
      wp_pull_exists
      wp_steps 12
      exact SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp,
         by rfl,
         by simpa [wp_norm, arm64_norm] using hx0,
         by simpa [wp_norm, arm64_norm] using hx20,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hlsr],
         by simp [wp_norm, arm64_norm, bv64_and15_ofNat],
         by simp [wp_norm, arm64_norm, hx20],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩)
  · rintro sf hpc_f hstat_f hvm_f
      ⟨hsp_f, htr_f, hx0_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx29_f, hx30_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f
      hx0_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hx26_f hx27_f hx29_f hx30_f

/-- Fast-path execution (`+32..ret`) when `dec.isComplete = true` (`[LibsignalPlacement]`, `SepWP`). -/
theorem decodedMessage_isComplete_true_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (s0 : State) (decA out_sret : BitVec 64) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (st : M.σ) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 32#64)
    (hstat : s.status = .Running) (hsp : s.sp = s0.sp - 672#64)
    (hx0 : s.readReg64 .x0 = decA) (hx8 : s.readReg64 .x8 = out_sret)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp →
      traceVRegs sf = traceVRegs s → VmPreserved s sf → CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A.repAlloc out_sret none ∗ ((decA + 392#64) ↦₈ 1#8) ∗
          A.pool lim st sf ∗ stackAt s0.sp decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
        stackAt (s0.sp - 672#64) extHookStack ∗ memRegion out_sret vecHeaderBytes ∗
        ((decA + 392#64) ↦₈ 1#8) ∗ A.pool lim st s ∗ P) post := by
  have hout_split : memRegion out_sret vecHeaderBytes =
      (∃∗ w0 : BitVec 64, out_sret ↦₆₄ w0) ∗ memRegion (out_sret + 8#64) 16 := by
    rw [show vecHeaderBytes = 8 + 16 from rfl,
      memRegion_split out_sret 8 16 (by decide), ProofLib.memRegion_eight out_sret]
  have hnone_eq :
      (out_sret ↦₆₄ 18446744073709551615#64) ∗ memRegion (out_sret + 8#64) 16 =
        optVecU8Of A.repAlloc out_sret none := by unfold optVecU8Of noneCap; rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := (blkPl_418).base + 320#64)
    (P_mid := savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
      stackAt (s0.sp - 672#64) extHookStack ∗
      optVecU8Of A.repAlloc out_sret none ∗ ((decA + 392#64) ↦₈ 1#8) ∗ A.pool lim st s ∗ P)
    (Q := fun sm => sm.sp = s0.sp - 672#64 ∧ traceVRegs sm = traceVRegs s)
    ?_ ?_
  · by_vm_steps (
      wp_conv_pre =>
        rw [hout_split]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists
      wp_steps 5
      refine SepWP.weaken_pre
        (show _ ⊢
          savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
            stackAt (s0.sp - 672#64) extHookStack ∗
            optVecU8Of A.repAlloc out_sret none ∗ ((decA + 392#64) ↦₈ 1#8) ∗ A.pool lim st s ∗ P by
          rw [← hnone_eq]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.done (by rfl) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm]⟩)
  · rintro sm hpcm hstatm hvmm ⟨hspm, htrm⟩
    refine SepWP.transport_budgetPool hvmm (hnext := ?_)
    refine SepWP.weaken_pre
      (show _ ⊢
        savedRegsAt s0.sp s0 ∗ memRegion (s0.sp - 672#64) 576 ∗
          stackAt (s0.sp - 672#64) extHookStack ∗
          (optVecU8Of A.repAlloc out_sret none ∗ ((decA + 392#64) ↦₈ 1#8) ∗ A.pool lim st sm ∗ P) by
        exact Entails.of_eq (by sep_ac_rfl))
      (decodedMessage_epilogue_ret_placed_sepWP (ext := ext) s0 s0.sp hsp0 sm _ post
        hpcm hstatm hspm (fun sf hpc_f hrun_f hsp_f htr_f hvm_f _hacp_f hcs_f => ?_))
    refine SepWP.transport_budgetPool hvm_f (hnext := ?_)
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont sf hpc_f hrun_f hsp_f (htr_f.trans htrm) (hvmm.trans hvm_f) hcs_f)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofPlacedBudgetAux
