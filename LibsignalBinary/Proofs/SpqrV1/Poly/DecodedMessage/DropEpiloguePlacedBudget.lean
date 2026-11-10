/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpilogue
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Drop Glue and Epilogue for `<PolyDecoder as Decoder>::decoded_message`

Threads `RustCliAllocBudget M`, `FreeOnlyEvs`, and `AllocCallPreserved` through the `Option<Poly>`
cache drop glue and epilogue paths on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsρ)
open CryptoVerification.LibsignalSpqrV1 (Poly)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly (vecHeaderBytes)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  CalleeSavedGprsPreserved bv64_lsl1_toNat_of_le65536 bv64_ofNat_ne0_of_ge1
  bv64_slt_one_of_ge1_le65536 decodedMessageStack dropPolySlot_some_to_dealloc
  fold_optVecU8Of_some fold_optVecU8Of_some_nil list_length_16_eq memRegion24_eq_exists_three
  memRegion_24_8_8_8_8_entails_56 memRegion_48_8_entails_56 memRegion_56_8_512_entails_576
  memRegion_8_504_entails_512 merge_prev_slot_none merge_prev_slot_some noneCap_slt_one
  optPolyCacheListAt optPolyCacheListAt_15_eq optPolyCacheSlotAt
  optPolyCacheSlot_none_entails_memRegion24 optVecU8Of pointsTo64_three_entails_memRegion24
  pull_none_slot pull_some_slot savedRegsAt savedRegsAt_entails_memRegion96 sp216_add_16
  sp216_add_8 sp672_aligned spqrRustDeallocSym stackAt_decodedMessage_eq
  stackAt_extHook_eq_allocHook traceVRegs
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open scoped CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local wp_norm, local arm64_norm] noneCap_slt_one
attribute [local irreducible] noneCap
attribute [local wp_norm ↓, local arm64_norm ↓] sp216_add_8 sp216_add_16

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem acp_of_PureStep {s sm : State}
    (hfs : sm.fs = s.fs := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (htr : sm.trace = s.trace := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hsig : sm.sigActions = s.sigActions := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (htp : sm.tpidrEl0 = s.tpidrEl0 := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hbrk : sm.brkStart = s.brkStart := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (horc : sm.oracle = s.oracle := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hsym : sm.symtab = s.symtab := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl)) :
    AllocCallPreserved s sm :=
  ⟨hfs, htr, hsig, htp, hbrk, horc, hsym⟩

/-! ## Placed Drop-Glue Slots (`1..15`) & Cache Drop (`1404`, `1460`) -/

set_option hygiene false in
local macro "def_drop_poly_slot_placed " thmName:ident _startOff:num startBv:term:max endBv:term:max slotBv:term:max prevBytes:num nextBytes:num : command =>
  `(command|
    theorem $thmName [lsmpl : LibsignalPlacement] {M : AllocCostModel}
        {A : RustCliAllocBudget M} {lim : BudgetLimits}
        {ext : String → Option (State → State)} {ret_pc : BitVec 64}
        (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
          (rustCliDeallocBudgetSpec M A lim))
        (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
        (opt : Option Poly) (st : M.σ)
        (s : State) (P : SepProp) (post : State → SepProp → Prop)
        (hpc : s.pc = (blkPl_418).base + $startBv)
        (hstat : s.status = .Running)
        (hsp : s.sp = sp0 - 672#64)
        (hcont : ∀ (sf : State) (evs : List AllocEvent),
          FreeOnlyEvs evs →
          sf.pc = (blkPl_418).base + $endBv →
          sf.status = .Running →
          sf.sp = sp0 - 672#64 →
          traceVRegs sf = traceVRegs s →
          AllocCallPreserved s sf →
          SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
            (memRegion (sp0 - 600#64) $nextBytes ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
          (memRegion (sp0 - 600#64) $prevBytes ∗
            A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheSlotAt A.repAlloc (sp0 - $slotBv) opt ∗ P) post := by
      have hdealloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
          (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
        subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem hdealloc_sat)
      simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc
      try dsimp only [BitVec.ofNat_eq_ofNat] at *
      have hsp_align : s.sp &&& 15#64 = 0#64 := by
        rw [hsp]; exact sp672_aligned sp0 hsp0
      cases opt with
      | none =>
        unfold optPolyCacheSlotAt
        rw [pull_none_slot]
        have hslt := noneCap_slt_one
        wp_steps 3
        refine SepWP.transport_budgetPool ?_ (hnext := ?_)
        · simp [wp_norm, arm64_norm]
        refine SepWP.weaken_pre
          (show _ ⊢
            ((sp0 - $slotBv) ↦₆₄ noneCap) ∗ memRegion ((sp0 - $slotBv) + 8#64) 16 ∗
              memRegion (sp0 - 600#64) $prevBytes ∗
              (A.pool lim (M.stepEvents [] st) _ ∗
                stackAt (sp0 - 672#64) allocHookStack ∗ P) by
            simp only [AllocCostModel.stepEvents_nil]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        refine SepWP.weaken_pre
          (merge_prev_slot_none sp0 (sp0 - $slotBv) $prevBytes $nextBytes rfl (by decide) (by bv_omega) _) ?_
        apply hcont _ [] FreeOnlyEvs.nil
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm, hstat]
        · simpa [wp_norm, arm64_norm] using hsp
        · simp [wp_norm, arm64_norm]
        · exact acp_of_PureStep
      | some p =>
        rw [pull_some_slot]
        apply SepWP.exists_left; intro ptr_p
        refine SepWP.pure_elim ?_
        rintro ⟨hp_ge1, hp_le, _⟩
        have hslt := bv64_slt_one_of_ge1_le65536 hp_ge1 hp_le
        have htoNat := bv64_lsl1_toNat_of_le65536 hp_le
        have hne0 := bv64_ofNat_ne0_of_ge1 hp_ge1 hp_le
        refine SepWP.weaken_pre
          (dropPolySlot_some_to_dealloc A.repAlloc (sp0 - $slotBv) ptr_p p _) ?_
        dsimp only [RustCliAllocBudget.repAlloc_live]
        wp_steps 7
        refine SepWP.transport_budgetPool ?_ (hnext := ?_)
        · simp [wp_norm, arm64_norm]
        wp_call hdealloc ⟨ptr_p, 2 * p.coefficients.length, 2, st⟩
        wp_conv_pre => rw [hsp]
        refine SepWP.weaken_pre
          (show _ ⊢
            (((sp0 - $slotBv) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
              (((sp0 - $slotBv) + 8#64) ↦₆₄ ptr_p) ∗
              (((sp0 - $slotBv) + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length)) ∗
              (memRegion (sp0 - 600#64) $prevBytes ∗
                A.pool lim (M.stepEvents (rustDeallocEvents (2 * p.coefficients.length) 2) st) sf ∗
                stackAt (sp0 - 672#64) allocHookStack ∗ P) by
            try simp only [arm64_norm]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        refine SepWP.weaken_pre
          (merge_prev_slot_some sp0 (sp0 - $slotBv) $prevBytes $nextBytes rfl (by decide) (by bv_omega) _ _ _ _) ?_
        exact hcont sf (rustDeallocEvents (2 * p.coefficients.length) 2)
          (FreeOnlyEvs.singleton 2 (2 * p.coefficients.length))
          hpc_sf hrun_sf (by rw [hsp_sf, hsp])
          (by simp [traceVRegs, wp_norm, arm64_norm, *])
          (AllocCallPreserved.trans acp_of_PureStep (by assumption)))

def_drop_poly_slot_placed dropPolySlot_1_placed_sepWP  1484 1484#64 1512#64 576#64 24  48
def_drop_poly_slot_placed dropPolySlot_2_placed_sepWP  1512 1512#64 1540#64 552#64 48  72
def_drop_poly_slot_placed dropPolySlot_3_placed_sepWP  1540 1540#64 1568#64 528#64 72  96
def_drop_poly_slot_placed dropPolySlot_4_placed_sepWP  1568 1568#64 1596#64 504#64 96  120
def_drop_poly_slot_placed dropPolySlot_5_placed_sepWP  1596 1596#64 1624#64 480#64 120 144
def_drop_poly_slot_placed dropPolySlot_6_placed_sepWP  1624 1624#64 1652#64 456#64 144 168
def_drop_poly_slot_placed dropPolySlot_7_placed_sepWP  1652 1652#64 1680#64 432#64 168 192
def_drop_poly_slot_placed dropPolySlot_8_placed_sepWP  1680 1680#64 1708#64 408#64 192 216
def_drop_poly_slot_placed dropPolySlot_9_placed_sepWP  1708 1708#64 1736#64 384#64 216 240
def_drop_poly_slot_placed dropPolySlot_10_placed_sepWP 1736 1736#64 1764#64 360#64 240 264
def_drop_poly_slot_placed dropPolySlot_11_placed_sepWP 1764 1764#64 1792#64 336#64 264 288
def_drop_poly_slot_placed dropPolySlot_12_placed_sepWP 1792 1792#64 1820#64 312#64 288 312
def_drop_poly_slot_placed dropPolySlot_13_placed_sepWP 1820 1820#64 1848#64 288#64 312 336
def_drop_poly_slot_placed dropPolySlot_14_placed_sepWP 1848 1848#64 1876#64 264#64 336 360
def_drop_poly_slot_placed dropPolySlot_15_placed_sepWP 1876 1876#64 1904#64 240#64 360 384

/-- Drops slots `1..15` (`[LibsignalPlacement]`),
    merging `memRegion (sp0 - 600#64) 24` and the 15 slots into `memRegion (sp0 - 600#64) 384`
    while accumulating `FreeOnlyEvs` and `AllocCallPreserved`. -/
theorem dropOptPolyCache_1_to_15_placed_sepWP [lsmpl : LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Option Poly)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1484#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      sf.pc = (blkPl_418).base + 1904#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (memRegion (sp0 - 600#64) 384 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion (sp0 - 600#64) 24 ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
        optPolyCacheListAt A.repAlloc (sp0 - 576#64)
          [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗ P) post := by
  rw [optPolyCacheListAt_15_eq]
  refine dropPolySlot_1_placed_sepWP hdealloc_sat sp0 hsp0 p1 st s _ post hpc hstat hsp
    (fun s1 e1 he1 hpc1 hstat1 hsp1 htr1 ha1 => ?_)
  refine dropPolySlot_2_placed_sepWP hdealloc_sat sp0 hsp0 p2 _ s1 _ post hpc1 hstat1 hsp1
    (fun s2 e2 he2 hpc2 hstat2 hsp2 htr2 ha2 => ?_)
  refine dropPolySlot_3_placed_sepWP hdealloc_sat sp0 hsp0 p3 _ s2 _ post hpc2 hstat2 hsp2
    (fun s3 e3 he3 hpc3 hstat3 hsp3 htr3 ha3 => ?_)
  refine dropPolySlot_4_placed_sepWP hdealloc_sat sp0 hsp0 p4 _ s3 _ post hpc3 hstat3 hsp3
    (fun s4 e4 he4 hpc4 hstat4 hsp4 htr4 ha4 => ?_)
  refine dropPolySlot_5_placed_sepWP hdealloc_sat sp0 hsp0 p5 _ s4 _ post hpc4 hstat4 hsp4
    (fun s5 e5 he5 hpc5 hstat5 hsp5 htr5 ha5 => ?_)
  refine dropPolySlot_6_placed_sepWP hdealloc_sat sp0 hsp0 p6 _ s5 _ post hpc5 hstat5 hsp5
    (fun s6 e6 he6 hpc6 hstat6 hsp6 htr6 ha6 => ?_)
  refine dropPolySlot_7_placed_sepWP hdealloc_sat sp0 hsp0 p7 _ s6 _ post hpc6 hstat6 hsp6
    (fun s7 e7 he7 hpc7 hstat7 hsp7 htr7 ha7 => ?_)
  refine dropPolySlot_8_placed_sepWP hdealloc_sat sp0 hsp0 p8 _ s7 _ post hpc7 hstat7 hsp7
    (fun s8 e8 he8 hpc8 hstat8 hsp8 htr8 ha8 => ?_)
  refine dropPolySlot_9_placed_sepWP hdealloc_sat sp0 hsp0 p9 _ s8 _ post hpc8 hstat8 hsp8
    (fun s9 e9 he9 hpc9 hstat9 hsp9 htr9 ha9 => ?_)
  refine dropPolySlot_10_placed_sepWP hdealloc_sat sp0 hsp0 p10 _ s9 _ post hpc9 hstat9 hsp9
    (fun s10 e10 he10 hpc10 hstat10 hsp10 htr10 ha10 => ?_)
  refine dropPolySlot_11_placed_sepWP hdealloc_sat sp0 hsp0 p11 _ s10 _ post hpc10 hstat10 hsp10
    (fun s11 e11 he11 hpc11 hstat11 hsp11 htr11 ha11 => ?_)
  refine dropPolySlot_12_placed_sepWP hdealloc_sat sp0 hsp0 p12 _ s11 _ post hpc11 hstat11 hsp11
    (fun s12 e12 he12 hpc12 hstat12 hsp12 htr12 ha12 => ?_)
  refine dropPolySlot_13_placed_sepWP hdealloc_sat sp0 hsp0 p13 _ s12 _ post hpc12 hstat12 hsp12
    (fun s13 e13 he13 hpc13 hstat13 hsp13 htr13 ha13 => ?_)
  refine dropPolySlot_14_placed_sepWP hdealloc_sat sp0 hsp0 p14 _ s13 _ post hpc13 hstat13 hsp13
    (fun s14 e14 he14 hpc14 hstat14 hsp14 htr14 ha14 => ?_)
  refine dropPolySlot_15_placed_sepWP hdealloc_sat sp0 hsp0 p15 _ s14 _ post hpc14 hstat14 hsp14
    (fun s15 e15 he15 hpc15 hstat15 hsp15 htr15 ha15 => ?_)
  simp only [← AllocCostModel.stepEvents_append]
  exact hcont s15
    (e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15)
    ((((((((((((((he1.append he2).append he3).append he4).append he5).append he6).append he7).append
      he8).append he9).append he10).append he11).append he12).append he13).append he14).append he15)
    hpc15 hstat15 hsp15
    (by rw [htr15, htr14, htr13, htr12, htr11, htr10, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1])
    ((((((((((((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6).trans ha7).trans
      ha8).trans ha9).trans ha10).trans ha11).trans ha12).trans ha13).trans ha14).trans ha15)

/-- Copy `out` header to `out_sret` and drop `polys[0..16]` (`[LibsignalPlacement]`),
    entered after `decodedMessageLoop_placed_wpp` when `1 ≤ dec.ptsNeeded`. -/
theorem dropOptPolyCache_from1404_placed_sepWP [lsmpl : LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (sp0 out_sret out_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (ptsNeeded : Nat) (hge1 : 1 ≤ ptsNeeded) (hle : ptsNeeded ≤ 16 * 65536)
    (polys : List (Option Poly)) (hpolys : polys.length = 16)
    (outFinal : List (BitVec 8)) (hout_len : outFinal.length = 2 * ptsNeeded)
    (hout_ptr : out_ptr ≠ 0#64)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1404#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      sf.pc = (blkPl_418).base + 1904#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (optVecU8Of A.repAlloc out_sret (some outFinal) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        memRegion out_sret vecHeaderBytes ∗
        A.live out_ptr (2 * ptsNeeded) 1 ∗
        (out_ptr ↦ₛ outFinal) ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  rcases list_length_16_eq polys hpolys with
    ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, rfl⟩
  have hdealloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem hdealloc_sat)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc
  have h1_15 := @dropOptPolyCache_1_to_15_placed_sepWP lsmpl M A lim ext ret_pc hdealloc_sat sp0 hsp0
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsplit_head :
      optPolyCacheListAt A.repAlloc (sp0 - 600#64)
        [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] =
      optPolyCacheSlotAt A.repAlloc (sp0 - 600#64) p0 ∗
        optPolyCacheListAt A.repAlloc (sp0 - 576#64)
          [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] := by
    unfold optPolyCacheListAt vecHeaderBytes
    rw [CryptoVerification.RustHeap.arrayAt_cons]
    simp only [arm64_norm]
  rw [hsplit_head, memRegion24_eq_exists_three out_sret]
  wp_pull_exists
  cases p0 with
  | none =>
    unfold optPolyCacheSlotAt
    rw [sepConj_assoc]
    have hslt := noneCap_slt_one
    refine seq_vm_clean (mid := (blkPl_418).base + 1484#64)
      (P_mid :=
        memRegion (sp0 - 600#64) 24 ∗
          A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
          optPolyCacheListAt A.repAlloc (sp0 - 576#64)
            [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
          (optVecU8Of A.repAlloc out_sret (some outFinal) ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            memRegion (sp0 - 216#64) 24 ∗ P))
      (Q := fun s1 =>
        s1.sp = sp0 - 672#64 ∧ traceVRegs s1 = traceVRegs s ∧ AllocCallPreserved s s1)
      ?_ ?_
    · by_vm_steps (
        wp_steps 9
        refine SepWP.weaken_pre
          (show _ ⊢
            (((sp0 - 600#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 600#64 + 8#64) 16) ∗
              (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((sp0 - 216#64 + 8#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded))) ∗
              ((out_sret ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
                ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                A.repAlloc.live out_ptr (2 * ptsNeeded) 1 ∗
                (out_ptr ↦ₛ outFinal)) ∗
              (A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
                optPolyCacheListAt A.repAlloc (sp0 - 576#64)
                  [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
                ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
            dsimp only [RustCliAllocBudget.repAlloc_live]
            try simp only [arm64_norm]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        refine SepWP.weaken_pre
          (sepConj_mono (optPolyCacheSlot_none_entails_memRegion24 (sp0 - 600#64))
            (sepConj_mono
              (pointsTo64_three_entails_memRegion24 (sp0 - 216#64)
                (BitVec.ofNat 64 (2 * ptsNeeded)) out_ptr (BitVec.ofNat 64 (2 * ptsNeeded)))
              (sepConj_mono_left
                (fold_optVecU8Of_some A.repAlloc out_sret out_ptr outFinal (2 * ptsNeeded)
                  (by omega) (by omega) hout_len hout_ptr)))) ?_
        refine SepWP.weaken_pre
          (show _ ⊢
            memRegion (sp0 - 600#64) 24 ∗
              A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
              optPolyCacheListAt A.repAlloc (sp0 - 576#64)
                [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
              (optVecU8Of A.repAlloc out_sret (some outFinal) ∗
                ((sp0 - 632#64) ↦₆₄ out_sret) ∗
                memRegion (sp0 - 216#64) 24 ∗ P) by
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
          ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
           by simpa [wp_norm, arm64_norm] using hsp,
           by simp [wp_norm, arm64_norm],
           acp_of_PureStep⟩)
    · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, htr1, hacp1⟩
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
      refine SepWP.weaken_pre
        (show _ ⊢
          memRegion (sp0 - 600#64) 24 ∗
            A.pool lim st s1 ∗ stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheListAt A.repAlloc (sp0 - 576#64)
              [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
            (optVecU8Of A.repAlloc out_sret (some outFinal) ∗
              ((sp0 - 632#64) ↦₆₄ out_sret) ∗
              memRegion (sp0 - 216#64) 24 ∗ P) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine h1_15 st s1 _ post hpc1 hstat1 hsp1
        (fun sf evs hevs hpc_f hstat_f hsp_f htr_f hacp_f => ?_)
      refine SepWP.weaken_pre
        (show _ ⊢
          optVecU8Of A.repAlloc out_sret (some outFinal) ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            memRegion (sp0 - 600#64) 384 ∗
            memRegion (sp0 - 216#64) 24 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (sp0 - 672#64) allocHookStack ∗ P by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact hcont sf evs hevs hpc_f hstat_f hsp_f (htr_f.trans htr1) (hacp1.trans hacp_f)
  | some p =>
    unfold optPolyCacheSlotAt
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro ptr_p
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim ?_
    rintro ⟨hp_ge1, hp_le, hptr_p⟩
    have hslt := bv64_slt_one_of_ge1_le65536 hp_ge1 hp_le
    have htoNat := bv64_lsl1_toNat_of_le65536 hp_le
    have hne0 := bv64_ofNat_ne0_of_ge1 hp_ge1 hp_le
    simp only [sepConj_assoc]
    refine SepWP.weaken_pre (dropPolySlot_some_to_dealloc A.repAlloc (sp0 - 600#64) ptr_p p _) ?_
    dsimp only [RustCliAllocBudget.repAlloc_live]
    refine seq_vm_clean (mid := lsρ spqrRustDeallocSym)
      (P_mid :=
        A.live ptr_p (2 * p.coefficients.length) 2 ∗
          memRegion ptr_p (2 * p.coefficients.length) ∗
          A.pool lim st s ∗
          stackAt (sp0 - 672#64) allocHookStack ∗
          (((sp0 - 600#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
            ((sp0 - 600#64 + 8#64) ↦₆₄ ptr_p) ∗
            ((sp0 - 600#64 + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length)) ∗
          (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            ((sp0 - 216#64 + 8#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded))) ∗
          ((out_sret ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
            ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
            A.repAlloc.live out_ptr (2 * ptsNeeded) 1 ∗
            (out_ptr ↦ₛ outFinal)) ∗
          (optPolyCacheListAt A.repAlloc (sp0 - 576#64)
            [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P))
      (Q := fun s1 =>
        s1.sp = sp0 - 672#64 ∧
        s1.readReg64 .x0 = ptr_p ∧
        s1.readReg64 .x1 = (BitVec.ofNat 64 p.coefficients.length) <<< 1 ∧
        s1.readReg64 .x2 = 2#64 ∧
        s1.readReg64 .x30 = (blkPl_418).base + 1456#64 ∧
        traceVRegs s1 = traceVRegs s ∧
        AllocCallPreserved s s1)
      ?_ ?_
    · by_vm_steps (
        wp_steps 13
        refine SepWP.weaken_pre
          (show _ ⊢
            A.live ptr_p (2 * p.coefficients.length) 2 ∗
              memRegion ptr_p (2 * p.coefficients.length) ∗
              A.pool lim st s ∗
              stackAt (sp0 - 672#64) allocHookStack ∗
              (((sp0 - 600#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
                ((sp0 - 600#64 + 8#64) ↦₆₄ ptr_p) ∗
                ((sp0 - 600#64 + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length)) ∗
              (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((sp0 - 216#64 + 8#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded))) ∗
              ((out_sret ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
                ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
                A.repAlloc.live out_ptr (2 * ptsNeeded) 1 ∗
                (out_ptr ↦ₛ outFinal)) ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 576#64)
                [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
                ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
            dsimp only [RustCliAllocBudget.repAlloc_live]
            try simp only [arm64_norm]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
          ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
           by simpa [wp_norm, arm64_norm] using hsp,
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm],
           acp_of_PureStep⟩)
    · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx30_1, htr1, hacp1⟩
      simp only [traceVRegs, Prod.mk.injEq] at htr1
      have hsp1_al : s1.sp &&& 15#64 = 0#64 := by
        rw [hsp1]; exact sp672_aligned sp0 hsp0
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
      wp_conv_pre => rw [← hsp1]
      wp_call hdealloc ⟨ptr_p, 2 * p.coefficients.length, 2, st⟩
      wp_conv_pre => rw [hsp1]
      wp_steps 1
      refine SepWP.weaken_pre
        (show _ ⊢
          (((sp0 - 600#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
            ((sp0 - 600#64 + 8#64) ↦₆₄ ptr_p) ∗
            ((sp0 - 600#64 + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length)) ∗
            (((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
              ((sp0 - 216#64 + 8#64) ↦₆₄ out_ptr) ∗
              ((sp0 - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded))) ∗
            ((out_sret ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
              ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
              ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
              A.repAlloc.live out_ptr (2 * ptsNeeded) 1 ∗
              (out_ptr ↦ₛ outFinal)) ∗
            (A.pool lim (M.stepEvents (rustDeallocEvents (2 * p.coefficients.length) 2) st) sf ∗
              stackAt (sp0 - 672#64) allocHookStack ∗
              optPolyCacheListAt A.repAlloc (sp0 - 576#64)
                [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
              ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
          try simp only [arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono
          (pointsTo64_three_entails_memRegion24 (sp0 - 600#64)
            (BitVec.ofNat 64 p.coefficients.length) ptr_p (BitVec.ofNat 64 p.coefficients.length))
          (sepConj_mono
            (pointsTo64_three_entails_memRegion24 (sp0 - 216#64)
              (BitVec.ofNat 64 (2 * ptsNeeded)) out_ptr (BitVec.ofNat 64 (2 * ptsNeeded)))
            (sepConj_mono_left
              (fold_optVecU8Of_some A.repAlloc out_sret out_ptr outFinal (2 * ptsNeeded)
                (by omega) (by omega) hout_len hout_ptr)))) ?_
      refine SepWP.weaken_pre
        (show _ ⊢
          A.pool lim (M.stepEvents (rustDeallocEvents (2 * p.coefficients.length) 2) st) sf ∗
            memRegion (sp0 - 600#64) 24 ∗
            stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheListAt A.repAlloc (sp0 - 576#64)
              [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
            (optVecU8Of A.repAlloc out_sret (some outFinal) ∗
              ((sp0 - 632#64) ↦₆₄ out_sret) ∗
              memRegion (sp0 - 216#64) 24 ∗ P) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.transport_budgetPool ?_ (hnext := ?_)
      · simp [wp_norm, arm64_norm]
      refine SepWP.weaken_pre
        (show _ ⊢
          memRegion (sp0 - 600#64) 24 ∗
            A.pool lim (M.stepEvents (rustDeallocEvents (2 * p.coefficients.length) 2) st) _ ∗
            stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheListAt A.repAlloc (sp0 - 576#64)
              [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗
            (optVecU8Of A.repAlloc out_sret (some outFinal) ∗
              ((sp0 - 632#64) ↦₆₄ out_sret) ∗
              memRegion (sp0 - 216#64) 24 ∗ P) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine h1_15 (M.stepEvents (rustDeallocEvents (2 * p.coefficients.length) 2) st) _ _ post
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_sf])
        (by rw [State.sp_setPC, hsp_sf, hsp1])
        (fun sf' evs_rest hevs_rest hpc_f hstat_f hsp_f htr_f hacp_f => ?_)
      rw [← AllocCostModel.stepEvents_append]
      refine SepWP.weaken_pre
        (show _ ⊢
          optVecU8Of A.repAlloc out_sret (some outFinal) ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            memRegion (sp0 - 600#64) 384 ∗
            memRegion (sp0 - 216#64) 24 ∗
            A.pool lim (M.stepEvents (rustDeallocEvents (2 * p.coefficients.length) 2 ++ evs_rest) st) sf' ∗
            stackAt (sp0 - 672#64) allocHookStack ∗ P by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact hcont sf' (rustDeallocEvents (2 * p.coefficients.length) 2 ++ evs_rest)
        ((FreeOnlyEvs.singleton 2 (2 * p.coefficients.length)).append hevs_rest)
        hpc_f hstat_f hsp_f
        (by rw [htr_f]; simp [traceVRegs, wp_norm, arm64_norm, *])
        (((hacp1.trans (by assumption)).trans acp_of_PureStep).trans hacp_f)

/-- Copy empty `out` header `(0, 1, 0)` to `out_sret` and drop `polys[0..16] = replicate 16 none`
    (`[LibsignalPlacement]`), entered when `dec.ptsNeeded = 0`. -/
theorem dropOptPolyCache_from1460_placed_sepWP [lsmpl : LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (sp0 out_sret : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1460#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      sf.pc = (blkPl_418).base + 1904#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (optVecU8Of A.repAlloc out_sret (some []) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (List.replicate 16 none) ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 216#64) ↦₆₄ 0#64) ∗
        ((sp0 - 208#64) ↦₆₄ 1#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗
        memRegion out_sret vecHeaderBytes ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have h1_15 := @dropOptPolyCache_1_to_15_placed_sepWP lsmpl M A lim ext ret_pc hdealloc_sat sp0 hsp0
    none none none none none none none none none none none none none none none
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsplit_head :
      optPolyCacheListAt A.repAlloc (sp0 - 600#64) (List.replicate 16 none) =
      ((sp0 - 600#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 600#64 + 8#64) 16 ∗
        optPolyCacheListAt A.repAlloc (sp0 - 576#64)
          [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] := by
    change optPolyCacheListAt A.repAlloc (sp0 - 600#64)
      (none :: [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]) = _
    unfold optPolyCacheListAt vecHeaderBytes
    rw [CryptoVerification.RustHeap.arrayAt_cons]
    unfold optPolyCacheSlotAt
    simp only [arm64_norm, sepConj_assoc]
  rw [hsplit_head, memRegion24_eq_exists_three out_sret]
  wp_pull_exists
  refine seq_vm_clean (mid := (blkPl_418).base + 1484#64)
    (P_mid :=
      A.pool lim st s ∗
        memRegion (sp0 - 600#64) 24 ∗
        stackAt (sp0 - 672#64) allocHookStack ∗
        optPolyCacheListAt A.repAlloc (sp0 - 576#64)
          [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] ∗
        (optVecU8Of A.repAlloc out_sret (some []) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 216#64) 24 ∗ P))
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧ traceVRegs s1 = traceVRegs s ∧ AllocCallPreserved s s1)
    ?_ ?_
  · by_vm_steps (
      wp_steps 6
      refine SepWP.weaken_pre
        (show _ ⊢
          (((sp0 - 600#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 600#64 + 8#64) 16) ∗
            (((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64 + 8#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64 + 16#64) ↦₆₄ 0#64)) ∗
            ((out_sret ↦₆₄ 0#64) ∗ ((out_sret + 8#64) ↦₆₄ 1#64) ∗ ((out_sret + 16#64) ↦₆₄ 0#64)) ∗
            (A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
              optPolyCacheListAt A.repAlloc (sp0 - 576#64)
                [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] ∗
              ((sp0 - 632#64) ↦₆₄ out_sret) ∗ P) by
          try simp only [arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono (optPolyCacheSlot_none_entails_memRegion24 (sp0 - 600#64))
          (sepConj_mono (pointsTo64_three_entails_memRegion24 (sp0 - 216#64) 0#64 1#64 0#64)
            (sepConj_mono_left (fold_optVecU8Of_some_nil A.repAlloc out_sret)))) ?_
      refine SepWP.weaken_pre
        (show _ ⊢
          A.pool lim st s ∗
            memRegion (sp0 - 600#64) 24 ∗
            stackAt (sp0 - 672#64) allocHookStack ∗
            optPolyCacheListAt A.repAlloc (sp0 - 576#64)
              [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] ∗
            (optVecU8Of A.repAlloc out_sret (some []) ∗
              ((sp0 - 632#64) ↦₆₄ out_sret) ∗
              memRegion (sp0 - 216#64) 24 ∗ P) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm],
         acp_of_PureStep⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, htr1, hacp1⟩
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    refine SepWP.weaken_pre
      (show _ ⊢
        memRegion (sp0 - 600#64) 24 ∗
          A.pool lim st s1 ∗ stackAt (sp0 - 672#64) allocHookStack ∗
          optPolyCacheListAt A.repAlloc (sp0 - 576#64)
            [none, none, none, none, none, none, none, none, none, none, none, none, none, none, none] ∗
          (optVecU8Of A.repAlloc out_sret (some []) ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            memRegion (sp0 - 216#64) 24 ∗ P) by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine h1_15 st s1 _ post hpc1 hstat1 hsp1
      (fun sf evs hevs hpc_f hstat_f hsp_f htr_f hacp_f => ?_)
    refine SepWP.weaken_pre
      (show _ ⊢
        optVecU8Of A.repAlloc out_sret (some []) ∗
          ((sp0 - 632#64) ↦₆₄ out_sret) ∗
          memRegion (sp0 - 600#64) 384 ∗
          memRegion (sp0 - 216#64) 24 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    exact hcont sf evs hevs hpc_f hstat_f hsp_f (htr_f.trans htr1) (hacp1.trans hacp_f)

/-! ## Epilogue Return & `points_vecs` Deallocation (`320`, `304`, `1904`, `288`) -/

/-- Epilogue register restoration and `ret` (`[LibsignalPlacement]`), exposing both `VmPreserved`
    and `AllocCallPreserved`. -/
theorem decodedMessage_epilogue_ret_placed_sepWP [lsmpl : LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (sp0 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 320#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      AllocCallPreserved s sf →
      CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (savedRegsAt sp0 s0 ∗
        memRegion (sp0 - 672#64) 576 ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsp96_align : (sp0 - 96#64) &&& 15#64 = 0#64 := by
    have h : (sp0 - 96#64) &&& 15#64 = sp0 &&& 15#64 := by bv_bits
    rw [h, hsp0]
  unfold savedRegsAt
  simp only [sepConj_assoc]
  wp_steps 8
  refine SepWP.weaken_pre
    (show _ ⊢ stackAt sp0 decodedMessageStack ∗ P by
      rw [stackAt_decodedMessage_eq sp0]
      refine Entails.trans ?_
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (savedRegsAt_entails_memRegion96 sp0 s0))))
      unfold savedRegsAt
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply hcont
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm, hstat]
  · simp [wp_norm, arm64_norm, hsp]
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · exact acp_of_PureStep
  · unfold CalleeSavedGprsPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

/-- Epilogue `points_vecs` deallocation (`size = 256, align = 8`) and return (`[LibsignalPlacement]`). -/
theorem decodedMessage_epilogue_dealloc_placed_sepWP [lsmpl : LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp0 pv_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 304#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx8 : s.readReg64 .x8 = 16#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
          stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool lim st s ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  have hdealloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem hdealloc_sat)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc
  have hret := @decodedMessage_epilogue_ret_placed_sepWP lsmpl ext s0 sp0 hsp0
  try dsimp only [BitVec.ofNat_eq_ofNat] at hdealloc hret hpc hcont ⊢
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hsub16384 : sp0 - 672#64 - 16384#64 = sp0 - 17056#64 := by bv_omega
  rw [stackAt_extHook_eq_allocHook (sp0 - 672#64)]
  simp only [sepConj_assoc]
  wp_steps 4
  refine SepWP.weaken_pre
    (show _ ⊢
      A.pool lim st s ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        stackAt (sp0 - 672#64) allocHookStack ∗
        memRegion (sp0 - 672#64 - 16384#64) 12288 ∗ P by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  wp_call hdealloc ⟨pv_ptr, 256, 8, st⟩
  wp_conv_pre => rw [hsp]
  have hacp0 : AllocCallPreserved s sf := AllocCallPreserved.trans acp_of_PureStep (by assumption)
  refine SepWP.weaken_pre
    (show _ ⊢
      savedRegsAt sp0 s0 ∗
        memRegion (sp0 - 672#64) 576 ∗
        stackAt (sp0 - 672#64) extHookStack ∗
        (A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗ P) by
      rw [stackAt_extHook_eq_allocHook (sp0 - 672#64), hsub16384]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_left (memRegion_56_8_512_entails_576 sp0 pv_ptr)))
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine hret sf (A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗ P) post
    hpc_sf hrun_sf (by rw [hsp_sf, hsp])
    (fun sf' hpc_f hstat_f hsp_f htr_f hvm_f hacp_f hcs_f => ?_)
  refine SepWP.weaken_pre
    (show _ ⊢
      A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
        stackAt sp0 decodedMessageStack ∗ P by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.transport_budgetPool hvm_f (hnext := ?_)
  exact hcont sf' hpc_f hstat_f hsp_f
    (by rw [htr_f]; simp [traceVRegs, wp_norm, arm64_norm, *])
    (hacp0.trans hacp_f) hcs_f

/-- Epilogue from `entry + 1904#64` (`ldr x8, [sp, #0x30]; cbnz x8, entry + 304#64`) to return (`[LibsignalPlacement]`). -/
theorem decodedMessage_epilogue_from1904_placed_sepWP [lsmpl : LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp0 pv_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1904#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
          stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 48 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool lim st s ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  have hdealloc_ep := @decodedMessage_epilogue_dealloc_placed_sepWP lsmpl M A lim ext hdealloc_sat s0 sp0 pv_ptr hsp0 st
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  wp_steps 2
  refine SepWP.weaken_pre
    (show _ ⊢
      A.pool lim st s ∗
        ((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 48 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  refine SepWP.weaken_pre
    (show _ ⊢
      (memRegion (sp0 - 672#64) 48 ∗ ((sp0 - 624#64) ↦₆₄ 16#64)) ∗
        (((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
          A.live pv_ptr 256 8 ∗
          memRegion pv_ptr 256 ∗
          memRegion (sp0 - 608#64) 512 ∗
          savedRegsAt sp0 s0 ∗
          A.pool lim st _ ∗
          stackAt (sp0 - 672#64) extHookStack ∗ P) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_48_8_entails_56 sp0 16#64)) ?_
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        A.pool lim st _ ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine hdealloc_ep _ P post
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simpa [wp_norm, arm64_norm] using hsp)
    (by simp [wp_norm, arm64_norm])
    (fun sf hpc_f hstat_f hsp_f htr_f hacp_f hcs_f => ?_)
  exact hcont sf hpc_f hstat_f hsp_f
    (by simpa [wp_norm, arm64_norm] using htr_f)
    (AllocCallPreserved.trans acp_of_PureStep hacp_f) hcs_f

/-- Epilogue from `entry + 288#64` (when `(collectPointsVecsTotal dec 0 16 false []).1 = true`):
    stores `none` to `out_sret`, deallocates `points_vecs`, and returns (`[LibsignalPlacement]`). -/
theorem decodedMessage_epilogue_from288_placed_sepWP [lsmpl : LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp0 out_sret pv_ptr w648 pvLenFinal : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 288#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hcont : ∀ sf : State,
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp0 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      CalleeSavedGprsPreserved s0 sf →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (optVecU8Of A.repAlloc out_sret none ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
          stackAt sp0 decodedMessageStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((sp0 - 648#64) ↦₆₄ w648) ∗
        ((sp0 - 632#64) ↦₆₄ out_sret) ∗
        ((sp0 - 624#64) ↦₆₄ 16#64) ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ pvLenFinal) ∗
        memRegion out_sret vecHeaderBytes ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 24 ∗
        memRegion (sp0 - 640#64) 8 ∗
        memRegion (sp0 - 600#64) 504 ∗
        savedRegsAt sp0 s0 ∗
        A.pool lim st s ∗
        stackAt (sp0 - 672#64) extHookStack ∗ P) post := by
  have hdealloc_ep := @decodedMessage_epilogue_dealloc_placed_sepWP lsmpl M A lim ext hdealloc_sat s0 sp0 pv_ptr hsp0 st
  try dsimp only [BitVec.ofNat_eq_ofNat] at *
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hout_split : memRegion out_sret vecHeaderBytes =
      (∃∗ w0 : BitVec 64, out_sret ↦₆₄ w0) ∗ memRegion (out_sret + 8#64) 16 := by
    rw [show vecHeaderBytes = 8 + 16 from rfl,
      memRegion_split out_sret 8 16 (by decide),
      ProofLib.memRegion_eight out_sret]
  rw [hout_split]
  wp_pull_exists
  refine seq_vm_clean (mid := (blkPl_418).base + 304#64)
    (P_mid :=
      A.pool lim st s ∗
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
        A.live pv_ptr 256 8 ∗
        memRegion pv_ptr 256 ∗
        memRegion (sp0 - 672#64) 56 ∗
        memRegion (sp0 - 608#64) 512 ∗
        savedRegsAt sp0 s0 ∗
        stackAt (sp0 - 672#64) extHookStack ∗
        (optVecU8Of A.repAlloc out_sret none ∗ P))
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧
      s1.readReg64 .x8 = 16#64 ∧
      traceVRegs s1 = traceVRegs s ∧
      AllocCallPreserved s s1)
    ?_ ?_
  · by_vm_steps (
      wp_steps 4
      have hnone_eq :
          (out_sret ↦₆₄ BitVec.allOnes 64) ∗ memRegion (out_sret + 8#64) 16 =
            optVecU8Of A.repAlloc out_sret none := by
        unfold optVecU8Of noneCap; rfl
      refine SepWP.weaken_pre
        (show _ ⊢
          (memRegion (sp0 - 672#64) 24 ∗
            ((sp0 - 648#64) ↦₆₄ w648) ∗
            memRegion (sp0 - 640#64) 8 ∗
            ((sp0 - 632#64) ↦₆₄ out_sret) ∗
            ((sp0 - 624#64) ↦₆₄ 16#64)) ∗
          (((sp0 - 608#64) ↦₆₄ pvLenFinal) ∗ memRegion (sp0 - 600#64) 504) ∗
          (((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
            A.live pv_ptr 256 8 ∗
            memRegion pv_ptr 256 ∗
            savedRegsAt sp0 s0 ∗
            A.pool lim st s ∗
            stackAt (sp0 - 672#64) extHookStack ∗
            (optVecU8Of A.repAlloc out_sret none ∗ P)) by
          rw [← hnone_eq]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono (memRegion_24_8_8_8_8_entails_56 sp0 w648 out_sret 16#64)
          (sepConj_mono_left (memRegion_8_504_entails_512 sp0 pvLenFinal))) ?_
      refine SepWP.weaken_pre
        (show _ ⊢
          A.pool lim st s ∗
            ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
            A.live pv_ptr 256 8 ∗
            memRegion pv_ptr 256 ∗
            memRegion (sp0 - 672#64) 56 ∗
            memRegion (sp0 - 608#64) 512 ∗
            savedRegsAt sp0 s0 ∗
            stackAt (sp0 - 672#64) extHookStack ∗
            (optVecU8Of A.repAlloc out_sret none ∗ P) by
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         acp_of_PureStep⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx8_1, htr1, hacp1⟩
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    refine SepWP.weaken_pre
      (show _ ⊢
        ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗
          A.live pv_ptr 256 8 ∗
          memRegion pv_ptr 256 ∗
          memRegion (sp0 - 672#64) 56 ∗
          memRegion (sp0 - 608#64) 512 ∗
          savedRegsAt sp0 s0 ∗
          A.pool lim st s1 ∗
          stackAt (sp0 - 672#64) extHookStack ∗
          (optVecU8Of A.repAlloc out_sret none ∗ P) by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine hdealloc_ep s1 (optVecU8Of A.repAlloc out_sret none ∗ P) post
      hpc1 hstat1 hsp1 hx8_1
      (fun sf hpc_f hstat_f hsp_f htr_f hacp_f hcs_f => ?_)
    refine SepWP.weaken_pre
      (show A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
            stackAt sp0 decodedMessageStack ∗ (optVecU8Of A.repAlloc out_sret none ∗ P) ⊢
          optVecU8Of A.repAlloc out_sret none ∗
            A.pool lim (M.stepEvents (rustDeallocEvents 256 8) st) sf ∗
            stackAt sp0 decodedMessageStack ∗ P by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    exact hcont sf hpc_f hstat_f hsp_f (htr_f.trans htr1) (hacp1.trans hacp_f) hcs_f

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DropEpiloguePlacedBudget
