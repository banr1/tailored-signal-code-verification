/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopy
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Success Copy and Deallocation for `<PolyDecoder>::from_pb`

Threads `RustCliAllocBudget M`, `FreeOnlyEvs`, and `AllocCallPreserved` through the `+876 → s0.lr`
success exit of `<PolyDecoder>::from_pb` on Block `376`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkLib_eq_376 blkPC_376 blkPl_376 lsρ)
open CryptoVerification.LibsignalSpqrV1 (
  CHUNK_SIZE NUM_POLYS ProtoPolynomialDecoder Pt SortedSetPt
)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  memRegion_rejoin_vecBuf
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt arrayAt_nil vecU8)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym)
open CryptoVerification.SpqrV1.Drop (
  dropGluePoly16Stack slot0_entails_memRegion_24 slot_join_memRegion_at
  sortedSetPtListOf_eq_vecPtListOf vecCapPtrDealloc vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyDecoderAt polyDecoderIsCompleteOff polyDecoderPadOff
  polyDecoderPadSize polyDecoderPtsNeededOff resultPolyDecoderFromPbAt
  sortedSetPtListOf
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  HiddenEq align_pre_wp fromPbCoreStack fromPb_bv384_toNat
  fromPb_stackAt_dropGluePoly16_split_bottom fsp_rejoin_448
  headers_heaps_entails_vecPtListOf length_vecHeadersBytesOf list_length_16_elim
  memRegion_400_split_ok pbA_rejoin_40 pbA_tail_entails_memRegion_16
  replace_sub_entails savedRegsAt
  spqrRustDeallocSym truncate8_truncate32_zeroExtend64 u32_zeroExtend64_eq_ofNat_toNat
  vecHeadersBytesOf vecPtHeapList vecPtListOf_entails_headers_heaps
  vecU8_frame_entails vecU8_step_entails vecVecU8BufDealloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved allocMemcpyVmSpec rustCliDeallocBudgetSpec
  rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget (
  fromPb_tail_1236_placed_sepWP
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate8_truncate32_zeroExtend64 fromPb_bv384_toNat
attribute [local simp] truncate8_truncate32_zeroExtend64 fromPb_bv384_toNat

/-! ## `memcpy` Budget Contract & Private Sequencing Combinators -/

/-- `sessionMemcpySpec` strengthened with `AllocCallPreserved` and `VmPreserved` so both
    `A.pool lim st` and `AllocCallPreserved` transport across `memcpy` in `<PolyDecoder>::from_pb`. -/
def sessionMemcpyVmAcpSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (sessionMemcpySpec hookStack).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧
      AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

/-- Lift `subroutine_ok P a allocMemcpyVmSpec` (`LibsignalBinary.Heap.MallocngBridgeBudget`) to
    `sessionMemcpyVmAcpSpec hookStack` by framing `stackAt s0.sp hookStack`. -/
theorem subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm {P : Program} {a : BitVec 64}
    (hookStack : Nat := 4096)
    (h : subroutine_ok P a allocMemcpyVmSpec) :
    subroutine_ok P a (sessionMemcpyVmAcpSpec hookStack) := by
  refine subroutine_ok_outcome_intro fun (dst, src, bs) R s0 hpc hrun hpre hal => ?_
  dsimp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, ProofLib.libcMemcpySpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  let R' : SepProp := stackAt s0.sp hookStack ∗ R
  have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ R' := by
    dsimp only [allocMemcpyVmSpec, R']
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    ac_nf at hm ⊢
  refine h.mono_outcome (dst, src, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, R'] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    dsimp only [sessionMemcpyVmAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0f, hacp.2.1, hacp, hvm⟩, ?_⟩
    ac_nf at hm' ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

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

private theorem sync_pool_vm (s1 : State) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    {s2 : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hnext : VmPreserved s1 s2 → SepWP prog target s2 (A.pool lim st s2 ∗ F) post)
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hvm : VmPreserved s1 s2 := by simp [VmPreserved, Heap.PoolPreserved, wp_norm, arm64_norm]) :
    SepWP prog target s2 P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]; exact hnext hvm

private def PostEvs (M : AllocCostModel) (st : M.σ) (s : State)
    (P_out : M.σ → State → SepProp) (Q_out : State → Prop) : State → SepProp → Prop :=
  fun sf Pf =>
    ∃ evs, FreeOnlyEvs evs ∧ (Pf ⊢ P_out (M.stepEvents evs st) sf) ∧
      AllocCallPreserved s sf ∧ Q_out sf

private theorem seq_evs_step {M : AllocCostModel} {prog : Program} {mid target : BitVec 64}
    {st : M.σ} {s : State} {P : SepProp}
    {P_mid : M.σ → State → SepProp} {Q_mid : State → Prop}
    {P_out : M.σ → State → SepProp} {Q_out : State → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧
        AllocCallPreserved s sm ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → AllocCallPreserved s sm → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (PostEvs M st1 sm P_out Q_out)) :
    SepWP prog target s P (PostEvs M st s P_out Q_out) := by
  refine SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs1, hevs1, hent1, hacp1, hQ1⟩ => ?_
  refine SepWP.weaken_pre hent1 ?_
  refine SepWP.mono (h2 (M.stepEvents evs1 st) sm hpc hrun hacp1 hQ1)
    fun sf _Pf _ _ ⟨evs2, hevs2, hent2, hacp2, hQ2⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hacp1.trans hacp2, hQ2⟩
  rwa [M.stepEvents_append]

private theorem dealloc_u8_list_cons_step_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {target_pc : BitVec 64} {st : M.σ} {s : State}
    (arrA off off8 off16 offNext : BitVec 64) (n m : Nat)
    (hoff : arrA + BitVec.ofNat 64 n = arrA + off)
    (hoff8 : (arrA + off) + 8#64 = arrA + off8)
    (hoff16 : (arrA + off) + 16#64 = arrA + off16)
    (hoffNext : (arrA + off) + 24#64 = arrA + offNext)
    (hm : n + 24 = m) (hbound : m ≤ 2 ^ 64)
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (TailFixed : SepProp)
    {Q : State → Prop}
    (h_zero : ∀ cap ptr : BitVec 64, (cap == 0#64) = true →
      SepWP prog target_pc s
        ((((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8) ∗
          (memRegion arrA n ∗
            (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + offNext) rest ∗
              (A.pool lim st s ∗ TailFixed))))
        (fun sm Pm =>
          VmPreserved s sm ∧
          (Pm ⊢ (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8) ∗
            memRegion arrA n ∗
            (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + offNext) rest ∗
              (A.pool lim st s ∗ TailFixed))) ∧
          AllocCallPreserved s sm ∧ Q sm))
    (h_nonzero : ∀ cap ptr : BitVec 64, (cap == 0#64) = false →
      SepWP prog target_pc s
        ((((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8 ∗
          (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) ∗
          (memRegion arrA n ∗
            (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + offNext) rest ∗
              (A.pool lim st s ∗ TailFixed))))
        (fun sm Pm =>
          (Pm ⊢ (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8) ∗
            memRegion arrA n ∗
            (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + offNext) rest ∗
              (A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗ TailFixed))) ∧
          AllocCallPreserved s sm ∧ Q sm)) :
    SepWP prog target_pc s
      (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + off) (bs :: rest) ∗
        (memRegion arrA n ∗ (A.pool lim st s ∗ TailFixed)))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + offNext) rest ∗
          (memRegion arrA m ∗ (A.pool lim (M.stepEvents evs st) sm ∗ TailFixed))) ∧
        AllocCallPreserved s sm ∧ Q sm) := by
  have hpre :
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + off) (bs :: rest) ∗
        (memRegion arrA n ∗ (A.pool lim st s ∗ TailFixed)) =
      vecU8 A.repAlloc (arrA + off) bs ∗
        (memRegion arrA n ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (arrA + offNext) rest ∗
            (A.pool lim st s ∗ TailFixed))) := by
    show (vecU8 A.repAlloc (arrA + off) bs ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ((arrA + off) + 24#64) rest) ∗
      (memRegion arrA n ∗ (A.pool lim st s ∗ TailFixed)) = _
    rw [hoffNext]
    sep_ac_rfl
  rw [hpre]
  refine SepWP.weaken_pre (vecU8_step_entails A.repAlloc arrA off off8 off16 hoff8 hoff16 bs _) ?_
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  cases hcap : (cap == 0#64) <;> simp only [Bool.false_eq_true, ↓reduceIte, sepConj_emp]
  · refine SepWP.mono (h_nonzero cap ptr hcap) fun sm _Pm _ _ ⟨hPm, hacp, hq⟩ => ?_
    refine ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, ?_, hacp, hq⟩
    refine Entails.trans hPm ?_
    refine Entails.trans (slot_join_memRegion_at arrA off off8 off16 cap ptr n m hoff hoff8 hoff16 hm hbound _) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · refine SepWP.mono (h_zero cap ptr hcap) fun sm _Pm _ _ ⟨hvm, hPm, hacp, hq⟩ => ?_
    refine ⟨[], FreeOnlyEvs.nil, ?_, hacp, hq⟩
    have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
    rw [hst_nil, A.pool_of_vmPreserved hvm]
    refine Entails.trans hPm ?_
    refine Entails.trans (slot_join_memRegion_at arrA off off8 off16 cap ptr n m hoff hoff8 hoff16 hm hbound _) ?_
    exact Entails.of_eq (by sep_ac_rfl)

local macro "dealloc_u8_slot_step " _M:ident _A:ident _lim:ident ptsPtr:term:max off0:term:max off8:term:max off16:term:max off24:term:max k:term:max k24:term:max c:term:max scur:ident _stcur:term:max hsp:ident : tactic =>
  `(tactic| (
    refine dealloc_u8_list_cons_step_budget $ptsPtr $off0 $off8 $off16 $off24 $k $k24
      rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) $c _ _ ?_ ?_
    · intro cap ptr hcap
      by_vm_steps (wp_steps; dsimp only [AllocCallPreserved]; wp_done)
    · intro cap ptr hcap
      wp_steps
      refine sync_pool_vm $scur fun _ => ?_
      wp_apply
      rcases (‹AllocCallPreserved $scur _› : AllocCallPreserved $scur _) with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.weaken_pre (Entails.of_eq (by rw [$hsp:ident])) ?_
      dsimp only [AllocCallPreserved]
      wp_done))

/-! ## Unrolled 16-Slot `Vec<u8>` Deallocation (`+904 -> +1076` and `+1076 -> +1236`) -/

theorem fromPb_success_dealloc_first8_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out pbA ptsPtr d384 ptsNeeded64 : BitVec 64)
    (b392 isComplete8 : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = ptsNeeded64)
    (hx20 : s.readReg64 .x20 = isComplete8.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx22 : s.readReg64 .x22 = out)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 1076#64)
      s
      (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr
        (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 192#64) rest ∗
          (memRegion ptsPtr 192 ∗ (A.pool lim (M.stepEvents evs st) sm ∗
            (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
              ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame))))) ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, spqrRustDeallocSym] at hdealloc_fo
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc hx19 hx20 hx21 hx22 ⊢
  change SepWP _ _ s _ (PostEvs M st s
    (fun stf sm =>
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 192#64) rest ∗
        (memRegion ptsPtr 192 ∗ (A.pool lim stf sm ∗
          (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
    (fun sm =>
      sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace))
  refine seq_evs_step (mid := (blkPl_376).base + 932#64)
    (P_mid := fun st1 sm =>
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 24#64)
        (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion ptsPtr 24 ∗ (A.pool lim st1 sm ∗
          (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
    (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · have hpre0 :
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr
          (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
            ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
        vecU8 A.repAlloc ptsPtr c0 ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      show (vecU8 A.repAlloc ptsPtr c0 ∗ _) ∗ _ = _
      sep_ac_rfl
    rw [hpre0]
    refine SepWP.weaken_pre (vecU8_frame_entails A.repAlloc ptsPtr c0 _) ?_
    apply ProofLib.SepWP.exists_left; intro cap
    apply ProofLib.SepWP.exists_left; intro ptr
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    have hpost0 : ∀ P_pool : SepProp,
        ((ptsPtr ↦₆₄ cap) ∗ ((ptsPtr + 8#64) ↦₆₄ ptr) ∗ memRegion (ptsPtr + 16#64) 8) ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (((out + 384#64) ↦₆₄ ptsNeeded64) ∗ ((out + 392#64) ↦₈ isComplete8) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗ P_pool ∗ stackAt fsp allocHookStack ∗ Frame)) ⊢
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 24#64)
          (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 24 ∗ (P_pool ∗
            (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
              ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))) := by
      intro P_pool
      refine Entails.trans (slot0_entails_memRegion_24 ptsPtr cap ptr _) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · refine SepWP.mono
        (show SepWP _ _ s _ (fun sm Pm =>
          VmPreserved s sm ∧
          (Pm ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion ptsPtr 24 ∗ (A.pool lim st s ∗
              (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame))))) ∧
          AllocCallPreserved s sm ∧ sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) from by
          by_vm_steps (
            wp_steps
            refine SepWP.weaken_pre (hpost0 _) ?_
            dsimp only [AllocCallPreserved]
            wp_done))
        fun sm _Pm _ _ ⟨hvm, hPm, hacp, hq⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, ?_, hacp, hq⟩
      have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
      rw [hst_nil, A.pool_of_vmPreserved hvm]; exact hPm
    · refine SepWP.mono
        (show SepWP _ _ s _ (fun sm Pm =>
          (Pm ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion ptsPtr 24 ∗ (A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
              (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame))))) ∧
          AllocCallPreserved s sm ∧ sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) from by
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_apply
          have hacp_call : AllocCallPreserved s sf := by assumption
          rcases hacp_call with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by rw [hsp]; sep_ac_rfl)) (hpost0 _)) ?_
          dsimp only [AllocCallPreserved]
          wp_done)
        fun _ _ _ _ ⟨hPm, hacp, hq⟩ =>
          ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, hPm, hacp, hq⟩
  · intro st1 s1 hpc1 hrun1 _ ⟨hsp_1, hx21_1, hvregs_1, htrace_1⟩
    refine seq_evs_step (mid := (blkPl_376).base + 952#64)
      (P_mid := fun st2 sm =>
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 48#64)
          (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 48 ∗ (A.pool lim st2 sm ∗
            (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
              ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
      (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step M A lim ptsPtr 24#64 32#64 40#64 48#64 24 48 c1 s1 st1 hsp_1
    · intro st2 s2 hpc2 hrun2 _ ⟨hsp_2, hx21_2, hvregs_2, htrace_2⟩
      refine seq_evs_step (mid := (blkPl_376).base + 976#64)
        (P_mid := fun st3 sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 72#64)
            (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion ptsPtr 72 ∗ (A.pool lim st3 sm ∗
              (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
        (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step M A lim ptsPtr 48#64 56#64 64#64 72#64 48 72 c2 s2 st2 hsp_2
      · intro st3 s3 hpc3 hrun3 _ ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine seq_evs_step (mid := (blkPl_376).base + 996#64)
          (P_mid := fun st4 sm =>
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 96#64)
              (c4 :: c5 :: c6 :: c7 :: rest) ∗
              (memRegion ptsPtr 96 ∗ (A.pool lim st4 sm ∗
                (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                  ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
          (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step M A lim ptsPtr 72#64 80#64 88#64 96#64 72 96 c3 s3 st3 hsp_3
        · intro st4 s4 hpc4 hrun4 _ ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine seq_evs_step (mid := (blkPl_376).base + 1016#64)
            (P_mid := fun st5 sm =>
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 120#64)
                (c5 :: c6 :: c7 :: rest) ∗
                (memRegion ptsPtr 120 ∗ (A.pool lim st5 sm ∗
                  (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                    ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
            (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
              calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step M A lim ptsPtr 96#64 104#64 112#64 120#64 96 120 c4 s4 st4 hsp_4
          · intro st5 s5 hpc5 hrun5 _ ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine seq_evs_step (mid := (blkPl_376).base + 1036#64)
              (P_mid := fun st6 sm =>
                arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 144#64)
                  (c6 :: c7 :: rest) ∗
                  (memRegion ptsPtr 144 ∗ (A.pool lim st6 sm ∗
                    (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                      ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
              (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
                calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step M A lim ptsPtr 120#64 128#64 136#64 144#64 120 144 c5 s5 st5 hsp_5
            · intro st6 s6 hpc6 hrun6 _ ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine seq_evs_step (mid := (blkPl_376).base + 1056#64)
                (P_mid := fun st7 sm =>
                  arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 168#64)
                    (c7 :: rest) ∗
                    (memRegion ptsPtr 168 ∗ (A.pool lim st7 sm ∗
                      (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                        ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame)))))
                (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                  sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
                  calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
              · dealloc_u8_slot_step M A lim ptsPtr 144#64 152#64 160#64 168#64 144 168 c6 s6 st6 hsp_6
              · intro st7 s7 hpc7 hrun7 _ ⟨hsp_7, hx19_7, hx21_7, hvregs_7, htrace_7⟩
                unfold PostEvs
                dealloc_u8_slot_step M A lim ptsPtr 168#64 176#64 184#64 192#64 168 192 c7 s7 st7 hsp_7

theorem fromPb_success_dealloc_last8_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 c15 : List (BitVec 8))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 1236#64)
      s
      (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 192#64)
        (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 192 ∗ (A.pool lim st s ∗ (stackAt fsp allocHookStack ∗ Frame))))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion ptsPtr 384 ∗
          (A.pool lim (M.stepEvents evs st) sm ∗ (stackAt fsp allocHookStack ∗ Frame))) ∧
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, spqrRustDeallocSym] at hdealloc_fo
  dsimp only [Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc hx19 hx21 ⊢
  change SepWP _ _ s _ (PostEvs M st s
    (fun stf sm =>
      memRegion ptsPtr 384 ∗
        (A.pool lim stf sm ∗ (stackAt fsp allocHookStack ∗ Frame)))
    (fun sm =>
      sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace))
  refine seq_evs_step (mid := (blkPl_376).base + 1096#64)
    (P_mid := fun st1 sm =>
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 216#64)
        (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 216 ∗ (A.pool lim st1 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
    (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
      sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dealloc_u8_slot_step M A lim ptsPtr 192#64 200#64 208#64 216#64 192 216 c8 s st hsp
  · intro st1 s1 hpc1 hrun1 _ ⟨hsp_1, hx19_1, hx21_1, hvregs_1, htrace_1⟩
    refine seq_evs_step (mid := (blkPl_376).base + 1116#64)
      (P_mid := fun st2 sm =>
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 240#64)
          (c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
          (memRegion ptsPtr 240 ∗ (A.pool lim st2 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
      (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
        sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step M A lim ptsPtr 216#64 224#64 232#64 240#64 216 240 c9 s1 st1 hsp_1
    · intro st2 s2 hpc2 hrun2 _ ⟨hsp_2, hx19_2, hx21_2, hvregs_2, htrace_2⟩
      refine seq_evs_step (mid := (blkPl_376).base + 1136#64)
        (P_mid := fun st3 sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 264#64)
            (c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
            (memRegion ptsPtr 264 ∗ (A.pool lim st3 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
        (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step M A lim ptsPtr 240#64 248#64 256#64 264#64 240 264 c10 s2 st2 hsp_2
      · intro st3 s3 hpc3 hrun3 _ ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine seq_evs_step (mid := (blkPl_376).base + 1156#64)
          (P_mid := fun st4 sm =>
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 288#64)
              (c12 :: c13 :: c14 :: c15 :: []) ∗
              (memRegion ptsPtr 288 ∗ (A.pool lim st4 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
          (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step M A lim ptsPtr 264#64 272#64 280#64 288#64 264 288 c11 s3 st3 hsp_3
        · intro st4 s4 hpc4 hrun4 _ ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine seq_evs_step (mid := (blkPl_376).base + 1176#64)
            (P_mid := fun st5 sm =>
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 312#64)
                (c13 :: c14 :: c15 :: []) ∗
                (memRegion ptsPtr 312 ∗ (A.pool lim st5 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
            (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
              calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step M A lim ptsPtr 288#64 296#64 304#64 312#64 288 312 c12 s4 st4 hsp_4
          · intro st5 s5 hpc5 hrun5 _ ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine seq_evs_step (mid := (blkPl_376).base + 1196#64)
              (P_mid := fun st6 sm =>
                arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 336#64)
                  (c14 :: c15 :: []) ∗
                  (memRegion ptsPtr 336 ∗ (A.pool lim st6 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
              (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
                calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step M A lim ptsPtr 312#64 320#64 328#64 336#64 312 336 c13 s5 st5 hsp_5
            · intro st6 s6 hpc6 hrun6 _ ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine seq_evs_step (mid := (blkPl_376).base + 1216#64)
                (P_mid := fun st7 sm =>
                  arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 360#64)
                    (c15 :: []) ∗
                    (memRegion ptsPtr 360 ∗ (A.pool lim st7 sm ∗ (stackAt fsp allocHookStack ∗ Frame))))
                (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                  sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧
                  calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
              · dealloc_u8_slot_step M A lim ptsPtr 336#64 344#64 352#64 360#64 336 360 c14 s6 st6 hsp_6
              · intro st7 s7 hpc7 hrun7 _ ⟨hsp_7, hx19_7, hx21_7, hvregs_7, htrace_7⟩
                unfold PostEvs
                refine SepWP.mono
                  (show SepWP _ ((blkPl_376).base + 1236#64) s7 _
                    (fun sm Pm =>
                      ∃ evs, FreeOnlyEvs evs ∧
                      (Pm ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 384#64) [] ∗
                        (memRegion ptsPtr 384 ∗
                          (A.pool lim (M.stepEvents evs st7) sm ∗ (stackAt fsp allocHookStack ∗ Frame)))) ∧
                      AllocCallPreserved s7 sm ∧
                      sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
                      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) from by
                    dealloc_u8_slot_step M A lim ptsPtr 360#64 368#64 376#64 384#64 360 384 c15 s7 st7 hsp_7)
                  fun _ _ _ _ ⟨evs, hevs, hp, hacp, hq⟩ => ?_
                simp only [arrayAt_nil, emp_sepConj] at hp
                exact ⟨evs, hevs, hp, hacp, hq⟩

/-! ## Placed Success Exit (`+876 -> s0.lr`) -/

theorem fromPb_success_exit_876_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpyVmAcpSpec)
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pb : ProtoPolynomialDecoder) (hbss_len : pb.pts.length = 16)
    (outPts : List SortedSetPt) (hout_len : outPts.length = 16)
    (hle : pb.pts.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 876#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (sortedSetPtListOf A.repAlloc (fsp + 32#64) outPts ∗
        memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        ∃ evs, FreeOnlyEvs evs ∧
        (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          memRegion pbA 40 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        AllocCallPreserved s sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, spqrMemcpySym] at hmemcpy
  rw [sortedSetPtListOf_eq_vecPtListOf]
  have hvecs_len : (outPts.map SortedSetPt.vec).length = 16 := by simp [hout_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecPtListOf_entails_headers_heaps A.repAlloc (outPts.map SortedSetPt.vec) (fsp + 32#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply SepWP.pure_elim; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  conv => arg 4; rw [memRegion_400_split_ok out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b392
  apply ProofLib.SepWP.exists_left; intro d384
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hpts_eq⟩ :=
    list_length_16_elim hbss_len
  change SepWP _ _ s _ (PostEvs M st s
    (fun stf sf =>
      resultPolyDecoderFromPbAt A.repAlloc out
          (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
        memRegion pbA 40 ∗ A.pool lim stf sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame)
    (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
  refine seq_evs_step
    (mid := (blkPl_376).base + 904#64)
    (P_mid := fun st1 sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
      (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
        ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗
        (sortedSetPtListOf A.repAlloc out outPts ∗
          memRegion (out + 393#64) 7 ∗
          memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ Frame)))
    (Q_mid := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = BitVec.ofNat 64 pb.ptsNeeded.toNat ∧
      sm.readReg64 .x20 = (boolByte pb.isComplete).zeroExtend 64 ∧
      sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x22 = out ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hmemcpy hpc hx21 ⊢
    wp_steps
    rw [← hbs_len]
    wp_call hmemcpy (out, fsp + 32#64, vecHeadersBytesOf pins (outPts.map SortedSetPt.vec))
    have hacp_mc : AllocCallPreserved s sf := by assumption
    have hvm_mc : VmPreserved s sf := by
      simpa [VmPreserved, Heap.PoolPreserved, wp_norm, arm64_norm] using ‹VmPreserved _ sf›
    have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp])
    apply SepWP.done hpc_sf hrun_sf
    refine ⟨[], FreeOnlyEvs.nil, ?_, hacp_mc, ?_⟩
    · have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
      rw [← hsp_sf, hsp_sf', hst_nil, A.pool_of_vmPreserved hvm_mc, hbs_len, sortedSetPtListOf_eq_vecPtListOf]
      have hdst : (out ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ∗
          vecPtHeapList A.repAlloc pins (outPts.map SortedSetPt.vec) ⊢
          vecPtListOf A.repAlloc out (outPts.map SortedSetPt.vec) :=
        headers_heaps_entails_vecPtListOf A.repAlloc pins (outPts.map SortedSetPt.vec) out hpins_len
      have hsrc : ((fsp + 32#64) ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ⊢
          memRegion (fsp + 32#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion (fsp + 32#64) _
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      refine Entails.trans (replace_sub_entails hdst
        (((fsp + 32#64) ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (by sep_ac_rfl) (by sep_ac_rfl)) ?_
      refine Entails.trans (replace_sub_entails hsrc
        (vecPtListOf A.repAlloc out (outPts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (by sep_ac_rfl) (by sep_ac_rfl)) ?_
      exact replace_sub_entails hpb16
        (vecPtListOf A.repAlloc out (outPts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (by sep_ac_rfl) (by sep_ac_rfl)
    · rw [← u32_zeroExtend64_eq_ofNat_toNat pb.ptsNeeded]
      simp [wp_norm, arm64_norm, *]
  · intro st1 s1 hpc1 hrun1 _ ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hvregs1, htr1⟩
    have harr_eq : arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts =
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr
          [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] := by
      rw [hpts_eq]
    conv => arg 4; rw [harr_eq]
    let Frame1 : SepProp :=
      sortedSetPtListOf A.repAlloc out outPts ∗
        memRegion (out + 393#64) 7 ∗
        memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        memRegion (fsp + 32#64) 384 ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ Frame
    refine seq_evs_step
      (mid := (blkPl_376).base + 1076#64)
      (P_mid := fun st2 sm =>
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + 192#64)
          [c8, c9, c10, c11, c12, c13, c14, c15] ∗
          (memRegion ptsPtr 192 ∗ (A.pool lim st2 sm ∗
            (stackAt fsp allocHookStack ∗ (((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
              ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame1)))))
      (Q_mid := fun sm =>
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace)
      (fromPb_success_dealloc_first8_placed hdealloc s0 fsp out pbA ptsPtr d384
        (BitVec.ofNat 64 pb.ptsNeeded.toNat) b392 (boolByte pb.isComplete) hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] st1 s1 Frame1
        hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hvregs1 htr1) ?_
    intro st2 s2 hpc2 hrun2 _ ⟨hsp2, hx19_2, hx21_2, hvregs2, htr2⟩
    let Frame2 : SepProp :=
      ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
        ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
        ((fsp + 16#64) ↦₆₄ pbA) ∗ Frame1
    refine align_pre_wp
      (seq_evs_step
        (mid := (blkPl_376).base + 1236#64)
        (P_mid := fun st3 sm =>
          memRegion ptsPtr 384 ∗
            (A.pool lim st3 sm ∗ (stackAt fsp allocHookStack ∗ Frame2)))
        (Q_mid := fun sm =>
          sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace)
        (fromPb_success_dealloc_last8_placed hdealloc s0 fsp pbA ptsPtr hfsp_align
          c8 c9 c10 c11 c12 c13 c14 c15 st2 s2 Frame2
          hpc2 hrun2 hsp2 hx19_2 hx21_2 hvregs2 htr2) ?_)
      (by rfl)
    intro st3 s3 hpc3 hrun3 _ ⟨hsp3, hx19_3, hx21_3, hvregs3, htr3⟩
    dsimp only [Frame2, Frame1] at *
    have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
    have hrejoin_buf := memRegion_rejoin_vecBuf A.repAlloc 24 8 cap_pts ptsPtr pb.pts.length hle hcap_bound
    have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
    have hok_out :
        sortedSetPtListOf A.repAlloc out outPts ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (out + 393#64) 7 ⊢
        resultPolyDecoderFromPbAt A.repAlloc out
          (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) := by
      unfold resultPolyDecoderFromPbAt polyDecoderAt
      dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, polyDecoderPadSize]
      have hpure : outPts.length = NUM_POLYS ∧ pb.ptsNeeded.toNat < 2 ^ 64 :=
        ⟨by simp [hout_len, NUM_POLYS, CHUNK_SIZE], by omega⟩
      exact Entails.pure_right hpure (Entails.of_eq (by sep_ac_rfl))
    have hpre_1236 :
        memRegion ptsPtr 384 ∗
          (A.pool lim st3 s3 ∗ (stackAt fsp allocHookStack ∗
            (((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
              ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗
              (sortedSetPtListOf A.repAlloc out outPts ∗
                memRegion (out + 393#64) 7 ∗
                memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                memRegion (fsp + 32#64) 384 ∗
                ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
                memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
                (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
                memRegion (pbA + 24#64) 16 ∗
                (if cap_pts = 0 then emp
                  else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
                memRegion (fsp - 4128#64) 32 ∗ Frame)))) ⊢
        (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool lim st3 s3 ∗ stackAt fsp dropGluePoly16Stack ∗
          (resultPolyDecoderFromPbAt A.repAlloc out
              (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) := by
      have h384 : memRegion ptsPtr 384 = memRegion ptsPtr (pb.pts.length * 24) := by rw [hbss_len]
      rw [h384, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
      unfold vecVecU8BufDealloc
      refine Entails.trans (replace_sub_entails hrejoin_buf
        (A.pool lim st3 s3 ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32 ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          sortedSetPtListOf A.repAlloc out outPts ∗
          memRegion (out + 393#64) 7 ∗
          memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)) ?_
      refine Entails.trans (replace_sub_entails hfsp448
        ((if (cap_pts == 0#64) = true then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24)) ∗
          A.pool lim st3 s3 ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32 ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          sortedSetPtListOf A.repAlloc out outPts ∗
          memRegion (out + 393#64) 7 ∗
          savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)) ?_
      exact replace_sub_entails hok_out
        ((pbA ↦₆₄ cap_pts) ∗
          (if (cap_pts == 0#64) = true then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24)) ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool lim st3 s3 ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)
    have hpost_final : ∀ P_pool : SepProp,
        (pbA ↦₆₄ cap_pts) ∗ P_pool ∗ stackAt s0.sp fromPbCoreStack ∗
          (resultPolyDecoderFromPbAt A.repAlloc out
              (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
        resultPolyDecoderFromPbAt A.repAlloc out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          memRegion pbA 40 ∗ P_pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame := by
      intro P_pool
      exact replace_sub_entails hrejoin_pb
        (resultPolyDecoderFromPbAt A.repAlloc out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          P_pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)
    unfold PostEvs
    refine SepWP.weaken_pre hpre_1236 ?_
    refine SepWP.mono
      (fromPb_tail_1236_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
        st3 s3 _ hpc3 hrun3 hsp3 hx19_3 hx21_3 hvregs3 htr3)
      fun sf _Pf _ _ ⟨evs, hevs, hent, hspf, hacpf, hcsf, htrf⟩ => ?_
    exact ⟨evs, hevs, Entails.trans hent (hpost_final _), hacpf, ⟨hspf, hcsf, htrf⟩⟩

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
