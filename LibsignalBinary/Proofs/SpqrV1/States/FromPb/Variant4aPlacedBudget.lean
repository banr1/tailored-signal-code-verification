/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 4 (`EkSentCt1Received`) — Part A

Relocatable Block-`333` `+5348` error exit, `FreeOnlyEvs` decoder deallocation (`+5264..+5348`),
and `EkSentCt1Received` cleanup paths under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_add_one_beq_zero_false cap_mul_24 chunkedStatesSize cons_len_mul
   header_cells_entails_memRegion_24 ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24
   ofNat_succ_eq_add_one sep_pull_body sep_push_body sep_rejoin_loop
   tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v4_Saved5276Preserved v4_Saved8540Preserved)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
  (v4_ptsCap_add_one_ne_zero v4_sub_ok_dealloc_125316_fo_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

private theorem sepWP_with_evs {prog : Program} {target : BitVec 64} {s : State}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

/-! ## Shared `Err(err)` Exit at `+5348` (`+5348 -> +5944 -> +60 -> s0.x30`) -/

/-- `VmPreserved`-strengthened relocatable shared `Err(err)` exit at `+5348`
    (`+5348 -> +5944 -> +60 -> s0.x30`): when `x26` has low byte `spqrErrorByte err` and
    `x19 = out`, writes `x25, x22` to `[out + 16..32]`, branches to `+5944`, sets `x8 = noneCap`,
    writes `x26` to `[out + 8]`, and branches to `+60`. -/
theorem v4_states_from_pb_err_5348_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v4_states_from_pb_err_5348_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx26_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v4_states_from_pb_err_5348_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          Rest ∗ A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v4_states_from_pb_err_5348_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## Budget-Threaded `ProtoPolynomialDecoder` Deallocation Loop (`+5264..+5348`) -/

theorem v4_proto_decoder_dealloc_body_5300_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 5300#64 →
      s.status = .Running →
      v4_Saved5276Preserved s0 s fsp out ptsPtr ptsCap x26_val →
      s.readReg64 .x20 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5288#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
          sm.readReg64 .x20 = cnt ∧
          sm.readReg64 .x21 = cur + 8#64) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hx20 hx21
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 5300#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5288#64) s _ _
  rcases hpres with ⟨hsp, hx19, hx23, hx28, hx26, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro vptr
  have hpost24 (Pool : SepProp) :
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
        Pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
      memRegion cur 24 ∗ Pool ∗ stackAt fsp allocHookStack ∗ Frame :=
    sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 5288#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 _)
    · wp_done
  · apply sepWP_evs_dealloc cap.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (vptr, cap.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
    wp_steps_sync_333 ((blkPl_333).base + 5288#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      rw [hsp]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 _)
    · wp_done

theorem v4_proto_decoder_dealloc_loop_5300_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 5300#64 →
      s.status = .Running →
      v4_Saved5276Preserved s0 s fsp out ptsPtr ptsCap x26_val →
      s.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5324#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val) := by
  have hbody := v4_proto_decoder_dealloc_body_5300_placed
    hA s0 fsp out ptsPtr ptsCap x26_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx20 hx21
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 5288#64)
      (P_evs := fun evs1 sm =>
        memRegion cur 24 ∗ A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x21 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hx20 hx21) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx20_1, hx21_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx20_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx23_1, hx28_1, hx26_1, htrace_1⟩
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5288#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5324#64) s1 _ _
      apply sepWP_with_evs evs1 hevs1
      wp_steps_sync_333 ((blkPl_333).base + 5324#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx20_1
      refine seq_clean_st (mid := lsmpl.base 333 + 5300#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x21 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx23_1, hx28_1, hx26_1, htrace_1⟩
        rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 5288#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5300#64) s1 _ _
        rw [sep_push_body]
        wp_steps_sync_333 ((blkPl_333).base + 5300#64)
        simp only [State.setMem_setMem]
        rw [add_24_add_8]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx20_2, hx21_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx20_2 hx21_2
        refine SepWP.mono hrec fun sm _Pm _ _ ⟨evs2, hevs2, hp, hpres_f⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_f⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        refine Entails.trans hp ?_
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Budget-threaded shared `ProtoPolynomialDecoder` inline deallocation at `+5276 -> +5348`:
    when `x28 = ptsCap`, `x23 = ptsPtr`, `x20 = BitVec.ofNat 64 pts.length`, deallocates all
    `Vec<u8>` elements in `pts` and the `pts` buffer itself under `FreeOnlyEvs`, then falls through
    to `+5348`. -/
theorem v4_states_from_pb_dealloc_proto_decoder_5276_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5276#64)
    (hrun : s.status = .Running)
    (hpres : v4_Saved5276Preserved s0 s fsp out ptsPtr ptsCap x26_val)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  have hloop := v4_proto_decoder_dealloc_loop_5300_placed
    hA s0 fsp out ptsPtr ptsCap x26_val hfsp_align
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [BitVec.ofNat_eq_ofNat] at hdealloc_fo hloop hpc ⊢
  refine seq_clean_evs (mid := lsmpl.base 333 + 5324#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx23, hx28, hx26, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx20 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
      change s.pc = (blkPl_333).base + 5276#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5324#64) s _ _
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5324#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine seq_clean_st (mid := lsmpl.base 333 + 5300#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x21 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx23, hx28, hx26, htrace⟩
        rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
        change s.pc = (blkPl_333).base + 5276#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5300#64) s _ _
        wp_steps_sync_333 ((blkPl_333).base + 5300#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx20_loop, hx21_loop⟩
        have hsplit : ptsCap.toNat * 24 =
            (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion ptsPtr ((bs :: tl).length * 24) ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
            A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
          rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
            ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWP.mono
          (hloop (bs :: tl) ptsPtr st s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx20_loop hx21_loop)
          fun sm _Pm _ _ ⟨evs, hevs, hPm, hpres_m⟩ => ?_
        refine ⟨evs, hevs, Entails.trans hPm ?_, hpres_m⟩
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl))
          (sepConj_mono_left hjoin)
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp_3, hx19_3, hx23_3, hx28_3, hx26_3, htrace_3⟩
    rw [← ls_blockPlacement_base (i := 333)] at hpc3 ⊢
    change s3.pc = (blkPl_333).base + 5324#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5348#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx28_3 ⊢
      apply sepWP_with_evs evs1 hevs1
      wp_steps_sync_333 ((blkPl_333).base + 5348#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      apply sepWP_with_evs (evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8)
        (hevs1.append (FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)))
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ptsPtr, ptsCap.toNat * 24, 8, M.stepEvents evs1 st)
      have hacp : AllocCallPreserved s3 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace_3.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htrace_3.2
      wp_steps_sync_333 ((blkPl_333).base + 5348#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp_3]) ?_
      wp_done

/-- `VmPreserved`-strengthened relocatable `Option<ProtoPolynomialDecoder>::None` inline
    deallocation at `+5264 -> +5348`: when `x28 = noneCap`, `cmn x28, #1; mov x23, x24; b.eq +5348`
    jumps directly to `+5348`. -/
theorem v4_states_from_pb_dealloc_none_proto_decoder_5264_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x26_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = noneCap)
    (hx26 : s.readReg64 .x26 = x26_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s sm ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr noneCap x26_val) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v4_states_from_pb_dealloc_none_proto_decoder_5264_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr x26_val P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx24) (by simpa using hx28) (by simpa using hx26)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx23_m, hx28_m, hx26_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx23_m,
       by simpa using hx28_m, by simpa using hx26_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v4_states_from_pb_dealloc_none_proto_decoder_5264_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x26_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = noneCap)
    (hx26 : s.readReg64 .x26 = x26_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s (P ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr noneCap x26_val) := by
  have hwp := v4_states_from_pb_dealloc_none_proto_decoder_5264_placed (ext := ext)
    s0 s fsp out ptsPtr x26_val (P ∗ A.pool lim st s) hpc hrun hsp hx19 hx24 hx28 hx26 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hpres_m⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hpres_m⟩

/-- Budget-threaded relocatable `Option<ProtoPolynomialDecoder>::Some` inline deallocation
    at `+5264 -> +5348`: when `x28 = ptsCap` with `ptsCap.toNat * 24 < 2^63`, falls through
    to `+5276` and deallocates `pts` under `FreeOnlyEvs`. -/
theorem v4_states_from_pb_dealloc_some_proto_decoder_5264_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (hx26 : s.readReg64 .x26 = x26_val)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val) := by
  have h5276 := v4_states_from_pb_dealloc_proto_decoder_5276_placed hA s0
  refine seq_clean_st (mid := lsmpl.base 333 + 5276#64)
    (P_mid := fun sm =>
      (if ptsCap = 0 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) ∗
      A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
    rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 5264#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5276#64) s _ _
    wp_steps_sync_333 ((blkPl_333).base + 5276#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx20_1⟩
    exact h5276 s1 fsp out ptsPtr ptsCap x26_val pts st Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx20_1

/-! ## Budget-Threaded `EkSentCt1Received` Cleanup Paths (`+8540`, `+8500`, `+6860`, `+304`, `+388`) -/

/-- Shared cleanup at `+8540 -> +5348`: drops `dk` (`cap = x22`, `ptr = [fsp + 144]`) and
    `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`) under `FreeOnlyEvs`, sets `x26 = 0#64`,
    and branches to `+5348`. -/
theorem v4_states_from_pb_drop_uc_8540_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8540#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved8540Preserved s0 sm fsp out) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs (mid := lsmpl.base 333 + 8560#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 144#64) ↦₆₄ dkPtr) ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 8540#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8560#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    by_cases hdk : (dkCap == 0#64) = true
    · simp only [hdk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 8560#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hdk_f : (dkCap == 0#64) = false := Bool.eq_false_iff.mpr hdk
      simp only [hdk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc dkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (dkPtr, dkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      have hsp_f : sf.sp = fsp := (‹sf.sp = s.sp›).trans hsp
      have hx19_f : sf.readReg64 .x19 = out :=
        (‹sf.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5)›).trans hx19
      exact SepWP.done (by assumption) (by assumption)
        ⟨Entails.of_eq (by rw [hsp]; sep_ac_rfl), hsp_f, hx19_f, htr_sf, hvregs_sf⟩
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx19_1, htrace1⟩
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 8560#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5348#64) s1 _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    by_cases hct1 : (ct1Cap == 0#64) = true
    · simp only [hct1, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_with_evs evs1 hevs1
      wp_steps_sync_333 ((blkPl_333).base + 5348#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hct1_f : (ct1Cap == 0#64) = false := Bool.eq_false_iff.mpr hct1
      simp only [hct1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_with_evs (evs1 ++ rustDeallocEvents ct1Cap.toNat 1)
        (hevs1.append (FreeOnlyEvs.singleton 1 ct1Cap.toNat))
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ct1Ptr, ct1Cap.toNat, 1, M.stepEvents evs1 st)
      have hacp : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
      wp_steps_sync_333 ((blkPl_333).base + 5348#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp1]; sep_ac_rfl) ?_
      wp_done

/-- Cleanup at `+8500 -> +5348`: drops `rootKey` (`cap = [fsp + 56]`, `ptr = x26`),
    `macKey` (`cap = [fsp + 216]`, `ptr = [fsp + 136]`), `dk` (`cap = x22`, `ptr = [fsp + 144]`),
    and `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`) under `FreeOnlyEvs`, sets `x26 = 0#64`,
    and branches to `+5348`. -/
theorem v4_states_from_pb_drop_uc_8500_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s
      (((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved8540Preserved s0 sm fsp out) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have h8540 := v4_states_from_pb_drop_uc_8540_placed hA s0
  refine seq_clean_evs (mid := lsmpl.base 333 + 8520#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 136#64) ↦₆₄ mkPtr) ∗
      ((fsp + 144#64) ↦₆₄ dkPtr) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗
      vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
      vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 8500#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8520#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 8520#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc rkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (rkPtr, rkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      have hsp_f : sf.sp = fsp := (‹sf.sp = s.sp›).trans hsp
      have hx19_f : sf.readReg64 .x19 = out :=
        (‹sf.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5)›).trans hx19
      have hx22_f : sf.readReg64 .x22 = dkCap :=
        (‹sf.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5)›).trans hx22
      exact SepWP.done (by assumption) (by assumption)
        ⟨Entails.of_eq (by rw [hsp]; sep_ac_rfl), hsp_f, hx19_f, hx22_f, htr_sf, hvregs_sf⟩
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, htrace1⟩
    refine seq_clean_evs (mid := lsmpl.base 333 + 8540#64)
      (P_evs := fun evs2 sm =>
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗
        stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 8520#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8540#64) s1 _ _
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 8540#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc mkCap.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (mkPtr, mkCap.toNat, 1, M.stepEvents evs1 st)
        have hacp : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
        have hsp_f : sf.sp = fsp := (‹sf.sp = s1.sp›).trans hsp1
        have hx19_f : sf.readReg64 .x19 = out :=
          (‹sf.readReg64 (Reg.gpr 19#5) = s1.readReg64 (Reg.gpr 19#5)›).trans hx19_1
        have hx22_f : sf.readReg64 .x22 = dkCap :=
          (‹sf.readReg64 (Reg.gpr 22#5) = s1.readReg64 (Reg.gpr 22#5)›).trans hx22_1
        exact SepWP.done (by assumption) (by assumption)
          ⟨Entails.of_eq (by rw [hsp1]; sep_ac_rfl), hsp_f, hx19_f, hx22_f, htr_sf, hvregs_sf⟩
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htrace2⟩
      have hcall := h8540 s2 fsp out dkPtr dkCap ct1Ptr ct1Cap
        (M.stepEvents evs2 (M.stepEvents evs1 st))
        (((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗ Frame)
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htrace2
      refine SepWP.weaken_pre ?_
        (SepWP.mono hcall fun sm _Pm _ _ ⟨evs3, hevs3, hPm, hpres⟩ => ?_)
      · exact Entails.of_eq (by sep_ac_rfl)
      · refine ⟨(evs1 ++ evs2) ++ evs3, (hevs1.append hevs2).append hevs3, ?_, hpres⟩
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hPm ⊢
        exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

/-- Cleanup at `+6860 -> +5348`: drops `rootKey` (`cap = x9`, `ptr = x26`),
    `macKey` (`cap = x1`, `ptr = x0`), `dk` (`cap = x22`, `ptr = [fsp + 144]`),
    and `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`) under `FreeOnlyEvs`, sets `x26 = 0#64`,
    and branches to `+5348`. -/
theorem v4_states_from_pb_drop_uc_6860_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6860#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr)
    (hx1 : s.readReg64 .x1 = mkCap)
    (hx9 : s.readReg64 .x9 = rkCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5348#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved8540Preserved s0 sm fsp out) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have h8540 := v4_states_from_pb_drop_uc_8540_placed hA s0
  refine seq_clean_evs (mid := lsmpl.base 333 + 6896#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 144#64) ↦₆₄ dkPtr) ∗
      vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
      vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = mkPtr ∧ sm.readReg64 .x1 = mkCap ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 6860#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6896#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 6896#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc rkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (rkPtr, rkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      wp_steps_sync_333 ((blkPl_333).base + 6896#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx22_1, htrace1⟩
    refine seq_clean_evs (mid := lsmpl.base 333 + 8540#64)
      (P_evs := fun evs2 sm =>
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗
        stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 6896#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8540#64) s1 _ _
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 8540#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc mkCap.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (mkPtr, mkCap.toNat, 1, M.stepEvents evs1 st)
        have hacp : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
        have hsp_f : sf.sp = fsp := (‹sf.sp = s1.sp›).trans hsp1
        have hx19_f : sf.readReg64 .x19 = out :=
          (‹sf.readReg64 (Reg.gpr 19#5) = s1.readReg64 (Reg.gpr 19#5)›).trans hx19_1
        have hx22_f : sf.readReg64 .x22 = dkCap :=
          (‹sf.readReg64 (Reg.gpr 22#5) = s1.readReg64 (Reg.gpr 22#5)›).trans hx22_1
        exact SepWP.done (by assumption) (by assumption)
          ⟨Entails.of_eq (by rw [hsp1]; sep_ac_rfl), hsp_f, hx19_f, hx22_f, htr_sf, hvregs_sf⟩
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htrace2⟩
      have hcall := h8540 s2 fsp out dkPtr dkCap ct1Ptr ct1Cap
        (M.stepEvents evs2 (M.stepEvents evs1 st)) Frame
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htrace2
      refine SepWP.mono hcall fun sm _Pm _ _ ⟨evs3, hevs3, hPm, hpres⟩ => ?_
      refine ⟨(evs1 ++ evs2) ++ evs3, (hevs1.append hevs2).append hevs3, ?_, hpres⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hPm ⊢
      exact hPm

/-- `VmPreserved`-strengthened early error path `+304 -> +4380 -> +5276` when
    `receivingCt2 = some d` (`d.ptsNeeded ≠ 80#32`) and `uc = none` (`x22 = noneCap`).
    Sets `x26 = 2#64` (`spqrErrorByte .msgDecode`) and `x23 = ptsPtr`. -/
theorem v4_states_from_pb_drop_proto_uc_none_304_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x20_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s sm ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v4_states_from_pb_drop_proto_uc_none_304_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap x20_val P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx22)
      (by simpa using hx24) (by simpa using hx28)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, ⟨hsp_m, hx19_m, hx23_m, hx28_m, hx26_m, htr_m⟩, hx20_m⟩ =>
      ⟨hPm, hvm,
       ⟨by simpa using hsp_m, by simpa using hx19_m, by simpa using hx23_m,
        by simpa using hx28_m, by simpa using hx26_m,
        ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩,
       by simpa using hx20_m⟩

theorem v4_states_from_pb_drop_proto_uc_none_304_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x20_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s (P ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have hwp := v4_states_from_pb_drop_proto_uc_none_304_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap x20_val (P ∗ A.pool lim st s)
    hpc hrun hsp hx19 hx20 hx22 hx24 hx28 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Early error path `+388 -> +5276`: drops `dk` (`x22 = dkCap`, `x11 = dkPtr`) and
    `ct1` (`x21 = ct1Cap`, `x12 = ct1Ptr`) under `FreeOnlyEvs`, sets `x26 = 2#64`,
    and branches to `+5276`. -/
theorem v4_states_from_pb_drop_proto_uc_388_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State)
    (fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 388#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx11 : s.readReg64 .x11 = dkPtr)
    (hx12 : s.readReg64 .x12 = ct1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = ct1Cap)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx23 : s.readReg64 .x23 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s
      (vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs (mid := lsmpl.base 333 + 416#64)
    (P_evs := fun evs1 sm =>
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x12 = ct1Ptr ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = x20_val ∧
      sm.readReg64 .x21 = ct1Cap ∧ sm.readReg64 .x23 = ptsPtr ∧
      sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 388#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 416#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    by_cases hdk : (dkCap == 0#64) = true
    · simp only [hdk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 416#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hdk_f : (dkCap == 0#64) = false := Bool.eq_false_iff.mpr hdk
      simp only [hdk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc dkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (dkPtr, dkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      wp_steps_sync_333 ((blkPl_333).base + 416#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx12_1, hx19_1, hx20_1, hx21_1, hx23_1, hx28_1, htrace1⟩
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 416#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5276#64) s1 _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    by_cases hct1 : (ct1Cap == 0#64) = true
    · simp only [hct1, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_with_evs evs1 hevs1
      wp_steps_sync_333 ((blkPl_333).base + 5276#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hct1_f : (ct1Cap == 0#64) = false := Bool.eq_false_iff.mpr hct1
      simp only [hct1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_with_evs (evs1 ++ rustDeallocEvents ct1Cap.toNat 1)
        (hevs1.append (FreeOnlyEvs.singleton 1 ct1Cap.toNat))
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ct1Ptr, ct1Cap.toNat, 1, M.stepEvents evs1 st)
      have hacp : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
      wp_steps_sync_333 ((blkPl_333).base + 5276#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp1]) ?_
      wp_done

/-- Early error path `+304 -> +388 -> +5276` when `uc = some u` (`dkCap.toNat < 2^63`)
    and `u.auth = none` (`x1 = noneCap`), under `FreeOnlyEvs`. -/
theorem v4_states_from_pb_drop_proto_uc_none_auth_304_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State)
    (fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdk_lt : dkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = noneCap)
    (hx11 : s.readReg64 .x11 = dkPtr)
    (hx12 : s.readReg64 .x12 = ct1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = ct1Cap)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s
      (vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have h388 := v4_states_from_pb_drop_proto_uc_388_placed hA s0
  have hdk_ne := cap_add_one_beq_zero_false hdk_lt
  change s.readReg64 .x1 = 0xffffffffffffffff#64 at hx1
  refine seq_clean_st (mid := lsmpl.base 333 + 388#64)
    (P_mid := fun sm =>
      vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x11 = dkPtr ∧
      sm.readReg64 .x12 = ct1Ptr ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x21 = ct1Cap ∧
      sm.readReg64 .x22 = dkCap ∧ sm.readReg64 .x23 = ptsPtr ∧
      sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 304#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 388#64) s _ _
    wp_steps_sync_333 ((blkPl_333).base + 388#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx28_1, htrace1⟩
    exact h388 s1 fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap st Frame
      hfsp_align hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx28_1 htrace1

/-- Early error path `+304 -> +388 -> +5276` when `uc = some u` (`dkCap.toNat < 2^63`)
    and `u.auth = some auth` (`rkCap.toNat < 2^63`), under `FreeOnlyEvs`. -/
theorem v4_states_from_pb_drop_proto_uc_some_auth_304_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State)
    (fsp out ptsPtr ptsCap x20_val rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdk_lt : dkCap.toNat < 2 ^ 63)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = rkPtr)
    (hx1 : s.readReg64 .x1 = rkCap)
    (hx11 : s.readReg64 .x11 = dkPtr)
    (hx12 : s.readReg64 .x12 = ct1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = ct1Cap)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx25 : s.readReg64 .x25 = mkPtr)
    (hx26 : s.readReg64 .x26 = mkCap)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s
      (vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have h388 := v4_states_from_pb_drop_proto_uc_388_placed hA s0
  have hdk_ne := cap_add_one_beq_zero_false hdk_lt
  have hrk_ne := cap_add_one_beq_zero_false hrk_lt
  refine seq_clean_evs (mid := lsmpl.base 333 + 352#64)
    (P_evs := fun evs1 sm =>
      vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
      vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x11 = dkPtr ∧
      sm.readReg64 .x12 = ct1Ptr ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x21 = ct1Cap ∧
      sm.readReg64 .x22 = dkCap ∧ sm.readReg64 .x23 = ptsPtr ∧
      sm.readReg64 .x25 = mkPtr ∧ sm.readReg64 .x26 = mkCap ∧
      sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 304#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 352#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 352#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc rkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (rkPtr, rkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      wp_steps_sync_333 ((blkPl_333).base + 352#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx28_1, htrace1⟩
    refine seq_clean_evs (mid := lsmpl.base 333 + 388#64)
      (P_evs := fun evs2 sm =>
        vecCapPtrDealloc A.repAlloc dkCap dkPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗
        stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x11 = dkPtr ∧
        sm.readReg64 .x12 = ct1Ptr ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x21 = ct1Cap ∧
        sm.readReg64 .x22 = dkCap ∧ sm.readReg64 .x23 = ptsPtr ∧
        sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 352#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 388#64) s1 _ _
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 388#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc mkCap.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (mkPtr, mkCap.toNat, 1, M.stepEvents evs1 st)
        have hacp : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
        wp_steps_sync_333 ((blkPl_333).base + 388#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by rw [hsp1]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx11_2, hx12_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx28_2, htrace2⟩
      have hcall := h388 s2 fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap
        (M.stepEvents evs2 (M.stepEvents evs1 st)) Frame
        hfsp_align hpc2 hrun2 hsp2 hx11_2 hx12_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx28_2 htrace2
      refine SepWP.mono hcall fun sm _Pm _ _ ⟨evs3, hevs3, hPm, hpres⟩ => ?_
      refine ⟨(evs1 ++ evs2) ++ evs3, (hevs1.append hevs2).append hevs3, ?_, hpres⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hPm ⊢
      exact hPm

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4aPlacedBudget
