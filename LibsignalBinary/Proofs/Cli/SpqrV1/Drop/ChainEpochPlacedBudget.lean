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
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[ChainEpoch]` Drop Glue (Block `446`)

Proves `drop_chain_epoch_slice_local1_placed_ok` (plus `HookSat` and `withPanics` wrappers) for
`core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]` on Block `446` (`lsProg_446 H`) under
`RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.Cli.SpqrV1.Drop.Placed (blkPC_446 blkPl_446 lsProg_446)
open CryptoVerification.LibsignalSpqrV1 (ChainEpoch)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.ChainProofs (chainEpoch chainEpochSize)
open CryptoVerification.SpqrV1.Drop (DropChainEpochSliceGhost Saved32x20Preserved add_112_add_56 chainEpochHeadersAt chainEpochHeadersAt_entails_memRegion_112 chainEpoch_entails_dealloc cons_len_mul dropStack32 ofNat_add_one_beq_one_false_112 ofNat_beq_zero_false_112 ofNat_succ_eq_add_one sep_pull_body sep_push_body sep_rejoin_loop stackAt_dropStack32_split stack_restore_32_allocHook tail_len_mul_lt vecCapPtrDealloc)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Heap (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem drop_chain_epoch_slice_local1_cli_placed_body [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpoch) (st : M.σ)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_446).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      AllocCallPreserved s0 s →
      s.readReg64 .x19 = cnt →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_446).rebase (blkPl_446).base H)
        ((blkPl_446).base + 28#64)
        s
        (chainEpoch A.repAlloc ep cur ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧
          AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = cnt ∧
          sm.readReg64 .x20 = cur + 56#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt ep st s Frame hpc hrun hpres hacp hx19 hx20
  rcases hpres with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine SepWP.weaken_pre (sepConj_mono_left (chainEpoch_entails_dealloc A.repAlloc cur ep)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro g
  refine seq_clean_evs (mid := (blkPl_446).base + 60#64) (P_evs := fun evs sm =>
    (chainEpochHeadersAt cur g ∗
      vecCapPtrDealloc A.repAlloc g.send.prev.cap g.send.prev.ptr ∗
      vecCapPtrDealloc A.repAlloc g.recv.next.cap g.recv.next.ptr ∗
      vecCapPtrDealloc A.repAlloc g.recv.prev.cap g.recv.prev.ptr) ∗
    A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
    ?_ ?_
  · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (g.send.next.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
    · apply sepWP_evs_dealloc g.send.next.cap.toNat 1
      wp_steps; wp_apply; rw [hsp]
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_clean_evs (mid := (blkPl_446).base + 80#64) (P_evs := fun evs sm =>
      (chainEpochHeadersAt cur g ∗
        vecCapPtrDealloc A.repAlloc g.recv.next.cap g.recv.next.ptr ∗
        vecCapPtrDealloc A.repAlloc g.recv.prev.cap g.recv.prev.ptr) ∗
      A.pool lim (M.stepEvents evs (M.stepEvents evs1 st)) sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
      ?_ ?_
    · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hcap : (g.send.prev.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.send.prev.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2, hx20_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_clean_evs (mid := (blkPl_446).base + 100#64) (P_evs := fun evs sm =>
        (chainEpochHeadersAt cur g ∗
          vecCapPtrDealloc A.repAlloc g.recv.prev.cap g.recv.prev.ptr) ∗
        A.pool lim (M.stepEvents evs (M.stepEvents evs2 (M.stepEvents evs1 st))) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
        ?_ ?_
      · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hcap : (g.recv.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc g.recv.next.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3, hx20_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        let st3 := M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))
        have hstep4 : SepWP ((blkPC_446).rebase (blkPl_446).base H) ((blkPl_446).base + 28#64) s3
            ((chainEpochHeadersAt cur g ∗ vecCapPtrDealloc A.repAlloc g.recv.prev.cap g.recv.prev.ptr) ∗
              A.pool lim st3 s3 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              ∃ evs4, FreeOnlyEvs evs4 ∧
              (Pm ⊢ chainEpochHeadersAt cur g ∗ A.pool lim (M.stepEvents evs4 st3) sm ∗
                stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧
              AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = cnt ∧
              sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [chainEpochHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hcap : (g.recv.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc g.recv.prev.cap.toNat 1
            wp_steps; wp_apply; wp_steps; rw [hsp_3]
            have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            wp_done
        refine SepWP.mono hstep4 (fun sm Pm _ _ ⟨evs4, hevs4, hp, hq⟩ => ?_)
        refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4,
          ((hevs1.append hevs2).append hevs3).append hevs4, ?_, hq⟩
        have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st = M.stepEvents evs4 st3 := by
          simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        exact Entails.trans hp (sepConj_mono_left (chainEpochHeadersAt_entails_memRegion_112 cur g))

private theorem drop_chain_epoch_slice_local1_cli_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpoch) (cur : BitVec 64) (st : M.σ)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_446).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      AllocCallPreserved s0 s →
      s.readReg64 .x19 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_446).rebase (blkPl_446).base H)
        ((blkPl_446).base + 124#64)
        s
        (arrayAt (chainEpoch A.repAlloc) 112 cur rest ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧
          AllocCallPreserved s0 sm) := by
  have hbody := drop_chain_epoch_slice_local1_cli_placed_body hdealloc s0 fsp hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20
    rw [show arrayAt (chainEpoch A.repAlloc) 112 cur (ep :: tl) =
          chainEpoch A.repAlloc ep cur ∗ arrayAt (chainEpoch A.repAlloc) 112 (cur + 112#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_446).base + 28#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep st s
        (arrayAt (chainEpoch A.repAlloc) 112 (cur + 112#64) tl ∗ Frame)
        hpc hrun hpres hacp hx19 hx20) ?_
    intro evs_hd s4 hevs_hd hpc4 hrun4 ⟨⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4, hx20_4⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_4
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx19_4 ⊢
      have hfin : SepWP ((blkPC_446).rebase (blkPl_446).base H) ((blkPl_446).base + 124#64) s4
          (memRegion cur 112 ∗ A.pool lim (M.stepEvents evs_hd st) s4 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧
            AllocCallPreserved s0 sm) := by
        wp_steps
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    | cons ep2 tl2 =>
      have htl_ne : ep2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show (ep :: ep2 :: tl2).length = (ep2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx19_4
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) htl_len
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_446).base + 40#64)
        (P_mid := arrayAt (chainEpoch A.repAlloc) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s4 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun s5 => Saved32x20Preserved s0 s5 fsp ∧ AllocCallPreserved s0 s5 ∧
          s5.readReg64 .x19 = BitVec.ofNat 64 (ep2 :: tl2).length ∧
          s5.readReg64 .x20 = cur + 168#64)
        ?_ ?_
      · wp_steps_vm
      · intro s5 hpc5 hrun5 hvm5 ⟨hpres5, hacp5, hx19_5, hx20_5⟩
        rw [← A.pool_of_vmPreserved hvm5]
        refine SepWP.mono
          (ih (cur + 112#64) (M.stepEvents evs_hd st) s5 (memRegion cur 112 ∗ Frame)
            htl_ne htl_len hpc5 hrun5 hpres5 hacp5 hx19_5
            (by simp only [hx20_5, add_112_add_56, wp_norm, arm64_norm])) ?_
        intro sf Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _

private theorem sepWP_close_drop {prog : Program} {s0 s : State} {P : SepProp}
    {Post : State → SepProp → Prop}
    (Q_out : State → SepProp)
    (h : SepWP prog (s0.readReg64 .lr) s P (fun sf Pf =>
      (Pf ⊢ Q_out sf) ∧
      sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
      AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      AllocCallPreserved s0 sf → CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP prog (s0.readReg64 .lr) s P Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    hpost sf Pf hp hsp_f htr_f hacp_f hcs_f

/-- Relocatable `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]` (Block `446`)
meets `dropChainEpochSliceSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_chain_epoch_slice_local1_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (blkPl_446).base (dropChainEpochSliceSpec M A lim) := by
  simp only [dropChainEpochSliceSpec]
  have hloop := drop_chain_epoch_slice_local1_cli_placed_loop hdealloc
  dsimp only [chainEpochSize, BitVec.ofNat_eq_ofNat] at hloop ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨ptr, eps⟩, st⟩
  have hx0 : s0.readReg64 .x0 = ptr := h_1
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 eps.length := h_2
  have hlen_lt : eps.length * 112 < 2 ^ 63 := h
  dsimp only [CryptoVerification.SpqrV1.Drop.DropChainEpochSliceGhost.ptr, CryptoVerification.SpqrV1.Drop.DropChainEpochSliceGhost.eps] at *
  cases eps with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj] at hx1 ⊢
    refine sepWP_close_drop (fun sf => A.pool lim st sf ∗ stackAt s0.sp dropStack32) ?_
      (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
    · wp_steps
      wp_done
    · rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨[], ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
  | cons ep tl =>
    have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 32#64 (by assumption) (by decide)
    have hne0 := ofNat_beq_zero_false_112 (n := (ep :: tl).length) (by simp) hlen_lt
    nth_rw 1 [stackAt_dropStack32_split s0.sp]
    cells_unfold
    wp_pull_exists
    refine seq_vm_clean (mid := (blkPl_446).base + 40#64)
      (P_mid := arrayAt (chainEpoch A.repAlloc) 112 ptr (ep :: tl) ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun s_entry => Saved32x20Preserved s0 s_entry (s0.sp - 32#64) ∧
        AllocCallPreserved s0 s_entry ∧
        s_entry.readReg64 .x19 = BitVec.ofNat 64 (ep :: tl).length ∧
        s_entry.readReg64 .x20 = ptr + 56#64)
      ?_ ?_
    · wp_steps_vm
    · intro s_entry hpc_e hrun_e hvm_e ⟨hpres_e, hacp_e, hx19_e, hx20_e⟩
      rw [← A.pool_of_vmPreserved hvm_e]
      refine seq_clean_evs (mid := (blkPl_446).base + 124#64)
        (P_evs := fun evs sm =>
          memRegion ptr ((ep :: tl).length * 112) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm)
        ?_ ?_
      · exact hloop s0 (s0.sp - 32#64) hfsp_align (ep :: tl) ptr st s_entry _
          (List.cons_ne_nil _ _) hlen_lt hpc_e hrun_e hpres_e hacp_e hx19_e hx20_e
      · intro evs sm hevs hpcm hrunm ⟨⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacp_m⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_m
        refine sepWP_close_drop
          (fun sf => memRegion ptr ((ep :: tl).length * 112) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack32) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · wp_steps
          refine SepWP.weaken_pre
            (sepConj_mono_right (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
          wp_done
        · rw [satisfies_sepExists]; refine ⟨evs, ?_⟩
          rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, hevs⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_chain_epoch_slice_local1_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_446 H) (blkPl_446).base (dropChainEpochSliceSpec M A lim) :=
  drop_chain_epoch_slice_local1_placed_ok
    (CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

private theorem hookSat_dealloc_withPanics [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem drop_chain_epoch_slice_local1_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_446 (Rust.withPanics ext)) (blkPl_446).base
      (dropChainEpochSliceSpec M A lim) :=
  drop_chain_epoch_slice_local1_placed (hookSat_dealloc_withPanics hdealloc)

theorem drop_chain_epoch_slice_local1_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 446)
      (CryptoVerification.withLsCodeLoaded CryptoVerification.lsmpl
        (dropChainEpochSliceSpec M A lim)) :=
  CryptoVerification.ls_subroutine_ok_of_block (callerProg := callerProg)
    (CryptoVerification.subroutine_ok_withLsCodeLoaded_of_plain
      (drop_chain_epoch_slice_local1_placed hdealloc)) hi

theorem drop_chain_epoch_slice_local1_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 446)
      (CryptoVerification.withLsCl CryptoVerification.lsmpl
        (dropChainEpochSliceSpec M A lim)) :=
  CryptoVerification.ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (drop_chain_epoch_slice_local1_placed hdealloc) hi

end LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
