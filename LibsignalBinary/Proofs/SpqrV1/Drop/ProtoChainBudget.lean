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
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.SpqrV1.Drop.DecodesBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Drop Glue for `proto::pq_ratchet::chain::Epoch`, `Chain`, and `Option<Chain>`

Defines budget-threaded specifications (`dropProtoEpochSliceSpec`, `dropProtoSpqrChainSpec`,
`dropOptProtoSpqrChainSpec`) under `RustCliAllocBudget M` (`FreeOnlyEvs`), and proves relocatable
`[LibsignalPlacement]` contracts for Blocks `288`, `136`, and `266`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (
  LibsignalPlacement blkPC_136 blkPC_266 blkPl_136 blkPl_266 lsmpl lsρ
)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB ChainPB EpochDirectionPB)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoSpqrChainGhost DropProtoEpochSliceGhost DropProtoSpqrChainGhost
  Saved32x20Preserved Saved48Preserved add_112_add_56 cap_add_one_beq_zero_false
  cap_lsl7_sub_lsl4 chainEpochPB_regions_entails_112 chainPBAt_entails_dealloc
  chainPBHeaders_entails_memRegion_80 cons_len_mul dropStack32 dropStack48 dropStack80
  epochDirPBHeadersAt epochDirPBHeadersAt_entails_memRegion_56
  epochDirectionPBAt_entails_dealloc ofNat_add_one_beq_one_false_112
  ofNat_beq_zero_false_112 ofNat_succ_eq_add_one optChainPBAt_none_entails_memRegion_80
  optEpochDirectionPBAt_none_entails_memRegion_56 sep_pull_body sep_push_body
  sep_rejoin_loop stackAt_dropStack32_split stackAt_dropStack32_split_bottom
  stackAt_dropStack48_split stackAt_dropStack48_split_bottom stackAt_dropStack80_split
  stackAt_dropStack80_split_bottom stack_restore_32_allocHook stack_restore_48_allocHook
  stack_restore_48_dropStack80 tail_len_mul_lt vecCapPtrDealloc
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop.Blk337_338 (blkPC_288 blkPl_288)
open CryptoVerification.SpqrV1.ProtoRepr (
  chainEpochPBAt chainEpochPBSize chainPBAt chainPBSize epochDirectionPBAt
  optChainPBAt optEpochDirectionPBAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget-Threaded Specifications -/

def dropProtoEpochSliceSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropProtoEpochSliceGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ptr ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.eps.length ∧
      x.eps.length * chainEpochPBSize < 2 ^ 63⌝ ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) chainEpochPBSize x.ptr x.eps ∗
      A.pool lim st s ∗ stackAt s.sp dropStack32
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ptr (x.eps.length * chainEpochPBSize) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack32

def dropProtoSpqrChainSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropProtoSpqrChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      chainPBAt A.repAlloc x.a x.ch ∗
      A.pool lim st s ∗ stackAt s.sp dropStack48
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a chainPBSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack48

def dropOptProtoSpqrChainSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropOptProtoSpqrChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      optChainPBAt A.repAlloc x.a x.optCh ∗
      A.pool lim st s ∗ stackAt s.sp dropStack80
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a chainPBSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack80

/-! ## Sequencing Helpers -/

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

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P = P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) := by
  subst h; exact hwp

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

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

@[local simp]
private theorem optEpochDirectionPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48) := rfl

@[local simp]
private theorem optEpochDirectionPBAt_some (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

@[local simp]
private theorem optChainPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optChainPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72) := rfl

@[local simp]
private theorem optChainPBAt_some (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    optChainPBAt A a (some ch) = chainPBAt A a ch := rfl

/-! ## Block `288`: `drop_glue::<[proto::chain::Epoch]>` -/

private theorem drop_proto_epoch_slice_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB) (st : M.σ)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_288).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      AllocCallPreserved s0 s →
      s.readReg64 .x19 = cnt →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_288).rebase (blkPl_288).base H)
        ((blkPl_288).base + 28#64)
        s
        (chainEpochPBAt A.repAlloc cur ep ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
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
  unfold chainEpochPBAt
  refine seq_clean_evs (mid := (blkPl_288).base + 88#64) (P_evs := fun evs sm =>
    (memRegion cur 56 ∗ optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
    A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
    ?_ ?_
  · cases hsend : ep.send with
    | none =>
      rw [optEpochDirectionPBAt_none]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      have hstep : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 88#64) s
          (((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
            optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
              optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
              A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
        ⟨Entails.trans hp (sepConj_mono_left (sepConj_mono_left
          (optEpochDirectionPBAt_none_entails_memRegion_56 A.repAlloc cur))), hq⟩
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (epochDirectionPBAt_entails_dealloc A.repAlloc cur d))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]
      apply ProofLib.SepWP.exists_left; intro gs
      wp_focus_pure; intro hcap_lt_s
      have hne_none_s := cap_add_one_beq_zero_false hcap_lt_s
      refine seq_clean_evs (mid := (blkPl_288).base + 68#64) (P_evs := fun evs sm =>
        ((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A.repAlloc gs.prev.cap gs.prev.ptr) ∗
          optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
        ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hcap : (gs.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc gs.next.cap.toNat 1
          wp_steps; wp_apply; rw [hsp]
          have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          wp_done
      · intro evs_s1 s1 hevs_s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        let st1 := M.stepEvents evs_s1 st
        have hstep2 : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 88#64) s1
            (((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A.repAlloc gs.prev.cap gs.prev.ptr) ∗
              optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
              A.pool lim st1 s1 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              ∃ evs_s2, FreeOnlyEvs evs_s2 ∧
              (Pm ⊢ (epochDirPBHeadersAt cur gs ∗
                optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
                A.pool lim (M.stepEvents evs_s2 st1) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hcap : (gs.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc gs.prev.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_1]
            have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            wp_done
        refine SepWP.mono hstep2 fun sm _Pm _ _ ⟨evs_s2, hevs_s2, hp, hq⟩ => ?_
        refine ⟨evs_s1 ++ evs_s2, hevs_s1.append hevs_s2, ?_, hq⟩
        have heq_st : M.stepEvents (evs_s1 ++ evs_s2) st = M.stepEvents evs_s2 st1 := by
          simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        exact Entails.trans hp
          (sepConj_mono_left (sepConj_mono_left (epochDirPBHeadersAt_entails_memRegion_56 cur gs)))
  · intro evsA s2 hevsA hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2, hx20_2⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_2
    let stA := M.stepEvents evsA st
    have hstepB : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 28#64) s2
        ((memRegion cur 56 ∗ optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
          A.pool lim stA s2 ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evsB, FreeOnlyEvs evsB ∧
          (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evsB stA) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
      cases hrecv : ep.recv with
      | none =>
        rw [optEpochDirectionPBAt_none]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        have hstep : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 28#64) s2
            ((memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
              A.pool lim stA s2 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
                A.pool lim stA sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          wp_steps; wp_done
        exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
          ⟨Entails.trans hp (sepConj_mono_left (Entails.trans
            (sepConj_mono_right (optEpochDirectionPBAt_none_entails_memRegion_56 A.repAlloc (cur + 56#64)))
            (chainEpochPB_regions_entails_112 cur))), hq⟩
      | some d =>
        rw [optEpochDirectionPBAt_some]
        refine SepWP.weaken_pre
          (sepConj_mono_left (sepConj_mono_right (epochDirectionPBAt_entails_dealloc A.repAlloc (cur + 56#64) d))) ?_
        rw [sepExists_sepConj_right, sepExists_sepConj_left]
        apply ProofLib.SepWP.exists_left; intro gr
        wp_focus_pure; intro hcap_lt_r
        have hne_none_r := cap_add_one_beq_zero_false hcap_lt_r
        refine seq_clean_evs (mid := (blkPl_288).base + 116#64) (P_evs := fun evs sm =>
          (memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A.repAlloc gr.prev.cap gr.prev.ptr)) ∗
          A.pool lim (M.stepEvents evs stA) sm ∗ stackAt fsp allocHookStack ∗ Frame)
          (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
          ?_ ?_
        · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hcap : (gr.next.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc gr.next.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            wp_done
        · intro evs_r1 s3 hevs_r1 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3, hx20_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          let st3 := M.stepEvents evs_r1 stA
          have hstep4 : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 28#64) s3
              ((memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A.repAlloc gr.prev.cap gr.prev.ptr)) ∗
                A.pool lim st3 s3 ∗ stackAt fsp allocHookStack ∗ Frame)
              (fun sm Pm =>
                ∃ evs_r2, FreeOnlyEvs evs_r2 ∧
                (Pm ⊢ (memRegion cur 56 ∗ epochDirPBHeadersAt (cur + 56#64) gr) ∗
                  A.pool lim (M.stepEvents evs_r2 st3) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
                Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
            dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hcap : (gr.prev.cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
            · apply sepWP_evs_dealloc gr.prev.cap.toNat 1
              wp_steps; wp_apply; wp_steps; rw [hsp_3]
              have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              wp_done
          refine SepWP.mono hstep4 fun sm _Pm _ _ ⟨evs_r2, hevs_r2, hp, hq⟩ => ?_
          refine ⟨evs_r1 ++ evs_r2, hevs_r1.append hevs_r2, ?_, hq⟩
          have heq_st : M.stepEvents (evs_r1 ++ evs_r2) stA = M.stepEvents evs_r2 st3 := by
            simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Entails.trans hp
            (sepConj_mono_left (Entails.trans
              (sepConj_mono_right (epochDirPBHeadersAt_entails_memRegion_56 (cur + 56#64) gr))
              (chainEpochPB_regions_entails_112 cur)))
    refine SepWP.mono hstepB fun sm _Pm _ _ ⟨evsB, hevsB, hp, hq⟩ => ?_
    refine ⟨evsA ++ evsB, hevsA.append hevsB, ?_, hq⟩
    have heq_st : M.stepEvents (evsA ++ evsB) st = M.stepEvents evsB stA := by
      simp only [stA, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    rw [heq_st]
    exact hp

private theorem drop_proto_epoch_slice_loop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64) (st : M.σ)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_288).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      AllocCallPreserved s0 s →
      s.readReg64 .x19 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_288).rebase (blkPl_288).base H)
        ((blkPl_288).base + 140#64)
        s
        (arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧
          AllocCallPreserved s0 sm) := by
  have hbody := drop_proto_epoch_slice_body_placed hdealloc s0 fsp hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_288).base + 28#64)
      (P_evs := fun evs sm => memRegion cur 112 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 (cur + 112#64) tl ∗ Frame))
      (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = BitVec.ofNat 64 (ep :: tl).length ∧
        sm.readReg64 .x20 = cur + 56#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep st s _ hpc hrun hpres hacp hx19 hx20)
      ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨ep2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx19_1 ⊢
      rcases hpres1 with ⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 140#64) s1
          (memRegion cur 112 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm) := by
        wp_steps
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (ep2 :: tl2).length * 112 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx19_1
      rcases hpres1 with ⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_288).base + 40#64)
        (P_mid := arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun s2 => Saved32x20Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = BitVec.ofNat 64 (ep2 :: tl2).length ∧
          s2.readReg64 .x20 = cur + 168#64)
        ?_ ?_
      · wp_steps_vm
      · intro s2 hpc2 hrun2 hvm2 ⟨hpres2, hacp2, hx19_2, hx20_2⟩
        rw [← A.pool_of_vmPreserved hvm2]
        have hrec := ih (cur + 112#64) (M.stepEvents evs_hd st) s2 (memRegion cur 112 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2
          (by simp only [hx20_2, add_112_add_56, wp_norm, arm64_norm])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>` (Block `288`)
satisfies `dropProtoEpochSliceSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_proto_epoch_slice_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (blkPl_288).base (dropProtoEpochSliceSpec M A lim) := by
  simp only [dropProtoEpochSliceSpec]
  have hloop := drop_proto_epoch_slice_loop_placed hdealloc
  dsimp only [chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hloop ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨ptr, eps⟩, st⟩
  have hx0 : s0.readReg64 .x0 = ptr := h_1
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 eps.length := h_2
  have hlen_lt : eps.length * 112 < 2 ^ 63 := h
  dsimp only [DropProtoEpochSliceGhost.ptr, DropProtoEpochSliceGhost.eps] at *
  cases eps with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj] at hx1 ⊢
    refine sepWP_close_drop (fun sf => A.pool lim st sf ∗ stackAt s0.sp dropStack32) ?_
      (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
    · wp_steps
      wp_done
    · rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨[], ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
  | cons ep tl =>
    have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 32#64 (by assumption) (by decide)
    have hne0 := ofNat_beq_zero_false_112 (n := (ep :: tl).length) (by simp) hlen_lt
    nth_rw 1 [stackAt_dropStack32_split s0.sp]
    cells_unfold
    wp_pull_exists
    refine seq_vm_clean (mid := (blkPl_288).base + 40#64)
      (P_mid := arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr (ep :: tl) ∗
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
      refine seq_clean_evs (mid := (blkPl_288).base + 140#64)
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

/-! ## Block `136`: `drop_glue::<proto::Chain> [local#1]` -/

private theorem drop_proto_spqr_chain_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp a lPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB) (st : M.σ)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_136).base + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      AllocCallPreserved s0 s →
      s.readReg64 .x19 = a →
      s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 56#64 →
      SepWP ((blkPC_136).rebase (blkPl_136).base H)
        ((blkPl_136).base + 36#64)
        s
        (chainEpochPBAt A.repAlloc cur ep ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 56#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt ep st s Frame hpc hrun hpres hacp hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  unfold chainEpochPBAt
  refine seq_clean_evs (mid := (blkPl_136).base + 96#64) (P_evs := fun evs sm =>
    (memRegion cur 56 ∗ optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
    A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64)
    ?_ ?_
  · cases hsend : ep.send with
    | none =>
      rw [optEpochDirectionPBAt_none]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      have hstep : SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 96#64) s
          (((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
            optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
              optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
              A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
        ⟨Entails.trans hp (sepConj_mono_left (sepConj_mono_left
          (optEpochDirectionPBAt_none_entails_memRegion_56 A.repAlloc cur))), hq⟩
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (epochDirectionPBAt_entails_dealloc A.repAlloc cur d))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]
      apply ProofLib.SepWP.exists_left; intro gs
      wp_focus_pure; intro hcap_lt_s
      have hne_none_s := cap_add_one_beq_zero_false hcap_lt_s
      refine seq_clean_evs (mid := (blkPl_136).base + 76#64) (P_evs := fun evs sm =>
        ((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A.repAlloc gs.prev.cap gs.prev.ptr) ∗
          optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64)
        ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hcap : (gs.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc gs.next.cap.toNat 1
          wp_steps; wp_apply; rw [hsp]
          have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          wp_done
      · intro evs_s1 s1 hevs_s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1, hx21_1, hx22_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        let st1 := M.stepEvents evs_s1 st
        have hstep2 : SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 96#64) s1
            (((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A.repAlloc gs.prev.cap gs.prev.ptr) ∗
              optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
              A.pool lim st1 s1 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              ∃ evs_s2, FreeOnlyEvs evs_s2 ∧
              (Pm ⊢ (epochDirPBHeadersAt cur gs ∗
                optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
                A.pool lim (M.stepEvents evs_s2 st1) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hcap : (gs.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc gs.prev.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_1]
            have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            wp_done
        refine SepWP.mono hstep2 fun sm _Pm _ _ ⟨evs_s2, hevs_s2, hp, hq⟩ => ?_
        refine ⟨evs_s1 ++ evs_s2, hevs_s1.append hevs_s2, ?_, hq⟩
        have heq_st : M.stepEvents (evs_s1 ++ evs_s2) st = M.stepEvents evs_s2 st1 := by
          simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        exact Entails.trans hp
          (sepConj_mono_left (sepConj_mono_left (epochDirPBHeadersAt_entails_memRegion_56 cur gs)))
  · intro evsA s2 hevsA hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2, hx20_2, hx21_2, hx22_2⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_2
    let stA := M.stepEvents evsA st
    have hstepB : SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 36#64) s2
        ((memRegion cur 56 ∗ optEpochDirectionPBAt A.repAlloc (cur + 56#64) ep.recv) ∗
          A.pool lim stA s2 ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evsB, FreeOnlyEvs evsB ∧
          (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evsB stA) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
      cases hrecv : ep.recv with
      | none =>
        rw [optEpochDirectionPBAt_none]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        have hstep : SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 36#64) s2
            ((memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
              A.pool lim stA s2 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
                A.pool lim stA sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
          wp_steps; wp_done
        exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
          ⟨Entails.trans hp (sepConj_mono_left (Entails.trans
            (sepConj_mono_right (optEpochDirectionPBAt_none_entails_memRegion_56 A.repAlloc (cur + 56#64)))
            (chainEpochPB_regions_entails_112 cur))), hq⟩
      | some d =>
        rw [optEpochDirectionPBAt_some]
        refine SepWP.weaken_pre
          (sepConj_mono_left (sepConj_mono_right (epochDirectionPBAt_entails_dealloc A.repAlloc (cur + 56#64) d))) ?_
        rw [sepExists_sepConj_right, sepExists_sepConj_left]
        apply ProofLib.SepWP.exists_left; intro gr
        wp_focus_pure; intro hcap_lt_r
        have hne_none_r := cap_add_one_beq_zero_false hcap_lt_r
        refine seq_clean_evs (mid := (blkPl_136).base + 124#64) (P_evs := fun evs sm =>
          (memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A.repAlloc gr.prev.cap gr.prev.ptr)) ∗
          A.pool lim (M.stepEvents evs stA) sm ∗ stackAt fsp allocHookStack ∗ Frame)
          (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64)
          ?_ ?_
        · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hcap : (gr.next.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc gr.next.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            wp_done
        · intro evs_r1 s3 hevs_r1 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3, hx20_3, hx21_3, hx22_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          let st3 := M.stepEvents evs_r1 stA
          have hstep4 : SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 36#64) s3
              ((memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A.repAlloc gr.prev.cap gr.prev.ptr)) ∗
                A.pool lim st3 s3 ∗ stackAt fsp allocHookStack ∗ Frame)
              (fun sm Pm =>
                ∃ evs_r2, FreeOnlyEvs evs_r2 ∧
                (Pm ⊢ (memRegion cur 56 ∗ epochDirPBHeadersAt (cur + 56#64) gr) ∗
                  A.pool lim (M.stepEvents evs_r2 st3) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
                Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
                sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
            dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hcap : (gr.prev.cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
            · apply sepWP_evs_dealloc gr.prev.cap.toNat 1
              wp_steps; wp_apply; wp_steps; rw [hsp_3]
              have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              wp_done
          refine SepWP.mono hstep4 fun sm _Pm _ _ ⟨evs_r2, hevs_r2, hp, hq⟩ => ?_
          refine ⟨evs_r1 ++ evs_r2, hevs_r1.append hevs_r2, ?_, hq⟩
          have heq_st : M.stepEvents (evs_r1 ++ evs_r2) stA = M.stepEvents evs_r2 st3 := by
            simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Entails.trans hp
            (sepConj_mono_left (Entails.trans
              (sepConj_mono_right (epochDirPBHeadersAt_entails_memRegion_56 (cur + 56#64) gr))
              (chainEpochPB_regions_entails_112 cur)))
    refine SepWP.mono hstepB fun sm _Pm _ _ ⟨evsB, hevsB, hp, hq⟩ => ?_
    refine ⟨evsA ++ evsB, hevsA.append hevsB, ?_, hq⟩
    have heq_st : M.stepEvents (evsA ++ evsB) st = M.stepEvents evsB stA := by
      simp only [stA, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    rw [heq_st]
    exact hp

private theorem drop_proto_spqr_chain_loop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp a lPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64) (st : M.σ)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_136).base + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      AllocCallPreserved s0 s →
      s.readReg64 .x19 = a →
      s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 56#64 →
      SepWP ((blkPC_136).rebase (blkPl_136).base H)
        ((blkPl_136).base + 148#64)
        s
        (arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = lPtr) := by
  have hbody := drop_proto_spqr_chain_body_placed hdealloc s0 fsp a lPtr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_136).base + 36#64)
      (P_evs := fun evs sm => memRegion cur 112 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 (cur + 112#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (ep :: tl).length ∧
        sm.readReg64 .x22 = cur + 56#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep st s _ hpc hrun hpres hacp hx19 hx20 hx21 hx22)
      ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨ep2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 148#64) s1
          (memRegion cur 112 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 112 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr) := by
        wp_steps
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (ep2 :: tl2).length * 112 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_136).base + 48#64)
        (P_mid := arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun s2 => Saved48Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = a ∧ s2.readReg64 .x20 = lPtr ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (ep2 :: tl2).length ∧
          s2.readReg64 .x22 = cur + 168#64)
        ?_ ?_
      · wp_steps_vm
      · intro s2 hpc2 hrun2 hvm2 ⟨hpres2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        rw [← A.pool_of_vmPreserved hvm2]
        have hrec := ih (cur + 112#64) (M.stepEvents evs_hd st) s2 (memRegion cur 112 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2 hx20_2 hx21_2
          (by simp only [hx22_2, add_112_add_56, wp_norm, arm64_norm])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]` (Block `136`)
satisfies `dropProtoSpqrChainSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_proto_spqr_chain_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (blkPl_136).base
      (dropProtoSpqrChainSpec M A lim) := by
  simp only [dropProtoSpqrChainSpec]
  have hloop := drop_proto_spqr_chain_loop_placed hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [chainPBSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_fo ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨a, ch⟩, st⟩
  dsimp only [DropProtoSpqrChainGhost.a, DropProtoSpqrChainGhost.ch] at *
  refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A.repAlloc a ch)) ?_
  dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  wp_pull_exists
  rename_i g
  nth_rw 1 [stackAt_dropStack48_split s0.sp]
  cells_unfold
  wp_pull_exists
  wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  refine seq_clean_evs (mid := (blkPl_136).base + 148#64)
    (P_evs := fun evs sm =>
      (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      (if g.links.cap = 0 then emp
       else A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
         memRegion g.links.ptr (g.links.cap.toNat * 112)) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      memRegion (a + 40#64) 40 ∗
      vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr)
    ?_ ?_
  · generalize hxs : ch.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj]
      refine seq_vm_clean (mid := (blkPl_136).base + 148#64)
        (P_mid :=
          (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          (if g.links.cap = 0 then emp
           else A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
             memRegion g.links.ptr (g.links.cap.toNat * 112)) ∗
          ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
          memRegion (a + 40#64) 40 ∗
          vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
          A.pool lim st s0 ∗
          stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr)
        ?_ ?_
      · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
      · intro sm hpcm hrunm hvmm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m, hx20m⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacpm
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_done
    | cons ep tl =>
      have hlen_pos : 0 < (ep :: tl).length := by simp
      have hlen_lt : (ep :: tl).length * 112 < 2 ^ 63 := by
        have : (ep :: tl).length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
      have hcap_ne : g.links.cap ≠ 0 := by
        intro hc0; rw [hc0] at hlen_le; simp at hlen_le
      simp only [hcap_ne, ↓reduceIte]
      refine seq_vm_clean (mid := (blkPl_136).base + 48#64)
        (P_mid :=
          arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr (ep :: tl) ∗
          A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (ep :: tl).length) ∗
           A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
           memRegion (g.links.ptr + BitVec.ofNat 64 ((ep :: tl).length * 112))
             ((g.links.cap.toNat - (ep :: tl).length) * 112) ∗
           ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
           memRegion (a + 40#64) 40 ∗
           vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (ep :: tl).length ∧
          sm.readReg64 .x22 = g.links.ptr + 56#64)
        ?_ ?_
      · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
      · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
        rw [← A.pool_of_vmPreserved hvm_loop]
        refine SepWP.mono
          (hloop s0 (s0.sp - 48#64) a g.links.ptr hfsp_align (ep :: tl) g.links.ptr st s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
            hx19_loop hx20_loop hx21_loop hx22_loop) ?_
        intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
        refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
        have hsplit : g.links.cap.toNat * 112 =
            (ep :: tl).length * 112 + (g.links.cap.toNat - (ep :: tl).length) * 112 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (ep :: tl).length * 112 + (g.links.cap.toNat - (ep :: tl).length) * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        conv_rhs =>
          arg 2; arg 2; arg 2; arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.links.ptr ((ep :: tl).length * 112)
                ((g.links.cap.toNat - (ep :: tl).length) * 112) hbound]
        exact Entails.of_eq (by sep_ac_rfl)
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs (mid := (blkPl_136).base + 176#64)
      (P_evs := fun evs sm =>
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗
        vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        wp_done
      · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        simp only [hc, ↓reduceIte]
        apply sepWP_evs_dealloc (g.links.cap.toNat * 112) 8
        wp_steps
        wp_call hdealloc_fo (g.links.ptr, g.links.cap.toNat * 112, 8, st1)
        rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ∗ stackAt s0.sp dropStack48) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st2 : M.stepEvents (evs1 ++ evs2) st = st2 := by
            simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st2]
          wp_steps
          refine SepWP.focus_weaken
            (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
              (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          wp_done
        · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2, ?_⟩
          rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents g.nextRoot.cap.toNat 1) st) sf ∗
            stackAt s0.sp dropStack48) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st3 : M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents g.nextRoot.cap.toNat 1) st =
              M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st2 := by
            simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st3]
          have htail : SepWP ((blkPC_136).rebase (blkPl_136).base H) (s0.readReg64 .lr) s2
              ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗
                (A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗
                  memRegion g.nextRoot.ptr g.nextRoot.cap.toNat) ∗
                A.pool lim st2 s2 ∗
                stackAt (s0.sp - 48#64) allocHookStack ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sf Pf =>
                (Pf ⊢ memRegion a 80 ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st2) sf ∗
                  stackAt s0.sp dropStack48) ∧
                sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                AllocCallPreserved s2 sf ∧ CalleeSavedPreserved s0 sf) := by
            wp_steps
            refine SepWP.focus_weaken
              (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
                (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr)
              (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            rw [stackAt_dropStack48_split_bottom s0.sp]
            wp_call hdealloc_fo (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1, st2)
            have hpost2 : AllocCallPreserved s2 sf := by assumption
            rcases hpost2 with ⟨_, _, _, _, _, _, _⟩
            wp_done
          exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_2f, hcs_f⟩ =>
            ⟨hp, hsp_f, htr_f, hacp_2.trans hacp_2f, hcs_f⟩
        · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ rustDeallocEvents g.nextRoot.cap.toNat 1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.nextRoot.cap.toNat)⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

/-! ## Block `266`: `drop_glue::<Option<proto::Chain>>` -/

/-- Relocatable `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>`
(Block `266`) satisfies `dropOptProtoSpqrChainSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_opt_proto_spqr_chain_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_266).rebase (blkPl_266).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hslice_raw : subroutine_ok ((blkPC_266).rebase (blkPl_266).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec M A lim)) :
    subroutine_ok ((blkPC_266).rebase (blkPl_266).base H) (blkPl_266).base
      (dropOptProtoSpqrChainSpec M A lim) := by
  simp only [dropOptProtoSpqrChainSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [dropProtoEpochSliceSpec, chainPBSize, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw hdealloc_fo ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨a, optCh⟩, st⟩
  dsimp only [DropOptProtoSpqrChainGhost.a, DropOptProtoSpqrChainGhost.optCh] at *
  nth_rw 1 [stackAt_dropStack80_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  cases optCh with
  | none =>
    rw [optChainPBAt_none]
    refine seq_vm_clean (mid := s0.readReg64 .lr)
      (P_mid := memRegion a 80 ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStack80)
      (Q := fun sf => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
        AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (optChainPBAt_none_entails_memRegion_80 a) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_
        wp_done)
    · intro sf hpcf hrunf hvmf ⟨hsp_f, htr_f, hacp_f, hcs_f⟩
      rw [← A.pool_of_vmPreserved hvmf]
      apply SepWP.done hpcf hrunf
      refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
      rw [satisfies_sepExists]; refine ⟨[], ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  | some ch =>
    rw [optChainPBAt_some]
    refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A.repAlloc a ch)) ?_
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    wp_pull_exists; rename_i g
    wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
    have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
    have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
      have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le; omega
    have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
    refine seq_clean_evs (mid := (blkPl_266).base + 68#64)
      (P_evs := fun evs sm =>
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22)
      ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
        have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        have h0 : arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr [] = emp := rfl
        simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte,
          emp_sepConj, sepConj_emp]
        refine seq_vm_clean (mid := lsmpl.base 288)
          (P_mid :=
            arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr [] ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
            ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
             ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
             memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.links.ptr ∧ sc.readReg64 .x1 = 0#64 ∧
            sc.readReg64 .lr = (blkPl_266).base + 44#64 ∧
            sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.links.ptr ∧
            sc.readReg64 .x21 = 0#64 ∧ sc.readReg64 .x22 = s0.readReg64 .x22)
          ?_ ?_
        · by_vm_steps (
            wp_steps
            rw [← sepConj_emp (a ↦₆₄ 0#64), ← h0]
            refine align_pre_vm (by sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
          wp_call hslice_raw (⟨g.links.ptr, []⟩, st)
          rw [hsp_c]
          have hacp_s : AllocCallPreserved sc sf := by assumption
          have hevs_s : FreeOnlyEvs w := by assumption
          have hacp_cs : AllocCallPreserved s0 sf := hacp_c.trans hacp_s
          rcases hacp_cs with ⟨_, _, _, _, _, _, _⟩
          rcases hacp_s with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢
                (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ 0#64) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
                A.pool lim (M.stepEvents w st) sm ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_s, hp, hq⟩)
          wp_steps
          refine align_pre_st
            (by simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC]
                try simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]
                sep_ac_rfl) ?_
          wp_done
      · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        have hsp_sub : s0.sp - 4176#64 = (s0.sp - 48#64) - 4128#64 := by bv_omega
        have hsplit : g.links.cap.toNat * 112 =
            ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hrejoin :
            memRegion g.links.ptr (ch.links.length * 112) ∗
              memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
                ((g.links.cap.toNat - ch.links.length) * 112) ⊢
            memRegion g.links.ptr (g.links.cap.toNat * 112) := by
          rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112)
                ((g.links.cap.toNat - ch.links.length) * 112) hbound]
          exact Entails.refl _
        simp only [hc, ↓reduceIte]
        refine seq_vm_clean (mid := lsmpl.base 288)
          (P_mid :=
            arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr ch.links ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
            ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
             ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
             A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
             memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
               ((g.links.cap.toNat - ch.links.length) * 112) ∗
             ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
             memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.links.ptr ∧
            sc.readReg64 .x1 = BitVec.ofNat 64 ch.links.length ∧
            sc.readReg64 .lr = (blkPl_266).base + 44#64 ∧
            sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.links.ptr ∧
            sc.readReg64 .x21 = g.links.cap ∧ sc.readReg64 .x22 = s0.readReg64 .x22)
          ?_ ?_
        · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
        · intro sc hpcc hrunc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
          wp_call hslice_raw (⟨g.links.ptr, ch.links⟩, st)
          rw [hsp_c]
          have hacp_s : AllocCallPreserved sc sf := by assumption
          have hevs_s : FreeOnlyEvs w := by assumption
          have hacp_cs : AllocCallPreserved s0 sf := hacp_c.trans hacp_s
          have ⟨_, _, _, _, _, _, _⟩ := hacp_cs
          have ⟨_, _, _, _, _, _, _⟩ := hacp_s
          refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
          conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
          wp_steps
          wp_call hdealloc_fo (g.links.ptr, g.links.cap.toNat * 112, 8, M.stepEvents w st)
          have hacp_d : AllocCallPreserved s0 sf_1 := hacp_cs.trans (by assumption)
          rcases hacp_d with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢
                (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
                A.pool lim (M.stepEvents (w ++ rustDeallocEvents (g.links.cap.toNat * 112) 8) st) sm ∗
                stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
              ⟨w ++ rustDeallocEvents (g.links.cap.toNat * 112) 8,
                hevs_s.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.links.cap.toNat * 112)),
                hp, hq⟩)
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          refine align_pre_st (by
            try simp only [hsp_sf, hsp_c, hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64), *]
            sep_ac_rfl) ?_
          wp_done
    · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx22_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      let st1 := M.stepEvents evs1 st
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents evs1 st) sf ∗ stackAt s0.sp dropStack80) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · wp_steps
          refine SepWP.focus_weaken
            (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
              (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · rw [satisfies_sepExists]; refine ⟨evs1, ?_⟩
          rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, hevs1⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents (evs1 ++ rustDeallocEvents g.nextRoot.cap.toNat 1) st) sf ∗
            stackAt s0.sp dropStack80) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st2 : M.stepEvents (evs1 ++ rustDeallocEvents g.nextRoot.cap.toNat 1) st =
              M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st1 := by
            simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st2]
          have htail : SepWP ((blkPC_266).rebase (blkPl_266).base H) (s0.readReg64 .lr) s1
              ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗
                (A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗
                  memRegion g.nextRoot.ptr g.nextRoot.cap.toNat) ∗
                A.pool lim st1 s1 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sf Pf =>
                (Pf ⊢ memRegion a 80 ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st1) sf ∗
                  stackAt s0.sp dropStack80) ∧
                sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                AllocCallPreserved s1 sf ∧ CalleeSavedPreserved s0 sf) := by
            wp_steps
            refine SepWP.focus_weaken
              (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
                (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            rw [stackAt_dropStack80_split_bottom s0.sp]
            wp_call hdealloc_fo (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1, st1)
            have hpost1 : AllocCallPreserved s1 sf := by assumption
            rcases hpost1 with ⟨_, _, _, _, _, _, _⟩
            wp_done
          exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_1f, hcs_f⟩ =>
            ⟨hp, hsp_f, htr_f, hacp_1.trans hacp_1f, hcs_f⟩
        · rw [satisfies_sepExists]; refine ⟨evs1 ++ rustDeallocEvents g.nextRoot.cap.toNat 1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.nextRoot.cap.toNat)⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
