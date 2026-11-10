/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Contract for `drop_glue::<SessionStructure> [local#4]` (Block `512`)

Budget-threaded (`RustCliAllocBudget M`) proof of `drop_session_structure4_placed_ok`
(`dropSessionStructureLocal2Spec M A lim`) on Block `512`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ReceiverChain SenderChain)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsRustDeallocSym lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
  ls_subroutine_ok_of_block ls_subroutine_ok_cl_of_block
)
open CryptoVerification.CliHandshake.Placed (blkPC_512 blkPl_512)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecAt vecBuf_expose_arrayAt vecHeader)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost SessionGhost noneCap optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  dropChainStack ls_hook_ok_rustDealloc
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  chainAt_of_exposed_sender_shared_lb chains_header24_weaken_shared_lb
  dropSessionStructureLocal2Stack optSenderChainAt_some_expose_shared_lb
  post_loop_weaken_at_72_shared_lb pq_header24_weaken_shared_lb
  sender_none_entails_memRegion_104_shared_lb session_memRegions_entails_344_shared_lb
  ssFirst3HeadersAt_shared_lb ssTail3HeadersAt_shared_lb
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon (
  SepWP.false_elim_left header_cells_entails_memRegion_24
  sessionStateAt_entails_dealloc sgnPinDealloc
  ssFirst3HeadersAt_entails_memRegions ssTail3HeadersAt_entails_memRegions
  stackAt_split_bottom' vecPinDealloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpec dropProtoChainSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget (
  drop_chain_placed_ok drop_proto_chain_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem freeOnlyPool_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs₁ evs₂ st]
  exact Entails.sepExists_right (evs₁ ++ evs₂)
    (Entails.pure_right (FreeOnlyEvs.append h1 h2) (Entails.refl _))

private theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st sm :=
  freeOnlyPool_append A lim st hevs (FreeOnlyEvs.singleton al sz) hvm

private theorem SepWP.seq_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 (fun sm _Pm hpcm hrunm ⟨hent, hq⟩ =>
    SepWP.weaken_pre hent (h2 sm hpcm hrunm hq))

private theorem seq_state_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem SepWP.unpack_freeOnlyPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = freeOnlyPool A lim st s ∗ Frame := by sep_focus)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hf]; unfold freeOnlyPool
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem SepWP.fold_keep {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs st) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_keep A lim st hevs hvm) hf hk

private theorem SepWP.fold_append {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs₁ evs₂ : List AllocEvent} (h1 : FreeOnlyEvs evs₁)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ∗ Frame := by sep_focus)
    (h2 : FreeOnlyEvs evs₂ := by assumption)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_append A lim st h1 h2 hvm) hf hk

private theorem SepWP.fold_dealloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs) (sz al : Nat)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_dealloc A lim st hevs sz al hvm) hf hk

private theorem SepWP.sync_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (A.pool lim st sm ∗ Frame) post) :
    SepWP prog target sm P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]
  exact hk

private theorem SepWP.mono_ac {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h1 : SepWP prog target s P' post)
    (h2 : ∀ sf Pf, sf.pc = target → sf.status = .Running → post sf Pf → post' sf Pf)
    (heq : P = P') :
    SepWP prog target s P post' :=
  SepWP.weaken_pre (Entails.of_eq heq) (SepWP.mono h1 h2)

@[reducible]
private def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem stackAt_ss_local2_split (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp dropChainStack 6 (by decide)

private theorem stackAt_dropChain_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropChainStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropChainStack = allocHookStack + 48 from rfl,
      stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

private theorem stack_96_eq_ss_local2 (sp : BitVec 64) :
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack =
      stackAt sp dropSessionStructureLocal2Stack := by
  rw [← stackAt_split_bottom' sp allocHookStack 96 (by decide)]
  rfl

private theorem cells6_sub48_entails_stack (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropChainStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSessionStructureLocal2Stack := by
  rw [stackAt_ss_local2_split sp]
  cells_unfold
  refine Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x22 (Entails.sepExists_right x21
      (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))

private theorem tail_dealloc_ss_local2_pre_weaken (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 48#64) dropChainStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack := by
    rw [stack_96_eq_ss_local2 sp]
    exact cells6_sub48_entails_stack sp fp lr x22 x21 x20 x19
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 48#64) dropChainStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem ss_local2_regions_entails_344 (ss : BitVec 64) :
    memRegion (ss + 120#64) 24 ∗
      (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
        memRegion (ss + 72#64) 24 ∗ memRegion (ss + 96#64) 24 ∗ memRegion (ss + 144#64) 104 ∗
        memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 328#64) 16) ⊢
    memRegion ss 344 := by
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) (session_memRegions_entails_344_shared_lb ss)

private theorem ss_local2_post_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ast : M.σ) {s0 sf : State} (htr : sf.trace = s0.trace)
    (ss sp : BitVec 64) :
    memRegion ss 344 ∗ freeOnlyPool A lim ast sf ∗ stackAt sp dropSessionStructureLocal2Stack ⊢
      ∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
          memRegion ss 344 ∗ A.pool lim (M.stepEvents evs ast) sf ∗
          stackAt sp dropSessionStructureLocal2Stack := by
  unfold freeOnlyPool
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro evs
  refine Entails.sepExists_right evs ?_
  have hpure :
      memRegion ss 344 ∗ (⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
        stackAt sp dropSessionStructureLocal2Stack =
      ⌜FreeOnlyEvs evs⌝ ∗
        (memRegion ss 344 ∗ A.pool lim (M.stepEvents evs ast) sf ∗
          stackAt sp dropSessionStructureLocal2Stack) := by sep_ac_rfl
  rw [hpure]
  apply Entails.pure_left; intro hevs
  exact Entails.pure_right ⟨htr, hevs⟩ (Entails.refl _)

private theorem SepWP.finish_ss_local2 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ast : M.σ) {prog : Program} {target : BitVec 64}
    {s0 sf : State} {P : SepProp} {post : State → SepProp → Prop}
    (ss sp : BitVec 64)
    (hP : P ⊢ memRegion ss 344 ∗ freeOnlyPool A lim ast sf ∗ stackAt sp dropSessionStructureLocal2Stack)
    (htr : sf.trace = s0.trace)
    (hk : ∀ evs : List AllocEvent, sf.trace = s0.trace ∧ FreeOnlyEvs evs →
      SepWP prog target sf
        (memRegion ss 344 ∗ A.pool lim (M.stepEvents evs ast) sf ∗
          stackAt sp dropSessionStructureLocal2Stack) post) :
    SepWP prog target sf P post := by
  refine SepWP.weaken_pre (Entails.trans hP (ss_local2_post_entails A lim ast htr ss sp)) ?_
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem ofNat_succ_eq_add_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 :=
  BitVec.ofNat_add n 1

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  have hlt2 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h
  omega

private theorem ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n == 0#64) = true) := by
  rw [beq_iff_eq]
  exact ofNat_ne_zero_of_pos hpos hlt

private theorem ofNat_add_one_beq_one_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n + 1#64 == 1#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h0 : BitVec.ofNat 64 n = 0#64 := by bv_omega
  exact ofNat_ne_zero_of_pos hpos hlt h0

private theorem tail_len_mul_lt {α : Type} {x : α} {xs : List α} {k m : Nat}
    (h : (x :: xs).length * k < m) : xs.length * k < m := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at h
  omega

private theorem cons_len_mul {α : Type} (x : α) (xs : List α) (k : Nat) :
    (x :: xs).length * k = k + xs.length * k := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
  omega

private theorem sep_pull_body (M0 Arr Pool Stk Frame : SepProp) :
    (M0 ∗ Arr) ∗ Pool ∗ Stk ∗ Frame = M0 ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) := by sep_ac_rfl

private theorem sep_rejoin_loop (M1 M2 Pool Stk Frame : SepProp) :
    M2 ∗ Pool ∗ Stk ∗ (M1 ∗ Frame) = (M1 ∗ M2) ∗ Pool ∗ Stk ∗ Frame := by sep_ac_rfl

private theorem vecAt_expose_loop_at_72 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (ss cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (ss + 72#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        arrayAt elem sz ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * sz) align ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz))) := by
  unfold vecAt vecHeader
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A sz align elem cap ptr xs)) ?_
  have h1 : (ss + 72#64) + 8#64 = ss + 80#64 := by bv_omega
  have h2 : (ss + 72#64) + 16#64 = ss + 88#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem drop_ss_local2_placed_first3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_512).base + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 80#64)
        s
        ((ssFirst3HeadersAt_shared_lb ss G ∗
          vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc G.root) ∗
          freeOnlyPool A lim ast s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := (blkPl_512).base + 40#64) (P_mid := fun sm =>
    (ssFirst3HeadersAt_shared_lb ss G ∗
      vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A.repAlloc G.root) ∗
    freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    · wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1, M.stepEvents evs ast)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs G.localIk.cap.toNat 1 (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp]; try sep_ac_rfl)) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := (blkPl_512).base + 60#64) (P_mid := fun sm =>
      (ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      · wp_steps
        refine SepWP.sync_pool (hk := ?_)
        rw [← hsp_1]
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1, M.stepEvents evs ast)
        have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
        refine SepWP.fold_dealloc hevs G.remoteIk.cap.toNat 1 (hk := ?_)
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_1]; try sep_ac_rfl)) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_512).rebase (blkPl_512).base H) ((blkPl_512).base + 80#64) s2
          ((ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
            freeOnlyPool A lim ast s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt_shared_lb ss G ∗ freeOnlyPool A lim ast sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps
          refine SepWP.fold_keep hevs (hk := ?_)
          wp_done
        · wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_2]
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1, M.stepEvents evs ast)
          have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
          refine SepWP.fold_dealloc hevs G.root.cap.toNat 1 (hk := ?_)
          refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_2]; try sep_ac_rfl)) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss_local2_placed_sender [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdrop_chain : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropProtoChainSpec M A lim)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_512).base + 80#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 100#64)
        s
        (optSenderChainAt A.repAlloc (ss + 144#64) senderG senderSt ∗
          freeOnlyPool A lim ast s ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ freeOnlyPool A lim ast sm ∗
            stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [withLsCodeLoaded, dropProtoChainSpec] at hdrop_chain
  intro senderG senderSt s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP ((blkPC_512).rebase (blkPl_512).base H) ((blkPl_512).base + 100#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
            freeOnlyPool A lim ast s ∗ stackAt fsp dropChainStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
              freeOnlyPool A lim ast sm ∗ stackAt fsp dropChainStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [noneCap]
        wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      exact SepWP.mono hstep (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (sender_none_entails_memRegion_104_shared_lb (ss + 144#64))), h.2⟩)
    | some _ => simp only [optSenderChainAt]; exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none => simp only [optSenderChainAt]; exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre
        (sepConj_mono_left (optSenderChainAt_some_expose_shared_lb A.repAlloc (ss + 144#64) sg sc)) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hpk, hlen, hcap_lt, hptr_ne, hcmn⟩
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps
      refine SepWP.sync_pool (hk := ?_)
      refine SepWP.weaken_pre (P' :=
        A.pool lim (M.stepEvents evs ast) _ ∗
        ((ss + 144#64) ↦₆₄ sg.srk.cap ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.srkRest_shared_lb A.repAlloc (ss + 144#64) sg.srk ∗
          CryptoVerification.LibsignalSessionRepr.vecGhostAt A.repAlloc sg.priv (ss + 144#64 + 24#64) ∗
          vecAt A.repAlloc 104 8 (CryptoVerification.LibsignalSessionRepr.messageKeyAt A.repAlloc) (ss + 144#64 + 48#64) sg.mkCap sg.mkPtr [] ∗
          CryptoVerification.LibsignalSessionRepr.optChainKeyAt A.repAlloc sg.ck (some sc.chainKey) (ss + 144#64 + 72#64)) ∗
        stackAt fsp dropChainStack ∗ Frame)
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left
          (chainAt_of_exposed_sender_shared_lb A.repAlloc (ss + 144#64) sg sc hpk hlen hcap_lt hptr_ne))) ?_
      rw [← hsp]
      wp_call hdrop_chain (⟨ss + 144#64, (⟨sg.srk, sg.priv, sg.mkCap, sg.mkPtr, [], sg.ck⟩, ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩)⟩, M.stepEvents evs ast)
      have htr_c : sf.trace = s0.trace := (by assumption : sf.trace = _).trans htrace
      refine SepWP.fold_append hevs (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp]; try sep_ac_rfl)) ?_
      wp_done

private theorem drop_ss_local2_placed_receiver_loop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdrop_chain : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropChainSpec M A lim)))
    (s0 : State) (fsp ss ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_512).base + 112#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 132#64)
        s
        (arrayAt (chainAt A.repAlloc) 104 cur rest ∗ freeOnlyPool A lim ast s ∗
          stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freeOnlyPool A lim ast sm ∗
            stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          sm.readReg64 .x20 = ptr) := by
  simp only [withLsCodeLoaded, dropChainSpec] at hdrop_chain
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    rw [show arrayAt (chainAt A.repAlloc) 104 cur ((g, c) :: tl) =
          chainAt A.repAlloc (g, c) cur ∗ arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_state_lscl hcl (mid := (blkPl_512).base + 120#64)
      (P_mid := fun sm => memRegion cur 104 ∗ freeOnlyPool A lim ast sm ∗ stackAt fsp dropChainStack ∗
        (arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cur ∧ sm.readReg64 .x22 = BitVec.ofNat 64 ((g, c) :: tl).length)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdrop_chain (⟨cur, (g, c)⟩, M.stepEvents evs ast)
      have htr_c : sf.trace = s0.trace := (by assumption : sf.trace = _).trans htrace
      refine SepWP.fold_append hevs (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp]; try sep_ac_rfl)) ?_
      wp_done
    · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
      cases tl with
      | nil =>
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          arrayAt, emp_sepConj] at hx22_1 ⊢
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      | cons hd2 tl2 =>
        have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
        have htl_len := tail_len_mul_lt hlen
        rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
            ofNat_succ_eq_add_one] at hx22_1
        have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps
        have hpc_next : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
          rw [bne_iff_ne]; intro h; exact hne1 (beq_iff_eq.mpr h)
        refine SepWP.fold_keep hevs (hk := ?_)
        apply SepWP.mono_ac
        · exact ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
            htl_ne htl_len (by simp only [State.setPC, hpc_next, ↓reduceIte]) (by assumption) hcl1
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
            hx19_1 hx20_1 rfl rfl
        · intro sf Pf _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
          have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
            rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
          rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
          exact Entails.refl _
        · sep_ac_rfl

private theorem drop_ss_local2_placed_tail3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_512).base + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 228#64)
        s
        ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          freeOnlyPool A lim ast s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := (blkPl_512).base + 184#64) (P_mid := fun sm =>
    (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A.repAlloc kCap kPtr ∗
      vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
    freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    · wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdealloc (pPtr, pCap.toNat, 1, M.stepEvents evs ast)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs pCap.toNat 1 (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp]; try sep_ac_rfl)) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := (blkPl_512).base + 208#64) (P_mid := fun sm =>
      (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
      freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      · wp_steps
        refine SepWP.sync_pool (hk := ?_)
        rw [← hsp_1]
        wp_call hdealloc (kPtr, kCap.toNat, 1, M.stepEvents evs ast)
        have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
        refine SepWP.fold_dealloc hevs kCap.toNat 1 (hk := ?_)
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_1]; try sep_ac_rfl)) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_512).rebase (blkPl_512).base H) ((blkPl_512).base + 228#64) s2
          ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freeOnlyPool A lim ast s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
              freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [ssTail3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps
          refine SepWP.fold_keep hevs (hk := ?_)
          wp_done
        · wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_2]
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1, M.stepEvents evs ast)
          have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
          refine SepWP.fold_dealloc hevs G.alice.cap.toNat 1 (hk := ?_)
          refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_2]; try sep_ac_rfl)) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

set_option maxHeartbeats 2000000 in
/-- Block `512` (`core::ptr::drop_glue::<SessionStructure> [local#4]`) meets
`dropSessionStructureLocal2Spec M A lim` under `[LibsignalPlacement]`, given `subroutine_ok` for
`__rust_dealloc` and `drop_glue<Chain>`. -/
theorem drop_session_structure4_placed_ok_of_dealloc_and_chain [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_proto_chain_raw : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropProtoChainSpec M A lim)))
    (hdrop_chain_raw : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropChainSpec M A lim))) :
    subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (blkPl_512).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) := by
  simp only [withLsCodeLoaded, dropSessionStructureLocal2Spec]
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_init x s0
  rcases x with ⟨⟨ss, G, st⟩, ast⟩
  have hfirst3 := drop_ss_local2_placed_first3 (ast := ast) hdealloc_raw
  have hsender := drop_ss_local2_placed_sender (ast := ast) hdrop_proto_chain_raw
  have hloop := drop_ss_local2_placed_receiver_loop (ast := ast) hdrop_chain_raw
  have htail3 := drop_ss_local2_placed_tail3 (ast := ast) hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = ss := by assumption
  subst hx0
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_ss_local2_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3 v4 v5
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_state_lscl hcl0 (mid := (blkPl_512).base + 16#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
    have hsp_sub : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
    rw [hsp_sub]
    wp_steps_sync_pool ((blkPl_512).base + 16#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (freeOnlyPool_intro A lim ast _) (by sep_focus)
    dsimp only [ssFirst3HeadersAt_shared_lb, ssTail3HeadersAt_shared_lb, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx0_1⟩
    refine seq_state_lscl hcl1 (mid := (blkPl_512).base + 80#64)
      (P_mid := fun sm =>
        optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
        (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
      have hsp_sub1 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
      rw [hsp_sub1]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
      refine seq_state_lscl hcl2 (mid := (blkPl_512).base + 100#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hcl2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by sep_ac_rfl)), h.2⟩
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine SepWP.weaken_pre
          (sepConj_mono_left (vecAt_expose_loop_at_72 A.repAlloc 104 8 (chainAt A.repAlloc)
            (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains))) ?_
        rw [sepConj_assoc]
        refine SepWP.pure_elim ?_
        rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
        generalize G.chains.zip st.receiverChains = cs at hlen_le hlen_lt ⊢
        refine seq_state_lscl hcl3 (mid := (blkPl_512).base + 132#64)
          (P_mid := fun sm =>
            ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            memRegion G.chainsPtr (cs.length * 104) ∗
            (if G.chainsCap = 0 then emp
             else A.repAlloc.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
               memRegion (G.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((G.chainsCap.toNat - cs.length) * 104)) ∗
            (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
              vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧ sm.readReg64 .x20 = G.chainsPtr)
          ?_ ?_
        · cases cs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
            refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
            wp_steps
            refine SepWP.fold_keep hevs (hk := ?_)
            refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [ssTail3HeadersAt_shared_lb]; try sep_ac_rfl)) ?_
            wp_done
          | cons hd tl =>
            have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
            apply sepWP_seq_lscl hcl3 (mid := (blkPl_512).base + 112#64)
            refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
            wp_steps
            refine SepWP.fold_keep hevs (hk := ?_)
            apply SepWP.done
            · wp_norm_lhs
            · wp_norm_lhs
            intro hcl_loop
            apply SepWP.mono_ac
            · exact hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) G.chainsPtr hfsp_align
                (hd :: tl) G.chainsPtr _
                (((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                  (if G.chainsCap = 0 then emp
                   else A.repAlloc.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
                     memRegion (G.chainsPtr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((G.chainsCap.toNat - (hd :: tl).length) * 104)) ∗
                  (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
                    sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
                    vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
                  (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                    ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
                  (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
                (List.cons_ne_nil _ _) hlen_lt rfl (by assumption) hcl_loop
                ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
                hx19_3 rfl rfl rfl
            · intro sm Pm _ _ h
              exact ⟨Entails.trans h.1 (Entails.of_eq (by dsimp only [ssTail3HeadersAt_shared_lb]; sep_ac_rfl)), h.2⟩
            · dsimp only [ssTail3HeadersAt_shared_lb]; sep_ac_rfl
        · intro sm hpcm hrunm hclm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩, hx19_m, hx20_m⟩
          refine SepWP.weaken_pre
            (post_loop_weaken_at_72_shared_lb A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
              cs.length hlen_le hcap_lt _) ?_
          refine seq_state_lscl hclm (mid := (blkPl_512).base + 160#64)
            (P_mid := fun sm =>
              (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
                sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
                vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
              freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
            have hsp_subm : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
            rw [hsp_subm]
            refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
            cases hcap : (G.chainsCap == 0#64) <;>
              simp only [Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
            · wp_steps
              have hmul : 104#64 * G.chainsCap = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by bv_omega
              have hmul2 : G.chainsCap * 104#64 = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by bv_omega
              refine SepWP.sync_pool (hk := ?_)
              rw [← hsp_m]
              wp_call hdealloc (G.chainsPtr, G.chainsCap.toNat * 104, 8, M.stepEvents evs ast)
              have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_m
              refine SepWP.fold_dealloc hevs (G.chainsCap.toNat * 104) 8 (hk := ?_)
              refine SepWP.weaken_pre
                (sepConj_mono_right (sepConj_mono_right
                  (chains_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _))) ?_
              rw [hsp_m]
              refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [ssTail3HeadersAt_shared_lb]; try sep_ac_rfl)) ?_
              wp_done
            · wp_steps
              refine SepWP.fold_keep hevs (hk := ?_)
              refine SepWP.weaken_pre
                (sepConj_mono_right (chains_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _)) ?_
              refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [ssTail3HeadersAt_shared_lb]; try sep_ac_rfl)) ?_
              wp_done
          · intro s4 hpc4 hrun4 hcl4 ⟨hpres4, hx19_4⟩
            refine seq_state_lscl hcl4 (mid := (blkPl_512).base + 228#64)
              (P_mid := fun sm =>
                ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq ∗
                (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
                freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
              ?_ ?_
            · refine SepWP.mono
                (htail3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                  hpc4 hrun4 hpres4 hx19_4) ?_
              intro sm Pm _ _ h
              refine ⟨Entails.trans h.1 ?_, h.2⟩
              rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
              have hsp_sub4 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
              rw [hsp_sub4]
              exact Entails.of_eq (by sep_ac_rfl)
            · intro s5 hpc5 hrun5 _ ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
              refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
              dsimp only [vecPinDealloc]
              cases hcap : (G.pq.cap == 0#64) <;>
                simp only [Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
              · wp_steps
                refine SepWP.sync_pool (hk := ?_)
                refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
                  (tail_dealloc_ss_local2_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                    (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat)
                    _ (A.pool lim (M.stepEvents evs ast) _) s0.sp _ _ _ _ _ _)) ?_
                wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1, M.stepEvents evs ast)
                have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_5
                refine SepWP.fold_dealloc hevs G.pq.cap.toNat 1 (hk := ?_)
                refine SepWP.finish_ss_local2 A lim ast (s0 := s0) (s0.readReg64 (Reg.gpr 0#5)) s0.sp ?_ htr_d fun evs_f ⟨htr_f, hevs_f⟩ => ?_
                · have hss := ss_local2_regions_entails_344 (s0.readReg64 (Reg.gpr 0#5))
                  have hstk : memRegion (s0.sp - 4192#64) 96 ∗ stackAt s0.sp allocHookStack ⊢
                      stackAt s0.sp dropSessionStructureLocal2Stack :=
                    Entails.of_eq (stack_96_eq_ss_local2 s0.sp)
                  refine Entails.trans (Entails.of_eq ?_)
                    (sepConj_mono hss (sepConj_mono_right (P := freeOnlyPool A lim ast _) hstk))
                  sep_ac_rfl
                · wp_done
              · wp_steps
                refine SepWP.fold_keep hevs (hk := ?_)
                refine SepWP.finish_ss_local2 A lim ast (s0 := s0) (s0.readReg64 (Reg.gpr 0#5)) s0.sp ?_
                  (by simpa [wp_norm, arm64_norm] using htrace_5) fun evs_f ⟨htr_f, hevs_f⟩ => ?_
                · have hstk := cells6_sub48_entails_stack s0.sp
                    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22)
                    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
                  have hhdr := pq_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr emp
                  simp only [sepConj_emp] at hhdr
                  have hss := Entails.trans (sepConj_mono_left hhdr)
                    (ss_local2_regions_entails_344 (s0.readReg64 (Reg.gpr 0#5)))
                  refine Entails.trans (Entails.of_eq ?_)
                    (sepConj_mono hss (sepConj_mono_right (P := freeOnlyPool A lim ast _) hstk))
                  sep_ac_rfl
                · wp_done

private theorem withLsCodeLoaded_of_raw [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

/-- Block `512` (`core::ptr::drop_glue::<SessionStructure> [local#4]`) meets
`withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)` under `[LibsignalPlacement]`. -/
theorem drop_session_structure4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (blkPl_512).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) := by
  have hp : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (lsmpl.base 513)
      (withLsCodeLoaded lsmpl (dropProtoChainSpec M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_512).rebase (blkPl_512).base H)
      (withLsCodeLoaded_of_raw (drop_proto_chain_placed_ok h_dealloc)) (by decide)
  have hc : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (lsmpl.base 513)
      (withLsCodeLoaded lsmpl (dropChainSpec M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_512).rebase (blkPl_512).base H)
      (withLsCodeLoaded_of_raw (drop_chain_placed_ok h_dealloc)) (by decide)
  exact drop_session_structure4_placed_ok_of_dealloc_and_chain
    (ls_hook_ok_rustDealloc h_dealloc) hp hc

/-- Caller-lifted `dropSessionStructureLocal2Spec M A lim` (`withLsCodeLoaded`) at `lsmpl.base 512`. -/
theorem drop_session_structure4_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (drop_session_structure4_placed_ok h_dealloc) hi

/-- Caller-lifted `dropSessionStructureLocal2Spec M A lim` (`withLsCl`) at `lsmpl.base 512`. -/
theorem drop_session_structure4_placed_cl_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCl lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (drop_session_structure4_placed_ok h_dealloc) hi

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
