/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoderBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Leaf Drop Glue for `SpqrV1/States/Recv`

Budget-threaded `withLsCodeLoaded` `subroutine_ok` proofs (`FreeOnlyEvs`) for `drop_glue::<[SortedSet<Pt>; 16]>`
(Block `264`), `[Poly; 16]` (Block `265`), `PolyDecoder` (Block `137`), and `PolynomialEncoder` (Block `271`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.SpqrV1.States.Recv (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Drop (
  DropChunkedCt1ReceivedGhost DropChunkedCt2SampledGhost
  DropChunkedEkReceivedCt1SampledGhost DropChunkedEkSentCt1ReceivedGhost
  DropChunkedHeaderSentGhost DropGluePolyEncoderGhost Saved32x19Preserved
  chunkedCt1ReceivedAt chunkedCt1ReceivedSize
  chunkedCt2SampledAt chunkedCt2SampledSize
  chunkedEkReceivedCt1SampledAt chunkedEkReceivedCt1SampledSize
  chunkedEkSentCt1ReceivedAt chunkedEkSentCt1ReceivedSize
  chunkedHeaderSentAt chunkedHeaderSentSize
  chunked_104_400_join chunked_400_join chunked_880_join
  dropGluePoly16Stack dropStack32 dropStackPoly64
  fiveVec400HeadersAt fiveVec400HeadersAt_entails_memRegion_128
  fourVec104HeadersAt fourVec104HeadersAt_entails_memRegion_104
  fourVec400HeadersAt fourVec400HeadersAt_entails_memRegion_104
  polyDecoderAt_entails_vecs_tail polyEncoderAt_entails_tag_vecs_tail
  polyEncoder_local2_post_join
  stackAt_dropStack32_split stackAt_dropStack32_split_bottom
  stackAt_dropStackPoly64_split stackAt_dropStackPoly64_split_bottom
  stack_restore_32_allocHook stack_restore_64_dropStack32
  threeVec400HeadersAt threeVec400HeadersAt_entails_memRegion_80
  twoVec400HeadersAt twoVec400HeadersAt_entails_memRegion_56
  unchunkedCt1SentEkReceived400_entails_dealloc
  unchunkedCt2Sent400_entails_dealloc
  unchunkedEkSent400_entails_dealloc
  unchunkedEkSentCt1Received400_entails_dealloc
  unchunkedEkSentCt1ReceivedAt_entails_dealloc
  vecCapPtrDealloc vecGF16ListOf vecPtListOf
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget (
  dropChunkedCt1ReceivedSpec dropChunkedCt2SampledSpec
  dropChunkedEkReceivedCt1SampledSpec dropChunkedEkSentCt1ReceivedSpec
  dropChunkedHeaderSentSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (
  dropGluePoly16Spec drop_glue_poly16_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoderBudget (
  drop_glue_poly_decoder_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (
  dropGluePolyEncoderSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (
  dropProtoPolyEncoderSpec drop_glue_proto_poly_encoder_placed_ok
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (
  dropGlueSortedSetPt16Spec drop_glue_sorted_set_pt16_placed_ok
)

open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_272 blkPC_274 blkPl_272 blkPl_274 extract_withLsCodeLoaded libsignalSessionLib lsProg_137 lsProg_264 lsProg_265 lsProg_271 lsProg_272 lsProg_274 ls_blockPlacement_base ls_subroutine_ok_of_block lscall_blk_cl lsmpl lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withMemEq)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyEncoderAt polyEncoderSize)

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `withLsCodeLoaded` & Budget Sequencing Helpers -/

theorem subroutine_ok_withLsCodeLoaded_intro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ m : Memory, LibsignalCodeLoaded lsmpl m →
      subroutine_ok prog entry (withMemEq m spec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  refine (h s0.mem hcl).mono_outcome x R s0 hpc hrun ?_ halign fun _ hout => hout
  dsimp only [withMemEq]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨rfl, hpre'⟩

theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

abbrev savedFrame32 (s0 : State) (w3 : BitVec 64) : SepProp :=
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)

def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem seq_vm_clean_lscl [LibsignalPlacement]
    {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ hcl' =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hcl' hvm hQ))

theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P = P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) := by
  subst h; exact hwp

theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

theorem sepWP_vm_evs_nil {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (hpool : ∀ sm, VmPreserved s sm → P_evs [] s = P_evs [] sm)
    (h : SepWP (P.rebase b Hk) target s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_evs [] s) ∧ Q sm)) :
    SepWP (P.rebase b Hk) target s Pre (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun sm _Pm _ _ ⟨hvm, hp, hq⟩ =>
    ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hpool sm hvm ▸ hp, hq⟩

theorem seq_evs_step {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {mid target : BitVec 64}
    {st : M.σ} {s : State} {P X1 X2 : SepProp}
    {P_mid : M.σ → State → SepProp} {Q_mid Q_out : State → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧
          (Pf ⊢ X1 ∗ A.pool lim (M.stepEvents evs2 st1) sf ∗ X2) ∧ Q_out sf)) :
    SepWP prog target s P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ A.pool lim (M.stepEvents evs st) sf ∗ X2) ∧ Q_out sf) :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs1, hevs1, hent, hQ⟩ =>
    SepWP.mono (SepWP.weaken_pre hent (h2 (M.stepEvents evs1 st) sm hpc hrun hQ))
      fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hQo⟩ =>
        ⟨evs1 ++ evs2, hevs1.append hevs2, by
          rwa [LibsignalBinary.Heap.AllocCostModel.stepEvents_append], hQo⟩

theorem seq_evs_step_lscl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {mid target : BitVec 64}
    {st : M.σ} {s : State} {P X1 X2 : SepProp}
    {P_mid : M.σ → State → SepProp} {Q_mid Q_out : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧
          (Pf ⊢ X1 ∗ A.pool lim (M.stepEvents evs2 st1) sf ∗ X2) ∧ Q_out sf)) :
    SepWP prog target s P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ A.pool lim (M.stepEvents evs st) sf ∗ X2) ∧ Q_out sf) :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨evs1, hevs1, hent, hQ⟩ hcl' =>
    SepWP.mono (SepWP.weaken_pre hent (h2 (M.stepEvents evs1 st) sm hpc hrun hcl' hQ))
      fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hQo⟩ =>
        ⟨evs1 ++ evs2, hevs1.append hevs2, by
          rwa [LibsignalBinary.Heap.AllocCostModel.stepEvents_append], hQo⟩)

theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

theorem sepWP_open_evs_outer {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {s0 : State} {P R : SepProp} {a : BitVec 64} {sz stk : Nat} {st : M.σ}
    (h : SepWP prog (s0.readReg64 .lr) s0 P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ memRegion a sz ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk) ∧
        (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))) :
    SepWP prog (s0.readReg64 .lr) s0 P (fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R → sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
          memRegion a sz ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono h fun sf _Pf _ _ ⟨evs, hevs, hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    ⟨fun hm => by
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr_f, hacp_f, hevs⟩,
        Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩,
     hsp_f, hcs_f⟩

theorem sepWP_open_evs {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {s0 : State} {P R : SepProp} {a : BitVec 64} {sz stk : Nat} {st : M.σ}
    (h : SepWP prog (s0.readReg64 .lr) s0 P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ memRegion a sz ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk) ∧
        (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))) :
    SepWP prog (s0.readReg64 .lr) s0 P (fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R → sf.mem ⊨
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
          memRegion a sz ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono h fun sf _Pf _ _ ⟨evs, hevs, hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    ⟨fun hm => by
      rw [satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨htr_f, hacp_f, hevs⟩,
        Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩,
     hsp_f, hcs_f⟩

/-! ## Leaf Drop Blocks (`264`, `265`, `137`, `271`) -/

theorem drop_glue_sorted_set_pt16_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_264 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 264)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_sorted_set_pt16_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_sorted_set_pt16_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 264 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  ls_to_blockProgram (drop_glue_sorted_set_pt16_cl_placed_ok hdealloc)

theorem drop_glue_sorted_set_pt16_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  ls_subroutine_ok_of_block (drop_glue_sorted_set_pt16_cl_placed_ok hdealloc) hidx

theorem drop_glue_sorted_set_pt16_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264)
      (withMemEq m (dropGlueSortedSetPt16Spec M A lim)) :=
  lscall_blk_cl (drop_glue_sorted_set_pt16_cl_placed_ok hdealloc) hcl hidx

theorem drop_glue_poly16_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_265 (Rust.withPanics ext)) (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 265)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_poly16_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 265 (Rust.withPanics ext)) (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  ls_to_blockProgram (drop_glue_poly16_cl_placed_ok hdealloc)

theorem drop_glue_poly16_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  ls_subroutine_ok_of_block (drop_glue_poly16_cl_placed_ok hdealloc) hidx

theorem drop_glue_poly16_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec M A lim)) :=
  lscall_blk_cl (drop_glue_poly16_cl_placed_ok hdealloc) hcl hidx

theorem drop_glue_poly_decoder_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_137 (Rust.withPanics ext)) (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 137)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_poly_decoder_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_poly_decoder_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 137 (Rust.withPanics ext)) (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  ls_to_blockProgram (drop_glue_poly_decoder_cl_placed_ok hdealloc)

theorem drop_glue_poly_decoder_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  ls_subroutine_ok_of_block (drop_glue_poly_decoder_cl_placed_ok hdealloc) hidx

theorem drop_glue_poly_decoder_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 137)
      (withMemEq m (dropGlueSortedSetPt16Spec M A lim)) :=
  lscall_blk_cl (drop_glue_poly_decoder_cl_placed_ok hdealloc) hcl hidx

theorem drop_glue_proto_poly_encoder_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_271 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 271)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_proto_poly_encoder_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_proto_poly_encoder_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  ls_to_blockProgram (drop_glue_proto_poly_encoder_cl_placed_ok hdealloc)

theorem drop_glue_proto_poly_encoder_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_glue_proto_poly_encoder_cl_placed_ok hdealloc) hidx

theorem drop_glue_proto_poly_encoder_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec M A lim)) :=
  lscall_blk_cl (drop_glue_proto_poly_encoder_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `272`: `drop_glue::<PolyEncoder> [local#2]` -/

theorem drop_glue_poly_encoder_local2_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_272 (Rust.withPanics ext)) (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 272)]
  change subroutine_ok ((blkPC_272).rebase (blkPl_272).base (Rust.withPanics ext)) (blkPl_272).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropGluePolyEncoderSpec, polyEncoderSize]
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := _hlr0_gpr
  rcases x_st with ⟨⟨encA, enc⟩, st⟩
  dsimp only [CryptoVerification.SpqrV1.Drop.DropGluePolyEncoderGhost.encA, CryptoVerification.SpqrV1.Drop.DropGluePolyEncoderGhost.enc] at *
  have hx0 : s0.readReg64 .x0 = encA := by assumption
  have hm : s0.mem = m := by assumption
  subst hm hx0
  refine SepWP.weaken_pre
    (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A.repAlloc (s0.readReg64 .x0) enc)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
  wp_focus_pure; intro hvecs_len
  apply sepWP_open_evs_outer
  refine seq_vm_clean_lscl hcl (mid := lsmpl.base 265)
    (P_mid :=
      vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 8#64) vecs ∗
      A.pool lim st s0 ∗ stackAt s0.sp dropGluePoly16Stack ∗
      ((s0.readReg64 .x0 ↦₆₄ tag) ∗ memRegion (s0.readReg64 .x0 + 392#64) 8))
    (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
      sc.readReg64 .x0 = s0.readReg64 .x0 + 8#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
      AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc) ?_ ?_
  · wp_steps_vm
  · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
    have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_272 (Rust.withPanics ext)) hdealloc hclc
    dsimp only [lsProg_272, withMemEq, dropGluePoly16Spec] at hpoly16_raw
    have ⟨_, _, _, _, _, _, _⟩ := hacp_c
    have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
    have _hlr_sc_gpr : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := hlr_sc
    rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
    wp_call hpoly16_raw (⟨s0.readReg64 .x0 + 8#64, vecs⟩, st)
    rw [hsp_c]
    have hacp_cf : AllocCallPreserved sc sf := by assumption
    have hevs_w : FreeOnlyEvs w := by assumption
    have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
    have ⟨_, _, _, _, _, _, _⟩ := hacp_f
    refine SepWP.focus_weaken (polyEncoder_local2_post_join (s0.readReg64 .x0) tag) (by sep_focus) ?_
    refine SepWP.mono (post := fun sf' Pf =>
        (Pf ⊢ memRegion (s0.readReg64 .x0) 400 ∗ A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropGluePoly16Stack) ∧
        (sf'.sp = s0.sp ∧ sf'.trace = s0.trace ∧ AllocCallPreserved s0 sf' ∧ CalleeSavedPreserved s0 sf'))
      (by wp_done)
      (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)

theorem drop_glue_poly_encoder_local2_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 272 (Rust.withPanics ext)) (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  ls_to_blockProgram (drop_glue_poly_encoder_local2_cl_placed_ok hdealloc)

theorem drop_glue_poly_encoder_local2_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_glue_poly_encoder_local2_cl_placed_ok hdealloc) hidx

theorem drop_glue_poly_encoder_local2_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec M A lim)) :=
  lscall_blk_cl (drop_glue_poly_encoder_local2_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `274`: `drop_glue::<chunked::send_ct::Ct2Sampled>` -/

theorem drop_chunked_ct2_sampled_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_274 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 274)]
  change subroutine_ok ((blkPC_274).rebase (blkPl_274).base (Rust.withPanics ext)) (blkPl_274).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_fo := subroutine_ok_deallocFreeOnly
    (spqr_hook_ok_of_mem (prog := lsProg_274 (Rust.withPanics ext)) hdealloc)
  simp only [lsProg_274, deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropChunkedCt2SampledSpec, chunkedCt2SampledSize]
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := _hlr0_gpr
  rcases x_st with ⟨⟨a, st_c⟩, st⟩
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [CryptoVerification.SpqrV1.Drop.DropChunkedCt2SampledGhost.a, CryptoVerification.SpqrV1.Drop.DropChunkedCt2SampledGhost.st, chunkedCt2SampledAt] at *
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedCt2Sent400_entails_dealloc A.repAlloc a st_c.uc))) ?_
  wp_pull_exists; rename_i g
  apply sepWP_open_evs
  refine seq_evs_step_lscl hcl (mid := (blkPl_274).base + 56#64)
    (P_mid := fun st2 sm =>
      (polyEncoderAt A.repAlloc a st_c.sending_ct2 ∗ memRegion (a + 400#64) 56) ∗
      A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
  · refine seq_evs_step (mid := (blkPl_274).base + 36#64)
      (P_mid := fun st1 sm =>
        (polyEncoderAt A.repAlloc a st_c.sending_ct2 ∗
          (twoVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr)) ∗
        A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ savedFrame32 s0 w3_old)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · dsimp only [twoVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st s0 ∗ A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat ∗
            stackAt (s0.sp - 32#64) allocHookStack ∗
            ((polyEncoderAt A.repAlloc a st_c.sending_ct2 ∗
              (twoVec400HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr)) ∗ savedFrame32 s0 w3_old))
          (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.v1.ptr ∧ sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_274).base + 36#64 ∧ sc.readReg64 .x19 = a) ?_ ?_
        · by_vm_steps (
            wp_steps
            dsimp only [twoVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c⟩
          rcases hpres_c with ⟨hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
          have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
            change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
            simp (config := { decide := true }) only [arm64_norm, wp_norm]
          have _hlr_sc_lr : LsRetAddr624 (sc.readReg64 .lr) := _hlr_sc
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, st)
          rw [hsp_c, hlr_c]
          have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          dsimp only [twoVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
    · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      dsimp only [twoVec400HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        have hhdr := twoVec400HeadersAt_entails_memRegion_56 a g; dsimp only [twoVec400HeadersAt] at hhdr
        refine SepWP.focus_weaken hhdr (by sep_focus) ?_
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        have hhdr := twoVec400HeadersAt_entails_memRegion_56 a g; dsimp only [twoVec400HeadersAt] at hhdr
        refine SepWP.focus_weaken hhdr (by sep_focus) ?_
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st2 s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_2
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A.repAlloc a st_c.sending_ct2))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
    wp_focus_pure; intro hvecs_len
    refine seq_vm_clean_lscl hcl2 (mid := lsmpl.base 265)
      (P_mid := vecGF16ListOf A.repAlloc (a + 8#64) vecs ∗ A.pool lim st2 s2 ∗
        stackAt s0.sp dropGluePoly16Stack ∗ ((a ↦₆₄ tag) ∗ memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 56))
      (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
        sc.readReg64 .x0 = a + 8#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
        AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc) ?_ ?_
    · by_vm_steps (
        dsimp only [savedFrame32]; wp_steps
        refine SepWP.focus_weaken (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
    · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
      have hpoly16_raw := drop_glue_poly16_mem_on
        (callerProg := lsProg_274 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_274, withMemEq, dropGluePoly16Spec] at hpoly16_raw
      have ⟨_, _, _, _, _, _, _⟩ := hacp_c
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
      have _hlr_sc_gpr : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := hlr_sc
      rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
      wp_call hpoly16_raw (⟨a + 8#64, vecs⟩, st2)
      rw [hsp_c]
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
            memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 56) ∗
            A.pool lim (M.stepEvents w st2) sf ∗ stackAt s0.sp dropGluePoly16Stack by sep_ac_rfl))
          (sepConj_mono_left (chunked_400_join a tag 56 456 rfl (by decide)))) ?_
      refine SepWP.mono (post := fun sf' Pf =>
          (Pf ⊢ memRegion a 456 ∗ A.pool lim (M.stepEvents w st2) sf' ∗ stackAt s0.sp dropGluePoly16Stack) ∧
          (sf'.sp = s0.sp ∧ sf'.trace = s0.trace ∧ AllocCallPreserved s0 sf' ∧ CalleeSavedPreserved s0 sf'))
        (by wp_done) (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)

theorem drop_chunked_ct2_sampled_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 274 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)) :=
  ls_to_blockProgram (drop_chunked_ct2_sampled_cl_placed_ok hdealloc)

theorem drop_chunked_ct2_sampled_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ct2_sampled_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ct2_sampled_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 274)
      (withMemEq m (dropChunkedCt2SampledSpec M A lim F)) :=
  lscall_blk_cl (drop_chunked_ct2_sampled_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
