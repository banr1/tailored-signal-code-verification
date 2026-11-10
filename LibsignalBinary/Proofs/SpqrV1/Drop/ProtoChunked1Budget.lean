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
public import LibsignalBinary.Proofs.SpqrV1.Drop.DecodesBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Drop Glue for PB Chunked States (`Ct1Received`, `NoHeaderReceived`)

Defines the five `RustCliAllocBudget`-threaded `dropProtoChunked*Spec` contracts (`FreeOnlyEvs`)
and proves relocatable `[LibsignalPlacement]` subroutine contracts for `chunked::Ct1Received`
(Block `282`) and `chunked::NoHeaderReceived` (Block `284`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (
  LibsignalPlacement blkPC_282 blkPC_284 blkPl_282 blkPl_284 lsmpl lsρ
)
open CryptoVerification.LibsignalSpqrV1 (pbToProtoPolyDecoder pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (
  DropProtoChunkedCt1ReceivedGhost DropProtoChunkedEkSentCt1ReceivedGhost
  DropProtoChunkedHeaderReceivedGhost DropProtoChunkedHeaderSentGhost
  DropProtoChunkedNoHeaderReceivedGhost Saved32x20Preserved Saved48Preserved
  add_24_add_8 auth40HeadersAt auth40HeadersAt_entails_memRegion_56
  auth48HeadersAt auth48HeadersAt_entails_memRegion_48
  cap_add_one_beq_zero_false cap_add_two_beq_zero_false cap_mul_24 cons_len_mul
  dropStack48 dropStack96 header_cells_entails_memRegion_24
  none2Cap none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
  optProtoAuthenticatorAt optProtoAuthenticatorAt_40_none_entails_memRegion_56
  optProtoAuthenticatorAt_48_none optProtoAuthenticatorAt_48_none_entails_memRegion_48
  optProtoAuthenticatorAt_none optProtoAuthenticatorAt_some
  optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialDecoderAt_none' optProtoPolynomialDecoderAt_some'
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  optProtoUnchunked2Vec_none_entails_memRegion_104
  optProtoUnchunkedEkSentCt1ReceivedAt_none optProtoUnchunkedEkSentCt1ReceivedAt_some
  optProtoUnchunkedNoHeaderReceivedAt_none
  optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56
  optProtoUnchunkedNoHeaderReceivedAt_some
  protoAuthenticatorAt_entails_dealloc
  protoChunkedCt1ReceivedAt protoChunkedCt1ReceivedSize
  protoChunkedEkSentCt1ReceivedAt protoChunkedEkSentCt1ReceivedSize
  protoChunkedHeaderReceivedAt protoChunkedHeaderReceivedSize
  protoChunkedHeaderSentAt protoChunkedHeaderSentSize
  protoChunkedNoHeaderReceivedAt protoChunkedNoHeaderReceivedSize
  protoPolyDecoderAt_entails_dealloc protoPolyDecoderHeaders_entails_memRegion_40
  protoPolynomialEncoderAt_expose_cap protoPolynomialEncoderAt_unexpose_cap
  protoUnchunked2VecHeadersAt protoUnchunked2VecHeadersAt_entails_memRegion_104'
  protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc protoUnchunkedNoHeaderReceivedAt
  sep_pull_body sep_push_body sep_rejoin_loop
  stackAt_allocHook16_split_bottom stackAt_dropStack48_split stackAt_dropStack48_split32
  stackAt_dropStack48_split_bottom stack_restore_48_allocHook stack_restore_48_from_32
  tail_len_mul_lt twoVecHeadersAt twoVecHeadersAt_40_eq twoVecHeadersAt_48_eq
  vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialDecoderAt optProtoPolynomialEncoderAt
  protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Budget-Threaded Specifications -/

def dropProtoChunkedCt1ReceivedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoChunkedCt1ReceivedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      protoChunkedCt1ReceivedAt A.repAlloc x.a x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropStack48
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a protoChunkedCt1ReceivedSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack48

def dropProtoChunkedNoHeaderReceivedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoChunkedNoHeaderReceivedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      protoChunkedNoHeaderReceivedAt A.repAlloc x.a x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropStack48
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a protoChunkedNoHeaderReceivedSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack48

def dropProtoChunkedHeaderReceivedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoChunkedHeaderReceivedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      protoChunkedHeaderReceivedAt A.repAlloc x.a x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropStack48
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a protoChunkedHeaderReceivedSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack48

def dropProtoChunkedEkSentCt1ReceivedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoChunkedEkSentCt1ReceivedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      protoChunkedEkSentCt1ReceivedAt A.repAlloc x.a x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropStack48
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a protoChunkedEkSentCt1ReceivedSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack48

def dropProtoChunkedHeaderSentSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoChunkedHeaderSentGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      protoChunkedHeaderSentAt A.repAlloc x.a x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropStack96
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a protoChunkedHeaderSentSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStack96

/-! ## Sequencing Helpers -/

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
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

private theorem sepWP_vm_evs_nil {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (hpool : ∀ sm, VmPreserved s sm → P_evs [] s = P_evs [] sm)
    (h : SepWP (P.rebase b Hk) target s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_evs [] s) ∧ Q sm)) :
    SepWP (P.rebase b Hk) target s Pre (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun sm _Pm _ _ ⟨hvm, hp, hq⟩ =>
    ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hpool sm hvm ▸ hp, hq⟩

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

/-! ## Block `282`: `drop_glue::<chunked::Ct1Received>` -/

/-- Relocatable `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>`
(Block `282`) satisfies `dropProtoChunkedCt1ReceivedSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_proto_chunked_ct1_received_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_282).rebase (blkPl_282).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpoly_enc_raw : subroutine_ok ((blkPC_282).rebase (blkPl_282).base H)
      (lsmpl.base 271) (ProtoPolyBudget.dropProtoPolyEncoderSpec M A lim)) :
    subroutine_ok ((blkPC_282).rebase (blkPl_282).base H) (blkPl_282).base
      (dropProtoChunkedCt1ReceivedSpec M A lim) := by
  simp only [dropProtoChunkedCt1ReceivedSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [protoChunkedCt1ReceivedSize] at *
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases x_st with ⟨⟨a, st_pb⟩, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [DropProtoChunkedCt1ReceivedGhost.a, DropProtoChunkedCt1ReceivedGhost.st,
    protoChunkedCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4144 : (s0.sp - 32#64) - 4112#64 = s0.sp - 4144#64 := by bv_omega
  nth_rw 1 [stackAt_dropStack48_split32 s0.sp]
  nth_rw 1 [stackAt_allocHook16_split_bottom (s0.sp - 32#64)]
  rw [hsub_4144]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x20_old x19_old
  refine seq_clean_evs (mid := (blkPl_282).base + 116#64)
    (P_evs := fun evs sm =>
      (memRegion a 104 ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
      refine sepWP_vm_evs_nil (fun sm hvm => by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken
          (optProtoUnchunked2Vec_none_entails_memRegion_104 a)
          (by sep_focus) ?_
        refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done)
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A.repAlloc a u)) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean_evs (mid := (blkPl_282).base + 76#64)
        (P_evs := fun evs sm =>
          ((protoUnchunked2VecHeadersAt a g ∗
            memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
            optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
        ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_48_none]
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]
          refine sepWP_vm_evs_nil (fun sm hvm => by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
          by_vm_steps (
            wp_steps
            refine SepWP.focus_weaken
              (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc a)
              (by sep_focus) ?_
            refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken
            (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 48#64) auth)
            (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [twoVecHeadersAt_48_eq]
          wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean_evs (mid := (blkPl_282).base + 56#64)
            (P_evs := fun evs sm =>
              ((protoUnchunked2VecHeadersAt a g ∗
                (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 96#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
              A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
            ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
              vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
              simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · refine sepWP_vm_evs_nil (fun sm hvm => by
                simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
              by_vm_steps (
                wp_steps
                refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done)
            · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
              refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
                (P_mid :=
                  A.pool lim st s0 ∗ A.live ga.v1.ptr ga.v1.cap.toNat 1 ∗ memRegion ga.v1.ptr ga.v1.cap.toNat ∗
                  stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((protoUnchunked2VecHeadersAt a g ∗
                     (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                     memRegion (a + 96#64) 8 ∗
                     vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                     vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                   memRegion (s0.sp - 4144#64) 16 ∗
                   (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
                (Q := fun sc => Saved32x20Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
                  sc.readReg64 .x0 = ga.v1.ptr ∧ sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
                  sc.readReg64 .lr = (blkPl_282).base + 56#64 ∧
                  sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.v1.cap)
                ?_ ?_
              · by_vm_steps (
                  wp_steps
                  dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
                    vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                  refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                  wp_done)
              · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c⟩
                rcases hpres_c with ⟨hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
                have ⟨_, _, _, _, _, _, _⟩ := hacp_c
                rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
                have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
                  change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
                  simp (config := { decide := true }) only [arm64_norm, wp_norm]
                wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
                rw [hsp_c, hlr_c]
                have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
                rcases hacp' with ⟨_, _, _, _, _, _, _⟩
                dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
                  vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done
          · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1, hx20_a1⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
            let sta1 := M.stepEvents evsa1 st
            dsimp only [auth48HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · refine SepWP.mono (post := fun sm Pm =>
                  (Pm ⊢
                    ((protoUnchunked2VecHeadersAt a g ∗
                      memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
                      vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                      optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                    A.pool lim sta1 sm ∗
                    (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                  Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                  sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
                ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                  ⟨evsa1, hevsa1,
                    Entails.trans hp (Entails.of_eq (by
                      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, sta1]
                      sep_ac_rfl)),
                    hq⟩)
              dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              wp_steps
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
            · refine SepWP.mono (post := fun sm Pm =>
                  (Pm ⊢
                    ((protoUnchunked2VecHeadersAt a g ∗
                      memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
                      vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                      optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                    A.pool lim (M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1) sm ∗
                    (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                  Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                  sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
                ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                  ⟨evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1,
                    hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat),
                    Entails.trans hp (Entails.of_eq (by
                      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                      simp only [sta1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                      sep_ac_rfl)),
                    hq⟩)
              dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              wp_steps
              wp_apply
              rw [hsp_a1]
              have hacp' : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
      · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        let st1 := M.stepEvents evs1 st
        refine seq_clean_evs (mid := (blkPl_282).base + 96#64)
          (P_evs := fun evs sm =>
            ((protoUnchunked2VecHeadersAt a g ∗
              memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
            A.pool lim (M.stepEvents evs st1) sm ∗
            (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;>
            simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; wp_done
          · apply sepWP_evs_dealloc g.v1.cap.toNat 1
            wp_steps
            wp_apply
            rw [hsp_1]
            have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
        · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_2
          let st2 := M.stepEvents evs2 st1
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 104 ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                  A.pool lim st2 sm ∗
                  (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evs1 ++ evs2, hevs1.append hevs2,
                  Entails.trans hp (Entails.of_eq (by
                    simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    sep_ac_rfl)),
                  hq⟩)
            wp_steps
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            wp_done
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 104 ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 104#64) (st_pb.sendingEk.map pbToProtoPolyEncoder)) ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.v2.cap.toNat 1) st2) sm ∗
                  (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evs1 ++ evs2 ++ rustDeallocEvents g.v2.cap.toNat 1,
                  (hevs1.append hevs2).append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v2.cap.toNat),
                  Entails.trans hp (Entails.of_eq (by
                    simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    sep_ac_rfl)),
                  hq⟩)
            wp_steps
            wp_apply
            rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
  · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_3
    let st3 := M.stepEvents evs3 st
    cases hek : st_pb.sendingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h112 : (a + 104#64) + 8#64 = a + 112#64 := BitVec.add_assoc a 104#64 8#64
      rw [h112]
      refine sepWP_close_drop
        (fun sf => memRegion a 160 ∗ A.pool lim st3 sf ∗ stackAt s0.sp dropStack48)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        have hjoin : memRegion a 104 ∗ ((a + 104#64) ↦₆₄ noneCap) ∗ memRegion (a + 112#64) 48 ⊢
            memRegion a 160 := by
          rw [← h112,
              ProofLib.memRegion_split' (b := a) (n := 104) (k := 56) (b' := a + 104#64) rfl rfl (by decide)]
          exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 104#64))
        refine SepWP.focus_weaken hjoin (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · rw [satisfies_sepExists]
        refine ⟨evs3, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs3⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken
        (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 104#64) (pbToProtoPolyEncoder enc))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      refine seq_vm_clean (mid := lsmpl.base 271)
        (P_mid :=
          protoPolynomialEncoderAt A.repAlloc (a + 104#64) (pbToProtoPolyEncoder enc) ∗
          A.pool lim st3 s3 ∗ stackAt s0.sp dropStack48 ∗
          memRegion a 104)
        (Q := fun sc => sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
          sc.readReg64 .x0 = a + 104#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
          AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken
            (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 104#64) cap ptr (pbToProtoPolyEncoder enc))
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          refine align_pre_vm (by sep_ac_rfl) ?_
          wp_done)
      · intro sc hpcc hrunc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
        have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
          change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]; assumption
        wp_call hpoly_enc_raw (⟨a + 104#64, pbToProtoPolyEncoder enc⟩, st3)
        rw [hsp_c]
        have hacp_cf : AllocCallPreserved sc sf := by assumption
        have hevs_w : FreeOnlyEvs w := by assumption
        have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
        have ⟨_, _, _, _, _, _, _⟩ := hacp_f
        have hjoin : memRegion a 104 ∗ memRegion (a + 104#64) protoPolynomialEncoderSize ⊢
            memRegion a 160 := by
          rw [show (160 : Nat) = 104 + protoPolynomialEncoderSize from rfl,
              ProofLib.memRegion_split a 104 protoPolynomialEncoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin (by sep_focus) ?_
        refine sepWP_close_drop
          (fun sf' => memRegion a 160 ∗ A.pool lim (M.stepEvents w st3) sf' ∗ stackAt s0.sp dropStack48)
          (by wp_done)
          (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        rw [satisfies_sepExists]
        refine ⟨evs3 ++ w, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f', hevs3.append hevs_w⟩, ?_⟩
        have heq_st : M.stepEvents (evs3 ++ w) st = M.stepEvents w st3 := by
          simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

/-! ## Block `284`: `drop_glue::<chunked::NoHeaderReceived>` -/

section PlacedProtoChunkedNoHeaderReceived
variable [LibsignalPlacement]

private theorem drop_proto_chunked_no_header_received_body_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_284).rebase (blkPl_284).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_284).base + 116#64 → s.status = .Running →
      Saved48Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 104#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hacp hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 104#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 104#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      wp_steps
      wp_apply
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      rw [hsp]
      wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

private theorem drop_proto_chunked_no_header_received_loop_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_284).rebase (blkPl_284).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_284).base + 116#64 → s.status = .Running →
      Saved48Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 140#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_no_header_received_body_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_284).base + 104#64)
      (P_evs := fun evs sm => memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hacp hx19 hx20 hx21 hx22) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP ((blkPC_284).rebase (blkPl_284).base H) ((blkPl_284).base + 140#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_284).base + 116#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => Saved48Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ s2.readReg64 .x22 = cur + 32#64)
        ?_ ?_
      · wp_steps_vm
      · intro s2 hpc2 hrun2 hvm2 ⟨hpres2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        rw [← A.pool_of_vmPreserved hvm2]
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2 hx20_2 hx21_2
          (by simp only [hx22_2, add_24_add_8, wp_norm, arm64_norm])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>`
(Block `284`) satisfies `dropProtoChunkedNoHeaderReceivedSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_proto_chunked_no_header_received_placed_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_284).rebase (blkPl_284).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_284).rebase (blkPl_284).base H) (blkPl_284).base
      (dropProtoChunkedNoHeaderReceivedSpec M A lim) := by
  simp only [dropProtoChunkedNoHeaderReceivedSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop := drop_proto_chunked_no_header_received_loop_placed hdealloc
  dsimp only [protoChunkedNoHeaderReceivedSize] at *
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases x_st with ⟨⟨a, st_pb⟩, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [DropProtoChunkedNoHeaderReceivedGhost.a, DropProtoChunkedNoHeaderReceivedGhost.st,
    protoChunkedNoHeaderReceivedAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_evs (mid := (blkPl_284).base + 76#64)
    (P_evs := fun evs sm =>
      (optProtoPolynomialDecoderAt A.repAlloc a (st_pb.receivingHdr.map pbToProtoPolyDecoder) ∗
        memRegion (a + 40#64) 56) ∗
      A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      have h48 : (a + 40#64) + 8#64 = a + 48#64 := BitVec.add_assoc a 40#64 8#64
      rw [optProtoUnchunkedNoHeaderReceivedAt_none, h48]
      refine sepWP_vm_evs_nil (fun sm hvm => by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      by_vm_steps (
        wp_steps
        have hjoin : ((a + 40#64) ↦₆₄ none2Cap) ∗ memRegion (a + 48#64) 48 ⊢ memRegion (a + 40#64) 56 := by
          rw [← h48]
          exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (a + 40#64)
        refine SepWP.focus_weaken hjoin (by sep_focus) ?_
        refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done)
    | some u =>
      rw [optProtoUnchunkedNoHeaderReceivedAt_some]
      unfold protoUnchunkedNoHeaderReceivedAt
      cases hauth : u.auth with
      | none =>
        have hnone40 : optProtoAuthenticatorAt A.repAlloc (a + 40#64) none =
            ((a + 40#64) ↦₆₄ noneCap) ∗ memRegion (a + 48#64) 40 := by
          rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 40#64 8#64]; rfl
        rw [hnone40]
        refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken
            (optProtoAuthenticatorAt_40_none_entails_memRegion_56 A.repAlloc a u.epoch)
            (by sep_focus) ?_
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken
          (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 40#64) auth)
          (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [twoVecHeadersAt_40_eq]
        wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        refine seq_clean_evs (mid := (blkPl_284).base + 56#64)
          (P_evs := fun evs sm =>
            (optProtoPolynomialDecoderAt A.repAlloc a (st_pb.receivingHdr.map pbToProtoPolyDecoder) ∗
              ((auth40HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
               (((a + 40#64) + 48#64) ↦₆₄ u.epoch))) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [auth40HeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine sepWP_vm_evs_nil (fun sm hvm => by
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
            by_vm_steps (
              wp_steps
              refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done)
          · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
            refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
              (P_mid :=
                A.pool lim st s0 ∗ A.live ga.v1.ptr ga.v1.cap.toNat 1 ∗ memRegion ga.v1.ptr ga.v1.cap.toNat ∗
                stackAt (s0.sp - 48#64) allocHookStack ∗
                ((optProtoPolynomialDecoderAt A.repAlloc a (st_pb.receivingHdr.map pbToProtoPolyDecoder) ∗
                  ((auth40HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                   (((a + 40#64) + 48#64) ↦₆₄ u.epoch))) ∗
                 (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
                sc.readReg64 .x0 = ga.v1.ptr ∧ sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
                sc.readReg64 .lr = (blkPl_284).base + 56#64 ∧
                sc.readReg64 .x19 = a)
              ?_ ?_
            · by_vm_steps (
                wp_steps
                dsimp only [auth40HeadersAt, vecCapPtrDealloc,
                  LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done)
            · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c⟩
              rcases hpres_c with ⟨hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
              have ⟨_, _, _, _, _, _, _⟩ := hacp_c
              rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
              have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
                change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
                simp (config := { decide := true }) only [arm64_norm, wp_norm]
              wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
              rw [hsp_c, hlr_c]
              have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              dsimp only [auth40HeadersAt, vecCapPtrDealloc,
                LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
        · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
          let sta1 := M.stepEvents evsa1 st
          dsimp only [auth40HeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (optProtoPolynomialDecoderAt A.repAlloc a (st_pb.receivingHdr.map pbToProtoPolyDecoder) ∗
                    memRegion (a + 40#64) 56) ∗
                  A.pool lim sta1 sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evsa1, hevsa1,
                  Entails.trans hp (Entails.of_eq (by dsimp only [sta1]; sep_ac_rfl)),
                  hq⟩)
            wp_steps
            refine SepWP.focus_weaken (auth40HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (optProtoPolynomialDecoderAt A.repAlloc a (st_pb.receivingHdr.map pbToProtoPolyDecoder) ∗
                    memRegion (a + 40#64) 56) ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1) sm ∗
                  stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1,
                  hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat),
                  Entails.trans hp (Entails.of_eq (by
                    simp only [sta1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    sep_ac_rfl)),
                  hq⟩)
            wp_steps
            wp_apply
            rw [hsp_a1]
            have hacp' : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine SepWP.focus_weaken (auth40HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    have hjoin96_from_40 : memRegion a 40 ∗ memRegion (a + 40#64) 56 ⊢ memRegion a 96 := by
      rw [ProofLib.memRegion_split' (b := a) (n := 40) (k := 56) (b' := a + 40#64) rfl rfl (by decide)]
      exact Entails.refl _
    cases hhdr : st_pb.receivingHdr with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      refine sepWP_close_drop
        (fun sf => memRegion a 96 ∗ A.pool lim st1 sf ∗ stackAt s0.sp dropStack48)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        refine SepWP.focus_weaken (optProtoPolyDecoder_none_entails_memRegion_40 a) (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin96_from_40 (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · rw [satisfies_sepExists]
        refine ⟨evs1, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs1⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc a pb) (by sep_focus) ?_
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      wp_pull_exists; rename_i g
      wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      refine seq_clean_evs (mid := (blkPl_284).base + 140#64)
        (P_evs := fun evs sm =>
          (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp
           else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 24#64) 16 ∗ memRegion (a + 40#64) 56 ∗
          A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap)
        ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
            BitVec.add_zero, arrayAt, emp_sepConj]
          refine seq_vm_clean (mid := (blkPl_284).base + 140#64)
            (P_mid :=
              (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
              (if g.cap = 0 then emp
               else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
              memRegion (a + 24#64) 16 ∗ memRegion (a + 40#64) 56 ∗
              A.pool lim st1 s1 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s1 sm ∧
              sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap)
            ?_ ?_
          · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
          · intro sm hpcm hrunm hvmm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩, hacpm, hx19m, hx20m⟩
            have hacp_s0m : AllocCallPreserved s0 sm := hacp_1.trans hacpm
            have ⟨_, _, _, _, _, _, _⟩ := hacp_s0m
            rw [← A.pool_of_vmPreserved hvmm]
            apply sepWP_evs_nil
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
            omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_vm_clean (mid := (blkPl_284).base + 116#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
              A.pool lim st1 s1 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗
               ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                 ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 24#64) 16 ∗ memRegion (a + 40#64) 56 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s1 sm ∧
              sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64)
            ?_ ?_
          · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
          · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop1, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            have hacp_loop : AllocCallPreserved s0 s_loop := hacp_1.trans hacp_loop1
            rw [← A.pool_of_vmPreserved hvm_loop]
            refine SepWP.mono
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr st1 s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
                hx19_loop hx20_loop hx21_loop hx22_loop) ?_
            intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
            refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
            have hsplit : g.cap.toNat * 24 =
                (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
              rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                    ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by sep_ac_rfl)
      · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2, hx20_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        let st2 := M.stepEvents evs2 st1
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_2 ⊢
          refine sepWP_close_drop
            (fun sf => memRegion a 96 ∗ A.pool lim st2 sf ∗ stackAt s0.sp dropStack48)
            ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · wp_steps
            refine SepWP.focus_weaken
              (protoPolyDecoderHeaders_entails_memRegion_40 a 0 g.ptr (BitVec.ofNat 64 pb.pts.length))
              (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin96_from_40 (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            wp_done
          · rw [satisfies_sepExists]
            refine ⟨evs1 ++ evs2, ?_⟩
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
            have heq_st : M.stepEvents (evs1 ++ evs2) st = st2 := by
              simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]
          refine sepWP_close_drop
            (fun sf => memRegion a 96 ∗
              A.pool lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents (g.cap.toNat * 24) 8) st) sf ∗
              stackAt s0.sp dropStack48)
            ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · have heq_st3 : M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents (g.cap.toNat * 24) 8) st =
                M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st2 := by
              simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st3]
            have htail : SepWP ((blkPC_284).rebase (blkPl_284).base H) (s0.readReg64 .lr) s2
                ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗
                  ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                  (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
                  memRegion (a + 24#64) 16 ∗ memRegion (a + 40#64) 56 ∗
                  A.pool lim st2 s2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
                (fun sf Pf =>
                  (Pf ⊢ memRegion a 96 ∗
                    A.pool lim (M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st2) sf ∗
                    stackAt s0.sp dropStack48) ∧
                  sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                  AllocCallPreserved s2 sf ∧ CalleeSavedPreserved s0 sf) := by
              wp_steps
              refine SepWP.focus_weaken
                (protoPolyDecoderHeaders_entails_memRegion_40 a g.cap g.ptr (BitVec.ofNat 64 pb.pts.length))
                (by sep_focus) ?_
              refine SepWP.focus_weaken hjoin96_from_40 (by sep_focus) ?_
              refine SepWP.focus_weaken
                (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                  (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
                (by sep_focus) ?_
              rw [stackAt_dropStack48_split_bottom s0.sp]
              wp_call hdealloc_fo (g.ptr, g.cap.toNat * 24, 8, st2)
              have hpost2 : AllocCallPreserved s2 sf := by assumption
              rcases hpost2 with ⟨_, _, _, _, _, _, _⟩
              wp_done
            exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_2f, hcs_f⟩ =>
              ⟨hp, hsp_f, htr_f, hacp_2.trans hacp_2f, hcs_f⟩
          · rw [satisfies_sepExists]
            refine ⟨evs1 ++ evs2 ++ rustDeallocEvents (g.cap.toNat * 24) 8, ?_⟩
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append
              (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.cap.toNat * 24))⟩, ?_⟩
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end PlacedProtoChunkedNoHeaderReceived

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
