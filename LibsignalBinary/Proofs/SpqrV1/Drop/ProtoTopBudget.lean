/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.DecodesBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Specifications and Simple/Compound Variants for `Option<InnerState>` (Block `267`)

Defines `dropOptProtoInnerStatePlacedSpec`, `dropProtoPqRatchetStatePlacedSpec`, and
`dropOptProtoInnerStatePlacedVariantSpec` under `RustCliAllocBudget M` (`FreeOnlyEvs`), and
proves the ten non-looping variant contracts of Block `267`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

open CryptoVerification (LibsignalPlacement blkPC_267 blkPl_267 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (V1State pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoInnerStateGhost DropProtoPqRatchetStateGhost Saved48Preserved
  auth64HeadersAt auth64HeadersAt_entails_memRegion_56
  auth8HeadersAt auth8HeadersAt_entails_memRegion_56
  cap_add_one_beq_zero_false cap_add_two_beq_zero_false cap_xor_highBit_cc_11_false
  dropStack32 dropStack48 dropStack96 keysSampledToCt1Received
  none2Cap none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  optProtoAuthenticatorAt optProtoAuthenticatorAt_64_none_entails_memRegion_56
  optProtoAuthenticatorAt_8_none_entails_memRegion_56
  optProtoAuthenticatorAt_none optProtoAuthenticatorAt_some
  optProtoInnerStateAt optProtoInnerStateJumpTableBytes
  optProtoInnerStateJumpTablePlacedAt optProtoInnerStateJumpTablePlacedExpanded
  optProtoInnerStateJumpTableSym optProtoInnerStateSize
  optProtoInnerState_none_entails_224 optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  optProtoUnchunkedCt1SentEkReceivedAt_none
  optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
  optProtoUnchunkedCt1SentEkReceivedAt_some optProtoUnchunkedCt2SentAt
  optProtoUnchunkedKeysUnsampledAt
  optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56
  protoAuthenticatorAt_entails_dealloc protoChunkedCt1ReceivedAt protoChunkedCt2SampledAt
  protoChunkedEkReceivedCt1SampledAt protoChunkedEkSentCt1ReceivedAt
  protoChunkedHeaderReceivedAt protoChunkedHeaderSentAt
  protoChunkedKeysSampledAt_eq_ct1ReceivedAt protoChunkedKeysUnsampledAt
  protoChunkedNoHeaderReceivedAt protoInnerStateAt
  protoPolynomialEncoderAt_expose_cap protoPolynomialEncoderAt_unexpose_cap
  protoPqRatchetStateAt protoPqRatchetStateSize
  protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedAt_expose_cap
  protoUnchunkedCt1SentEkReceivedAt_unexpose_cap protoUnchunkedCt1SentEkReceivedSize
  protoUnchunkedCt2SentAt protoUnchunkedKeysUnsampledAt
  stackAt_dropStack96_split stackAt_dropStack96_split_48
  stackAt_dropStack96_split_bottom stackAt_sub48_split_32
  stack_restore_96_allocHook tag_and_two_regions_entails_224
  twoVecHeadersAt_64_eq twoVecHeadersAt_8_eq vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialEncoderAt protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget (
  dropProtoChunkedCt1ReceivedSpec dropProtoChunkedEkSentCt1ReceivedSpec
  dropProtoChunkedHeaderReceivedSpec dropProtoChunkedHeaderSentSpec
  dropProtoChunkedNoHeaderReceivedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropProtoUnchunkedCt1SentEkReceivedSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  none2Cap_add_two_beq_zero noneCap_add_two_beq_zero cap_xor_highBit_cc_11_false

/-! ## Budget-Threaded Specifications (Blocks `267` and `270`) -/

def dropOptProtoInnerStatePlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropOptProtoInnerStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ optProtoInnerStateAt A.repAlloc x.a x.st ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp dropStack96
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a optProtoInnerStateSize ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp dropStack96

def dropProtoPqRatchetStatePlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoPqRatchetStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ protoPqRatchetStateAt A.repAlloc x.a x.st ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp dropStack96
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a protoPqRatchetStateSize ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp dropStack96

/-- Per-variant budget-threaded specification of Block `267` (`Option<InnerState>`) for a fixed
`optSt`; `(dropOptProtoInnerStatePlacedSpec M A lim)` at `(⟨a, optSt⟩, st)` is definitionally
equal to `(dropOptProtoInnerStatePlacedVariantSpec M A lim optSt)` at `(a, st)`. -/
def dropOptProtoInnerStatePlacedVariantSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (optSt : Option V1State.InnerState) : Spec (BitVec 64 × M.σ) where
  pre := fun (a, st) s =>
    ⌜s.readReg64 .x0 = a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ optProtoInnerStateAt A.repAlloc a optSt ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s ∗ stackAt s.sp dropStack96
  post := fun (a, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion a optProtoInnerStateSize ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp dropStack96

/-! ## Prologue and Sequencing Helpers -/

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

private theorem sepWP_evs_inst {prog : Program} {target : BitVec 64}
    {s : State} (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

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

private theorem sepWP_vm_close_nil {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {s0 s : State} {Pre : SepProp}
    {Q_out : State → SepProp} {Post : State → SepProp → Prop}
    (hpool : ∀ sf, VmPreserved s sf → Q_out s = Q_out sf)
    (h : SepWP (P.rebase b Hk) (s0.readReg64 .lr) s Pre (fun sf Pf =>
      VmPreserved s sf ∧ (Pf ⊢ Q_out s) ∧
      sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
      AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      AllocCallPreserved s0 sf → CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP (P.rebase b Hk) (s0.readReg64 .lr) s Pre Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hvm, hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    hpost sf Pf (hpool sf hvm ▸ hp) hsp_f htr_f hacp_f hcs_f

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  sepWP_evs_inst (rustDeallocEvents sz al) (LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz) h

private theorem sepWP_sync_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    (s₁ : State) {s₂ : State} {P Q : SepProp} {post : State → SepProp → Prop}
    (hvm : VmPreserved s₁ s₂)
    (hfoc : P = A.pool lim st s₁ ∗ Q)
    (h : SepWP prog target s₂ (A.pool lim st s₂ ∗ Q) post) :
    SepWP prog target s₂ P post := by
  rw [hfoc, ← A.pool_of_vmPreserved hvm]
  exact h

private theorem jt_placed_eq_expanded [LibsignalPlacement] :
    optProtoInnerStateJumpTablePlacedAt = optProtoInnerStateJumpTablePlacedExpanded := by
  unfold optProtoInnerStateJumpTablePlacedAt optProtoInnerStateJumpTableBytes
    optProtoInnerStateJumpTablePlacedExpanded
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]

/-- Shared prologue step for Block `267` from `+0` to `+16` across the three `STP`s (before `+68`),
syncing `A.pool` to the post-prologue state `sv`. -/
private theorem proto_top_prologue_16 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {target : BitVec 64}
    {s0 : State} {a : BitVec 64} {st : M.σ} {Body : SepProp}
    {post : State → SepProp → Prop}
    (hpc0 : s0.pc = (blkPl_267).base)
    (hrun0 : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a)
    (hcont : ∀ sv : State,
      sv.pc = (blkPl_267).base + 16#64 →
      sv.status = .Running →
      Saved48Preserved s0 sv (s0.sp - 48#64) →
      AllocCallPreserved s0 sv →
      sv.readReg64 .x0 = a →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) target sv
        (Body ∗ optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st sv ∗
          (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        post) :
    SepWP ((blkPC_267).rebase (blkPl_267).base H) target s0
      (Body ∗ optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStack96)
      post := by
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_vm_clean (mid := (blkPl_267).base + 16#64)
    (P_mid := Body ∗ optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s0 ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sv => Saved48Preserved s0 sv (s0.sp - 48#64) ∧ AllocCallPreserved s0 sv ∧
      sv.readReg64 .x0 = a)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      refine align_pre_vm (by
        simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]) ?_
      wp_done)
  · intro sv hpcv hrunv hvmv ⟨hpres_v, hacp_v, hx0_v⟩
    rw [← A.pool_of_vmPreserved hvmv]
    exact hcont sv hpcv hrunv hpres_v hacp_v hx0_v

/-! ## Simple and Tail-Call Variants of Block `267` -/

local macro "opt_proto_tail48_budget_steps " tag:term:max sz1:term:max sz2:term:max
    off:term:max arg:term:max : tactic => `(tactic| (
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  wp_steps
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, $arg⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a $tag $sz1 $sz2 $off
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 $sz1)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩))

local macro "opt_proto_tail96_budget_steps " tag:term:max sz1:term:max sz2:term:max
    off:term:max arg:term:max : tactic => `(tactic| (
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  wp_steps
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, $arg⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a $tag $sz1 $sz2 $off
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 $sz1)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩))

section PlacedSimpleVariants
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {H : String → Option (State → State)}

theorem drop_opt_proto_inner_state_none_placed :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim none) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine sepWP_vm_close_nil
    (Q_out := fun sf =>
      memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
        A.pool lim st sf ∗ stackAt s0.sp dropStack96)
    (fun sf hvm => by simp only [A.pool_of_vmPreserved hvm])
    ?_
    (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  · by_vm_steps (
      wp_steps
      refine SepWP.focus_weaken (optProtoInnerState_none_entails_224 a) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done)
  · rw [satisfies_sepExists]
    refine ⟨[], ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_opt_proto_inner_state_keysSampled_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec M A lim))
    (st_pb : V1State.Chunked.KeysSampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.keysSampled st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]
  opt_proto_tail48_budget_steps 0x8000000000000001#64 160 56 168#64 (keysSampledToCt1Received st_pb)

theorem drop_opt_proto_inner_state_headerSent_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 281) (dropProtoChunkedHeaderSentSpec M A lim))
    (st_pb : V1State.Chunked.HeaderSent) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.headerSent st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  opt_proto_tail96_budget_steps 0x8000000000000002#64 176 40 184#64 st_pb

theorem drop_opt_proto_inner_state_ct1Received_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec M A lim))
    (st_pb : V1State.Chunked.Ct1Received) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ct1Received st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  opt_proto_tail48_budget_steps 0x8000000000000003#64 160 56 168#64 st_pb

theorem drop_opt_proto_inner_state_ekSentCt1Received_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 285) (dropProtoChunkedEkSentCt1ReceivedSpec M A lim))
    (st_pb : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ekSentCt1Received st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  opt_proto_tail48_budget_steps 0x8000000000000004#64 144 72 152#64 st_pb

theorem drop_opt_proto_inner_state_noHeaderReceived_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 284) (dropProtoChunkedNoHeaderReceivedSpec M A lim))
    (st_pb : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.noHeaderReceived st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  opt_proto_tail48_budget_steps 0x8000000000000005#64 96 120 104#64 st_pb

theorem drop_opt_proto_inner_state_headerReceived_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 283) (dropProtoChunkedHeaderReceivedSpec M A lim))
    (st_pb : V1State.Chunked.HeaderReceived) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.headerReceived st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  opt_proto_tail48_budget_steps 0x8000000000000006#64 120 96 128#64 st_pb

end PlacedSimpleVariants

/-! ## Compound Variants of Block `267` (`ekReceivedCt1Sampled`, `keysUnsampled`, `ct2Sampled`) -/

theorem drop_opt_proto_inner_state_ekReceivedCt1Sampled_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hct1_sent : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim))
    (hpoly_enc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (st_pb : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ekReceivedCt1Sampled st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hct1_sent hpoly_enc ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  refine seq_clean_evs (mid := (blkPl_267).base + 664#64)
    (P_evs := fun evs sm =>
      ((a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 128 ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 136#64) (st_pb.sendingCt1.map pbToProtoPolyEncoder) ∗
        memRegion (a + 192#64) 32) ∗
      optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentEkReceivedAt_none, h16]
      apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
      wp_steps
      have hnone128 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 120 ⊢ memRegion (a + 8#64) 128 := by
        rw [← h16]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc (a + 8#64)
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      dsimp only [optProtoInnerStateJumpTablePlacedExpanded, optProtoInnerStateJumpTableSym]
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A.repAlloc (a + 8#64) u) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A.repAlloc (a + 8#64) cap ptr u) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hct1_sent (⟨a + 8#64, u⟩, st)
      rw [hsp_v]
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
      rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
      apply sepWP_evs_inst w hevs_w
      wp_steps
      dsimp only [protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTablePlacedExpanded,
        optProtoInnerStateJumpTableSym]
      refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx0_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    have hjoin184 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 56 ⊢ memRegion (a + 8#64) 184 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 184 ∗ memRegion (a + 192#64) 32 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000008#64 184 32 192#64 (BitVec.add_assoc a 8#64 184#64).symm rfl
    cases hct1 : st_pb.sendingCt1 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]
      refine sepWP_close_drop
        (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim st1 sf ∗ stackAt s0.sp dropStack96)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        wp_steps
        have hnone56 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 48 ⊢ memRegion (a + 136#64) 56 := by
          rw [← h144]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 136#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        wp_done
      · rw [← jt_placed_eq_expanded] at hp
        simp only [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨evs1, ?_⟩
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨htr_f, hacp_f, hevs1⟩,
          Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
    | some enc =>
      conv => arg 4; dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 136#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 136#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hpoly_enc (⟨a + 136#64, pbToProtoPolyEncoder enc⟩, st1)
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine sepWP_close_drop
        (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim (M.stepEvents w st1) sf' ∗ stackAt s0.sp dropStack96)
        (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
        (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      rw [← jt_placed_eq_expanded] at hp
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs1 ++ w, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f', hevs1.append hevs_w⟩, ?_⟩
      have heq_st : M.stepEvents (evs1 ++ w) st = M.stepEvents w st1 := by
        simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      rw [heq_st]
      exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_opt_proto_inner_state_keysUnsampled_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.KeysUnsampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.keysUnsampled st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have hjoin224 : (a ↦₆₄ 0x8000000000000000#64) ∗ memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 160 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000000#64 56 160 64#64 (BitVec.add_assoc a 8#64 56#64).symm rfl
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  cases huc : st_pb.uc with
  | none =>
    have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
    conv => arg 4; dsimp only [optProtoUnchunkedKeysUnsampledAt]
    rw [h16]
    refine sepWP_close_drop
      (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
        A.pool lim st sf ∗ stackAt s0.sp dropStack96)
      ?_
      (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
    · wp_steps
      have hnone56 : ((a + 8#64) ↦₆₄ none2Cap) ∗ memRegion (a + 16#64) 48 ⊢ memRegion (a + 8#64) 56 := by
        rw [← h16]; exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (a + 8#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
      wp_done
    · rw [← jt_placed_eq_expanded] at hp
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨[], ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩,
        Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
  | some u =>
    have h56 : (a + 8#64) + 48#64 = a + 56#64 := BitVec.add_assoc a 8#64 48#64
    conv => arg 4; dsimp only [optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]
    rw [h56]
    cases hauth : u.auth with
    | none =>
      have hnone8 : optProtoAuthenticatorAt A.repAlloc (a + 8#64) none =
          ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 40 := by
        rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 8#64 8#64]; rfl
      rw [hnone8]
      refine sepWP_close_drop
        (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim st sf ∗ stackAt s0.sp dropStack96)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        refine SepWP.focus_weaken (optProtoAuthenticatorAt_8_none_entails_memRegion_56 A.repAlloc a u.epoch) (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        wp_done
      · rw [← jt_placed_eq_expanded] at hp
        simp only [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨[], ?_⟩
        simp only [sepConj_assoc, satisfies_pure_sepConj, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        exact ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩,
          Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 8#64) auth) (by sep_focus) ?_
      wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_8_eq]; wp_focus_pure; intro hga_lt
      have hne_none2 := cap_add_two_beq_zero_false hga_lt
      have hne_none1 := cap_add_one_beq_zero_false hga_lt
      refine seq_clean_evs (mid := (blkPl_267).base + 276#64)
        (P_evs := fun evs sm =>
          ((a ↦₆₄ 0x8000000000000000#64) ∗
            ((auth8HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗ ((a + 56#64) ↦₆₄ u.epoch)) ∗
            memRegion (a + 64#64) 160) ∗
          optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x0 = a)
        ?_ ?_
      · dsimp only [auth8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
          wp_steps
          dsimp only [auth8HeadersAt, vecCapPtrDealloc, optProtoInnerStateJumpTablePlacedExpanded,
            optProtoInnerStateJumpTableSym, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          refine align_pre_st (by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
              Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
            sep_ac_rfl) ?_
          wp_done
        · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
          wp_steps
          refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
          rw [hsp_v]
          have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
          rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
          wp_steps
          dsimp only [auth8HeadersAt, vecCapPtrDealloc, optProtoInnerStateJumpTablePlacedExpanded,
            optProtoInnerStateJumpTableSym, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          refine align_pre_st (by
            simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
            sep_ac_rfl) ?_
          wp_done
      · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx0_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        let st1 := M.stepEvents evs1 st
        dsimp only [auth8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · conv => arg 4; dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
          refine sepWP_close_drop
            (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
              A.pool lim st1 sf ∗ stackAt s0.sp dropStack96)
            ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · wp_steps
            refine SepWP.focus_weaken (auth8HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
            wp_done
          · rw [← jt_placed_eq_expanded] at hp
            simp only [sepExists_sepConj_left, satisfies_sepExists]
            refine ⟨evs1, ?_⟩
            simp only [sepConj_assoc, satisfies_pure_sepConj]
            exact ⟨⟨htr_f, hacp_f, hevs1⟩,
              Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
        · conv => arg 4; dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
          wp_steps
          refine SepWP.focus_weaken (auth8HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
          refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, st1)
          have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          have ⟨_, _, _, _, _, _, _⟩ := hacp_f
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_
          refine sepWP_close_drop
            (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
              A.pool lim (M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) st1) sf' ∗ stackAt s0.sp dropStack96)
            (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
            (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          rw [← jt_placed_eq_expanded] at hp
          simp only [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨evs1 ++ rustDeallocEvents ga.v2.cap.toNat 1, ?_⟩
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f', hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat)⟩, ?_⟩
          have heq_st : M.stepEvents (evs1 ++ rustDeallocEvents ga.v2.cap.toNat 1) st =
              M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) st1 := by
            simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_opt_proto_inner_state_ct2Sampled_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpoly_enc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (st_pb : V1State.Chunked.Ct2Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ct2Sampled st_pb))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpoly_enc ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
  refine proto_top_prologue_16 (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt2SampledAt]
  rw [h64]
  refine seq_clean_evs (mid := (blkPl_267).base + 600#64)
    (P_evs := fun evs sm =>
      ((a ↦₆₄ 0x800000000000000a#64) ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 8#64) (st_pb.sendingCt2.map pbToProtoPolyEncoder) ∗
        memRegion (a + 64#64) 56 ∗ memRegion (a + 120#64) 104) ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      have h72 : (a + 64#64) + 8#64 = a + 72#64 := BitVec.add_assoc a 64#64 8#64
      dsimp only [optProtoUnchunkedCt2SentAt]; rw [h72]
      apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
      wp_steps
      have hnone56 : ((a + 64#64) ↦₆₄ none2Cap) ∗ memRegion (a + 72#64) 48 ⊢ memRegion (a + 64#64) 56 := by
        rw [← h72]; exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (a + 64#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
    | some u =>
      have h112 : (a + 64#64) + 48#64 = a + 112#64 := BitVec.add_assoc a 64#64 48#64
      dsimp only [optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt]; rw [h112]
      cases hauth : u.auth with
      | none =>
        have hnone64 : optProtoAuthenticatorAt A.repAlloc (a + 64#64) none =
            ((a + 64#64) ↦₆₄ noneCap) ∗ memRegion (a + 72#64) 40 := by
          rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 64#64 8#64]; rfl
        rw [hnone64]
        apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
        wp_steps
        refine SepWP.focus_weaken (optProtoAuthenticatorAt_64_none_entails_memRegion_56 A.repAlloc a u.epoch) (by sep_focus) ?_
        refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        refine align_pre_st (by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
            Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
          sep_ac_rfl) ?_
        wp_done
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 64#64) auth) (by sep_focus) ?_
        wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_64_eq]; wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        refine seq_clean_evs (mid := (blkPl_267).base + 568#64)
          (P_evs := fun evs sm =>
            ((a ↦₆₄ 0x800000000000000a#64) ∗
              optProtoPolynomialEncoderAt A.repAlloc (a + 8#64) (st_pb.sendingCt2.map pbToProtoPolyEncoder) ∗
              ((auth64HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗ ((a + 112#64) ↦₆₄ u.epoch)) ∗
              memRegion (a + 120#64) 104) ∗
            optProtoInnerStateJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x0 = a)
          ?_ ?_
        · dsimp only [auth64HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
            wp_steps
            refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
                Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
          · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
            wp_steps
            refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
            rw [hsp_v]
            have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
            rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
            wp_steps
            refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by
              simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
        · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx0_a1⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
          let sta1 := M.stepEvents evsa1 st
          dsimp only [auth64HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_inst evsa1 hevsa1
            wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine sepWP_sync_pool sa1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by
              simp only [sta1, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
          · apply sepWP_evs_inst (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1)
              (hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat))
            wp_steps
            refine sepWP_sync_pool sa1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, sta1)
            rw [hsp_a1]
            have hacp_f : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
            rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
            wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            have heq_st : M.stepEvents (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1) st =
                M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1 := by
              simp only [sta1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            refine align_pre_st (by
              simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx0_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    have hjoin112 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 56 ⊢ memRegion (a + 8#64) 112 := by
      rw [← h64, ProofLib.memRegion_split (a + 8#64) 56 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 8#64) 112 ∗ memRegion (a + 120#64) 104 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x800000000000000a#64 112 104 120#64 (BitVec.add_assoc a 8#64 112#64).symm rfl
    cases hct2 : st_pb.sendingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [h16]
      refine sepWP_close_drop
        (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim st1 sf ∗ stackAt s0.sp dropStack96)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        have hnone56 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 48 ⊢ memRegion (a + 8#64) 56 := by
          rw [← h16]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 8#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        wp_done
      · simp only [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨evs1, ?_⟩
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨htr_f, hacp_f, hevs1⟩,
          Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 8#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 8#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hpoly_enc (⟨a + 8#64, pbToProtoPolyEncoder enc⟩, st1)
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine sepWP_close_drop
        (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents w st1) sf' ∗ stackAt s0.sp dropStack96)
        (by wp_done)
        (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs1 ++ w, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f', hevs1.append hevs_w⟩, ?_⟩
      have heq_st : M.stepEvents (evs1 ++ w) st = M.stepEvents w st1 := by
        simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      rw [heq_st]
      exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
