/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvictBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPackBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded DH Step Commit Sub-Segments 1 & 2 (`+0x8ac → +0xa84`)

Defines the deterministic allocator event list `dhCommitStep12Events` (`PublicKey::serialize`,
`__rust_alloc(33, 1)`, `ChainKey::to_pb`), `VmPreserved` basic-block `SepWP` bundles for blocks
`130` and `433`, and total-correctness / conditional-OOM `dhCommit_step1_2` theorems over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open scoped CryptoVerification.RustHeap
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey PublicKey RootKey)
open CryptoVerification (LibsignalPlacement lsRustAllocSym lsRustNoAllocShimSym lsmpl)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes optChainKeyAt)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf chainKeyToPbStack chainKeyToPbStackX extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_131 blkPC_434 blkPl_131 blkPl_434)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (add_assoc_const cell32_to_memRegion_4 cell_to_memRegion_8 cells_2_to_memRegion_16 chainKeyBytes_length elim_memRegion_16 elim_memRegion_32 elim_memRegion_4 elim_memRegion_8 optChainKeyAt_eq_exists_bytes optChainKeyHeap optChainKeyTailBytes pointsToBytes_32_eq_4_8_8_8_4 pointsToBytes_chainKey_eq_cells publicKey_serialize_length publicKey_serialize_ne_nil saturating_sub_one_u32 stackAt_split_from)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceSimp (ReachesOrPanicOom)

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  publicKeySerializeEvents PublicKeySerializeEnv fitsEnv_publicKeySerialize_iff
  publicKeySerializeSpecWithStack publicKeySerializeSpec publicKeySerializeSpecX
  chainKeyToPbEvents ChainKeyToPbEnv fitsEnv_chainKeyToPb_iff
  chainKeyToPbSpecWithStack chainKeyToPbSpec chainKeyToPbSpecX
  noAllocShimBudgetSpec framelessMemcpyBudgetSpec
)

/-! ## 1. Allocator Event List & Envelope for Steps 1 & 2 -/

/-- Deterministic `AllocEvent` list emitted by `dhCommit` Steps 1 & 2 (`+0x8ac → +0xa84`):
    `PublicKey::serialize` (`33`B), `__rust_alloc(33, 1)`, and `ChainKey::to_pb` (`32`B). -/
def dhCommitStep12Events : List AllocEvent :=
  publicKeySerializeEvents ++ rustAllocEvents 33 1 ++ chainKeyToPbEvents

/-- Singleton allocation envelope for `dhCommit` Steps 1 & 2. -/
def DhCommitStep12Env (evs : List AllocEvent) : Prop :=
  evs = dhCommitStep12Events

theorem fitsEnv_dhCommitStep12_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st DhCommitStep12Env ↔ FitsEvents M lim st dhCommitStep12Events :=
  ⟨fun h => h _ rfl, fun h _ he => he ▸ h⟩

/-- Decompose `FitsEvents M lim st0 dhCommitStep12Events` into the three sequential callee
    budget obligations (`PublicKey::serialize`, `__rust_alloc(33, 1)`, `ChainKey::to_pb`) and
    equate the three-step `M.stepEvents` chain with `M.stepEvents dhCommitStep12Events st0`. -/
theorem fitsEvents_dhCommitStep12_elim {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    (h : FitsEvents M lim st0 dhCommitStep12Events) :
    let st1 := M.stepEvents publicKeySerializeEvents st0
    let st2 := M.stepEvents (rustAllocEvents 33 1) st1
    FitsEnv M lim st0 PublicKeySerializeEnv ∧
    FitsEvents M lim st1 (rustAllocEvents 33 1) ∧
    FitsEnv M lim st2 ChainKeyToPbEnv ∧
    M.stepEvents chainKeyToPbEvents st2 = M.stepEvents dhCommitStep12Events st0 := by
  dsimp only [dhCommitStep12Events] at h ⊢
  rw [List.append_assoc, fitsEvents_append] at h
  rcases h with ⟨h1, h23⟩
  rw [fitsEvents_append] at h23
  rcases h23 with ⟨h2, h3⟩
  rw [List.append_assoc]
  refine ⟨fitsEnv_publicKeySerialize_iff.mpr h1, h2, fitsEnv_chainKeyToPb_iff.mpr h3, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append]

/-! ## 2. `VmPreserved`-Carrying Basic-Block `SepWP` Predicates & Block `130` / `433` Instances -/

abbrev CommitStep1VmWp (prog : Program) (entry pkSerEntry : BitVec 64) : Prop :=
  ∀ (sp msgA : BitVec 64) (scIdx : BitVec 32)
    (oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0 : BitVec 32)
    (oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3
     v440 v448 v4e0 v4e8 v4f0 v4f8 : BitVec 64) (s : State),
    s.pc = entry + 0x8ac#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x22 = msgA → s.readReg64 .x25 = sp + 0x190#64 →
    s.readReg64 .x27 = sp + 0x38#64 → s.readReg64 .x28 = sp + 0x3d0#64 →
    SepWP prog pkSerEntry s
      (((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦₃₂ oldRk0) ∗ ((sp + 0xbc#64) ↦₆₄ oldRk4) ∗
       ((sp + 0xc4#64) ↦₆₄ oldRk12) ∗ ((sp + 0xcc#64) ↦₆₄ oldRk20) ∗ ((sp + 0xd4#64) ↦₃₂ oldRk28) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗ ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗ ((sp + 0x1a8#64) ↦₆₄ rk20) ∗ ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗ ((sp + 0x1bc#64) ↦₆₄ sck1) ∗ ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗ ((sp + 0x1d0#64) ↦₆₄ sck3) ∗ ((sp + 0x440#64) ↦₆₄ v440) ∗
       ((sp + 0x448#64) ↦₆₄ v448) ∗ ((sp + 0x4e0#64) ↦₆₄ v4e0) ∗ ((sp + 0x4e8#64) ↦₆₄ v4e8) ∗
       ((sp + 0x4f0#64) ↦₆₄ v4f0) ∗ ((sp + 0x4f8#64) ↦₆₄ v4f8))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = msgA + 0x38#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = msgA ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sck16.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = sp + 0x38#64 ∧
        sf.readReg64 .x28 = sp + 0x3d0#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = entry + 0x8fc#64 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
          ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗ ((sp + 0xd4#64) ↦₃₂ rk28) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          ((sp + 0x194#64) ↦₃₂ rk0) ∗ ((sp + 0x198#64) ↦₆₄ rk4) ∗ ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
          ((sp + 0x1a8#64) ↦₆₄ rk20) ∗ ((sp + 0x1b0#64) ↦₃₂ rk28) ∗ ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
          ((sp + 0x1bc#64) ↦₆₄ sck1) ∗ ((sp + 0x1c4#64) ↦₃₂ sck16) ∗ ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
          ((sp + 0x1d0#64) ↦₆₄ sck3) ∗ ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗ ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1)))

abbrev CommitStep2PreShimVmWp (prog : Program) (entry shimEntry : BitVec 64) : Prop :=
  ∀ (sp boxPtr vSp0 : BitVec 64) (vSp8 sck16 : BitVec 32) (s : State),
    s.pc = entry + 0x8fc#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x0 = boxPtr → s.readReg64 .x1 = 33#64 → s.readReg64 .x24 = sck16.zeroExtend 64 →
    SepWP prog shimEntry s ((sp ↦₆₄ vSp0) ∗ ((sp + 8#64) ↦₃₂ vSp8))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sck16.zeroExtend 64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0x9f0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ (sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16)))

abbrev CommitStep2PreAllocVmWp (prog : Program) (entry allocEntry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (s : State),
    s.pc = entry + 0x9f0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x26 = 33#64 →
    SepWP prog allocEntry s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = 33#64 ∧ sf.readReg64 .x1 = 1#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = 1#64 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa00#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ (P_f ⊢ emp))

abbrev CommitStep2PostAllocVmWp (prog : Program) (entry memcpyEntry : BitVec 64) : Prop :=
  ∀ (sp srkPtr boxPtr : BitVec 64) (s : State),
    s.pc = entry + 0xa00#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x0 = srkPtr → srkPtr ≠ 0#64 → s.readReg64 .x26 = 33#64 →
    SepWP prog memcpyEntry s (sp ↦₆₄ boxPtr)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = srkPtr ∧ sf.readReg64 .x1 = boxPtr ∧ sf.readReg64 .x2 = 33#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = srkPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa18#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ (P_f ⊢ (sp ↦₆₄ boxPtr)))

abbrev CommitStep2ToPbVmWp (prog : Program) (entry toPbEntry : BitVec 64) : Prop :=
  ∀ (sp : BitVec 64) (s : State),
    s.pc = entry + 0xa18#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x25 = sp + 0x190#64 →
    SepWP prog toPbEntry s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x3d0#64 ∧ sf.readReg64 .x8 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa84#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ (P_f ⊢ emp))

/-- Relocatable `[LibsignalPlacement]` `VmPreserved` basic-block `SepWP` bundle for Steps 1 & 2. -/
structure DhCommitStep12BlockWp [LibsignalPlacement] (prog : Program) (entry : BitVec 64) : Prop where
  step1 : CommitStep1VmWp prog entry (lsmpl.base 205)
  step2_pre_shim : CommitStep2PreShimVmWp prog entry (lsmpl.ρ lsRustNoAllocShimSym)
  step2_pre_alloc : CommitStep2PreAllocVmWp prog entry (lsmpl.ρ lsRustAllocSym)
  step2_post_alloc : CommitStep2PostAllocVmWp prog entry (lsmpl.ρ "memcpy")
  step2_to_pb : CommitStep2ToPbVmWp prog entry (lsmpl.base 22)

section BlockWpInstances

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.writeReg64_trace, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.writeReg32_trace, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.setPC_trace,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.setPState_trace, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.setMem_trace, State.trace_writeVReg128,
    *])

local macro "wp_done_vm_reg" hsp_al:ident : tactic =>
  `(tactic|
    by_vm_steps (
      wp_steps
      refine SepWP.done (by rfl) (by wp_reg) ?_
      refine And.intro (by wp_reg) ?_
      refine And.intro (by wp_reg)
        (And.intro (CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.spAligned_of_sp_eq (by wp_reg) $hsp_al) ?_)
      repeat' (refine And.intro ?_ ?_ <;> [wp_reg; skip])
      try rw [← saturating_sub_one_u32 _]
      exact Entails.refl _))

set_option maxHeartbeats 800000 in
theorem dhCommitStep12BlockWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitStep12BlockWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base where
  step1 := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28
    wp_done_vm_reg hsp_align
  step2_pre_shim := by
    intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24
    wp_done_vm_reg hsp_align
  step2_pre_alloc := by
    intro _ s hpc hrun hsp hsp_align hx26
    wp_done_vm_reg hsp_align
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne
    wp_done_vm_reg hsp_align
  step2_to_pb := by
    intro _ s hpc hrun hsp hsp_align hx25
    wp_done_vm_reg hsp_align

set_option maxHeartbeats 800000 in
theorem dhCommitStep12BlockWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitStep12BlockWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base where
  step1 := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28
    wp_done_vm_reg hsp_align
  step2_pre_shim := by
    intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24
    wp_done_vm_reg hsp_align
  step2_pre_alloc := by
    intro _ s hpc hrun hsp hsp_align hx26
    wp_done_vm_reg hsp_align
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne
    wp_done_vm_reg hsp_align
  step2_to_pb := by
    intro _ s hpc hrun hsp hsp_align hx25
    wp_done_vm_reg hsp_align

end BlockWpInstances

/-! ## 3. Total-Correctness `Steps` Continuation Combinators -/

private theorem steps_of_sepWP {prog : Program} {s : State}
    {target : BitVec 64} {Pre Rest : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ Rest) →
      PostWP s1 P_out →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 P_out hpc1 hrun1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hm1 hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem steps_of_call_no_panic {α : Type} {prog : Program} {s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Rest : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ Rest) →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg Rest s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

/-! ## 4. Budget-Threaded Sub-Segments 1 & 2 Composition (`+0x8ac → +0xa84`) -/

/-- Stack-parameterized budget-threaded Steps 1 & 2 (`+0x8ac → +0xa84`): commits `root_key`
    and `previous_counter`, stages `senderChainKey` pieces, calls `PublicKey::serialize`,
    allocates and copies the 33-byte `sender_ratchet_key` buffer via `rustCliAllocNoOomSpec`,
    and calls `ChainKey::to_pb` on `receiverChainKey`, advancing `st0` by `dhCommitStep12Events`
    with zero OOM or panic branches under `FitsEvents M lim st0 dhCommitStep12Events`. -/
theorem dhCommit_step1_2_of_wp [LibsignalPlacement] {M : AllocCostModel} {prog : Program}
    {entry pkSerEntry shimEntry allocEntry memcpyEntry toPbEntry : BitVec 64}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hookStack : Nat)
    (hstack_lo : allocHookStack ≤ hookStack)
    (hstack_hi : hookStack + 48 < 2 ^ 64)
    (hwp_1 : CommitStep1VmWp prog entry pkSerEntry)
    (hwp_pre_shim : CommitStep2PreShimVmWp prog entry shimEntry)
    (hwp_pre_alloc : CommitStep2PreAllocVmWp prog entry allocEntry)
    (hwp_post_alloc : CommitStep2PostAllocVmWp prog entry memcpyEntry)
    (hwp_to_pb : CommitStep2ToPbVmWp prog entry toPbEntry)
    (hPkSer : subroutine_ok prog pkSerEntry (publicKeySerializeSpecWithStack M A lim hookStack))
    (hShim : subroutine_ok prog shimEntry noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog allocEntry (rustCliAllocNoOomSpec M A lim false))
    (hMemcpy : subroutine_ok prog memcpyEntry framelessMemcpyBudgetSpec)
    (hToPb : subroutine_ok prog toPbEntry (chainKeyToPbSpecWithStack M A lim hookStack))
    (hfits : FitsEvents M lim st0 dhCommitStep12Events)
    (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey)
    (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64)
    (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x440#64) 16 ∗
       memRegion (sp + 0x4e0#64) 32 ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool lim st0 s ∗
       stackAt sp (hookStack + 48)) ∗ (Frame ∗ R))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let sckBs := chainKeyBytes senderChainKey
    let sck0 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (sckBs.take 8)
    let sck1 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((sckBs.drop 8).take 8)
    let sck16 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack32 ((sckBs.drop 16).take 4)
    let sck2 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((sckBs.drop 20).take 8)
    let sck3 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (sckBs.drop 28)
    ∃ sf, Steps prog s sf ∧
      ∃ boxPtr srkPtr ckPtr : BitVec 64, ∃ pad : List (BitVec 8),
        srkPtr ≠ 0 ∧
        pad.length = 4 ∧
        sf.pc = entry + 0xa84#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = msgA ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧
        sf.readReg64 .x28 = srkPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          ((sp ↦₆₄ boxPtr) ∗
           ((sp + 8#64) ↦₃₂ sck16) ∗
           ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
           ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
           ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
           ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
           memRegion (sp + 0x1b0#64) 40 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
           ((sp + 0x440#64) ↦₆₄ sck0) ∗
           ((sp + 0x448#64) ↦₆₄ sck1) ∗
           ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
           ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
           ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
           ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
           ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
           (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
           (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
           optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
           A.pool lim (M.stepEvents dhCommitStep12Events st0) sf ∗
           stackAt sp (hookStack + 48)) ∗ (Frame ∗ R)) := by
  intro sckBs sck0 sck1 sck16 sck2 sck3
  obtain ⟨hfit_pk, hfit_alloc, hfit_pb, hst_final⟩ := fitsEvents_dhCommitStep12_elim hfits
  set st1 := M.stepEvents publicKeySerializeEvents st0
  set st2 := M.stepEvents (rustAllocEvents 33 1) st1
  have hm_440 : s.mem ⊨
      memRegion (sp + 0x440#64) 16 ∗
      (memRegion (sp + 0x4e0#64) 32 ∗
       memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool lim st0 s ∗
       stackAt sp (hookStack + 48) ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    sep_ac_rfl
  obtain ⟨v440, v448, hm_440⟩ := elim_memRegion_16 hm_440
  have hm_4e0 : s.mem ⊨
      memRegion (sp + 0x4e0#64) 32 ∗
      (((sp + 0x440#64) ↦₆₄ v440) ∗ ((sp + 0x440#64 + 8#64) ↦₆₄ v448) ∗
       memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       A.pool lim st0 s ∗
       stackAt sp (hookStack + 48) ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_440
    sep_ac_rfl
  obtain ⟨v4e0, v4e8, v4f0, v4f8, hm_4e0⟩ := elim_memRegion_32 hm_4e0
  have hrk0_len : (keyToBytes32 0).length = 32 := by simp [keyToBytes32]
  have hrk_len : (keyToBytes32 finalRootKey).length = 32 := by simp [keyToBytes32]
  have hb8_cells := pointsToBytes_32_eq_4_8_8_8_4 (sp + 0xb8#64) hrk0_len
  have h194_cells := pointsToBytes_32_eq_4_8_8_8_4 (sp + 0x194#64) hrk_len
  have h1b4_cells := pointsToBytes_chainKey_eq_cells (sp + 0x1b4#64) senderChainKey
  set oldRk0 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack32 ((keyToBytes32 0).take 4)
  set oldRk4 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (((keyToBytes32 0).drop 4).take 8)
  set oldRk12 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (((keyToBytes32 0).drop 12).take 8)
  set oldRk20 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (((keyToBytes32 0).drop 20).take 8)
  set oldRk28 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack32 ((keyToBytes32 0).drop 28)
  set rk0 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack32 ((keyToBytes32 finalRootKey).take 4)
  set rk4 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (((keyToBytes32 finalRootKey).drop 4).take 8)
  set rk12 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (((keyToBytes32 finalRootKey).drop 12).take 8)
  set rk20 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (((keyToBytes32 finalRootKey).drop 20).take 8)
  set rk28 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack32 ((keyToBytes32 finalRootKey).drop 28)
  have eb1 := add_assoc_const sp 0xb8#64 4#64 0xbc#64
  have eb2 := add_assoc_const sp 0xb8#64 12#64 0xc4#64
  have eb3 := add_assoc_const sp 0xb8#64 20#64 0xcc#64
  have eb4 := add_assoc_const sp 0xb8#64 28#64 0xd4#64
  rw [eb1, eb2, eb3, eb4] at hb8_cells
  have er1 := add_assoc_const sp 0x194#64 4#64 0x198#64
  have er2 := add_assoc_const sp 0x194#64 12#64 0x1a0#64
  have er3 := add_assoc_const sp 0x194#64 20#64 0x1a8#64
  have er4 := add_assoc_const sp 0x194#64 28#64 0x1b0#64
  rw [er1, er2, er3, er4] at h194_cells
  have es1 := add_assoc_const sp 0x1b4#64 8#64 0x1bc#64
  have es2 := add_assoc_const sp 0x1b4#64 16#64 0x1c4#64
  have es3 := add_assoc_const sp 0x1b4#64 20#64 0x1c8#64
  have es4 := add_assoc_const sp 0x1b4#64 28#64 0x1d0#64
  rw [es1, es2, es3, es4] at h1b4_cells
  have h440_off := add_assoc_const sp 0x440#64 8#64 0x448#64
  have ee1 := add_assoc_const sp 0x4e0#64 8#64 0x4e8#64
  have ee2 := add_assoc_const sp 0x4e0#64 16#64 0x4f0#64
  have ee3 := add_assoc_const sp 0x4e0#64 24#64 0x4f8#64
  rw [h440_off, ee1, ee2, ee3, hb8_cells, h194_cells, h1b4_cells] at hm_4e0
  have hm_step1 : s.mem ⊨
      (((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦₃₂ oldRk0) ∗
       ((sp + 0xbc#64) ↦₆₄ oldRk4) ∗
       ((sp + 0xc4#64) ↦₆₄ oldRk12) ∗
       ((sp + 0xcc#64) ↦₆₄ oldRk20) ∗
       ((sp + 0xd4#64) ↦₃₂ oldRk28) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x194#64) ↦₃₂ rk0) ∗
       ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
       ((sp + 0x1a8#64) ↦₆₄ rk20) ∗
       ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
       ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
       ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
       ((sp + 0x1d0#64) ↦₆₄ sck3) ∗
       ((sp + 0x440#64) ↦₆₄ v440) ∗
       ((sp + 0x448#64) ↦₆₄ v448) ∗
       ((sp + 0x4e0#64) ↦₆₄ v4e0) ∗
       ((sp + 0x4e8#64) ↦₆₄ v4e8) ∗
       ((sp + 0x4f0#64) ↦₆₄ v4f0) ∗
       ((sp + 0x4f8#64) ↦₆₄ v4f8)) ∗
      ((memRegion sp 12 ∗
        ((sp + 0x190#64) ↦₃₂ 0#32) ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        A.pool lim st0 s ∗
        stackAt sp (hookStack + 48) ∗
        Frame) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_4e0
    sep_ac_rfl
  refine steps_of_sepWP
    (hwp_1 sp msgA scIdx
      oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0
      oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3
      v440 v448 v4e0 v4e8 v4f0 v4f8
      s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28)
    hm_step1 hL ?_
  intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
  rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, _hx27_1, _hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  rw [← A.pool_transport lim st0 s s1 hvm1] at hm1'
  have hb8_final : ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) =
      ((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
      ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗
      ((sp + 0xd4#64) ↦₃₂ rk28) := by
    rw [pointsToBytes_32_eq_4_8_8_8_4 (sp + 0xb8#64) hrk_len, eb1, eb2, eb3, eb4]
  have h190_1b0_reg :
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦₃₂ rk0) ∗
       ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
       ((sp + 0x1a8#64) ↦₆₄ rk20)) ⊢ memRegion (sp + 0x190#64) 32 := by
    have hsplit32 := memRegion_split (sp + 0x190#64) 8 24 (by decide)
    rw [show (8 + 24 : Nat) = 32 from rfl] at hsplit32
    have hsplit8 := memRegion_split (sp + 0x190#64) 4 4 (by decide)
    rw [show (4 + 4 : Nat) = 8 from rfl] at hsplit8
    have hsplit24 := memRegion_split (sp + 0x198#64) 8 16 (by decide)
    rw [show (8 + 16 : Nat) = 24 from rfl] at hsplit24
    have h190_4 := add_assoc_const sp 0x190#64 (BitVec.ofNat 64 4) 0x194#64
    have h190_8 := add_assoc_const sp 0x190#64 (BitVec.ofNat 64 8) 0x198#64
    have h198_8 := add_assoc_const sp 0x198#64 (BitVec.ofNat 64 8) 0x1a0#64
    rw [hsplit32, hsplit8, h190_4, h190_8, hsplit24, h198_8]
    have ha0 := cells_2_to_memRegion_16 (sp + 0x1a0#64) rk12 rk20
    have ha0_off := add_assoc_const sp 0x1a0#64 8#64 0x1a8#64
    rw [ha0_off] at ha0
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono
        (sepConj_mono (cell32_to_memRegion_4 _ 0#32) (cell32_to_memRegion_4 _ rk0))
        (sepConj_mono (cell_to_memRegion_8 _ rk4) ha0))
    sep_ac_rfl
  have h1b0_40_reg :
      (((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
       ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
       ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
       ((sp + 0x1d0#64) ↦₆₄ sck3)) ⊢ memRegion (sp + 0x1b0#64) 40 := by
    have hsplit40 := memRegion_split (sp + 0x1b0#64) 4 36 (by decide)
    rw [show (4 + 36 : Nat) = 40 from rfl] at hsplit40
    have h1b0_4 := add_assoc_const sp 0x1b0#64 (BitVec.ofNat 64 4) 0x1b4#64
    rw [hsplit40, h1b0_4]
    have hsck_reg : ((sp + 0x1b4#64) ↦ₛ sckBs) ⊢ memRegion (sp + 0x1b4#64) 36 := by
      have h := pointsToBytes_entails_memRegion (sp + 0x1b4#64) sckBs
      rw [chainKeyBytes_length senderChainKey] at h
      exact h
    rw [h1b4_cells] at hsck_reg
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono (cell32_to_memRegion_4 _ rk28) hsck_reg)
    sep_ac_rfl
  have hstk_ser := stackAt_split_from sp (hookStack + 48) (hookStack + 32) (by omega) hstack_hi
  have hm_ser : s1.mem ⊨
      (publicKeySerializeSpecWithStack M A lim hookStack).pre (⟨msgA + 0x38#64, srk⟩, st0) s1 ∗
      ((memRegion sp 12 ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
        ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗
        memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗
        ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
        ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
        ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        memRegion (sp - BitVec.ofNat 64 (hookStack + 48)) ((hookStack + 48) - (hookStack + 32)) ∗
        Frame) ∗ R) := by
    dsimp only [publicKeySerializeSpecWithStack]
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hfit_pk⟩, ?_⟩
    rw [hb8_final]
    have hpull_s1 : s1.mem ⊨
        (((sp + 0x190#64) ↦₃₂ 0#32) ∗
         ((sp + 0x194#64) ↦₃₂ rk0) ∗
         ((sp + 0x198#64) ↦₆₄ rk4) ∗
         ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
         ((sp + 0x1a8#64) ↦₆₄ rk20)) ∗
        (((sp + 0x1b0#64) ↦₃₂ rk28) ∗
         ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
         ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
         ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
         ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
         ((sp + 0x1d0#64) ↦₆₄ sck3)) ∗
        (((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
         A.pool lim st0 s1 ∗
         stackAt sp (hookStack + 48) ∗
         memRegion sp 12 ∗
         ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
         (((sp + 0xb8#64) ↦₃₂ rk0) ∗ ((sp + 0xbc#64) ↦₆₄ rk4) ∗
          ((sp + 0xc4#64) ↦₆₄ rk12) ∗ ((sp + 0xcc#64) ↦₆₄ rk20) ∗
          ((sp + 0xd4#64) ↦₃₂ rk28)) ∗
         ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
         ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
         ((sp + 0x440#64) ↦₆₄ sck0) ∗
         ((sp + 0x448#64) ↦₆₄ sck1) ∗
         ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
         ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
         ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
         ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
         Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      sep_ac_rfl
    have hreg_s1 := Satisfies.mono
      (sepConj_mono h190_1b0_reg (sepConj_mono_left h1b0_40_reg))
      hpull_s1
    rw [hstk_ser] at hreg_s1
    refine Satisfies.mono (Entails.of_eq ?_) hreg_s1
    sep_ac_rfl
  refine steps_of_call_no_panic hPkSer hpc1 hrun1 hsp_align1 hx30_1 hm_ser hL1
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hL2 hm2
  dsimp only [publicKeySerializeSpecWithStack] at hm2
  rw [hsp1] at hm2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
  rcases hm2 with ⟨⟨hx1_2, htr2⟩, hm2⟩
  set boxPtr := s2.readReg64 .x0
  have hser_ne_nil : srk.serialize ≠ [] := publicKey_serialize_ne_nil srk
  have hser_len : srk.serialize.length = 33 := publicKey_serialize_length srk
  have hbox_buf : boxU8Buf A.repAlloc boxPtr srk.serialize =
      (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) := by
    unfold boxU8Buf
    simp only [hser_ne_nil, ↓reduceIte, hser_len, A.repAlloc_live]
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf] at hm2
  rw [hbox_buf] at hm2
  have hm2_sp : s2.mem ⊨
      memRegion sp 12 ∗
      ((⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool lim st1 s2 ∗ stackAt sp (hookStack + 48) ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
       memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ (Frame ∗ R)) := by
    rw [hstk_ser]; refine Satisfies.mono (Entails.of_eq ?_) hm2; sep_ac_rfl
  have hsplit12 := memRegion_split sp 8 4 (by decide)
  rw [show (8 + 4 : Nat) = 12 from rfl] at hsplit12
  rw [hsplit12, sepConj_assoc] at hm2_sp
  obtain ⟨vSp0, hm2_sp⟩ := elim_memRegion_8 hm2_sp
  have hm2_sp8 : s2.mem ⊨
      memRegion (sp + 8#64) 4 ∗
      ((sp ↦₆₄ vSp0) ∗
       (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool lim st1 s2 ∗ stackAt sp (hookStack + 48) ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
       memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm2_sp; sep_ac_rfl
  obtain ⟨vSp8, hm2_sp8⟩ := elim_memRegion_4 hm2_sp8
  have hm_pre_shim : s2.mem ⊨
      ((sp ↦₆₄ vSp0) ∗ ((sp + 8#64) ↦₃₂ vSp8)) ∗
      (((A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool lim st1 s2 ∗ stackAt sp (hookStack + 48) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R) := by
    have hdrop_pure :
        (⌜boxPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize))) ⊢
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) :=
      Entails.pure_left (fun _ => Entails.refl _)
    have hm2_sp8' := Satisfies.mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop_pure))) hm2_sp8
    refine Satisfies.mono (Entails.of_eq ?_) hm2_sp8'; sep_ac_rfl
  refine steps_of_sepWP
    (hwp_pre_shim sp boxPtr vSp0 vSp8 sck16
      s2 hpc2 hrun2 (by reg_chain) hsp_align2 rfl hx1_2 (by reg_chain))
    hm_pre_shim hL2 ?_
  intro s3 P3 hpc3 hrun3 hL3 hm3 hpost3
  rcases hpost3 with ⟨hvm3, hsp3, hsp_align3, htr3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, _hx24_3, hx25_3, hx26_3, hx27_3, _hx28_3, hx29_3, hx30_3, hvregs_3, hP3⟩
  have hm3' := Satisfies.mono (sepConj_mono_left hP3) hm3
  rw [← A.pool_transport lim st1 s2 s3 hvm3] at hm3'
  have hm_shim : s3.mem ⊨
      noAllocShimBudgetSpec.pre () s3 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool lim st1 s3 ∗ stackAt sp (hookStack + 48) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R) := by
    dsimp only [noAllocShimBudgetSpec]; rw [emp_sepConj]
    refine Satisfies.mono (Entails.of_eq ?_) hm3'; sep_ac_rfl
  refine steps_of_call_no_panic hShim hpc3 hrun3 hsp_align3 hx30_3 hm_shim hL3
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s4 hpc4 hrun4 hsp4 hsp_align4 hcs4 hL4 hm4
  dsimp only [noAllocShimBudgetSpec] at hm4
  rw [satisfies_pure_sepConj] at hm4
  rcases hm4 with ⟨⟨htr4, hvm4⟩, hm4⟩
  rw [← A.pool_transport lim st1 s3 s4 hvm4] at hm4
  have hm_pre_alloc : s4.mem ⊨
      emp ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗ A.pool lim st1 s4 ∗ stackAt sp (hookStack + 48) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R) := by
    rw [emp_sepConj]; exact hm4
  refine steps_of_sepWP
    (hwp_pre_alloc sp s4 hpc4 hrun4 (by reg_chain) hsp_align4 (by reg_chain))
    hm_pre_alloc hL4 ?_
  intro s5 P5 hpc5 hrun5 hL5 hm5 hpost5
  rcases hpost5 with ⟨hvm5, hsp5, hsp_align5, htr5, hx0_5, hx1_5,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, _hx24_5, hx25_5, hx26_5, _hx27_5, _hx28_5,
    hx29_5, hx30_5, hvregs_5, hP5⟩
  have hm5' := Satisfies.mono (sepConj_mono_left hP5) hm5
  rw [emp_sepConj, ← A.pool_transport lim st1 s4 s5 hvm5] at hm5'
  have hstk_alloc := stackAt_split_from sp (hookStack + 48) allocHookStack (by omega) hstack_hi
  have hm_alloc : s5.mem ⊨
      (rustCliAllocNoOomSpec M A lim false).pre (33, 1, st1) s5 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        memRegion (sp - BitVec.ofNat 64 (hookStack + 48)) ((hookStack + 48) - allocHookStack) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R) := by
    dsimp only [rustCliAllocNoOomSpec]
    rw [hstk_alloc] at hm5'
    rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [hx0_5]; rfl, by rw [hx1_5]; rfl, ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩, hfit_alloc, hx30_5.symm ▸ hlr_alloc⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm5'; sep_ac_rfl
  refine steps_of_call_no_panic hAlloc hpc5 hrun5 hsp_align5 hx30_5 hm_alloc hL5
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s6 hpc6 hrun6 hsp6 hsp_align6 hcs6 hL6 hm6
  dsimp only [rustCliAllocNoOomSpec] at hm6
  simp only [Bool.false_eq_true, ↓reduceIte] at hm6
  set srkPtr := s6.readReg64 .x0
  rw [hsp5] at hm6
  have hm6_pull : s6.mem ⊨
      ⌜AllocCallPreserved s5 s6 ∧ srkPtr ≠ 0#64 ∧ srkPtr.toNat % 1 = 0⌝ ∗
      ((sp ↦₆₄ boxPtr) ∗
       ((memRegion srkPtr 33 ∗ A.live srkPtr 33 1 ∗ A.pool lim st2 s6 ∗ stackAt sp (hookStack + 48) ∗
         ((sp + 8#64) ↦₃₂ sck16) ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
         ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
         ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
         ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
         memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
         ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
         ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
         ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
         ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R)) := by
    rw [hstk_alloc]; refine Satisfies.mono (Entails.of_eq ?_) hm6; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm6_pull
  rcases hm6_pull with ⟨⟨hacp6, hsrk0, _halign6⟩, hm_post_alloc⟩
  have htr6 : s6.trace = s5.trace := hacp6.2.1
  refine steps_of_sepWP
    (hwp_post_alloc sp srkPtr boxPtr
      s6 hpc6 hrun6 (by reg_chain) hsp_align6 rfl hsrk0 (by reg_chain))
    hm_post_alloc hL6 ?_
  intro s7 P7 hpc7 hrun7 hL7 hm7 hpost7
  rcases hpost7 with ⟨hvm7, hsp7, hsp_align7, htr7, hx0_7, hx1_7, hx2_7,
    hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, _hx24_7, hx25_7, hx26_7, hx27_7, hx28_7,
    hx29_7, hx30_7, hvregs_7, hP7⟩
  have hm7' := Satisfies.mono (sepConj_mono_left hP7) hm7
  rw [← A.pool_transport lim st2 s6 s7 hvm7] at hm7'
  have hm_memcpy : s7.mem ⊨
      framelessMemcpyBudgetSpec.pre (srkPtr, boxPtr, srk.serialize) s7 ∗
      (((sp ↦₆₄ boxPtr) ∗ A.live srkPtr 33 1 ∗ A.live boxPtr 33 1 ∗
        A.pool lim st2 s7 ∗ stackAt sp (hookStack + 48) ∗
        ((sp + 8#64) ↦₃₂ sck16) ∗ ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R) := by
    dsimp only [framelessMemcpyBudgetSpec]
    rw [hser_len, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_7, hx1_7, by rw [hx2_7]; rfl⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm7'; sep_ac_rfl
  refine steps_of_call_no_panic hMemcpy hpc7 hrun7 hsp_align7 hx30_7 hm_memcpy hL7
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s8 hpc8 hrun8 hsp8 hsp_align8 hcs8 hL8 hm8
  dsimp only [framelessMemcpyBudgetSpec] at hm8
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm8
  rcases hm8 with ⟨⟨_hx0_8, htr8, hvm8⟩, hm8⟩
  rw [← A.pool_transport lim st2 s7 s8 hvm8] at hm8
  have hm_to_pb_wp : s8.mem ⊨
      emp ∗
      (((srkPtr ↦ₛ srk.serialize) ∗ (boxPtr ↦ₛ srk.serialize) ∗ (sp ↦₆₄ boxPtr) ∗
        A.live srkPtr 33 1 ∗ A.live boxPtr 33 1 ∗
        A.pool lim st2 s8 ∗ stackAt sp (hookStack + 48) ∗
        ((sp + 8#64) ↦₃₂ sck16) ∗ ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
        memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗ Frame) ∗ R) := by
    rw [emp_sepConj]; refine Satisfies.mono (Entails.of_eq ?_) hm8; sep_ac_rfl
  refine steps_of_sepWP
    (hwp_to_pb sp s8 hpc8 hrun8 (by reg_chain) hsp_align8 (by reg_chain))
    hm_to_pb_wp hL8 ?_
  intro s9 P9 hpc9 hrun9 hL9 hm9 hpost9
  rcases hpost9 with ⟨hvm9, hsp9, hsp_align9, htr9, hx0_9, hx8_9,
    hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, _hx24_9, hx25_9, hx26_9, hx27_9, hx28_9,
    hx29_9, hx30_9, hvregs_9, hP9⟩
  have hm9' := Satisfies.mono (sepConj_mono_left hP9) hm9
  rw [emp_sepConj, ← A.pool_transport lim st2 s8 s9 hvm9] at hm9'
  have hm_to_pb : s9.mem ⊨
      (chainKeyToPbSpecWithStack M A lim hookStack).pre
        (⟨sp + 0x3d0#64, receiverChainKey, sp + 0x190#64⟩, st2) s9 ∗
      (((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗ Frame) ∗ R) := by
    dsimp only [chainKeyToPbSpecWithStack]
    rw [hsp9, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_9, hx8_9, hfit_pb⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm9'; sep_ac_rfl
  refine steps_of_call_no_panic hToPb hpc9 hrun9 hsp_align9 hx30_9 hm_to_pb hL9
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s10 hpc10 hrun10 hsp10 hsp_align10 hcs10 hL10 hm10
  dsimp only [chainKeyToPbSpecWithStack] at hm10
  rw [hsp9, hst_final, sepConj_assoc, satisfies_pure_sepConj] at hm10
  rcases hm10 with ⟨htr10, hm10⟩
  have hm10_pb : s10.mem ⊨
      (∃∗ p' : BitVec 64, optChainKeyAt A.repAlloc ⟨32#64, p'⟩ (some receiverChainKey) (sp + 0x190#64)) ∗
      (((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       A.pool lim (M.stepEvents dhCommitStep12Events st0) s10 ∗ stackAt sp (hookStack + 48) ∗
       ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
        ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗ memRegion (sp + 0x1b0#64) 40 ∗
        ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
        ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
        ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
        ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗ Frame) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm10; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm10_pb
  rcases hm10_pb with ⟨ckPtr, hm10_pb⟩
  rw [optChainKeyAt_eq_exists_bytes A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) (sp + 0x190#64),
      sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm10_pb
  rcases hm10_pb with ⟨pad, hm10_pb⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm10_pb
  rcases hm10_pb with ⟨hpad, hm10_pb⟩
  have hm10_final : s10.mem ⊨
      ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
       memRegion (sp + 0x1b0#64) 40 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
       A.pool lim (M.stepEvents dhCommitStep12Events st0) s10 ∗
       stackAt sp (hookStack + 48)) ∗ (Frame ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm10_pb; sep_ac_rfl
  exact ⟨s10, .refl _, boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc10, hrun10,
    by reg_chain, hsp_align10, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain,
    hL10, hm10_final⟩

/-! ## 5. Relocatable `[LibsignalPlacement]` Entrypoints -/

/-- Entry spatial precondition of `dhCommit_step1_2` parameterized by total stack height `stk`
    (`= hookStack + 48`). -/
abbrev dhCommitStep12Pre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st0 : M.σ) (stk : Nat) (s : State) (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey) :
    SepProp :=
  memRegion sp 12 ∗
  ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
  ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
  ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
  ((sp + 0x190#64) ↦₃₂ 0#32) ∗
  ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
  ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
  ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
  memRegion (sp + 0x440#64) 16 ∗
  memRegion (sp + 0x4e0#64) 32 ∗
  ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
  A.pool lim st0 s ∗
  stackAt sp stk

/-- Post-state predicate of `dhCommit_step1_2` at `entry + 0xa84` parameterized by total stack
    height `stk` (`= hookStack + 48`). -/
abbrev dhCommitStep12Post {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) (stk : Nat)
    (R Frame : SepProp) (s0 s : State) (sp msgA : BitVec 64) (scIdx : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (sf : State) : Prop :=
  let sckBs := chainKeyBytes senderChainKey
  let sck0 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (sckBs.take 8)
  let sck1 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((sckBs.drop 8).take 8)
  let sck16 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack32 ((sckBs.drop 16).take 4)
  let sck2 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((sckBs.drop 20).take 8)
  let sck3 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (sckBs.drop 28)
  ∃ boxPtr srkPtr ckPtr : BitVec 64, ∃ pad : List (BitVec 8),
    srkPtr ≠ 0 ∧ pad.length = 4 ∧
    sf.pc = entry + 0xa84#64 ∧ sf.status = .Running ∧ sf.sp = sp ∧ sf.spAligned = true ∧
    sf.trace = s0.trace ∧
    sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
    sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = msgA ∧
    sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
    sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = boxPtr ∧
    sf.readReg64 .x28 = srkPtr ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧
    (sf.mem ⊨
      ((sp ↦₆₄ boxPtr) ∗ ((sp + 8#64) ↦₃₂ sck16) ∗
       ((sp + 0xb4#64) ↦₃₂ scIdx) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
       memRegion (sp + 0x1b0#64) 40 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       ((sp + 0x440#64) ↦₆₄ sck0) ∗ ((sp + 0x448#64) ↦₆₄ sck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗ ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗ ((sp + 0x4f8#64) ↦₆₄ sck1) ∗
       ((msgA + 0x38#64) ↦ₛ srk.bytes.toList) ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
       A.pool lim (M.stepEvents dhCommitStep12Events st0) sf ∗
       stackAt sp stk) ∗ (Frame ∗ R))

/-- Relocatable `[LibsignalPlacement]` stack-parameterized Steps 1 & 2 (`+0x8ac → +0xa84`). -/
theorem dhCommit_step1_2_withStack_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep12BlockWp prog entry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hookStack : Nat) (hstack_lo : allocHookStack ≤ hookStack) (hstack_hi : hookStack + 48 < 2 ^ 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecWithStack M A lim hookStack))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecWithStack M A lim hookStack))
    (hfits : FitsEvents M lim st0 dhCommitStep12Events)
    (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64) (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      dhCommitStep12Pre A lim st0 (hookStack + 48) s sp msgA scIdx prevCtr0
        finalRootKey senderChainKey receiverChainKey srk ∗ (Frame ∗ R))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    ∃ sf, Steps prog s sf ∧
      dhCommitStep12Post prog entry A lim st0 (hookStack + 48) R Frame s0 s sp msgA scIdx
        finalRootKey senderChainKey receiverChainKey srk sf :=
  dhCommit_step1_2_of_wp (hlr_alloc := hlr_alloc) A lim st0 hookStack hstack_lo hstack_hi
    hwp.step1 hwp.step2_pre_shim hwp.step2_pre_alloc hwp.step2_post_alloc hwp.step2_to_pb
    hPkSer hShim hAlloc hMemcpy hToPb hfits
    R Frame s0 s sp msgA scIdx prevCtr0 finalRootKey senderChainKey receiverChainKey srk
    hpc hrun hsp hsp_align htrace hx22 hx25 hx27 hx28 hL hmem

/-- Relocatable `[LibsignalPlacement]` Steps 1 & 2 (`+0x8ac → +0xa84`) at `allocHookStack`. -/
theorem dhCommit_step1_2_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep12BlockWp prog entry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hfits : FitsEvents M lim st0 dhCommitStep12Events)
    (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64) (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      dhCommitStep12Pre A lim st0 chainKeyToPbStack s sp msgA scIdx prevCtr0
        finalRootKey senderChainKey receiverChainKey srk ∗ (Frame ∗ R))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    ∃ sf, Steps prog s sf ∧
      dhCommitStep12Post prog entry A lim st0 chainKeyToPbStack R Frame s0 s sp msgA scIdx
        finalRootKey senderChainKey receiverChainKey srk sf :=
  dhCommit_step1_2_withStack_placed (hlr_alloc := hlr_alloc) hwp A lim st0 allocHookStack (by decide) (by decide)
    hPkSer hShim hAlloc hMemcpy hToPb hfits
    R Frame s0 s sp msgA scIdx prevCtr0 finalRootKey senderChainKey receiverChainKey srk
    hpc hrun hsp hsp_align htrace hx22 hx25 hx27 hx28 hL hmem

/-- Relocatable `[LibsignalPlacement]` Steps 1 & 2 (`+0x8ac → +0xa84`) at `extHookStack`. -/
theorem dhCommit_step1_2_x_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep12BlockWp prog entry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecX M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecX M A lim))
    (hfits : FitsEvents M lim st0 dhCommitStep12Events)
    (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64) (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      dhCommitStep12Pre A lim st0 chainKeyToPbStackX s sp msgA scIdx prevCtr0
        finalRootKey senderChainKey receiverChainKey srk ∗ (Frame ∗ R))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    ∃ sf, Steps prog s sf ∧
      dhCommitStep12Post prog entry A lim st0 chainKeyToPbStackX R Frame s0 s sp msgA scIdx
        finalRootKey senderChainKey receiverChainKey srk sf :=
  dhCommit_step1_2_withStack_placed (hlr_alloc := hlr_alloc) hwp A lim st0 extHookStack (by decide) (by decide)
    hPkSer hShim hAlloc hMemcpy hToPb hfits
    R Frame s0 s sp msgA scIdx prevCtr0 finalRootKey senderChainKey receiverChainKey srk
    hpc hrun hsp hsp_align htrace hx22 hx25 hx27 hx28 hL hmem

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `dhCommit_step1_2_placed`. -/
theorem dhCommit_step1_2_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep12BlockWp prog entry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hfits : FitsEvents M lim st0 dhCommitStep12Events)
    (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64) (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      dhCommitStep12Pre A lim st0 chainKeyToPbStack s sp msgA scIdx prevCtr0
        finalRootKey senderChainKey receiverChainKey srk ∗ (Frame ∗ R))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    ∃ sf, Steps prog s sf ∧
      dhCommitStep12Post prog entry A lim st0 chainKeyToPbStack R Frame s0 s sp msgA scIdx
        finalRootKey senderChainKey receiverChainKey srk sf :=
  dhCommit_step1_2_placed (hlr_alloc := hlr_alloc) hwp A lim st0
    hPkSer hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hMemcpy hToPb hfits
    R Frame s0 s sp msgA scIdx prevCtr0 finalRootKey senderChainKey receiverChainKey srk
    hpc hrun hsp hsp_align htrace hx22 hx25 hx27 hx28 hL hmem

/-- `ReachesOrPanicOom` corollary of `dhCommit_step1_2_withStack_placed` for any `Pan`. -/
theorem dhCommit_step1_2_withStack_placed_oom [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (Pan : State → State → SepProp)
    (hwp : DhCommitStep12BlockWp prog entry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hookStack : Nat) (hstack_lo : allocHookStack ≤ hookStack) (hstack_hi : hookStack + 48 < 2 ^ 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecWithStack M A lim hookStack))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecWithStack M A lim hookStack))
    (hfits : FitsEvents M lim st0 dhCommitStep12Events)
    (R Frame : SepProp) (s0 s : State)
    (sp msgA : BitVec 64) (scIdx prevCtr0 : BitVec 32)
    (finalRootKey : RootKey) (senderChainKey receiverChainKey : ChainKey) (srk : PublicKey)
    (hpc : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msgA) (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64) (hx28 : s.readReg64 .x28 = sp + 0x3d0#64)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      dhCommitStep12Pre A lim st0 (hookStack + 48) s sp msgA scIdx prevCtr0
        finalRootKey senderChainKey receiverChainKey srk ∗ (Frame ∗ R))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    ReachesOrPanicOom prog Pan R s0 s
      (dhCommitStep12Post prog entry A lim st0 (hookStack + 48) R Frame s0 s sp msgA scIdx
        finalRootKey senderChainKey receiverChainKey srk) := by
  obtain ⟨sf, hsteps, hQ⟩ :=
    dhCommit_step1_2_withStack_placed (hlr_alloc := hlr_alloc) hwp A lim st0 hookStack hstack_lo hstack_hi
      hPkSer hShim hAlloc hMemcpy hToPb hfits
      R Frame s0 s sp msgA scIdx prevCtr0 finalRootKey senderChainKey receiverChainKey srk
      hpc hrun hsp hsp_align htrace hx22 hx25 hx27 hx28 hL hmem
  exact ⟨sf, hsteps, Or.inl hQ⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget
