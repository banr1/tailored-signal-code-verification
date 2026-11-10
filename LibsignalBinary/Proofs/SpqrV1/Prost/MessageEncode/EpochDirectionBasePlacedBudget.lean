/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Helpers for `EpochDirection::encode` (`Blocks 154 & 317`)

Defines placed contract propositions and pinned-to-unpinned bridges for Blocks `154` and `317`,
proves `VmPreserved`-threaded shared basic-block steppers, and provides polymorphic 64-byte-frame
budget call steppers (`memcpy`, `encode_varint`, and `do_reserve_and_handle`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_154 blkPC_317 blkPl_154 blkPl_317
   lsProg_154 lsProg_317 lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost StepInv StepInvPlaced)
open CryptoVerification.SpqrV1.ProtoRepr
  (EpochDirectionPBGhost bytesFieldEncodedLen epochDirectionPBAt_eq_exists_pinned
   epochDirectionPBEncodedLen u32VarintFieldEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq bv_bytesField_nonempty bv_u32VarintField_nonzero
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64
   ult_self_64 ult_zero_64 zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf sp_sub_64_aligned stackAt_authEncode stackAt_encodeVarint_eq_doReserve64
   vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (AuthEncodeCalleeSavedPlaced EncodeEpochDirectionGhost EncodeEpochDirectionPinnedGhost
   epochDirectionElemsAt epochDirectionSavedFrame withAuthEncodeCSPlaced
   zext64_orr_1_32 zext64_trunc32_orr_1 zext64_trunc32_orr_100000001)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (encodeVarintSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpecOf pushBytesStep)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget (sepWPp_call_cs_placed_noPanic)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (EncodeEpochDirectionEnv EncodeEpochDirectionPinnedEnv
   encodeEpochDirectionPinnedExactVmSpecOf encodeEpochDirectionPinnedSpec
   encodeEpochDirectionPinnedSpecOf encodeEpochDirectionPinnedSpecOfEnv
   encodeEpochDirectionPinnedSpecX encodeEpochDirectionSpec encodeEpochDirectionSpecOf
   encodeEpochDirectionSpecOfEnv encodeEpochDirectionSpecX
   epochDirection_post_unpinned_of_pinned_env)

private theorem bv_sub_add_lit (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

private theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hpost⟩

private theorem sepWP_done_vm_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hvm : VmPreserved s0 s)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => VmPreserved s0 sm ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨hvm, hpost⟩

/-! ## 1. Placed Pinned-to-Unpinned Bridges & Contracts (Blocks `154` & `317`) -/

theorem epochDirection_unpinned_of_pinned_placed_env [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreP : EncodeEpochDirectionPinnedGhost → (List AllocEvent → Prop) → Prop}
    {PreU : EncodeEpochDirectionGhost → (List AllocEvent → Prop) → Prop}
    {PostP : EncodeEpochDirectionPinnedGhost → List AllocEvent → Prop}
    {PostU : EncodeEpochDirectionGhost → List AllocEvent → Prop}
    (hpre_env : ∀ (x : EncodeEpochDirectionGhost) (g : EpochDirectionPBGhost) (st : M.σ),
      (∀ Env, PreU x Env → FitsEnv M lim st Env) →
      ∀ Env, PreP ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ Env → FitsEnv M lim st Env)
    (hpost_env : ∀ (x : EncodeEpochDirectionGhost) (g : EpochDirectionPBGhost) evs,
      PostP ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ evs → PostU x evs)
    (hpinned : subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOfEnv resStack A lim PreP PostP))) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecOfEnv resStack A lim PreU PostU)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodeEpochDirectionSpecOfEnv] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hfit, hEnvU⟩, hrest⟩
  rw [epochDirectionPBAt_eq_exists_pinned] at hrest
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hrest
  rcases hrest with ⟨g, hrest⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOfEnv resStack A lim PreP PostP)).pre
        (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv0, ?_⟩
    dsimp only [encodeEpochDirectionPinnedSpecOfEnv]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hx1, hx2, hfit, hpre_env x g st hEnvU⟩, hrest⟩
  refine hpinned.mono_outcome (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest_out
  · exact Or.inl ⟨hret, hcc, epochDirection_post_unpinned_of_pinned_env
      (PreP := PreP) (PreU := PreU) (hpost_env x g) hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest_out)

theorem epochDirection_unpinned_of_pinned_placed_x [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A lim))) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodeEpochDirectionSpecOf] at hpre
  rw [epochDirectionPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A lim)).pre
        (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome (⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest_out
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact epochDirection_post_unpinned_of_pinned_env
      (PreP := fun y Env => Env = EncodeEpochDirectionPinnedEnv y)
      (PreU := fun y Env => Env = EncodeEpochDirectionEnv y)
      (fun _ h => h)
      (by
        dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedSpecOf] at hq
        dsimp only [encodeEpochDirectionPinnedSpecOfEnv]
        exact hq)
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest_out)

/-- Relocatable base program for `EpochDirection::encode [local#1, 2]` (Blocks `154` & `317`). -/
def IsEpochDirectionEncodePlacedBase (P_blk : Program) (pl : Placement) : Prop :=
  (∃ (inst : LibsignalPlacement), P_blk = @blkPC_154 inst ∧ pl = @blkPl_154 inst) ∨
  (∃ (inst : LibsignalPlacement), P_blk = @blkPC_317 inst ∧ pl = @blkPl_317 inst)

/-- Relocatable rebased program for `EpochDirection::encode [local#1, 2]` (`lsProg_154 H` or `lsProg_317 H`). -/
def IsEpochDirectionEncodePlacedProg (prog : Program) (pl : Placement) : Prop :=
  ∃ P_blk H, prog = P_blk.rebase pl.base H ∧ IsEpochDirectionEncodePlacedBase P_blk pl

theorem isEpochDirectionEncodePlacedProg_154 [LibsignalPlacement]
    (H : String → Option (State → State)) :
    IsEpochDirectionEncodePlacedProg (lsProg_154 H) blkPl_154 :=
  ⟨blkPC_154, H, rfl, Or.inl ⟨‹_›, rfl, rfl⟩⟩

theorem isEpochDirectionEncodePlacedProg_317 [LibsignalPlacement]
    (H : String → Option (State → State)) :
    IsEpochDirectionEncodePlacedProg (lsProg_317 H) blkPl_317 :=
  ⟨blkPC_317, H, rfl, Or.inr ⟨‹_›, rfl, rfl⟩⟩

def EncodeEpochDirection154PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_154 H) (blkPl_154).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpec A lim))

def EncodeEpochDirection154PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_154 H) (blkPl_154).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionSpec A lim))

def EncodeEpochDirection154PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_154 H) (blkPl_154).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecX A lim))

def EncodeEpochDirection154PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_154 H) (blkPl_154).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecX A lim))

def EncodeEpochDirection154PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection154PinnedPlacedOk A lim (Rust.withPanics ext)

def EncodeEpochDirection154PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection154PlacedOk A lim (Rust.withPanics ext)

def EncodeEpochDirection154PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection154PinnedPlacedOkX A lim (Rust.withPanics ext)

def EncodeEpochDirection154PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection154PlacedOkX A lim (Rust.withPanics ext)

def EncodeEpochDirection154PinnedExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_154 H) (blkPl_154).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedExactVmSpecOf resStack A))

def EncodeEpochDirection317PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_317 H) (blkPl_317).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpec A lim))

def EncodeEpochDirection317PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_317 H) (blkPl_317).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionSpec A lim))

def EncodeEpochDirection317PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_317 H) (blkPl_317).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecX A lim))

def EncodeEpochDirection317PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_317 H) (blkPl_317).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecX A lim))

def EncodeEpochDirection317PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection317PinnedPlacedOk A lim (Rust.withPanics ext)

def EncodeEpochDirection317PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection317PlacedOk A lim (Rust.withPanics ext)

def EncodeEpochDirection317PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection317PinnedPlacedOkX A lim (Rust.withPanics ext)

def EncodeEpochDirection317PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection317PlacedOkX A lim (Rust.withPanics ext)

def EncodeEpochDirection317PinnedExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_317 H) (blkPl_317).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedExactVmSpecOf resStack A))

/-! ## 2. Placed Fetch Dispatch (Blocks `154` & `317`) -/

theorem epochDirectionPlaced_fetch_entry {P_blk : Program} {pl : Placement}
    (hbase : IsEpochDirectionEncodePlacedBase P_blk pl)
    (H : String → Option (State → State)) {ins : Instr}
    (h_154 : ∀ [LibsignalPlacement],
      (lsProg_154 H).fetch ((blkPl_154).base + 0#64) = some ins)
    (h_317 : ∀ [LibsignalPlacement],
      (lsProg_317 H).fetch ((blkPl_317).base + 0#64) = some ins) :
    (P_blk.rebase pl.base H).fetch pl.base = some ins := by
  rcases hbase with ⟨inst, rfl, rfl⟩ | ⟨inst, rfl, rfl⟩
  · simpa using @h_154 inst
  · simpa using @h_317 inst

theorem epochDirectionPlaced_fetch_add {P_blk : Program} {pl : Placement}
    (hbase : IsEpochDirectionEncodePlacedBase P_blk pl)
    (H : String → Option (State → State)) {k : Nat} {ins : Instr}
    (h_154 : ∀ [LibsignalPlacement],
      (lsProg_154 H).fetch ((blkPl_154).base + BitVec.ofNat 64 k) = some ins)
    (h_317 : ∀ [LibsignalPlacement],
      (lsProg_317 H).fetch ((blkPl_317).base + BitVec.ofNat 64 k) = some ins) :
    (P_blk.rebase pl.base H).fetch (pl.base + BitVec.ofNat 64 k) = some ins := by
  rcases hbase with ⟨inst, rfl, rfl⟩ | ⟨inst, rfl, rfl⟩
  · exact @h_154 inst
  · exact @h_317 inst

open Lean Elab Tactic in
scoped elab "ed_fetches_placed_only " hbase:ident H:ident kStart:num kEnd:num : tactic => do
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let kHex := String.ofList (Nat.toDigits 16 k)
    let p154 := mkIdent (`CryptoVerification |>.str s!"blkPC_154_rebase_fetch_0x{kHex}")
    let p317 := mkIdent (`CryptoVerification |>.str s!"blkPC_317_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := epochDirectionPlaced_fetch_entry $hbase $H
          (fun [LibsignalPlacement] => $p154 _ $H)
          (fun [LibsignalPlacement] => $p317 _ $H)))
    else
      evalTactic (← `(tactic|
        have := epochDirectionPlaced_fetch_add $hbase $H (k := $kq)
          (fun [LibsignalPlacement] => $p154 _ $H)
          (fun [LibsignalPlacement] => $p317 _ $H)))

/-! ## 3. Relocatable `VmPreserved`-Threaded Step Lemmas (Blocks `154` & `317`) -/

/-- Shared prologue (`+0..+40`) on Blocks `154` & `317`: allocates the 64-byte frame, saves
`fp, lr, x24..x19`, sets `x0 = (tag << 3) | 2`, `x1 = v`, `x19 = v`, `x21 = dirA`, and
proves `VmPreserved s sm`. -/
theorem step_epochDir_prologue_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {pl : Placement} (hfn : IsEpochDirectionEncodePlacedProg prog pl)
    (tag : BitVec 32) (dirA v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = pl.base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = stackAt sp (authEncodeStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 40#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64) →
      sm.readReg64 .x1 = v → sm.readReg64 .x19 = v → sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((stackAt (sp - 64#64) (0x30 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hx0_eq :
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (2#64 ||| BitVec.zeroExtend 64 (BitVec.truncate 32 (s.readReg64 (Reg.gpr 0#5)) <<< 3))) =
      (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64) := by
    change BitVec.zeroExtend 64 (BitVec.truncate 32
      (2#64 ||| BitVec.zeroExtend 64 (s.readReg32 .x0 <<< 3))) = _
    rw [hw0]; dsimp only [WireType.toU32]; bv_bits
  rw [stackAt_authEncode hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 40#64)
  by_vm_steps (
    ed_fetches_placed_only hbase trapHooks 0 40
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionSavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Shared inline `EpochDirection::encoded_len` computation (`+44..+168` and `+452..+484`)
with `VmPreserved s sm`. -/
theorem step_epochDir_len_placed {prog : Program} {pl : Placement}
    (hfn : IsEpochDirectionEncodePlacedProg prog pl)
    (v dirA nextPtr prevPtr sp : BitVec 64) (d : EpochDirectionPB)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63)
    (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = dirA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 168#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (epochDirectionPBEncodedLen d) → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm (epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  ed_fetches_placed_only hbase H 44 168
  ed_fetches_placed_only hbase H 452 484
  examples_hide_fetches; subst hP
  dsimp only [epochDirectionElemsAt]
  obtain ⟨hnext_beq, hnext_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  obtain ⟨hprev_beq, hprev_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hctr : (d.ctr == 0#32) <;> cases hn : d.next.isEmpty <;> cases hp : d.prev.isEmpty
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have hadd12 := CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.bv_add_ofNat_comm
      (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next)
        (c := epochDirectionPBEncodedLen d) rfl hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hadd12 := CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.bv_add_ofNat_comm
      (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    have htot_eq : epochDirectionPBEncodedLen d =
        u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr) (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have htot_eq : epochDirectionPBEncodedLen d = u32VarintFieldEncodedLen d.ctr := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : bytesFieldEncodedLen d.next + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := bytesFieldEncodedLen d.next) (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hn_val := bv_bytesField_nonempty hn
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hp_val := bv_bytesField_nonempty hp
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.prev := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hn]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have htot_eq : epochDirectionPBEncodedLen d = 0 := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hn, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp

/-- Shared `ctr` tag push (`+192..+220`) with `VmPreserved s sm`. -/
theorem step_epochDir_push_ctr_tag_placed {prog : Program} (A : RustAlloc)
    {pl : Placement} (hfn : IsEpochDirectionEncodePlacedProg prog pl)
    (v curCap curPtr dirA sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 192#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 220#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = d.ctr.zeroExtend 64 → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 220#64)
  by_vm_steps (
    ed_fetches_placed_only hbase trapHooks 192 220
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp)
    rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]
    exact Entails.of_eq (by sep_ac_rfl))

/-- Shared `next` tag push (`+248..+276`) with `VmPreserved s sm`. -/
theorem step_epochDir_push_next_tag_placed {prog : Program} (A : RustAlloc)
    {pl : Placement} (hfn : IsEpochDirectionEncodePlacedProg prog pl)
    (v curCap curPtr dirA nextPtr sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 248#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = nextPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 276#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.next.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = nextPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 276#64)
  by_vm_steps (
    ed_fetches_placed_only hbase trapHooks 248 276
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp)
    rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]
    exact Entails.of_eq (by sep_ac_rfl))

/-- Shared `prev` tag push (`+352..+380`) with `VmPreserved s sm`. -/
theorem step_epochDir_push_prev_tag_placed {prog : Program} (A : RustAlloc)
    {pl : Placement} (hfn : IsEpochDirectionEncodePlacedProg prog pl)
    (v curCap curPtr prevPtr sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 352#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = prevPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 380#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = prevPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x1a#8]) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 380#64)
  by_vm_steps (
    ed_fetches_placed_only hbase trapHooks 352 380
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp)
    rw [← vecU8At_close_one A v curCap curPtr curBs 0x1a#8 hlt]
    exact Entails.of_eq (by sep_ac_rfl))

/-- Shared epilogue (`+432..+452`) with `VmPreserved s sf`. -/
theorem step_epochDir_epilogue_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {pl : Placement} (hfn : IsEpochDirectionEncodePlacedProg prog pl)
    (sp : BitVec 64) {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 432#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
        (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInv s0 sf → VmPreserved s sf →
      Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  ed_fetches_placed_only hbase H 432 452
  examples_hide_fetches; subst hP
  dsimp only [epochDirectionSavedFrame]
  have hsp_aligned := sp_sub_64_aligned halign
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hinv0⟩
  apply sepWPp_of_sepWP_cs_placed_vm (mid := s0.readReg64 .lr); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1).1 hvmp))
  rw [stackAt_authEncode hres sp]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp)
    (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x24)
        (Entails.sepExists_right (s0.readReg64 .x23)
          (Entails.sepExists_right (s0.readReg64 .x22)
            (Entails.sepExists_right (s0.readReg64 .x21)
              (Entails.sepExists_right (s0.readReg64 .x20)
                (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

/-! ## 4. Polymorphic 64-Byte-Frame Budget Call Steppers (`Q`, `Qp`, `oom`) -/

/-- Execute `bl memcpy` at `call_pc` with `s.sp = sp - 64#64`, propagating
`AuthEncodeCalleeSavedPlaced s0 sm` and `VmPreserved s sm`. -/
theorem step_ed_memcpy_call_placed {prog : Program} {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionBudgetSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact ProofLib.allowPanic_not_exited hm
  · intro _ _ _ hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)

theorem step_ed_encode_varint_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt))
    (F := F) henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withAuthEncodeCSPlaced, encodeVarintFitSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)

/-- Execute `bl encode_varint` (`encodeVarintDetSpecOf`, supplying deterministic `nextCap.toNat`)
at `call_pc` with `s.sp = sp - 64#64`. -/
theorem step_ed_encode_varint_det_call_placed {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt))
    (F := F) henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withAuthEncodeCSPlaced, encodeVarintDetSpecOf, encodeVarintFitSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCSPlaced, encodeVarintDetSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres, hdet⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
        hge hpres hdet)

theorem step_ed_do_reserve2_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v
            (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)] at hm
    simp only [withAuthEncodeCSPlaced, doReserve2SpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCSPlaced, doReserve2SpecOf, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_ed_do_reserve7_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc
      (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v
            (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)] at hm
    simp only [withAuthEncodeCSPlaced, doReserveSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCSPlaced, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
