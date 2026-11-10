/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 Send-Leaf Transitions: `RustCliAllocBudget` Specifications & Call Helpers

Exact `AllocEvent` envelopes (`*Env` and `*_nonempty`), fixed-base and `[LibsignalPlacement]`
specifications under `RustCliAllocBudget M` (`*SpecOfEnv`, `*Spec`, `*PlacedOkX`) for
`<Ct2Sampled>::recv_next_epoch` and the five `send_*_chunk` leaf transitions, and `VmPreserved` /
`PolyEncoder::next_chunk` subroutine call helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPl_355 libsignalRoLoaded_of_keepsFrozen
   libsignalSessionLib lsProg_355 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Chunk Epoch GF16 NUM_POLYS PolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sessionMemcpyRegionSpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1ReceivedAt chunkedCt1SampledAt chunkedCt2SampledAt
   chunkedEkReceivedCt1SampledAt chunkedHeaderSentAt chunkedKeysUnsampledAt
   dropGluePoly16Stack vecGF16ListOf)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize polyArrayBytes polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost
   Ct2SampledRecvNextEpochGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost
   Regs19To27Eq Relocatable relocate_post_entails relocate_pre_entails relocatedHeap)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
  (PolyNextChunkEnv polyNextChunkEnv_nonempty
   polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv
   polyNextChunkSpec polyNextChunkSpecOfEnv)

/-! ## 1. Allocator Event Envelopes & Non-Vacuity Witnesses -/

/-- Exact allocator event envelope of `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, Block `355`):
    only `drop_glue::<[Poly; 16]>` runs, emitting `FreeOnlyEvs`. -/
def Ct2SampledRecvNextEpochEnv : List AllocEvent → Prop :=
  FreeOnlyEvs

theorem ct2SampledRecvNextEpochEnv_nonempty :
    ∃ evs, Ct2SampledRecvNextEpochEnv evs :=
  ⟨[], FreeOnlyEvs.nil⟩

/-- `PolyEncoder`-indexed specialization of `PolyNextChunkEnv` (`PolyNextChunkEnv` inspects only
    `x.enc`). -/
def PolyEncoderNextChunkEnv (enc : PolyEncoder) (evs : List AllocEvent) : Prop :=
  PolyNextChunkEnv
    ⟨0#64, 0#64, enc, enc, ⟨0#16, ⟨List.replicate 32 0#8, by decide⟩⟩⟩
    evs

@[simp]
theorem polyNextChunkEnv_eq_polyEncoderNextChunkEnv (x : PolyNextChunkGhost) :
    PolyNextChunkEnv x = PolyEncoderNextChunkEnv x.enc :=
  rfl

theorem polyEncoderNextChunkEnv_nonempty (enc : PolyEncoder) :
    ∃ evs, PolyEncoderNextChunkEnv enc evs :=
  polyNextChunkEnv_nonempty _

/-- Exact allocator event envelope of `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
def EkReceivedCt1SampledSendCt1ChunkEnv {F : ShaCompress}
    (x : EkReceivedCt1SampledSendCt1ChunkGhost F) (evs : List AllocEvent) : Prop :=
  PolyEncoderNextChunkEnv x.st.sending_ct1 evs

theorem ekReceivedCt1SampledSendCt1ChunkEnv_nonempty {F : ShaCompress}
    (x : EkReceivedCt1SampledSendCt1ChunkGhost F) :
    ∃ evs, EkReceivedCt1SampledSendCt1ChunkEnv x evs :=
  polyEncoderNextChunkEnv_nonempty x.st.sending_ct1

/-- Exact allocator event envelope of `<Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
def Ct2SampledSendCt2ChunkEnv {F : ShaCompress}
    (x : Ct2SampledSendCt2ChunkGhost F) (evs : List AllocEvent) : Prop :=
  PolyEncoderNextChunkEnv x.st.sending_ct2 evs

theorem ct2SampledSendCt2ChunkEnv_nonempty {F : ShaCompress}
    (x : Ct2SampledSendCt2ChunkGhost F) :
    ∃ evs, Ct2SampledSendCt2ChunkEnv x evs :=
  polyEncoderNextChunkEnv_nonempty x.st.sending_ct2

/-- Exact allocator event envelope of `<HeaderSent>::send_ek_chunk` (Block `336`). -/
def HeaderSentSendEkChunkEnv {F : ShaCompress}
    (x : HeaderSentSendEkChunkGhost F) (evs : List AllocEvent) : Prop :=
  PolyEncoderNextChunkEnv x.st.sending_ek evs

theorem headerSentSendEkChunkEnv_nonempty {F : ShaCompress}
    (x : HeaderSentSendEkChunkGhost F) :
    ∃ evs, HeaderSentSendEkChunkEnv x evs :=
  polyEncoderNextChunkEnv_nonempty x.st.sending_ek

/-- Exact allocator event envelope of `<Ct1Received>::send_ek_chunk` (Block `345`). -/
def Ct1ReceivedSendEkChunkEnv {F : ShaCompress}
    (x : Ct1ReceivedSendEkChunkGhost F) (evs : List AllocEvent) : Prop :=
  PolyEncoderNextChunkEnv x.st.sending_ek evs

theorem ct1ReceivedSendEkChunkEnv_nonempty {F : ShaCompress}
    (x : Ct1ReceivedSendEkChunkGhost F) :
    ∃ evs, Ct1ReceivedSendEkChunkEnv x evs :=
  polyEncoderNextChunkEnv_nonempty x.st.sending_ek

/-- Exact allocator event envelope of `<Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
def Ct1SampledSendCt1ChunkEnv {F : ShaCompress}
    (x : Ct1SampledSendCt1ChunkGhost F) (evs : List AllocEvent) : Prop :=
  PolyEncoderNextChunkEnv x.st.sending_ct1 evs

theorem ct1SampledSendCt1ChunkEnv_nonempty {F : ShaCompress}
    (x : Ct1SampledSendCt1ChunkGhost F) :
    ∃ evs, Ct1SampledSendCt1ChunkEnv x evs :=
  polyEncoderNextChunkEnv_nonempty x.st.sending_ct1

/-! ## 2. Fixed-Base (`b : BitVec 64`) Specifications -/

/-- Canonical specification of `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`,
    Block `355`): deallocation-only (`Ct2SampledRecvNextEpochEnv = FreeOnlyEvs`), requiring no
    `FitsEnv` hypothesis. -/
def ct2SampledRecvNextEpochSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct2SampledRecvNextEpochGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧ s.readReg64 .x2 = x.epoch ∧
      x.st.recv_next_epoch x.epoch = .ok x.out⌝ ∗
      memRegion x.outA 56 ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      A.pool lim st s ∗ stackAt s.sp (dropGluePoly16Stack + 32)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Ct2SampledRecvNextEpochEnv evs⌝ ∗
      chunkedKeysUnsampledAt A.repAlloc x.outA x.out ∗
      memRegion x.stA 456 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (dropGluePoly16Stack + 32)

/-- Canonical specification of `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`,
    Block `355`): deallocation-only (`Ct2SampledRecvNextEpochEnv = FreeOnlyEvs`), requiring no
    `FitsEnv` hypothesis. -/
def ct2SampledRecvNextEpochSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct2SampledRecvNextEpochGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧ s.readReg64 .x2 = x.epoch ∧
      x.st.recv_next_epoch x.epoch = .ok x.out ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA 56 ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      A.pool lim st s ∗ stackAt s.sp (dropGluePoly16Stack + 32)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Ct2SampledRecvNextEpochEnv evs⌝ ∗
      chunkedKeysUnsampledAt A.repAlloc x.outA x.out ∗
      memRegion x.stA 456 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (dropGluePoly16Stack + 32)

/-- Envelope-parametric specification of `<Ct2Sampled>::recv_next_epoch`. -/
def ct2SampledRecvNextEpochSpecOfEnvBase (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct2SampledRecvNextEpochGhost F → List AllocEvent → Prop) :
    Spec (Ct2SampledRecvNextEpochGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧ s.readReg64 .x2 = x.epoch ∧
      x.st.recv_next_epoch x.epoch = .ok x.out ∧ FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA 56 ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      A.pool lim st s ∗ stackAt s.sp (dropGluePoly16Stack + 32)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedKeysUnsampledAt A.repAlloc x.outA x.out ∗
      memRegion x.stA 456 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (dropGluePoly16Stack + 32)

/-- Envelope-parametric specification of `<Ct2Sampled>::recv_next_epoch`. -/
def ct2SampledRecvNextEpochSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct2SampledRecvNextEpochGhost F → List AllocEvent → Prop) :
    Spec (Ct2SampledRecvNextEpochGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧ s.readReg64 .x2 = x.epoch ∧
      x.st.recv_next_epoch x.epoch = .ok x.out ∧ FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA 56 ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      A.pool lim st s ∗ stackAt s.sp (dropGluePoly16Stack + 32)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedKeysUnsampledAt A.repAlloc x.outA x.out ∗
      memRegion x.stA 456 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (dropGluePoly16Stack + 32)

theorem subroutine_ok_ct2SampledRecvNextEpochSpecOfEnv_freeOnly [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (ct2SampledRecvNextEpochSpec M A lim F)) :
    subroutine_ok prog entry
      (ct2SampledRecvNextEpochSpecOfEnv M A lim F (fun _ => Ct2SampledRecvNextEpochEnv)) := by
  refine subroutine_ok_mono h (fun (x, st) R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [ct2SampledRecvNextEpochSpecOfEnv, ct2SampledRecvNextEpochSpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.2⟩, hp.2⟩

/-- Envelope-parametric fixed-base budget specification of
    `<EkReceivedCt1Sampled>::send_ct1_chunk` (`0x5e1d0`). -/
def ekReceivedCt1SampledSendCt1ChunkSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (528 + chunkSize) ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 960)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 528#64) x.chunk ∗
      memRegion x.stA 528 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 960)

abbrev ekReceivedCt1SampledSendCt1ChunkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F × M.σ) :=
  ekReceivedCt1SampledSendCt1ChunkSpecOfEnv M A lim F b EkReceivedCt1SampledSendCt1ChunkEnv

/-- Envelope-parametric fixed-base budget specification of
    `<Ct2Sampled>::send_ct2_chunk` (`0x5f9d4`). -/
def ct2SampledSendCt2ChunkSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct2SampledSendCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct2_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (456 + chunkSize) ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 896)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt2SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 456#64) x.chunk ∗
      memRegion x.stA 456 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 896)

abbrev ct2SampledSendCt2ChunkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (Ct2SampledSendCt2ChunkGhost F × M.σ) :=
  ct2SampledSendCt2ChunkSpecOfEnv M A lim F b Ct2SampledSendCt2ChunkEnv

/-- Envelope-parametric fixed-base budget specification of
    `<HeaderSent>::send_ek_chunk` (`0x5d860`). -/
def headerSentSendEkChunkSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop) :
    Spec (HeaderSentSendEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (880 + chunkSize) ∗
      chunkedHeaderSentAt A.repAlloc x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 1328)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedHeaderSentAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 880#64) x.chunk ∗
      memRegion x.stA 880 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 1328)

abbrev headerSentSendEkChunkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (HeaderSentSendEkChunkGhost F × M.σ) :=
  headerSentSendEkChunkSpecOfEnv M A lim F b HeaderSentSendEkChunkEnv

/-- Envelope-parametric fixed-base budget specification of
    `<Ct1Received>::send_ek_chunk` (`0x5e250`). -/
def ct1ReceivedSendEkChunkSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1ReceivedSendEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A.repAlloc x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 944)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt1ReceivedAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 504#64) x.chunk ∗
      memRegion x.stA 504 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 944)

abbrev ct1ReceivedSendEkChunkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (Ct1ReceivedSendEkChunkGhost F × M.σ) :=
  ct1ReceivedSendEkChunkSpecOfEnv M A lim F b Ct1ReceivedSendEkChunkEnv

/-- Envelope-parametric fixed-base budget specification of
    `<Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`). -/
def ct1SampledSendCt1ChunkSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1SampledSendCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (928 + chunkSize) ∗
      chunkedCt1SampledAt A.repAlloc x.stA x.st ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 1376)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt1SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 928#64) x.chunk ∗
      memRegion x.stA 928 ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 1376)

abbrev ct1SampledSendCt1ChunkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (Ct1SampledSendCt1ChunkGhost F × M.σ) :=
  ct1SampledSendCt1ChunkSpecOfEnv M A lim F b Ct1SampledSendCt1ChunkEnv

/-! ## 3. Relocatable `[LibsignalPlacement]` Budget Specifications & `*PlacedOkX` Contracts -/

/-- Relocatable budget specification of `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
def ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (528 + chunkSize) ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 960)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 528#64) x.chunk ∗
      memRegion x.stA 528 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 960)

abbrev ekReceivedCt1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F × M.σ) :=
  ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F EkReceivedCt1SampledSendCt1ChunkEnv

/-- Relocatable budget specification of `<Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
def ct2SampledSendCt2ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct2SampledSendCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct2_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (456 + chunkSize) ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 896)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt2SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 456#64) x.chunk ∗
      memRegion x.stA 456 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 896)

abbrev ct2SampledSendCt2ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct2SampledSendCt2ChunkGhost F × M.σ) :=
  ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Ct2SampledSendCt2ChunkEnv

/-- Relocatable budget specification of `<HeaderSent>::send_ek_chunk` (Block `336`). -/
def headerSentSendEkChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop) :
    Spec (HeaderSentSendEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (880 + chunkSize) ∗
      chunkedHeaderSentAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 1328)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedHeaderSentAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 880#64) x.chunk ∗
      memRegion x.stA 880 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 1328)

abbrev headerSentSendEkChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (HeaderSentSendEkChunkGhost F × M.σ) :=
  headerSentSendEkChunkPlacedSpecOfEnv M A lim F HeaderSentSendEkChunkEnv

/-- Relocatable budget specification of `<Ct1Received>::send_ek_chunk` (Block `345`). -/
def ct1ReceivedSendEkChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1ReceivedSendEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 944)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt1ReceivedAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 504#64) x.chunk ∗
      memRegion x.stA 504 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 944)

abbrev ct1ReceivedSendEkChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1ReceivedSendEkChunkGhost F × M.σ) :=
  ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Ct1ReceivedSendEkChunkEnv

/-- Relocatable budget specification of `<Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
def ct1SampledSendCt1ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1SampledSendCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (928 + chunkSize) ∗
      chunkedCt1SampledAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 1376)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt1SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 928#64) x.chunk ∗
      memRegion x.stA 928 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 1376)

abbrev ct1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1SampledSendCt1ChunkGhost F × M.σ) :=
  ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Ct1SampledSendCt1ChunkEnv

def Ct2SampledRecvNextEpochPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_355 (Rust.withPanics ext)) (blkPl_355).base
    (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec M A lim F))

def Ct2SampledRecvNextEpochPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : Ct2SampledRecvNextEpochGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (lsProg_355 (Rust.withPanics ext)) (blkPl_355).base
    (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpecOfEnv M A lim F Env))

def HeaderSentSendEkChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext)) (lsmpl.base 336)
    (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpecOfEnv M A lim F Env))

abbrev HeaderSentSendEkChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F ext HeaderSentSendEkChunkEnv

def Ct1ReceivedSendEkChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext)) (lsmpl.base 345)
    (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Env))

abbrev Ct1ReceivedSendEkChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F ext Ct1ReceivedSendEkChunkEnv

def Ct1SampledSendCt1ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext)) (lsmpl.base 335)
    (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env))

abbrev Ct1SampledSendCt1ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F ext Ct1SampledSendCt1ChunkEnv

def EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext)) (lsmpl.base 344)
    (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env))

abbrev EkReceivedCt1SampledSendCt1ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F ext EkReceivedCt1SampledSendCt1ChunkEnv

def Ct2SampledSendCt2ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext)) (lsmpl.base 354)
    (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Env))

abbrev Ct2SampledSendCt2ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F ext Ct2SampledSendCt2ChunkEnv

/-! ## 4. Subroutine Call & Sequencing Helpers -/

/-- Total-correctness `SepWP` sequencing preserving `LibsignalCodeRoLoaded` across `mid`. -/
theorem sepWP_seq_lscro {prog : Program} {pl : Arm64.Obj.MultiPlacement} {mid tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen
    (fun _ _ ⟨hcl, hro⟩ hkf =>
      ⟨hcl.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hro hkf⟩) hcro h

/-- Framed `memcpy` call rule under `withVmPreserved sessionMemcpyRegionSpec`, relocating any
    `Relocatable n F` predicate from `src` to `dst` while forwarding `Regs19To27Eq` and
    `VmPreserved sbase sf`. -/
theorem call_memcpy_relocate_vm {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {sbase s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hvm : VmPreserved sbase s)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      VmPreserved sbase sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [withVmPreserved, sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun hvm_sf => ?_
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hregs.of_cs hcs_sf)
      (htr.trans htrace) (hvm.trans hvm_sf)

/-- Pool-transporting `memcpy` relocation call rule: relocates `Relocatable n F` from `src` to `dst`
    and transports `A.pool lim st s` to `A.pool lim st sf` automatically via `VmPreserved`. -/
theorem call_memcpy_relocate_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      VmPreserved s sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  have hsplit' : P = (memRegion dst n ∗ F src) ∗ (A.pool lim st s ∗ Frame) := by
    rw [hsplit]; ac_rfl
  refine call_memcpy_relocate_vm hcall hrel dst src hpc hrun hsp hsp_align hlr htrace hregs
    (VmPreserved.refl s) hx0 hx1 hx2 hsplit' (fun sf hpc_sf hrun_sf hsp_sf hregs_sf htr_sf hvm_sf => ?_)
  have hpool : (F dst ∗ memRegion src n) ∗ (A.pool lim st s ∗ Frame) =
      (F dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame := by
    rw [← A.pool_of_vmPreserved hvm_sf]; ac_rfl
  rw [hpool]
  exact hnext sf hpc_sf hrun_sf hsp_sf hregs_sf htr_sf hvm_sf

/-- Framed relocatable call rule for `withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)`
    (Block `265`). -/
theorem call_dropGluePoly16_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)))
    (arrA : BitVec 64) (vecs : List (List GF16)) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecGF16ListOf A.repAlloc arrA vecs ∗ A.pool lim st s ∗
      stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → FreeOnlyEvs evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((memRegion arrA polyArrayBytes ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp_call dropGluePoly16Stack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine SepWP.call_subroutine_frame hcall (x := (⟨arrA, vecs⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit, sepConj_assoc] at hm
    dsimp only [withLsCodeLoaded, dropGluePoly16Spec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hlen, hlr.symm ▸ hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, dropGluePoly16Spec]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hacp, hevs⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs

/-- Envelope-parametric framed fixed-base call rule for
    `(polyNextChunkSpecOfEnv Env M A lim img.base).inImage img` (`0x6a384`). -/
theorem call_polyNextChunk_ofEnv {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {img : Obj.Image} {prog : Program} {entry ret_pc : BitVec 64}
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    (hcall : subroutine_ok prog entry ((polyNextChunkSpecOfEnv Env M A lim img.base).inImage img))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (outChunkA encA : BitVec 64) (enc enc' : PolyEncoder) (chunk : Chunk) (st : M.σ)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx8 : s.readReg64 Reg.x8 = outChunkA)
    (hx0 : s.readReg64 Reg.x0 = encA)
    (hnc : enc.nextChunk = .ok (enc', chunk))
    (hfit : FitsEnv M lim st (Env ⟨outChunkA, encA, enc, enc', chunk⟩))
    (hsplit : P = (memRegion outChunkA chunkSize ∗ polyEncoderAt A.repAlloc encA enc ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool lim st s ∗ stackAt sp_call polyNextChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      Env ⟨outChunkA, encA, enc, enc', chunk⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkAt outChunkA chunk ∗ polyEncoderAt A.repAlloc encA enc' ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp_call polyNextChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        img.FrozenLoaded sm ∧ sm.symtab = img.symtab →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hinv
  refine SepWP.call_subroutine_frame hcall (x := (⟨outChunkA, encA, enc, enc', chunk⟩, st))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [Spec.inImage, polyNextChunkSpecOfEnv]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hinv.1, hinv.2⟩, ⟨hb, hx8, hx0, hnc, hfit⟩, hm⟩
  · dsimp only [Spec.inImage, polyNextChunkSpecOfEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hevs, htr⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) (hregs.of_cs hcs_sf)
      (htr.trans htrace) hevs

/-- Canonical framed fixed-base call rule for `(polyNextChunkSpec M A lim img.base).inImage img`. -/
theorem call_polyNextChunk {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {img : Obj.Image} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((polyNextChunkSpec M A lim img.base).inImage img))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (outChunkA encA : BitVec 64) (enc enc' : PolyEncoder) (chunk : Chunk) (st : M.σ)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx8 : s.readReg64 Reg.x8 = outChunkA)
    (hx0 : s.readReg64 Reg.x0 = encA)
    (hnc : enc.nextChunk = .ok (enc', chunk))
    (hfit : FitsEnv M lim st (PolyEncoderNextChunkEnv enc))
    (hsplit : P = (memRegion outChunkA chunkSize ∗ polyEncoderAt A.repAlloc encA enc ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool lim st s ∗ stackAt sp_call polyNextChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      PolyEncoderNextChunkEnv enc evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkAt outChunkA chunk ∗ polyEncoderAt A.repAlloc encA enc' ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp_call polyNextChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        img.FrozenLoaded sm ∧ sm.symtab = img.symtab →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) :=
  call_polyNextChunk_ofEnv hcall hb outChunkA encA enc enc' chunk st
    hpc hrun hsp hsp_align hlr htrace hregs hx8 hx0 hnc hfit hsplit hnext

/-- Envelope-parametric framed relocatable call rule for
    `withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim)` (Block `416`). -/
theorem call_polyNextChunk_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim)))
    (outChunkA encA : BitVec 64) (enc enc' : PolyEncoder) (chunk : Chunk) (st : M.σ)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx8 : s.readReg64 Reg.x8 = outChunkA)
    (hx0 : s.readReg64 Reg.x0 = encA)
    (hnc : enc.nextChunk = .ok (enc', chunk))
    (hfit : FitsEnv M lim st (Env ⟨outChunkA, encA, enc, enc', chunk⟩))
    (hsplit : P = (memRegion outChunkA chunkSize ∗ polyEncoderAt A.repAlloc encA enc ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt sp_call polyNextChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      Env ⟨outChunkA, encA, enc, enc', chunk⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkAt outChunkA chunk ∗ polyEncoderAt A.repAlloc encA enc' ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp_call polyNextChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcro
  refine SepWP.call_subroutine_frame hcall (x := (⟨outChunkA, encA, enc, enc', chunk⟩, st))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded, polyNextChunkPlacedSpecOfEnv]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hnc, hfit⟩, hm⟩
  · dsimp only [withLsCodeRoLoaded, polyNextChunkPlacedSpecOfEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hevs, htr⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) (hregs.of_cs hcs_sf)
      (htr.trans htrace) hevs

/-- Canonical framed relocatable call rule for
    `withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim)` (Block `416`). -/
theorem call_polyNextChunk_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim)))
    (outChunkA encA : BitVec 64) (enc enc' : PolyEncoder) (chunk : Chunk) (st : M.σ)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx8 : s.readReg64 Reg.x8 = outChunkA)
    (hx0 : s.readReg64 Reg.x0 = encA)
    (hnc : enc.nextChunk = .ok (enc', chunk))
    (hfit : FitsEnv M lim st (PolyEncoderNextChunkEnv enc))
    (hsplit : P = (memRegion outChunkA chunkSize ∗ polyEncoderAt A.repAlloc encA enc ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt sp_call polyNextChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      PolyEncoderNextChunkEnv enc evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkAt outChunkA chunk ∗ polyEncoderAt A.repAlloc encA enc' ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp_call polyNextChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) :=
  call_polyNextChunk_placed_ofEnv hcall outChunkA encA enc enc' chunk st
    hpc hrun hsp hsp_align hlr htrace hregs hx8 hx0 hnc hfit hsplit hnext

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
