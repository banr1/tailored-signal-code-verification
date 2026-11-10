/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 7 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` common `recv_ek_chunk` prefix (`+11404 -> +11496`) and
Path 4a (`outMsg = none, ack = false`: `+11496 -> s0.x30`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open Obj.MultiPlacedLib
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkEnv addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  PolyDecoderDecodedMessagePostEnv PolyDecoderDecodedMessagePreEnv
  polyDecoderDecodedMessagePlacedSpec polyDecoderDecodedMessagePlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvEnv statesRecvVariantPlacedSpec statesRecvVariantPlacedSpecOfEnv
  statesRecvVariantPlacedSpecOfPrePostEnv
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local irreducible] addChunkTotal decodedMessageTotal
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Sequencing & Clean-Exit `SepWP` → `SepWPp` Combinators -/

theorem ct1Sampled_seq_vm_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hPm, hQ⟩ hcro' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcro' hvm hQ))

theorem ct1Sampled_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm (P_mid sm) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hq))

theorem ct1Sampled_sepWPp_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm (P_mid sm) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ hcrom =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hent (h2 sm hpc hrun hcrom hq))))

theorem sepWPp_of_ct1Sampled_exit_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (st : M.σ) (P R : SepProp)
    (hexit : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          PostEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv).post
              ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv).onPanic
              ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  DefsPlacedBudget.sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
    s0 s outA selfA msgA self msg st P R hexit

theorem sepWPp_of_ct1Sampled_exit_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (st : M.σ) (P R : SepProp)
    (hexit : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Env ⟨outA, selfA, msgA, self, msg⟩ evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env).post
              ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env).onPanic
              ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  DefsPlacedBudget.sepWPp_of_statesRecv_exit_placed_ofEnv
    s0 s outA selfA msgA self msg st P R hexit

theorem sepWPp_of_ct1Sampled_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (st : M.σ) (P R : SepProp)
    (hexit : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          StatesRecvEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K self msg).post
              ((outA, selfA, msgA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K self msg).onPanic
              ((outA, selfA, msgA), st) s0 sf ∗ R)) :=
  DefsPlacedBudget.sepWPp_of_statesRecv_exit_placed
    s0 s outA selfA msgA self msg st P R hexit

/-! ## 2. Common `recv_ek_chunk` Prefix (`+11404 -> +11496`) -/

set_option maxHeartbeats 1200000 in
/-- Two-envelope (`DecPre` / `DecPost`) budget-threaded common `recv_ek_chunk` prefix
    (`+11404 -> +11496`): extracts the stack frame and `c_uc : Words16`, copies `st.uc` to
    `fsp + 3696` and `st.receiving_ek` to `fsp + 2752`, and calls `PolyDecoder::add_chunk` and
    `PolyDecoder::decoded_message`. -/
theorem ct1Sampled_recv_ek_common_prefix_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {DecPre DecPost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits_add : FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (DecPre ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩))
    (Rest : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11496#64) s_in
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest)
      (fun sf Pf =>
        ∃ (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
          (evsAdd evsDec : List AllocEvent),
          (Pf ⊢
            optVecU8At A.repAlloc (fsp + 3832#64)
              (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
            polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
            chunkAt (msgA + 10#64) chunk ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
              wordsAt (selfA + 400#64) c_uc.toList ∗
              wordsAt (fsp + 3696#64) c_uc.toList ∗
              relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
                (wordsBytes c_uc.toList) ∗
              memRegion (selfA + 528#64) 400 ∗
              copyScratchStackAt fsp sc ∗
              epilogueStoreStackPart1At fsp k ∗
              ((fsp + 232#64) ↦₆₄ selfA) ∗
              ((fsp + 512#64) ↦₆₄ k.w200) ∗
              ((fsp + 520#64) ↦₆₄ k.w208) ∗
              wordsAt (fsp + 528#64) k.tail.toList ∗
              memRegion (fsp + 576#64) 376 ∗
              memRegion (fsp + 568#64) 8 ∗
              memRegion (fsp + 952#64) 8 ∗
              memRegion (fsp + 976#64) 1776 ∗
              memRegion (fsp + 3152#64) 544 ∗
              memRegion (fsp + 3824#64) 8 ∗
              memRegion (fsp + 3856#64) 288 ∗
              Rest)) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = outA ∧
          sf.readReg64 .x20 = st.uc.epoch ∧
          sf.readReg64 .x21 = fsp + 3856#64 ∧
          sf.readReg64 .x22 = ack_val ∧
          sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 ∧
          sf.readReg64 .x24 = msgA ∧
          sf.readReg64 .x28 = fsp + 3272#64 ∧
          sf.readReg64 .x29 = fsp + 4144#64 ∧
          TraceCalleeSaved sf s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          LibsignalCodeLoaded lsmpl sf.mem ∧
          AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd ∧
          DecPost ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal st.receiving_ek chunk,
            decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec ∧
          PolyDecoderStrictSorted (addChunkTotal st.receiving_ek chunk)) := by
  have ⟨_, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hpre :
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest ⊢
      ∃∗ c_uc : Words16, ∃∗ sc : CopyScratchStack, ∃∗ k : EpilogueStoreStack,
        wordsAt (selfA + 400#64) c_uc.toList ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (fsp + 3832#64) 24 ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono
        (Relocatable.extract_128 (Relocatable.of_unchunkedCt1SentAt A.repAlloc st.uc)
          (selfA + 400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (memRegion_4144_entails_copyScratch_and_epilogueStack fsp))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, memRegion_3168_split_prefix fsp]
    apply Arm64.Entails.sepExists_elim; intro sc
    apply Arm64.Entails.sepExists_elim; intro k
    apply Arm64.Entails.sepExists_elim; intro c_uc
    refine Arm64.Entails.sepExists_right c_uc
      (Arm64.Entails.sepExists_right sc (Arm64.Entails.sepExists_right k ?_))
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_uc
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  refine ct1Sampled_seq_vm_lscro hcro
    (ArmCt1SampledPart3PlacedBudget.ct1Sampled_recv_ek_prefix_copy_pool_placed
      hmemcpy st_cost s_in fsp selfA k.we8 c_uc st.receiving_ek _
      hfsp_align hpc hrun hsp hx1) ?_
  intro s1 hpc1 hrun1 hcro1 _hvm01
    ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hx29_1, htr1⟩
  have hreord :
      wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) st.receiving_ek ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        memRegion (selfA + 528#64) 400 ∗
        A.pool lim st_cost s1 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (fsp + 3832#64) 24 ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) ⊢
      memRegion (fsp + 3832#64) 24 ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s1 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
            (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗
          epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3856#64) 288 ∗
          Rest) := Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hreord ?_
  refine SepWP.mono
    (ArmCt1SampledPart3PlacedBudget.ct1Sampled_recv_ek_add_and_decode_placed_ofPrePostEnv
      hadd_call hdec_call st_cost s0 s1 fsp msgA st.receiving_ek chunk
      (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
      hsort hdm hfits_add hfits_dec _ hcro1 hfsp_align hpc1 hrun1 hsp1
      (hx24_1.trans hx24) (htr1.trans htr)) ?_
  rintro sf Pf _ _ ⟨evsAdd, evsDec, hPf, hsp_sf, hx19_sf, hx20_sf, hx21_sf, hx22_sf,
    hx23_sf, hx24_sf, hx28_sf, hx29_sf, htr_sf, hcro_sf, hevs_add, hevs_dec, hsorted'⟩
  exact ⟨c_uc, sc, k, evsAdd, evsDec, hPf, hsp_sf,
    hx19_sf.trans (hx19_1.trans hx19),
    hx20_sf.trans (hx20_1.trans hx20),
    hx21_sf.trans (hx21_1.trans hx21),
    hx22_sf.trans (hx22_1.trans hx22),
    hx23_sf.trans (hx23_1.trans hx23),
    hx24_sf,
    hx28_sf.trans (hx28_1.trans hx28),
    hx29_sf.trans (hx29_1.trans hx29),
    htr_sf, hcro_sf, hcro_sf.1, hevs_add, hevs_dec, hsorted'⟩

theorem ct1Sampled_recv_ek_common_prefix_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits_add : FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64,
          addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩))
    (Rest : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11496#64) s_in
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest)
      (fun sf Pf =>
        ∃ (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
          (evsAdd evsDec : List AllocEvent),
          (Pf ⊢
            optVecU8At A.repAlloc (fsp + 3832#64)
              (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
            polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
            chunkAt (msgA + 10#64) chunk ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
              wordsAt (selfA + 400#64) c_uc.toList ∗
              wordsAt (fsp + 3696#64) c_uc.toList ∗
              relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
                (wordsBytes c_uc.toList) ∗
              memRegion (selfA + 528#64) 400 ∗
              copyScratchStackAt fsp sc ∗
              epilogueStoreStackPart1At fsp k ∗
              ((fsp + 232#64) ↦₆₄ selfA) ∗
              ((fsp + 512#64) ↦₆₄ k.w200) ∗
              ((fsp + 520#64) ↦₆₄ k.w208) ∗
              wordsAt (fsp + 528#64) k.tail.toList ∗
              memRegion (fsp + 576#64) 376 ∗
              memRegion (fsp + 568#64) 8 ∗
              memRegion (fsp + 952#64) 8 ∗
              memRegion (fsp + 976#64) 1776 ∗
              memRegion (fsp + 3152#64) 544 ∗
              memRegion (fsp + 3824#64) 8 ∗
              memRegion (fsp + 3856#64) 288 ∗
              Rest)) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = outA ∧
          sf.readReg64 .x20 = st.uc.epoch ∧
          sf.readReg64 .x21 = fsp + 3856#64 ∧
          sf.readReg64 .x22 = ack_val ∧
          sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 ∧
          sf.readReg64 .x24 = msgA ∧
          sf.readReg64 .x28 = fsp + 3272#64 ∧
          sf.readReg64 .x29 = fsp + 4144#64 ∧
          TraceCalleeSaved sf s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          LibsignalCodeLoaded lsmpl sf.mem ∧
          AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd ∧
          PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
            addChunkTotal st.receiving_ek chunk,
            decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec ∧
          PolyDecoderStrictSorted (addChunkTotal st.receiving_ek chunk)) :=
  ct1Sampled_recv_ek_common_prefix_placed_ofPrePostEnv
    hmemcpy hadd_call hdec_call st_cost s0 s_in fsp selfA outA msgA ack_val st chunk
    hlen hsort hfits_add hfits_dec Rest hcro hfsp_align hpc hrun hsp
    hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx28 hx29 htr

theorem ct1Sampled_recv_ek_common_prefix_cont_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {DecPre DecPost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits_add : FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (DecPre ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩))
    (Rest : SepProp) {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
        (evsAdd evsDec : List AllocEvent),
      sf.pc = (blkPl_332).base + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = outA →
      sf.readReg64 .x20 = st.uc.epoch →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x22 = ack_val →
      sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = fsp + 3272#64 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      LibsignalCodeLoaded lsmpl sf.mem →
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      DecPost ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal st.receiving_ek chunk,
        decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec →
      PolyDecoderStrictSorted (addChunkTotal st.receiving_ek chunk) →
      SepWP (lsProg_332 (Rust.withPanics ext)) target_pc sf
        (optVecU8At A.repAlloc (fsp + 3832#64)
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            wordsAt (selfA + 400#64) c_uc.toList ∗
            wordsAt (fsp + 3696#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) target_pc s_in
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest) post := by
  refine SepWP.seq
    (ct1Sampled_recv_ek_common_prefix_placed_ofPrePostEnv
      hmemcpy hadd_call hdec_call st_cost s0 s_in fsp selfA outA msgA ack_val st chunk
      hlen hsort hfits_add hfits_dec Rest hcro hfsp_align hpc hrun hsp
      hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx28 hx29 htr) ?_
  rintro sf Pf hpc_sf hrun_sf ⟨c_uc, sc, k, evsAdd, evsDec, hPf, hsp_sf, hx19_sf, hx20_sf,
    hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx28_sf, hx29_sf, htr_sf, hcro_sf, hcl_sf,
    hevs_add, hevs_dec, hsorted'⟩
  exact SepWP.weaken_pre hPf
    (hnext sf c_uc sc k evsAdd evsDec hpc_sf hrun_sf hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf
      hx23_sf hx24_sf hx28_sf hx29_sf htr_sf hcro_sf hcl_sf hevs_add hevs_dec hsorted')

theorem ct1Sampled_recv_ek_common_prefix_cont_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits_add : FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64,
          addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩))
    (Rest : SepProp) {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
        (evsAdd evsDec : List AllocEvent),
      sf.pc = (blkPl_332).base + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = outA →
      sf.readReg64 .x20 = st.uc.epoch →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x22 = ack_val →
      sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = fsp + 3272#64 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      LibsignalCodeLoaded lsmpl sf.mem →
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
        addChunkTotal st.receiving_ek chunk,
        decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec →
      PolyDecoderStrictSorted (addChunkTotal st.receiving_ek chunk) →
      SepWP (lsProg_332 (Rust.withPanics ext)) target_pc sf
        (optVecU8At A.repAlloc (fsp + 3832#64)
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            wordsAt (selfA + 400#64) c_uc.toList ∗
            wordsAt (fsp + 3696#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) target_pc s_in
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest) post :=
  ct1Sampled_recv_ek_common_prefix_cont_placed_ofPrePostEnv
    hmemcpy hadd_call hdec_call st_cost s0 s_in fsp selfA outA msgA ack_val st chunk
    hlen hsort hfits_add hfits_dec Rest hcro hfsp_align hpc hrun hsp
    hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx28 hx29 htr hnext

theorem ct1Sampled_recv_ek_common_prefix_sepWPp_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {DecPre DecPost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits_add : FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (DecPre ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩))
    (Rest : SepProp) {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
        (evsAdd evsDec : List AllocEvent),
      sf.pc = (blkPl_332).base + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = outA →
      sf.readReg64 .x20 = st.uc.epoch →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x22 = ack_val →
      sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = fsp + 3272#64 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      LibsignalCodeLoaded lsmpl sf.mem →
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      DecPost ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal st.receiving_ek chunk,
        decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec →
      PolyDecoderStrictSorted (addChunkTotal st.receiving_ek chunk) →
      SepWPp (lsProg_332 (Rust.withPanics ext)) ret_pc sf
        (optVecU8At A.repAlloc (fsp + 3832#64)
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            wordsAt (selfA + 400#64) c_uc.toList ∗
            wordsAt (fsp + 3696#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) post onPanic) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) ret_pc s_in
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest) post onPanic := by
  apply SepWPp.of_sepWP
  refine ct1Sampled_recv_ek_common_prefix_cont_placed_ofPrePostEnv
    (target_pc := (blkPl_332).base + 11496#64)
    hmemcpy hadd_call hdec_call st_cost s0 s_in fsp selfA outA msgA ack_val st chunk
    hlen hsort hfits_add hfits_dec Rest hcro hfsp_align hpc hrun hsp
    hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx28 hx29 htr ?_
  intro sf c_uc sc k evsAdd evsDec hpc_sf hrun_sf hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf
    hx23_sf hx24_sf hx28_sf hx29_sf htr_sf hcro_sf hcl_sf hevs_add hevs_dec hsorted'
  exact SepWP.done hpc_sf hrun_sf
    (hnext sf c_uc sc k evsAdd evsDec hpc_sf hrun_sf hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf
      hx23_sf hx24_sf hx28_sf hx29_sf htr_sf hcro_sf hcl_sf hevs_add hevs_dec hsorted')

theorem ct1Sampled_recv_ek_common_prefix_sepWPp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits_add : FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64,
          addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩))
    (Rest : SepProp) {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
        (evsAdd evsDec : List AllocEvent),
      sf.pc = (blkPl_332).base + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = outA →
      sf.readReg64 .x20 = st.uc.epoch →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x22 = ack_val →
      sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = fsp + 3272#64 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      LibsignalCodeLoaded lsmpl sf.mem →
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
        addChunkTotal st.receiving_ek chunk,
        decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec →
      PolyDecoderStrictSorted (addChunkTotal st.receiving_ek chunk) →
      SepWPp (lsProg_332 (Rust.withPanics ext)) ret_pc sf
        (optVecU8At A.repAlloc (fsp + 3832#64)
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            wordsAt (selfA + 400#64) c_uc.toList ∗
            wordsAt (fsp + 3696#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) post onPanic) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) ret_pc s_in
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest) post onPanic :=
  ct1Sampled_recv_ek_common_prefix_sepWPp_placed_ofPrePostEnv
    hmemcpy hadd_call hdec_call st_cost s0 s_in fsp selfA outA msgA ack_val st chunk
    hlen hsort hfits_add hfits_dec Rest hcro hfsp_align hpc hrun hsp
    hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx28 hx29 htr hnext

/-! ## 3. Path 4a (`outMsg = none, ack = false`: `+11496 -> s0.x30`) -/

set_option maxHeartbeats 2000000 in
/-- `VmPreserved`-preserving Path 4a from `+11496 -> s0.x30` (`outMsg = none, ack = false`):
    returns `Ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }`. -/
theorem ct1Sampled_path_none_no_ack_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx22 : s_in.readReg64 .x22 = 0#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A (fsp + 3832#64) none ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          resultV1RecvAt A (F := F) outA
            (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
          memRegion selfA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.seq
    (ArmCt1SampledPart3PlacedBudget.ct1Sampled_recv_ek_decode_branch_none_placed
      s_in fsp _ hfsp_align hpc hrun hsp) ?_
  intro s1 P1 hpc1 hrun1 ⟨hvm01, hP1, hsp1, hx19_1, _, _, hx22_1, hx23_1, _, _, hx29_1, htr1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_none_branch_no_ack_placed
      s1 _ hpc1 hrun1 (hx22_1.trans hx22)) ?_
  intro s2 P2 hpc2 hrun2 ⟨hvm12, hP2, hs2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hsp2 : s2.sp = fsp := by rw [hs2]; exact hsp1
  have hx19_2 : s2.readReg64 .x19 = outA := by rw [hs2, State.readReg64_setPC, hx19_1, hx19]
  have hx23_2 : s2.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 := by
    rw [hs2, State.readReg64_setPC, hx23_1, hx23]
  have hx29_2 : s2.readReg64 .x29 = fsp + 4144#64 := by rw [hs2, State.readReg64_setPC, hx29_1, hx29]
  have htr2 : TraceCalleeSaved s2 s0 := by rw [hs2]; exact htr1.trans htr
  have hpre2 :
      memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest ⊢
      ∃∗ c_enc : Words50, ∃∗ d400 : Split400,
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64,
      ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
      ∃∗ v4096 : BitVec 64, ∃∗ v4104 : BitVec 64, ∃∗ v4112 : BitVec 64,
        ⌜c_enc.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗ ⌜d400.mid352.length = 352⌝ ∗
        wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
        wordsAt (selfA + 256#64) c_enc.c2.toList ∗
        wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
        ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ split400At (fsp + 2752#64) d400 ∗
        memRegion (fsp + 1872#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗ ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗ ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          (relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
            memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
              memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
              memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
              memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
              memRegion (fsp + 4120#64) 24) ∗
            memRegion outA v1RecvSize ∗
            statesRecvSavedCells s0 ∗ Rest)) := by
    refine Entails.trans (Entails.of_eq (show _ =
        polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
          (wordsAt (fsp + 3696#64) c_uc.toList ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288) ∗
          (wordsAt (selfA + 400#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
            statesRecvSavedCells s0 ∗ Rest) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (polyEncoderAt_extract_words50 A selfA st.sending_ct1)
      (sepConj_mono (Relocatable.extract_split400 (Relocatable.of_polyDecoderAt A dec') (fsp + 2752#64))
        (sepConj_mono_left (memRegion_none_no_ack_split fsp c_uc)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Arm64.Entails.sepExists_elim; intro v976; apply Arm64.Entails.sepExists_elim; intro v984
    apply Arm64.Entails.sepExists_elim; intro v992; apply Arm64.Entails.sepExists_elim; intro vc90
    apply Arm64.Entails.sepExists_elim; intro vc98; apply Arm64.Entails.sepExists_elim; intro c_ca0
    apply Arm64.Entails.sepExists_elim; intro v4096; apply Arm64.Entails.sepExists_elim; intro v4104
    apply Arm64.Entails.sepExists_elim; intro v4112; apply Arm64.Entails.sepExists_elim; intro d400
    apply Arm64.Entails.sepExists_elim; intro c_enc
    refine Arm64.Entails.sepExists_right c_enc (Arm64.Entails.sepExists_right d400
      (Arm64.Entails.sepExists_right v976 (Arm64.Entails.sepExists_right v984
        (Arm64.Entails.sepExists_right v992 (Arm64.Entails.sepExists_right vc90
          (Arm64.Entails.sepExists_right vc98 (Arm64.Entails.sepExists_right c_ca0
            (Arm64.Entails.sepExists_right v4096 (Arm64.Entails.sepExists_right v4104
              (Arm64.Entails.sepExists_right v4112 ?_))))))))))
    dsimp only [words50At, mkC3FromEnc2Uc14, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_
  apply ProofLib.SepWP.exists_left; intro c_enc; apply ProofLib.SepWP.exists_left; intro d400
  apply ProofLib.SepWP.exists_left; intro v976; apply ProofLib.SepWP.exists_left; intro v984
  apply ProofLib.SepWP.exists_left; intro v992; apply ProofLib.SepWP.exists_left; intro vc90
  apply ProofLib.SepWP.exists_left; intro vc98; apply ProofLib.SepWP.exists_left; intro c_ca0
  apply ProofLib.SepWP.exists_left; intro v4096; apply ProofLib.SepWP.exists_left; intro v4104
  apply ProofLib.SepWP.exists_left; intro v4112
  wp_focus_pure; intro htag_enc
  wp_focus_pure; intro hmid352
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_copy_none_no_ack_part1_placed
      hmemcpy s2 fsp selfA c_enc.c0 c_enc.c1 c_enc.c2
      (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc)
      c_uc.w14 c_uc.w15 d400 sc k v976 v984 v992 vc90 vc98 v4096 v4104 v4112 _
      hmid352 hfsp_align hpc2 hrun2 hsp2 hx29_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hvm23, hP3, hsp3, hx19_3, hx23_3, hx29_3, htr3⟩
  let d := mkSplit928From528And400 c_enc.c0 c_enc.c1 c_enc.c2
    (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15 d400
  have hP3' : P3 ⊢
      copyScratchStackAt fsp (copyFullScratch sc d) ∗
      epilogueStoreStackPart1At fsp
        { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      mid376At (fsp + 976#64) c_uc.w14 c_uc.w15 d400.w0 d400.mid352 ∗
      wordsAt (fsp + 1352#64) d400.tail.toList ∗
      ((fsp + 3216#64) ↦₆₄ (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).w13) ∗
      ((fsp + 3224#64) ↦₆₄ (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).w14) ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
        wordsAt (selfA + 256#64) c_enc.c2.toList ∗
        wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
        ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
        memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 1872#64) 400 ∗ memRegion (fsp + 4096#64) 24 ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
          memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
          memRegion (fsp + 4120#64) 24) ∗
        memRegion outA v1RecvSize ∗
        statesRecvSavedCells s0 ∗ Rest) := Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hP3' ?_
  have htag_01 : c_enc.c0.w0 = 0#64 ∨ c_enc.c0.w0 = 1#64 := by
    rw [htag_enc]; exact polyEncoderTagVal_zero_or_one st.sending_ct1
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_copy_none_no_ack_part2_placed
      hmemcpy s3 fsp selfA outA c_enc.c0 c_enc.c1 c_enc.c2
      (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc)
      c_uc.w14 c_uc.w15 d400 sc k c_ca0 _
      htag_01 hmid352 hfsp_align hpc3 hrun3 hsp3
      (hx19_3.trans hx19_2) (hx23_3.trans (hx23_2.trans htag_enc.symm))) ?_
  intro s4 P4 hpc4 hrun4 ⟨hvm34, hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  let k' := epilogueStackOfSplit928 d noneCap k.w200 k.w208
  have hmid' : k'.mid.length = 376 := by
    dsimp only [k', epilogueStackOfSplit928, d, mkSplit928From528And400]
    exact mid376Bytes_length c_uc.w14 c_uc.w15 d400.w0 hmid352
  have hP4' : P4 ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        statesRecvSavedCells s0 ∗ Rest) := by
    refine Entails.trans hP4 ?_
    simp only [memRegion_out_960_split_states_key]
    have hself := chunks528_and_400_entails_memRegion_928 selfA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15
    have hstk3168 := memRegion_none_no_ack_join fsp
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 976#64) 376 ∗ memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 1872#64) 400 ∗
          memRegion (fsp + 3216#64) 16 ∗ memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗ memRegion (fsp + 4096#64) 24 ∗
          (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
            memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
            memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
            memRegion (fsp + 4120#64) 24)) ∗
        (wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
          wordsAt (selfA + 256#64) c_enc.c2.toList ∗
          wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
          ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
          memRegion (selfA + 528#64) 400) ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        statesRecvSavedCells s0 ∗ Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself)))))))))
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq
    (ArmCt1SampledPart3PlacedBudgetAux.ct1Sampled_epilogue_store_placed
      hmemcpy s4 fsp outA k' _ hmid' hfsp_align hpc4 hrun4 hsp4 hx19_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hvm45, hP5, hsp5, htr5⟩
  have heq_split : epilogueSplit928 s4 k' = d :=
    epilogueSplit928_of_eq s4 d noneCap k.w200 k.w208 hregs4
  have hP5' : P5 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA
          (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
        memRegion selfA chunkedStatesSize ∗ Rest) := by
    refine Entails.trans hP5 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp (copyFullScratch sc d) k' hmid'
    have hst_out := split928At_reconstruct_ct1Sampled_updated
      (A := A) outA st dec' c_enc c_uc d400 htag_enc hmid352
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s4.readReg64 .x20) k.w200 k.w208
    dsimp only [resultV1RecvAt, v1RecvAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗
          relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s4.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.mono
    (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epilogue_19324_placed
      s0 s5 _ hsp0_align hpc5 hrun5 hsp5
      (htr5.trans (htr4.trans (htr3.trans htr2)))) ?_
  intro sf Pf _ _ ⟨hvm5f, hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨hvm01.trans (hvm12.trans (hvm23.trans (hvm34.trans (hvm45.trans hvm5f)))),
    Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem ct1Sampled_path_none_no_ack_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx22 : s_in.readReg64 .x22 = 0#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) none ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          resultV1RecvAt A.repAlloc (F := F) outA
            (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre ?_
    (SepWP.mono
      (ct1Sampled_path_none_no_ack_placed (A := A.repAlloc) hmemcpy s0 s_in fsp selfA outA st
        dec' c_uc sc k (A.pool lim st_cost s_in ∗ Rest)
        hfsp_align hsp0_align hfsp hpc hrun hsp hx19 hx22 hx23 hx29 htr) ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  · rintro sf Pf _ _ ⟨hvm, hPf, hq⟩
    exact ⟨hvm,
      Entails.trans hPf
        (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm]; sep_ac_rfl)),
      hq⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7PlacedBudget
