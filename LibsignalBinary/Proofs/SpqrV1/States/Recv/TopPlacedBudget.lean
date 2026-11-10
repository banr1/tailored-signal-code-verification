/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesTopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3PlacedBudget

/-!
# `<States>::recv` (Block `332`): Budget-Threaded Relocatable Top-Level Assembly

Defines the constructor-dispatched envelope `StatesRecvExactEnv` and combines all budget-threaded
arms of Block `332` to prove `states_recv_placed_ok_x` and `states_recv_placed_ok_x_closed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost statesRecvRoPlacedAt)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (spqrMlkemDecapsSym)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym spqrMlkemEncaps2Sym)
open LibsignalBinary.Heap
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (RecvCt2PlacedAlloc)

/-- Constructor-dispatched allocation-event envelope for `<States>::recv` (`Block 332`),
    dispatching each `States` constructor to its proved arm envelope with zero existentials. -/
def StatesRecvExactEnv {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .keysUnsampled _ => DefsPlacedBudget.StatesRecvEnv x evs
  | .keysSampled _ => DefsPlacedBudget.StatesRecvEnv x evs
  | .headerSent st => ArmHeaderSent2PlacedBudget.HeaderSentArmEnv st x.msg evs
  | .ct1Received _ => DefsPlacedBudget.StatesRecvEnv x evs
  | .ekSentCt1Received _ => ArmEkSentCt1Received2PlacedBudget.StatesRecvEkSentCt1ReceivedEnv x evs
  | .noHeaderReceived _ => ArmNoHeaderReceived2PlacedBudget.StatesRecvNoHeaderReceivedEnv x evs
  | .headerReceived _ => DefsPlacedBudget.StatesRecvEnv x evs
  | .ct1Sampled st => ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvEnv K st x.msg evs
  | .ekReceivedCt1Sampled _ =>
    ArmEkReceivedCt1SampledPlacedBudget.StatesRecvEkReceivedCt1SampledEnv K x evs
  | .ct1Acknowledged _ =>
    ArmCt1Acknowledged3PlacedBudget.StatesRecvCt1AcknowledgedEnv K x evs
  | .ct2Sampled _ => DefsPlacedBudget.StatesRecvEnv x evs

example {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    StatesRecvExactEnv K ⟨0#64, 0#64, 0#64, .keysUnsampled st, msg⟩ [] :=
  SpqrBoundedEvs.nil _ _

theorem states_recv_variant_placed_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K st msg
          (StatesRecvExactEnv K))) := by
  cases st with
  | keysUnsampled s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmsSimple1PlacedBudget.states_recv_keysUnsampled_placed_ok_cro_ext M A lim F K ext hC s msg)
  | keysSampled s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmKeysSampled2PlacedBudget.states_recv_keysSampled_cro_placed_ok_ext M A lim F K ext hC s msg)
  | headerSent s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmHeaderSent2PlacedBudget.states_recv_headerSent_env_placed_ok_ext M A lim F K ext hC s msg)
  | ct1Received s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmCt1Received2PlacedBudget.states_recv_ct1Received_cro_placed_ok_ext M A lim F K ext hC s msg)
  | ekSentCt1Received s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmEkSentCt1Received2PlacedBudget.states_recv_ekSentCt1Received_placed_ok_ext M A lim F K ext hC s msg)
  | noHeaderReceived s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmNoHeaderReceived2PlacedBudget.states_recv_noHeaderReceived_placed_ok_ext M A lim F K ext hC s msg)
  | headerReceived s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmsSimple2PlacedBudget.states_recv_headerReceived_placed_ok_cro_ext M A lim F K ext hC s msg)
  | ct1Sampled s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmCt1SampledPart10PlacedBudget.states_recv_ct1Sampled_placed_ok_ext M A lim F K ext hC s msg)
  | ekReceivedCt1Sampled s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmEkReceivedCt1SampledPlacedBudget.states_recv_ekReceivedCt1Sampled_placed_ofEnv_cro_ok_ext
        A lim F K ext hC s msg)
  | ct1Acknowledged s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmCt1Acknowledged3PlacedBudget.states_recv_ct1Acknowledged_placed_ofEnv_ok_ext
        A lim F K ext hC s msg)
  | ct2Sampled s =>
    exact DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (ArmsSimple3PlacedBudget.states_recv_ct2Sampled_placed_ok_cro_ext M A lim F K ext hC s msg)

theorem states_recv_variant_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K st msg
          (StatesRecvExactEnv K))) :=
  CryptoVerification.SpqrV1.ls_subroutine_ok_to_blockProgram
    (states_recv_variant_placed_ext A lim F K ext hC st msg)

theorem states_recv_placed_ok_ext_of_variants [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hvar : ∀ (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (lsProg_332 (Rust.withPanics ext))
        (lsmpl.base 332)
        (withLsCodeRoLoaded lsmpl
          (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K st msg
            (StatesRecvExactEnv K)))) :
    DefsPlacedBudget.StatesRecvPlacedOkExtOfEnv M A lim F K ext (StatesRecvExactEnv K) :=
  DefsPlacedBudget.states_recv_placed_ok_ext_of_variants_ofEnv hvar

theorem states_recv_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext) :
    DefsPlacedBudget.StatesRecvPlacedOkExtOfEnv M A lim F K ext (StatesRecvExactEnv K) :=
  states_recv_placed_ok_ext_of_variants A lim F K ext
    (states_recv_variant_placed_ext A lim F K ext hC)

theorem states_recv_placed_ok_x_of_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : DefsPlacedBudget.StatesRecvPlacedOkExtOfEnv M A lim F K ext (StatesRecvExactEnv K)) :
    StatesPlacedSeamsBudget.StatesRecvPlacedOkXOfEnv M A lim F K ext (StatesRecvExactEnv K) :=
  DefsPlacedBudget.states_recv_placed_ok_x_of_ext_ofEnv h

theorem states_recv_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext) :
    StatesPlacedSeamsBudget.StatesRecvPlacedOkXOfEnv M A lim F K ext (StatesRecvExactEnv K) :=
  states_recv_placed_ok_x_of_ext (states_recv_placed_ok_ext A lim F K ext hC)

theorem statesRecvPlacedContracts_of_ro_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk_sat : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2_sat : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hdecaps_sat : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac_sat : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec F M A lim)) :
    DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext :=
  let hmemcpy_reg_sat :=
    States.Leaves.LeavesTopPlacedBudget.hookSat_sessionMemcpyRegionBudget_of_framelessAcp hA.memcpy
  let hshim_sess :=
    States.Leaves.LeavesTopPlacedBudget.hookSat_sessionShimBudget_of_rustAllocShimVm hA.shim
  DefsPlacedBudget.StatesRecvPlacedContracts.of_callees
    (ls_subroutine_ok_of_block (i := 332) (j := 370)
      (States.Leaves.LeavesTopPlacedBudget.keys_sampled_recv_ct1_chunk_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 337)
      (States.Leaves.LeavesTopPlacedBudget.header_sent_recv_ct1_chunk_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hmemcpy_reg_sat hmemmove_sat hmemset_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 346)
      (States.Leaves.LeavesTopPlacedBudget.ct1_received_recv_ct2_chunk_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 350)
      (States.Leaves.LeavesTopPlacedBudget.ek_sent_ct1_received_recv_ct2_chunk_placed_ok_x
        hA hmemcpy_reg_sat hmemmove_sat hmemset_sat hdecaps_sat hhmac_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 369)
      (States.Leaves.LeavesTopPlacedBudget.noHeaderReceived_recv_hdr_chunk_placed_closed_okX
        hA.shim hA.alloc hA.realloc hA.dealloc hA.memcpy hmemcpy_reg_sat hA.memcpyRO
        hmemmove_sat hmemset_sat hhmac_sat
        hA.handleError hA.assertFailedU64 hA.sliceIndexFail hA.panicBoundsCheck))
    (ls_subroutine_ok_of_block (i := 332) (j := 419)
      (States.Leaves.LeavesTopPlacedBudget.add_chunk_cl_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hmemmove_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 418)
      (States.Leaves.LeavesTopPlacedBudget.polyDecoderDecodedMessage_cro_placed_ok_x
        hA.handleError hshim_sess hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat hmemset_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 338)
      (States.Leaves.LeavesTopPlacedBudget.unchunked_ct1_sent_recv_ek_placed_cl_twoEnv_ok_x
        (F := F) hA.dealloc hval_pk_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 347)
      (States.Leaves.LeavesTopPlacedBudget.unchunked_ct1_sent_ek_received_send_ct2_cl_placed_ok
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hA.memcpy hA.memcpyRO hencaps2_sat hhmac_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 382)
      (States.Leaves.LeavesTopPlacedBudget.send_ct2_encoder_placed_ok_x_of_rustAllocShimVm
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc hmemcpy_reg_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 343)
      (States.Leaves.LeavesTopPlacedBudget.ek_received_ct1_sampled_recv_ct1_ack_placed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hA.memcpy hmemcpy_reg_sat hA.memcpyRO hencaps2_sat hhmac_sat))
    (keys_ls_subroutine_ok_of_block_cro (i := 332) (j := 349)
      (States.Leaves.LeavesTopPlacedBudget.ct1_acknowledged_recv_ek_chunk_placed_closed_ok_x
        hA.handleError hA.shim hA.alloc hA.realloc hA.dealloc
        hA.memcpy hmemcpy_reg_sat hA.memcpyRO hmemmove_sat hmemset_sat
        hval_pk_sat hencaps2_sat hhmac_sat))
    (ls_subroutine_ok_of_block (i := 332) (j := 355)
      (States.Leaves.LeavesTopPlacedBudget.ct2_sampled_recv_next_epoch_placed_ok_x hA.dealloc))
    (States.Leaves.LeavesTopPlacedBudget.hookSat_withVmPreserved_noAllocShim_of_rustAllocShimVm
      hA.shim)
    hA.alloc
    hA.dealloc
    (States.Leaves.LeavesTopPlacedBudget.hookSat_sessionMemcpyBudget_of_framelessAcp hA.memcpy)
    (States.Leaves.LeavesTopPlacedBudget.hookSat_withVmPreserved_memcpyRO_of_ro hA.memcpyRO)

theorem states_recv_placed_ok_x_closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hmemset_sat : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hval_pk_sat : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K)))
    (hencaps2_sat : HookSat (Rust.withPanics ext) spqrMlkemEncaps2Sym
      (withVmPreserved (mlkemEncaps2Spec K)))
    (hdecaps_sat : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac_sat : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec F M A lim)) :
    StatesPlacedSeamsBudget.StatesRecvPlacedOkXOfEnv M A lim F K ext (StatesRecvExactEnv K) :=
  states_recv_placed_ok_x A lim F K ext
    (statesRecvPlacedContracts_of_ro_leaves
      hA hmemmove_sat hmemset_sat hval_pk_sat hencaps2_sat hdecaps_sat hhmac_sat)

theorem rodata_ctLabel_statesRecv_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ P :=
  CryptoVerification.SpqrV1.States.Recv.Top.rodata_ctLabel_statesRecv_placed hro hP

theorem rodata_statesRecvRoPlacedAt [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp}
    (hP : m ⊨ (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ P) :
    m ⊨ statesRecvRoPlacedAt ∗ P :=
  CryptoVerification.SpqrV1.States.Recv.Top.rodata_statesRecvRoPlacedAt hro hP

end LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget
