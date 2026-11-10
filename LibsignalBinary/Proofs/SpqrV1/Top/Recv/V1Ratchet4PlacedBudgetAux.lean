/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4Placed
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable V1 `chain_from` & `add_epoch` (`+1856 -> +1976`)

Deterministic `v1ChainAfterKeyEvents` and budget-threaded steppers for `spqr::chain_from`
(`+1856..+1884`) and optional `<Chain>::add_epoch` (`+1888..+1976`) in `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Chain EpochSecret Error Message MlKem MsgPreamble PqRatchetState SpqrRecvModel States
   V1Recv V1State chainFrom msgPreamble spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi
   spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.RustHeap (vecU8Buf)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainGhost chainAddEpochStackX chainAt chainRepr epochSecretAt)
open CryptoVerification.SpqrV1.Drop (cap_add_one_beq_zero_false chunkedStatesAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (extractLsb_hi_append64 extractLsb_lo_append64)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost optEpochSecretAt)
open CryptoVerification.SpqrV1.Top.ChainFrom
  (ChainFromCall chainFromStackX optChainPBAt_protoRepr_eq_exists)
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
  (add_one_beq_zero_of_ne_noneCap chainAtHeap)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (chainResultAt noneCap spqrErrorTag)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS chainAt_extract_links_len_or_grow_ok
   chainErrorAt_sub3056_entails_words4 chainFrom_links_length_le chainRepr_sub_entails_words11
   chainWords11 epochSecretAt_sub3056_fold memRegion_1976_split_for_1888
   memRegion_2792_join_after_reloc memRegion_3088_split_for_chainFrom memRegion_4064_join_none
   memRegion_4064_join_some optEpochSecret_none_entails_of_hfold
   optEpochSecret_some_entails_of_hfold_v1 setWidth32_zeroExtend64 sp_setPState_v1_r4
   sp_sub_1160_add_960 sp_sub_1160_add_992 sp_sub_4992_aligned sp_sub_96_sub_112
   sp_sub_96_sub_128 sp_sub_96_sub_136_add sp_sub_96_sub_136_r4 sp_sub_96_sub_56
   sp_writeVReg128_v1_r4 spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_v1_addEpoch_panic stackAt_spqrRecvCallee_split
   v1ChainAfterKey vnTail_entails_optVersionNegotiationRefAt words11SubAt
   words11SubAt_entails_chainAt words4_sub3056_to_memRegion_32)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromAllocEnv ChainFromEnv chainFromSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget (seq_vm_clean)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64
attribute [local arm64_norm, local wp_norm]
  sp_sub_96_sub_56 sp_sub_96_sub_112 sp_sub_96_sub_128 sp_sub_96_sub_136_add sp_sub_96_sub_136_r4
  sp_sub_1160_add_960 sp_sub_1160_add_992
attribute [local simp, local arm64_norm, local wp_norm] setWidth32_zeroExtend64

theorem frame_pure_pre {Q : Prop} {P R F : SepProp} (hQ : Q) (heq : P = R ∗ F) :
    P ⊢ (⌜Q⌝ ∗ R) ∗ F := by
  rw [heq, sepConj_assoc]; exact Entails.pure_right hQ (Entails.refl _)

private theorem onPanic_false_budget {M : SpqrRecvModel} {st msg : VecArg} (s sm : State) :
    (⌜False⌝ : SepProp) ⊢ ⌜M.recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap :=
  Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm)
    (Entails.pure_left fun h => False.elim h)

omit [LibsignalPlacement] in
private theorem onPanic_of_v1_chainAddEpoch_budget {F : ShaCompress} {K : MlKem} {st msg : VecArg}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 : Chain} {es : EpochSecret}
    (hpre : msgPreamble msg.bytes = .ok pre) (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hv_key : v.key = some es) (s sm : State) :
    (⌜(Chain.addEpoch (spqrHkdfWith F) chain0 es).isOk = false ∧ sm.trace = s.trace⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(spqrV1Recv F K).recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left; rintro ⟨hpan, htr⟩
  exact Entails.pure_right
    ⟨spqrV1Recv_v1_addEpoch_panic hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hv_key hpan,
     htr ▸ List.prefix_refl _⟩
    (Entails.refl _)

/-- Deterministic allocator event list emitted across the optional `<Chain>::add_epoch` step
    (`+1888 .. +1976`): `[]` when `v.key = none`, and `chainAddEpochEvents ⟨selfPtr, esPtr, G0,
    ⟨kw0, kw1⟩, chain0, es⟩` when `v.key = some es`. -/
def v1ChainAfterKeyEvents (selfPtr esPtr : BitVec 64) (G0 : ChainGhost)
    (kw0 kw1 : BitVec 64) (chain0 : Chain) : Option EpochSecret → List AllocEvent
  | none => []
  | some es => chainAddEpochEvents ⟨selfPtr, esPtr, G0, ⟨kw0, kw1⟩, chain0, es⟩

/-! ## 1. `spqr::chain_from` Call & Error Branch (`+1856 .. +1884`) -/

/-- Envelope-parametric step `+1856 .. +1884`: `spqr::chain_from` call and error branch
    (`+2568`). -/
theorem step_v1_chainFrom_1856_placed_ofEnv {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env : List AllocEvent → Prop} (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp) (s0 s : State) (P : SepProp)
    (hFit_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain pre_pb.versionNegotiation))
    (hs0_align : s0.spAligned = true) (hsp4640_ne : s0.sp - 4640#64 ≠ 0#64)
    (hpc : s.pc = spqrRecvPlacedEntry + 1856#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 4592#64)
    (hx2 : s.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64))
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err : ∀ (evs_cf : List AllocEvent) (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
      BitVec.truncate 8 q0_err = spqrErrorTag e →
      s1.pc = spqrRecvPlacedEntry + 2568#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = noneCap → s1.readReg64 .x9 = w3_err →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 → s1.readReg64 .x25 = kw1 →
      s1.readReg64 .x26 = s0.sp - 1160#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ noneCap) ∗
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗ memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G0 : ChainGhost) (pad0 : BitVec 32)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      G0.linksCap ≠ noneCap →
      s1.pc = spqrRecvPlacedEntry + 1888#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = G0.linksCap → s1.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 → s1.readReg64 .x25 = kw1 →
      s1.readReg64 .x26 = s0.sp - 1160#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A.repAlloc G0 chain0 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
        ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
        ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
        memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hcf_ok := hC.chainFrom_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hcf_ok hpc hcont_err hcont_ok ⊢
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 323)
  refine SepWP.focus_weaken
    (Entails.of_eq (optChainPBAt_protoRepr_eq_exists A.repAlloc (s0.sp - 4592#64) pre_pb.chain)) (by sep_focus) ?_
  wp_pull_exists; rename_i gPb
  refine SepWP.focus_weaken (memRegion_3088_split_for_chainFrom s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d2096_0 d2096_1 d2096_2
  refine SepWP.focus_weaken
    (vnTail_entails_optVersionNegotiationRefAt A.repAlloc s0.sp w0 w1 pre_pb.versionNegotiation hsp4640_ne)
    (by sep_focus) ?_
  wp_pull_exists; rename_i P_vn_keep; wp_focus_pure; intro hfold_vn; wp_steps 1
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide))) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hcf_ok
    ((⟨s0.sp - 3056#64, s0.sp - 4592#64, if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64,
      gPb, ⟨w0, w1⟩, pre_pb.chain, pre_pb.versionNegotiation⟩ : ChainFromCall),
      MC.stepEvents evs0 st_cost)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 1860#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun sm => onPanic_false_budget _ sm) (fun _ _ => rfl)
    (by
      dsimp only [chainFromSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *], hFit_cf⟩
        (by simp only [State.writeReg32, State.sp_setPC, State.sp_advancePC, State.sp_setMem, State.sp_writeReg64,
            RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            sp_writeVReg128_v1_r4, sp_setPState_v1_r4, reduceCtorEq, ↓reduceIte, hsp]; sep_focus)) ?_
  intro sm hpcm hrunm hspm hcsm
  dsimp only [spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hxfp_c, hvregs_c⟩
  dsimp only [chainFromSpecX]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPpLS.exists_elim; intro evs_cf
  refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_cf⟩
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = kw0 := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = kw1 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = s0.sp - 1160#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  have hsp_eq := congrArg (stackAt · chainFromStackX) (hspm.symm.trans hspm')
  refine SepWPpLS.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  clear hsp_eq htr_sm hspm hx19_c hx20_c hx21_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hxfp_c hvregs_c
  clear hpc hrun hsp htr hx0 hx1 hx2 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 s
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpLS.focus_weaken hfold_vn (by sep_focus) ?_
  rw [← MC.stepEvents_append]
  cases hcf_res : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation with
  | error e =>
    have hnone1 : (noneCap + 1#64 == 0#64) = true := rfl
    apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 2568#64)
    dsimp only [chainResultAt]
    refine SepWP.focus_weaken (chainErrorAt_sub3056_entails_words4 s0.sp e) (by sep_focus) ?_
    wp_pull_exists; rename_i q0_err w3_err; wp_focus_pure; intro htag_q0
    refine seq_vm_clean (mid := (blkPl_329).base + 2568#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ noneCap) ∗
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗ memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
        s1.readReg64 .x8 = noneCap ∧ s1.readReg64 .x9 = w3_err ∧
        s1.readReg64 .x19 = ret ∧ s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧ s1.readReg64 .x22 = pre.epoch ∧
        s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x24 = kw0 ∧ s1.readReg64 .x25 = kw1 ∧
        s1.readReg64 .x26 = s0.sp - 1160#64 ∧ s1.readReg64 .x27 = s0.sp - 3056#64 ∧
        s1.readReg64 .x28 = 0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 7
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm1
        ⟨hsp1, htr1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1,
         hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
      rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) sm s1 hvm1]
      apply ProofLib.SepWP.done hpc1 hrun1
      exact hcont_err evs_cf e q0_err w3_err s1 _ hevs_cf hcf_res htag_q0
        hpc1 hrun1 hsp1 htr1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1
        hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 rfl
  | ok chain0 =>
    apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 1888#64)
    dsimp only [chainResultAt]
    refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A.repAlloc s0.sp 3056 chain0) (by sep_focus) ?_
    wp_pull_exists; rename_i G0 pad0; wp_focus_pure; intro hcap_ne
    have hc0 : (G0.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
    refine seq_vm_clean (mid := (blkPl_329).base + 1888#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A.repAlloc G0 chain0 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
        ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
        ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
        memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
        s1.readReg64 .x8 = G0.linksCap ∧ s1.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3 ∧
        s1.readReg64 .x19 = ret ∧ s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧ s1.readReg64 .x22 = pre.epoch ∧
        s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x24 = kw0 ∧ s1.readReg64 .x25 = kw1 ∧
        s1.readReg64 .x26 = s0.sp - 1160#64 ∧ s1.readReg64 .x27 = s0.sp - 3056#64 ∧
        s1.readReg64 .x28 = 0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
        wp_steps 7
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm],
           Entails.of_eq (by
             try dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
             sep_ac_rfl),
           ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | simp only [chainWords11, wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm1
        ⟨hsp1, htr1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1,
         hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
      rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) sm s1 hvm1]
      apply ProofLib.SepWP.done hpc1 hrun1
      exact hcont_ok evs_cf chain0 G0 pad0 s1 _ hevs_cf hcf_res hcap_ne
        hpc1 hrun1 hsp1 htr1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1
        hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 rfl

theorem step_v1_chainFrom_1856_placed {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp) (s0 s : State) (P : SepProp)
    (hFit_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain pre_pb.versionNegotiation))
    (hs0_align : s0.spAligned = true) (hsp4640_ne : s0.sp - 4640#64 ≠ 0#64)
    (hpc : s.pc = spqrRecvPlacedEntry + 1856#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 4592#64)
    (hx2 : s.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64))
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err : ∀ (evs_cf : List AllocEvent) (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
      BitVec.truncate 8 q0_err = spqrErrorTag e →
      s1.pc = spqrRecvPlacedEntry + 2568#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = noneCap → s1.readReg64 .x9 = w3_err →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 → s1.readReg64 .x25 = kw1 →
      s1.readReg64 .x26 = s0.sp - 1160#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ noneCap) ∗
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗ memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok : ∀ (evs_cf : List AllocEvent) (chain0 : Chain) (G0 : ChainGhost) (pad0 : BitVec 32)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      G0.linksCap ≠ noneCap →
      s1.pc = spqrRecvPlacedEntry + 1888#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = G0.linksCap → s1.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 → s1.readReg64 .x25 = kw1 →
      s1.readReg64 .x26 = s0.sp - 1160#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_cf) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A.repAlloc G0 chain0 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
        ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
        ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
        memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_chainFrom_1856_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb w0 w1 kw0 kw1 kw2 kw3 sckaMsg v P_key R s0 s P hFit_cf
    hs0_align hsp4640_ne hpc hrun hsp htr hx0 hx1 hx2 hx19 hx20 hx21 hx22
    hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hcont_err hcont_ok

/-! ## 2. `Chain` Relocation & `<Chain>::add_epoch` (`+1888 .. +1976`) -/

/-- Envelope-parametric step `+1888 .. +1976`: relocates `chain0` (88 bytes) from `s0.sp -
    3056#64` to `s0.sp - 232#64` (`x29 - 136`), computes `x22 := pre.epoch - 1#64`, checks
    `v.key : Option EpochSecret`, and if `v.key = some es`, calls `<Chain>::add_epoch`
    (`+1972`), unifying at `+1976`. -/
theorem step_v1_chain_reloc_and_addEpoch_1888_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env : List AllocEvent → Prop} (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp)
    (chain0 : Chain) (G0 : ChainGhost) (pad0 : BitVec 32) (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (hFit_add : ∀ es, v.key = some es →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainAddEpochEnv (spqrHkdfWith F) ⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1888#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G0.linksCap) (hx9 : s.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A.repAlloc G0 chain0 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
      ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
      ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_1976 : ∀ (chain1 : Chain) (G1 : ChainGhost) (s1 : State) (P1 : SepProp),
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      s1.pc = spqrRecvPlacedEntry + 1976#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch - 1#64 →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
        chainAt A.repAlloc (s0.sp - 232#64) G1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hadd_ok := hC.chainAddEpoch_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  dsimp only [chainWords11] at hx9
  have hlen54 : chain0.links.length ≤ 2 ^ 54 := chainFrom_links_length_le (F := F) (K := K) hst_len hdec hcf
  have hchainAt_232 := words11SubAt_entails_chainAt A.repAlloc s0.sp 232 G0 chain0 pad0
  subst hP
  rw [ProofLib.memRegion_split' (b := s0.sp - 4064#64) (n := 16) (k := 16) (b' := s0.sp - 4048#64) rfl (by bv_omega) (by decide)]
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hadd_ok hpc hcont_1976 ⊢
  cases hvk : v.key with
  | none =>
    have hfold_none : ∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst none := fun dst => hvk ▸ hfold_key dst
    have hent_none := optEpochSecret_none_entails_of_hfold A.repAlloc (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key hfold_none
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hent_none
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hent_none
    refine SepWPpLS.focus_weaken hent_none (by sep_focus) ?_
    refine SepWPpLS.focus_pure (by sep_focus) ?_; intro hkw0
    have hkw0_beq : (kw0 + 1#64 == 0#64) = true := by subst hkw0; rfl
    refine SepWPpLS.focus_weaken (memRegion_4064_join_none s0.sp) (by sep_focus) ?_
    apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 1976#64)
    refine SepWP.focus_weaken (memRegion_1976_split_for_1888 s0.sp) (by sep_focus) ?_
    wp_pull_exists; rename_i u232
    refine seq_vm_clean (mid := (blkPl_329).base + 1976#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
        chainAt A.repAlloc (s0.sp - 232#64) G0 chain0 ∗ memRegion (s0.sp - 144#64) 48 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
        s1.readReg64 .x19 = ret ∧ s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧ s1.readReg64 .x22 = pre.epoch - 1#64 ∧
        s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x28 = 0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt_232 ⊢
        simp only [BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit, Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]
        wp_steps 15
        refine SepWP.focus_weaken hchainAt_232 (by sep_focus) ?_
        refine SepWP.focus_weaken (words4_sub3056_to_memRegion_32 s0.sp G0.linksCap G0.linksPtr G0.linksHead
          (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length)) (by sep_focus) ?_
        refine SepWP.focus_weaken (memRegion_2792_join_after_reloc s0.sp
          G0.nextRoot.cap G0.nextRoot.ptr (BitVec.ofNat 64 chain0.nextRoot.length)
          chain0.currentEpoch chain0.sendEpoch (chain0.params.maxOooKeys ++ chain0.params.maxJump)
          (pad0 ++ chain0.dir.toI32) G0.linksPtr G0.linksHead
          (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length)) (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx28_1, hx29_1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
      apply ProofLib.SepWP.done hpc1 hrun1
      exact hcont_1976 chain0 G0 s1 _ (by simp [v1ChainAfterKey, hvk])
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx28_1 hx29_1
        (by simp only [v1ChainAfterKeyEvents, hvk, List.append_nil])
  | some es =>
    have hfold_some : ∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst (some es) := fun dst => hvk ▸ hfold_key dst
    have hent_some := optEpochSecret_some_entails_of_hfold_v1 A.repAlloc (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key es hfold_some
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hent_some
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hent_some
    refine SepWPpLS.focus_weaken hent_some (by sep_focus) ?_
    refine SepWPpLS.focus_pure (by sep_focus) ?_; intro hkw0_lt
    have hkw0_beq : (kw0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hkw0_lt)
    apply SepWPpLS.of_sepWP (mid := lsmpl.base 368)
    refine SepWP.focus_weaken (memRegion_1976_split_for_1888 s0.sp) (by sep_focus) ?_
    wp_pull_exists; rename_i u232
    refine seq_vm_clean (mid := lsmpl.base 368)
      (P_mid :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        epochSecretAt A.repAlloc (s0.sp - 3056#64) ⟨kw0, kw1⟩ es ∗
        memRegion (s0.sp - 3024#64) 2792 ∗
        chainAt A.repAlloc (s0.sp - 232#64) G0 chain0 ∗ memRegion (s0.sp - 144#64) 48 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
        s1.readReg64 .x0 = s0.sp - 232#64 ∧ s1.readReg64 .x1 = s0.sp - 3056#64 ∧
        s1.readReg64 .x19 = ret ∧ s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧ s1.readReg64 .x22 = pre.epoch - 1#64 ∧
        s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x28 = 0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 Reg.lr = (blkPl_329).base + 1976#64)
      ?_ ?_
    · by_vm_steps (
        dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt_232 ⊢
        simp only [BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit, Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]
        wp_steps 22
        refine SepWP.focus_weaken hchainAt_232 (by sep_focus) ?_
        refine SepWP.focus_weaken (epochSecretAt_sub3056_fold A.repAlloc s0.sp kw0 kw1 es) (by sep_focus) ?_
        refine SepWP.focus_weaken (memRegion_4064_join_some s0.sp (BitVec.ofNat 64 es.secret.length) es.epoch) (by sep_focus) ?_
        refine SepWP.focus_weaken (memRegion_2792_join_after_reloc s0.sp
          G0.nextRoot.cap G0.nextRoot.ptr (BitVec.ofNat 64 chain0.nextRoot.length)
          chain0.currentEpoch chain0.sendEpoch (chain0.params.maxOooKeys ++ chain0.params.maxJump)
          (pad0 ++ chain0.dir.toI32) G0.linksPtr G0.linksHead
          (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length)) (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm1
        ⟨hsp1, ⟨htr1, hvregs1⟩, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx28_1, hx29_1, hlr1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
      apply ProofLib.SepWP.done hpc1 hrun1
      refine SepWPpLS.focus_weaken
        (chainAt_extract_links_len_or_grow_ok A.repAlloc (s0.sp - 232#64) G0 chain0 hlen54) (by sep_focus) ?_
      refine SepWPpLS.focus_pure (by sep_focus) ?_; intro hgrow
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainAddEpochStackX (by decide))) (by sep_focus) ?_
      have hs1_align : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact hfsp_align
      refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hadd_ok
        ((⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩ : ChainAddEpochGhost),
          MC.stepEvents evs0 st_cost)
        hpc1 hrun1 hs1_align hlr1
        (by rw [htr1])
        (fun sm => by
          dsimp only [chainAddEpochSpecX]
          exact onPanic_of_v1_chainAddEpoch_budget hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hvk s1 sm)
        (fun _ _ => rfl)
        (by
          dsimp only [chainAddEpochSpecX]
          rw [hsp1]
          exact frame_pure_pre ⟨hx0_1, hx1_1, hgrow, hFit_add es hvk, by
            rw [hlr1]
            exact lsRetAddr624_blockPlacement_base_add 329 1976#64 (by decide) (by decide)⟩ (by sep_focus)) ?_
      intro sm hpcm hrunm hspm hcsm
      rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, _, _, _, _, hx28_c, hxfp_c, hvregs_c⟩
      dsimp only [chainAddEpochSpecX]
      have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp1]
      have hsp_eq := congrArg (stackAt · chainAddEpochStackX) (hspm.symm.trans hspm')
      cases hadd_res : Chain.addEpoch (spqrHkdfWith F) chain0 es with
      | error _ => dsimp only; exact SepWPpLS.focus_pure (by sep_focus) False.elim
      | ok chain1 =>
        dsimp only
        refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, _⟩
        have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr1], by rw [hvregs_c, hvregs1]⟩
        have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_1]
        have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_1]
        have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_1]
        have hx22_sm : sm.readReg64 .x22 = pre.epoch - 1#64 := by rw [hx22_c, hx22_1]
        have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c, hx23_1]
        have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c, hx28_1]
        have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
          change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; exact hx29_1
        have hsp_stk : stackAt s1.sp chainAddEpochStackX = stackAt (s0.sp - 4992#64) chainAddEpochStackX := by
          rw [hsp1]
        refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk) (by sep_focus) ?_
        refine SepWPpLS.focus_weaken
          (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainAddEpochStackX (by decide)).symm)
          (by sep_focus) ?_
        unfold chainRepr; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWPpLS.exists_left hrunm; intro G1
        rw [← MC.stepEvents_append]
        exact hcont_1976 chain1 G1 sm _ (by simp [v1ChainAfterKey, hvk, hadd_res])
          hpcm hrunm hspm' htr_sm' hx19_sm hx20_sm hx21_sm hx22_sm hx23_sm hx28_sm hx29_sm
          (by simp only [v1ChainAfterKeyEvents, hvk]; sep_ac_rfl)

theorem step_v1_chain_reloc_and_addEpoch_1888_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp)
    (chain0 : Chain) (G0 : ChainGhost) (pad0 : BitVec 32) (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (hFit_add : ∀ es, v.key = some es →
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainAddEpochEnv (spqrHkdfWith F) ⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1888#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G0.linksCap) (hx9 : s.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A.repAlloc G0 chain0 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
      ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
      ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_1976 : ∀ (chain1 : Chain) (G1 : ChainGhost) (s1 : State) (P1 : SepProp),
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      s1.pc = spqrRecvPlacedEntry + 1976#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch - 1#64 →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
        chainAt A.repAlloc (s0.sp - 232#64) G1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_chain_reloc_and_addEpoch_1888_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb pb w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R
    chain0 G0 pad0 s0 s P hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
    hfold_key hFit_add hs0_align hpc hrun hsp htr hx8 hx9 hx19 hx20 hx21 hx22
    hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hcont_1976

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudgetAux
