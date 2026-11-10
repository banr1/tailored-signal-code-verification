/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500Placed

/-!
# Relocatable Top-Level Assembly for `spqr::recv`

Discharges `V0ChainPlacedTail`, `InitInnerPlacedTail`, and `V1RatchetPlacedTailLS` and proves
the relocatable `spqr_recv_placed_ok` and `blockProgram` theorems for `spqr::recv` (Block `329`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open CryptoVerification.SpqrV1.Top.Recv.Placed
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `V0ChainPlacedTail` (`+496 -> s0.x30`) and `InitInnerPlacedTail` (`+1076 -> s0.x30`) -/

/-- `Ordering::Greater` (`V0ChainPlacedTail` at `+496`) satisfied via
    `step_ordering_greater_placed` (`Part9Placed.lean`). -/
theorem v0ChainPlacedTail_ok
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true) :
    V0ChainPlacedTail A F K ext st msg ret s0 R :=
  step_ordering_greater_placed hC st msg ret hst_len s0 R hs0_align

/-- `Ordering::Less` (`InitInnerPlacedTail` at `+1076`) satisfied via
    `step_ordering_less_placed` (`Part7Placed.lean`). -/
theorem initInnerPlacedTail_ok
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat) :
    InitInnerPlacedTail A F K ext st msg ret s0 R := by
  intro pre remPtr pre_pb vn pb w0 w1 w26 s P
    hpre _hrem hdec hvn hinner _hw0 hw26 hmin hver_lt
    hpc hrun hsp htr hx19 hx20 _hx21 _hx22 _hx23 _hx24 hx25 hx26 _hx27 _hx28 hx29 hP
  exact step_ordering_less_placed hC st msg ret pre pre_pb vn pb w0 w1 w26
    hst_len hpre hdec hvn hinner hw26 hmin hver_lt s0 s P R hs0_align
    (sp_sub_4992_ne_zero hsp_lo) hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

/-! ## 2. `V1RatchetPlacedTailLS` (`+1532 -> s0.x30`) from `V1Ratchet3Placed`, `V1Ratchet4Placed`, `V1RatchetErr2500Placed`, `V1Ratchet5Placed` -/

/-- Introduce `Drop.chunkedStatesLocal2JumpTablePlacedAt` in `SepWPpLS` from
    `LibsignalCodeRoLoaded lsmpl s.mem`. -/
theorem sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt
    {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (h : SepWPpLS prog target s (Drop.chunkedStatesLocal2JumpTablePlacedAt ∗ P) Q Qp) :
    SepWPpLS prog target s P Q Qp := by
  intro hcrl F hmem hL
  exact h hcrl F
    (Satisfies.mono (Entails.of_eq (by ac_rfl))
      (rodata_chunkedStatesLocal2JumpTablePlacedAt hcrl.2 hmem))
    hL

/-- Post-`+1856` continuation interface for the relocatable V1 ratchet path (`+1856 -> s0.x30`),
    matching the `hok_1856` continuation of `step_v1_ratchet_1532_to_1856_placed`
    (`V1Ratchet3Placed.lean`). -/
def V1RatchetPlacedChainContinuation
    (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : Prop :=
  ∀ (_hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64),
    st.bytes.length < 2 ^ 32 →
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    Proto.spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ DecodeState.none2Cap →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    s0.spAligned = true →
    spqrRecvStack ≤ s0.sp.toNat →
    ∀ (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          States.Recv.optEpochSecretAt A dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        Top.MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)

/-- Unconditional proof of `V1RatchetPlacedChainContinuation` (`+1856 -> s0.x30`) composing
    `step_v1_ratchet_1856_to_2664_placed` (`V1Ratchet4Placed.lean`),
    `step_chainFrom_err_2568_placed` + `step_recvKey_err_2028_placed`
    (`V1RatchetErr2500Placed.lean`), and `step_v1_ok_2664_to_ret_placed`
    (`V1Ratchet5Placed.lean`). -/
theorem v1RatchetPlacedChainContinuation_ok
    (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) :
    V1RatchetPlacedChainContinuation H_inner A F K ext st msg ret s0 R := by
  intro hC pre _remPtr pre_pb pb w0 w1 hst_len hpre _hvalid hdec hinner _hw0 hmv hmin hs0_align hsp_lo
    sckaMsg st0 v kw0 kw1 kw2 kw3 P_key s1 P1 hmsg hfrom hrecv hfold_key
    hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
  have hep0 : (pre.epoch == 0#64) = false := msgPreamble_epoch_beq_zero_false hpre hmv
  have hsp4640_ne : s0.sp - 4640#64 ≠ 0#64 := sp_sub_4640_ne_zero hsp_lo
  refine step_v1_ratchet_1856_to_2664_placed hC st msg ret pre pre_pb pb
    w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R s0 s1 P1
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hfold_key hs0_align hsp4640_ne
    hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    ?_ ?_ ?_
  · intro e q0_err w3_err s_err P_err hcf htag_q0
      hpc_e hrun_e hsp_e htr_e _hx8_e _hx9_e hx19_e _hx20_e _hx21_e _hx22_e hx23_e hx24_e hx25_e _hx26_e _hx27_e hx28_e _hx29_e hP_err
    obtain ⟨herr, hnp⟩ := spqrV1Recv_v1_chainFrom_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
    subst hP_err
    apply sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
    exact step_chainFrom_err_2568_placed A F K ext hC
      st msg ret pre_pb w0 w1 sckaMsg v kw0 kw1 kw2 kw3 P_key hfold_key
      e q0_err w3_err herr htag_q0 s0 s_err _ R _ rfl hs0_align
      hpc_e hrun_e hsp_e htr_e hx19_e hx23_e hx24_e hx25_e hx28_e (by ac_rfl) hcl
  · intro chain0 chain1 err w1_err w2_err w3_err G1' s_err P_err
      hcf hkey hrk hw1_err hpc_e hrun_e hsp_e htr_e hx19_e hx21_e hx22_e hx23_e hx24_e hx26_e hx29_e hP_err
    obtain ⟨herr, hnp⟩ := spqrV1Recv_v1_recvKey_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
        (topResult_addEpoch_of_v1ChainAfterKey hkey) hrk
    subst hP_err
    apply sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
    exact step_recvKey_err_2028_placed A F K ext hC
      st msg ret pre_pb w0 w1 sckaMsg v G1' chain1 err w1_err w2_err w3_err herr hw1_err
      s0 s_err _ R _ rfl hs0_align
      hpc_e hrun_e hsp_e htr_e hx19_e hx21_e hx22_e hx23_e hx24_e hx26_e hx29_e (by ac_rfl) hcl
  · intro chain0 chain1 chain2 G2 rawKey cap_rk ptr_rk s_ok P_ok
      hcf hkey hrk hpc_ok hrun_ok hsp_ok htr_ok hx19_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx26_ok hx29_ok hP_ok
    rcases v with ⟨key, st1⟩
    exact step_v1_ok_2664_to_ret_placed hC st msg ret pre pre_pb pb sckaMsg st0 st1 key
      chain0 chain1 chain2 G2 rawKey w0 w1 cap_rk ptr_rk
      hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
      (topResult_addEpoch_of_v1ChainAfterKey hkey) hrk
      s0 s_ok P_ok R hs0_align hpc_ok hrun_ok hsp_ok htr_ok
      hx19_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx26_ok hx29_ok hP_ok

/-- Compose `step_v1_ratchet_1532_to_1856_placed` (`V1Ratchet3Placed.lean`) with
    `V1RatchetPlacedChainContinuation` to discharge `V1RatchetPlacedTailLS` (`+1532 -> s0.x30`). -/
theorem v1RatchetPlacedTail_of_chainContinuation
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hcont : V1RatchetPlacedChainContinuation H_inner A F K ext st msg ret s0 R) :
    V1RatchetPlacedTailLS A F K ext st msg ret s0 R := by
  intro pre remPtr pre_pb pb w0 w1 s P
    hpre hvalid hdec hinner hw0 hmv hmin
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP
  exact step_v1_ratchet_1532_to_1856_placed hC st msg ret pre remPtr pre_pb pb w0 w1
    hst_len hpre hvalid hdec hinner hmv hmin s0 s P R hs0_align
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP
    (hcont hC pre remPtr pre_pb pb w0 w1 hst_len hpre hvalid hdec hinner hw0 hmv hmin hs0_align hsp_lo)

/-- Unconditional proof of `V1RatchetPlacedTailLS` (`+1532 -> s0.x30`) from
    `SpqrRecvPlacedContracts` and `spqrRecvStack ≤ s0.sp.toNat`. -/
theorem v1RatchetPlacedTail_ok
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat) :
    V1RatchetPlacedTailLS A F K ext st msg ret s0 R :=
  v1RatchetPlacedTail_of_chainContinuation hC st msg ret s0 R hst_len hs0_align hsp_lo
    (v1RatchetPlacedChainContinuation_ok H_inner A F K ext st msg ret s0 R)

/-! ## 3. Top-Level Relocatable `spqr::recv` (`Block 329`) Composition -/

/-- `SepWPpLS` execution of `spqr::recv` (`Block 329`) from `SpqrRecvPlacedContracts` and
    `spqrRecvStack ≤ s0.sp.toNat` (with `v0ChainPlacedTail_ok`, `initInnerPlacedTail_ok`, and
    `v1RatchetPlacedTail_ok` wired in). -/
theorem spqrRecv_placed_sepWPpLS_of_contracts
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) :=
  spqrRecv_placed_sepWPpLS_of_tails H_inner hC st msg ret s0 P R hst_len
    (v0ChainPlacedTail_ok hC st msg ret s0 R hst_len hsp_align)
    (initInnerPlacedTail_ok hC st msg ret s0 R hst_len hsp_align hsp_lo)
    (v1RatchetPlacedTail_ok hC st msg ret s0 R hst_len hsp_align hsp_lo)
    hpc hrun hsp_align hx0 hx1 hx8 hP

/-- `spqr::recv` (`Block 329`) satisfies `spqrRecvPlacedSpecXT A (spqrV1Recv F K)` on
    `spqrRecvPlacedProg ext` from `SpqrRecvPlacedContracts` alone. -/
theorem spqrRecv_placed_ok_of_contracts
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) :=
  spqrRecv_placed_ok_of_tails H_inner hC
    (fun st msg ret s0 R hst_len hsp_align => v0ChainPlacedTail_ok hC st msg ret s0 R hst_len hsp_align)
    (fun st msg ret s0 R hst_len hsp_align hsp_lo => initInnerPlacedTail_ok hC st msg ret s0 R hst_len hsp_align hsp_lo)
    (fun st msg ret s0 R hst_len hsp_align hsp_lo => v1RatchetPlacedTail_ok hC st msg ret s0 R hst_len hsp_align hsp_lo)

theorem spqr_recv_placed_ok_of_contracts
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) :=
  spqrRecv_placed_ok_of_contracts hC

theorem spqr_recv_placed_ok_blockProgram_of_contracts
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) := by
  have hok := spqr_recv_placed_ok_of_contracts hC
  rwa [← IsLsBlockProg.eq_blockProgram (prog := spqrRecvPlacedProg ext)]

/-- Top-level relocatable `spqr::recv` (`Block 329`) theorem parameterized by
    `StatesPlacedSeams` and placed callee contracts. -/
theorem spqr_recv_placed_ok
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpySpec)
    (hDropEpochSlice : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (Drop.dropProtoEpochSliceSpec A)))
    (hDropOptProtoInnerState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hDropOptProtoChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (Drop.dropOptProtoSpqrChainSpec A)))
    (hDropChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (Drop.dropSpqrChainSpec A)))
    (hDropPqRatchetState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (Drop.dropProtoPqRatchetStatePlacedSpec A)))
    (hDropStates : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (Drop.dropChunkedStatesLocal2PlacedSpec A F)))
    (hDecodeState : DecodeStatePlacedOkX canonicalV1InnerHeap A ext)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX A))
    (hChainNew : subroutine_ok ((blkPC_363).rebase (blkPl_363).base (Rust.withPanics ext))
      (blkPl_363).base (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) A)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith F) A)))
    (hChainRecvKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base (Rust.withPanics ext))
      (blkPl_366).base (withLsCallInv lsmpl (chainRecvKeySpecX (spqrHkdfWith F) A)))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX A))
    (hMsgDeser : MessageDeserializePlacedOkX spqrPolyApi A ext)
    (hStatesIntoPb : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base (States.IntoPb.statesIntoPbPlacedRoSpecX A F))
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hSeams : StatesPlacedSeams A F K ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) :=
  spqr_recv_placed_ok_of_contracts
    (spqrRecvPlacedContracts_of_okX hdealloc hmemcpy
      hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain hDropPqRatchetState hDropStates
      hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hMsgDeser hStatesIntoPb hEncodeToVec hSeams)

theorem spqr_recv_placed_ok_blockProgram
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpySpec)
    (hDropEpochSlice : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (Drop.dropProtoEpochSliceSpec A)))
    (hDropOptProtoInnerState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hDropOptProtoChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (Drop.dropOptProtoSpqrChainSpec A)))
    (hDropChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (Drop.dropSpqrChainSpec A)))
    (hDropPqRatchetState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (Drop.dropProtoPqRatchetStatePlacedSpec A)))
    (hDropStates : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (Drop.dropChunkedStatesLocal2PlacedSpec A F)))
    (hDecodeState : DecodeStatePlacedOkX canonicalV1InnerHeap A ext)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX A))
    (hChainNew : subroutine_ok ((blkPC_363).rebase (blkPl_363).base (Rust.withPanics ext))
      (blkPl_363).base (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) A)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith F) A)))
    (hChainRecvKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base (Rust.withPanics ext))
      (blkPl_366).base (withLsCallInv lsmpl (chainRecvKeySpecX (spqrHkdfWith F) A)))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX A))
    (hMsgDeser : MessageDeserializePlacedOkX spqrPolyApi A ext)
    (hStatesIntoPb : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base (States.IntoPb.statesIntoPbPlacedRoSpecX A F))
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hSeams : StatesPlacedSeams A F K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) :=
  spqr_recv_placed_ok_blockProgram_of_contracts
    (spqrRecvPlacedContracts_of_okX hdealloc hmemcpy
      hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain hDropPqRatchetState hDropStates
      hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hMsgDeser hStatesIntoPb hEncodeToVec hSeams)

theorem spqr_recv_placed_ok_blockProgram_ext_of_contracts
    {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrRecvPlacedContracts H_inner A F K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 ext)
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) := by
  have heq : Rust.withPanics ext = ext := by
    funext sym; unfold Rust.withPanics; split
    · next h => exact (hp sym h).symm
    · rfl
  simpa only [heq] using spqr_recv_placed_ok_blockProgram_of_contracts hC

end CryptoVerification.SpqrV1.Top.Recv
