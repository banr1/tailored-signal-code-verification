/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Ext
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7Ext
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9Ext
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3Ext
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4Ext
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5Ext
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500

/-!
# `spqr::recv`: Extended Hook-Stack (`*Ext`) Top-Level Assembly

Discharges the three version-branch tails and proves `spqrRecv_ok_of_contracts_ext` for
`spqr::recv` under `SpqrRecvContractsExt`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. `V0ChainTail` (`+496 -> s0.x30`) and `InitInnerTail` (`+1076 -> s0.x30`) under `SpqrRecvContractsExt` -/

/-- `Ordering::Greater` (`V0ChainTail` at `+496`) satisfied via `step_ordering_greater_ext`
    (`Part9Ext.lean`). -/
theorem v0ChainTail_ok_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true) :
    V0ChainTail img A F K ext st msg ret s0 R :=
  step_ordering_greater_ext hC st msg ret hst_len s0 R hs0_align

/-- `Ordering::Less` (`InitInnerTail` at `+1076`) satisfied via `step_ordering_less_ext`
    (`Part7Ext.lean`). -/
theorem initInnerTail_ok_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat) :
    InitInnerTail img A F K ext st msg ret s0 R := by
  intro pre remPtr pre_pb vn pb w0 w1 w26 s P
    hpre _hrem hdec hvn hinner _hw0 hw26 hmin hver_lt
    hpc hrun hsp htr hx19 hx20 _hx21 _hx22 _hx23 _hx24 hx25 hx26 _hx27 _hx28 hx29 hP
  exact step_ordering_less_ext hC st msg ret pre pre_pb vn pb w0 w1 w26
    hst_len hpre hdec hvn hinner hw26 hmin hver_lt s0 s P R hs0_align
    (sp_sub_4992_ne_zero hsp_lo) hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

/-! ## 2. `V1RatchetTailI` (`+1532 -> s0.x30`) under `SpqrRecvContractsExt` -/

/-- Post-`+1856` continuation interface for the V1 ratchet path (`+1856 -> s0.x30`) under
    `SpqrRecvContractsExt`. -/
def V1RatchetChainContinuationExt
    (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) : Prop :=
  ∀ (_hC : SpqrRecvContractsExt H_inner img A F K ext)
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
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        Top.MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)

/-- Unconditional proof of `V1RatchetChainContinuationExt` (`+1856 -> s0.x30`) composing
    `step_v1_ratchet_1856_to_2664_ext`, `step_chainFrom_err_2568`, `step_recvKey_err_2028`, and
    `step_v1_ok_2664_to_ret_ext`. -/
theorem v1RatchetChainContinuation_ok_ext
    (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp) :
    V1RatchetChainContinuationExt H_inner img A F K ext st msg ret s0 R := by
  intro hC pre _remPtr pre_pb pb w0 w1 hst_len hpre _hvalid hdec hinner _hw0 hmv hmin hs0_align hsp_lo
    sckaMsg st0 v kw0 kw1 kw2 kw3 P_key s1 P1 hmsg hfrom hrecv hfold_key
    hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
  have hep0 : (pre.epoch == 0#64) = false := msgPreamble_epoch_beq_zero_false hpre hmv
  have hsp4640_ne : s0.sp - 4640#64 ≠ 0#64 := sp_sub_4640_ne_zero hsp_lo
  refine step_v1_ratchet_1856_to_2664_ext hC st msg ret pre pre_pb pb
    w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R s0 s1 P1
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hfold_key hs0_align hsp4640_ne
    hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    ?_ ?_ ?_
  · intro e q0_err w3_err s_err P_err hcf htag_q0
      hpc_e hrun_e hsp_e htr_e _hx8_e _hx9_e hx19_e _hx20_e _hx21_e _hx22_e hx23_e hx24_e hx25_e _hx26_e _hx27_e hx28_e _hx29_e hP_err
    obtain ⟨herr, hnp⟩ := spqrV1Recv_v1_chainFrom_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
    subst hP_err
    apply sepWPpI_intro_chunkedStatesLocal2JumpTableAt hC.himg
    apply SepWPpI.of_sepWP_ret
    refine sepWP_spqrRecvPost_of_post0 hnp ?_
    exact step_chainFrom_err_2568 img.base A F K ext hC.base_aligned hC.hdealloc
      st msg ret pre_pb w0 w1 sckaMsg v kw0 kw1 kw2 kw3 P_key hfold_key
      e q0_err w3_err herr htag_q0 s0 s_err _ R _ rfl hs0_align
      hpc_e hrun_e hsp_e htr_e hx19_e hx23_e hx24_e hx25_e hx28_e (by ac_rfl)
  · intro chain0 chain1 err w1_err w2_err w3_err G1' s_err P_err
      hcf hkey hrk hw1_err hpc_e hrun_e hsp_e htr_e hx19_e hx21_e hx22_e hx23_e hx24_e hx26_e hx29_e hP_err
    obtain ⟨herr, hnp⟩ := spqrV1Recv_v1_recvKey_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
        (topResult_addEpoch_of_v1ChainAfterKey hkey) hrk
    subst hP_err
    apply sepWPpI_intro_chunkedStatesLocal2JumpTableAt hC.himg
    apply SepWPpI.of_sepWP_ret
    refine sepWP_spqrRecvPost_of_post0 hnp ?_
    exact step_recvKey_err_2028 img.base A F K ext hC.base_aligned hC.hdealloc
      st msg ret pre_pb w0 w1 sckaMsg v G1' chain1 err w1_err w2_err w3_err herr hw1_err
      s0 s_err _ R _ rfl hs0_align
      hpc_e hrun_e hsp_e htr_e hx19_e hx21_e hx22_e hx23_e hx24_e hx26_e hx29_e (by ac_rfl)
  · intro chain0 chain1 chain2 G2 rawKey cap_rk ptr_rk s_ok P_ok
      hcf hkey hrk hpc_ok hrun_ok hsp_ok htr_ok hx19_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx26_ok hx29_ok hP_ok
    rcases v with ⟨key, st1⟩
    exact step_v1_ok_2664_to_ret_ext hC st msg ret pre pre_pb pb sckaMsg st0 st1 key
      chain0 chain1 chain2 G2 rawKey w0 w1 cap_rk ptr_rk
      hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
      (topResult_addEpoch_of_v1ChainAfterKey hkey) hrk
      s0 s_ok P_ok R hs0_align hpc_ok hrun_ok hsp_ok htr_ok
      hx19_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx26_ok hx29_ok hP_ok

/-- Compose `step_v1_ratchet_1532_to_1856_ext` with `V1RatchetChainContinuationExt` to discharge
    `V1RatchetTailI` (`+1532 -> s0.x30`). -/
theorem v1RatchetTail_of_chainContinuation_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hcont : V1RatchetChainContinuationExt H_inner img A F K ext st msg ret s0 R) :
    V1RatchetTailI img A F K ext st msg ret s0 R := by
  intro pre remPtr pre_pb pb w0 w1 s P
    hpre hvalid hdec hinner hw0 hmv hmin
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP
  exact step_v1_ratchet_1532_to_1856_ext hC st msg ret pre remPtr pre_pb pb w0 w1
    hst_len hpre hvalid hdec hinner hmv hmin s0 s P R hs0_align
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP
    (hcont hC pre remPtr pre_pb pb w0 w1 hst_len hpre hvalid hdec hinner hw0 hmv hmin hs0_align hsp_lo)

/-- Unconditional proof of `V1RatchetTailI` (`+1532 -> s0.x30`) from `SpqrRecvContractsExt` and
    `spqrRecvStack ≤ s0.sp.toNat`. -/
theorem v1RatchetTail_ok_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat) :
    V1RatchetTailI img A F K ext st msg ret s0 R :=
  v1RatchetTail_of_chainContinuation_ext hC st msg ret s0 R hst_len hs0_align hsp_lo
    (v1RatchetChainContinuation_ok_ext H_inner img A F K ext st msg ret s0 R)

/-! ## 3. Top-Level `spqr::recv` Composition under `SpqrRecvContractsExt` -/

/-- `SepWPpI` execution of `spqr::recv` from `SpqrRecvContractsExt` and `spqrRecvStack ≤
    s0.sp.toNat`. -/
theorem spqrRecv_sepWPpI_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_prologue_to_312 A F K ext st msg ret s0 P R hpc hrun hsp_align hx0 hx1 hx8 hP
    (fun pre msgPtr s1 P1 hpre hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1 =>
      step_decode_and_dispatch_ext H_inner hC st msg ret pre msgPtr hst_len hpre hvalid
        s0 s1 P1 R
        (v0ChainTail_ok_ext hC st msg ret s0 R hst_len hsp_align)
        (initInnerTail_ok_ext hC st msg ret s0 R hst_len hsp_align hsp_lo)
        (v1RatchetTail_ok_ext hC st msg ret s0 R hst_len hsp_align hsp_lo)
        hsp_align
        hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1)

/-- `spqr::recv` satisfies `spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img` on
    `tripleRatchetProgAtExt img.base ext` from `SpqrRecvContractsExt` alone. -/
theorem spqrRecv_ok_ext_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨st, msg, ret⟩ R s0 hpc hrun hpre hsp_align hL
  dsimp only [spqrRecvSpecExactKeyBounded, spqrRecvSpecExactKey, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hst_len, _hmsg_len, hsp_lo⟩, hpre⟩
  have hpre1 :
      s0.mem ⊨ ⌜ImgCallInv img s0⌝ ∗
        (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret⌝ ∗
          (logOff img ∗ TokenInit img ∗
            (st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R))) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [ImgCallInv]; ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨hinv0, hpre2⟩
  rw [satisfies_pure_sepConj] at hpre2
  rcases hpre2 with ⟨⟨hx0, hx1, hx8⟩, hmem0⟩
  have hmem_ro :
      s0.mem ⊨ spqrRecvRoAt img.base ∗
        (st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
    rodata_spqrRecvRoAt hC.himg hinv0.1 hmem0
  let P0 :=
    spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
  have hP0 : s0.mem ⊨ P0 ∗ R :=
    Satisfies.mono (Entails.of_eq (by dsimp only [P0]; ac_rfl)) hmem_ro
  have hwp :=
    spqrRecv_sepWPpI_of_contracts_ext hC st msg ret s0 P0 R
      hst_len hsp_lo hpc hrun hsp_align hx0 hx1 hx8 rfl
  obtain ⟨sf, hsteps, hout⟩ := hwp hinv0 R hP0 hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  dsimp only [SubroutineOutcome, spqrRecvSpecExactKeyBounded, spqrRecvSpecExactKey, Spec.inImage]
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom
  · refine Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩
    have hcore := hq hmf
    have hro :
        sf.mem ⊨ spqrRecvRoAt img.base ∗
          (⌜sf.trace = s0.trace ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
            recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
            A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by dsimp only [spqrRecvCorePost]; ac_rfl)) hcore
    have hlt := spqrRecvRoAt_restore hro
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hlt
  · exact Or.inr (Or.inl ⟨hpan, hqp hmf⟩)
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- `spqr::recv` satisfies `spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img` on
    `Program.ofImage img (Rust.withPanics ext)` at `entryOf img spqrRecvName` from
    `SpqrRecvContractsExt` alone. -/
theorem spqrRecv_ok_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) :=
  root_of_tripleRatchetProgAtExt hC.himg (spqrRecv_ok_ext_of_contracts_ext hC)

theorem spqr_recv_ok_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) :=
  spqrRecv_ok_of_contracts_ext hC

end CryptoVerification.SpqrV1.Top.Recv
