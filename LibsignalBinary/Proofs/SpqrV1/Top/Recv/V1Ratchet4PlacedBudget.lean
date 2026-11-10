/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
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
# Budget-Threaded Relocatable V1 Ratchet Chain Segment (`+1856 -> +2664`)

Budget-threaded `<Chain>::recv_key` stepper (`+1976..+2024`) and full `+1856 -> +2664` V1 chain
composition for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain EpochSecret Error Message MlKem MsgPreamble PqRatchetState States V1Recv
   V1State chainFrom msgPreamble spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.RustHeap (vecU8Buf)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainGhost ChainRecvKeyGhost RecvPrevFits chainAt chainRecvKeyStackX
   chainRepr recvKeyPostAt)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (extractLsb_hi_append64 extractLsb_lo_append64)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost optEpochSecretAt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (noneCap spqrErrorTag)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS memRegion_2856_join_v1_ok memRegion_576_join_v1_ok recvKeyErrAt_sub3056_expose_words4
   recvKeyOkAt_sub3056_expose recvPrevFits_of_v1ChainAfterKey setWidth32_zeroExtend64
   sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_v1_recvKey_panic stackAt_spqrRecvCallee_split
   v1ChainAfterKey)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (ChainAddEpochEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
  (ChainRecvKeyEnv chainRecvKeyEvents chainRecvKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromAllocEnv ChainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget (seq_vm_clean)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudgetAux
  (frame_pure_pre step_v1_chainFrom_1856_placed step_v1_chainFrom_1856_placed_ofEnv
   step_v1_chain_reloc_and_addEpoch_1888_placed step_v1_chain_reloc_and_addEpoch_1888_placed_ofEnv
   v1ChainAfterKeyEvents)

export LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudgetAux
  (v1ChainAfterKeyEvents step_v1_chainFrom_1856_placed_ofEnv step_v1_chainFrom_1856_placed
   step_v1_chain_reloc_and_addEpoch_1888_placed_ofEnv step_v1_chain_reloc_and_addEpoch_1888_placed)

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
attribute [local simp, local arm64_norm, local wp_norm] setWidth32_zeroExtend64

omit [LibsignalPlacement] in
private theorem onPanic_of_v1_chainRecvKey_budget {F : ShaCompress} {K : MlKem} {st msg : VecArg}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 chain1 : Chain}
    (hpre : msgPreamble msg.bytes = .ok pre) (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1) (s sm : State) :
    (⌜(Chain.recvKey (spqrHkdfWith F) chain1 (pre.epoch - 1#64) pre.index).isPanic = true ∧ sm.trace = s.trace⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(spqrV1Recv F K).recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left; rintro ⟨hpan, htr⟩
  exact Entails.pure_right
    ⟨spqrV1Recv_v1_recvKey_panic hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey hpan,
     htr ▸ List.prefix_refl _⟩
    (Entails.refl _)

/-! ## 3. `<Chain>::recv_key` Call & Dispatch (`+1976 .. +2024`) -/

/-- Envelope-parametric step `+1976 .. +2024`: calls `<Chain>::recv_key` at `+1996`, loads the
    4-word `Result` from `s0.sp - 3056#64`, sets `x26 := 0#64`, and branches at `+2024` (`b.ne
    +2664` on `Ok`, fallthrough `+2028` on `Err`). -/
theorem step_v1_chainRecvKey_1976_placed_ofEnv {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
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
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (R : SepProp)
    (chain0 chain1 : Chain) (G1 : ChainGhost) (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1)
    (hFit_rk : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainRecvKeyEnv (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1976#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch - 1#64)
    (hx23 : s.readReg64 .x23 = w0) (hx28 : s.readReg64 .x28 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err_2028 : ∀ (err : Error) (w1_err w2_err w3_err : BitVec 64)
        (G1' : ChainGhost) (s1 : State) (P1 : SepProp),
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
      (∀ r : BitVec 64,
        ((r + 8#64) ↦₆₄ w1_err) ⊢
          ((r + 8#64) ↦₈ spqrErrorTag err) ∗ memRegion (r + 9#64) 7) →
      s1.pc = spqrRecvPlacedEntry + 2028#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = w1_err →
      s1.readReg64 .x22 = w2_err → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = w3_err → s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗ chainAt A.repAlloc (s0.sp - 232#64) G1' chain1 ∗
        memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok_2664 : ∀ (chain2 : Chain) (G2 : ChainGhost) (rawKey : Bytes)
        (cap_rk ptr_rk : BitVec 64) (s1 : State) (P1 : SepProp),
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
      s1.pc = spqrRecvPlacedEntry + 2664#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = cap_rk →
      s1.readReg64 .x22 = ptr_rk → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length → s1.readReg64 .x25 = s0.sp - 3056#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ chainAt A.repAlloc (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hrk_ok := hC.chainRecvKey_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  have hfits : RecvPrevFits chain1 :=
    recvPrevFits_of_v1ChainAfterKey (F := F) (K := K) hst_len hdec hcf hkey
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hrk_ok hpc hcont_err_2028 hcont_ok_2664 ⊢
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 366); wp_steps 6
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide))) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hrk_ok
    ((⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩ : ChainRecvKeyGhost),
      MC.stepEvents evs0 st_cost)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 2000#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun sm => by
      dsimp only [chainRecvKeySpecX]
      have hpan := onPanic_of_v1_chainRecvKey_budget hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey s0 sm
      simpa only [State.writeReg32, State.trace_setPC, State.trace_advancePC, State.trace_writeReg64,
        htr] using hpan)
    (fun _ _ => rfl)
    (by
      dsimp only [chainRecvKeySpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], hfits, hFit_rk⟩
        (by simp only [State.writeReg32, State.sp_setPC, State.sp_advancePC, State.sp_writeReg64,
            RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            reduceCtorEq, ↓reduceIte, hsp]; sep_focus)) ?_
  intro sm hpcm hrunm hspm hcsm
  dsimp only [spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm
  rcases hcsm with ⟨hx19_c, hx20_c, _, _, hx23_c, _, hx25_c, _, _, hx28_c, hxfp_c, hvregs_c⟩
  dsimp only [chainRecvKeySpecX]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, _⟩
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 3056#64 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  have hsp_eq := congrArg (stackAt · chainRecvKeyStackX) (hspm.symm.trans hspm')
  refine SepWPpLS.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)).symm)
    (by sep_focus) ?_
  rw [← MC.stepEvents_append]
  cases hrk_res : Chain.recvKey (spqrHkdfWith F) chain1 (pre.epoch - 1#64) pre.index with
  | error ce =>
    cases ce with
    | panic _ => dsimp only [recvKeyPostAt]; exact SepWPpLS.focus_pure (by sep_focus) False.elim
    | err err =>
      dsimp only [recvKeyPostAt]; unfold chainRepr
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPpLS.exists_left hrunm; intro G1'
      apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 2028#64)
      refine SepWP.focus_weaken (recvKeyErrAt_sub3056_expose_words4 s0.sp err) (by sep_focus) ?_
      wp_pull_exists; rename_i w1_err w2_err w3_err
      wp_focus_pure; intro hw1_err
      refine seq_vm_clean (mid := (blkPl_329).base + 2028#64)
        (P_mid :=
          spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
          A.pool lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) sm ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
          ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
          memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
          messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
          chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
          ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
          ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
          memRegion (s0.sp - 3024#64) 2792 ∗ chainAt A.repAlloc (s0.sp - 232#64) G1' chain1 ∗
          memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun s1 =>
          s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
          s1.readReg64 .x19 = ret ∧ s1.readReg64 .x21 = w1_err ∧
          s1.readReg64 .x22 = w2_err ∧ s1.readReg64 .x23 = w0 ∧
          s1.readReg64 .x24 = w3_err ∧ s1.readReg64 .x26 = 0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64)
        ?_ ?_
      · by_vm_steps (
          wp_steps 7
          refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
        )
      · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, htr1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx29_1⟩
        rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) sm s1 hvm1]
        apply ProofLib.SepWP.done hpc1 hrun1
        exact hcont_err_2028 err w1_err w2_err w3_err G1' s1 _ hrk_res hw1_err
          hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx29_1 rfl
  | ok pair =>
    rcases pair with ⟨chain2, rawKey⟩
    dsimp only [recvKeyPostAt]; unfold chainRepr
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPpLS.exists_left hrunm; intro G2
    apply SepWPpLS.of_sepWP (mid := (blkPl_329).base + 2664#64)
    refine SepWP.focus_weaken (recvKeyOkAt_sub3056_expose A.repAlloc s0.sp rawKey) (by sep_focus) ?_
    wp_pull_exists; rename_i cap_rk ptr_rk
    refine seq_vm_clean (mid := (blkPl_329).base + 2664#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ chainAt A.repAlloc (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
        s1.readReg64 .x19 = ret ∧ s1.readReg64 .x21 = cap_rk ∧
        s1.readReg64 .x22 = ptr_rk ∧ s1.readReg64 .x23 = w0 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length ∧ s1.readReg64 .x25 = s0.sp - 3056#64 ∧
        s1.readReg64 .x26 = 0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 7
        refine SepWP.focus_weaken (memRegion_576_join_v1_ok s0.sp sckaMsg) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (memRegion_2856_join_v1_ok s0.sp 0#64 cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length)) (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, htr1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx29_1⟩
      rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) sm s1 hvm1]
      apply ProofLib.SepWP.done hpc1 hrun1
      exact hcont_ok_2664 chain2 G2 rawKey cap_rk ptr_rk s1 _ hrk_res
        hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 rfl

theorem step_v1_chainRecvKey_1976_placed {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (R : SepProp)
    (chain0 chain1 : Chain) (G1 : ChainGhost) (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1)
    (hFit_rk : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainRecvKeyEnv (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1976#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch - 1#64)
    (hx23 : s.readReg64 .x23 = w0) (hx28 : s.readReg64 .x28 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
      chainAt A.repAlloc (s0.sp - 232#64) G1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err_2028 : ∀ (err : Error) (w1_err w2_err w3_err : BitVec 64)
        (G1' : ChainGhost) (s1 : State) (P1 : SepProp),
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
      (∀ r : BitVec 64,
        ((r + 8#64) ↦₆₄ w1_err) ⊢
          ((r + 8#64) ↦₈ spqrErrorTag err) ∗ memRegion (r + 9#64) 7) →
      s1.pc = spqrRecvPlacedEntry + 2028#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = w1_err →
      s1.readReg64 .x22 = w2_err → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = w3_err → s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗ chainAt A.repAlloc (s0.sp - 232#64) G1' chain1 ∗
        memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok_2664 : ∀ (chain2 : Chain) (G2 : ChainGhost) (rawKey : Bytes)
        (cap_rk ptr_rk : BitVec 64) (s1 : State) (P1 : SepProp),
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
      s1.pc = spqrRecvPlacedEntry + 2664#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = cap_rk →
      s1.readReg64 .x22 = ptr_rk → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length → s1.readReg64 .x25 = s0.sp - 3056#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ chainAt A.repAlloc (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_chainRecvKey_1976_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb pb w0 w1 sckaMsg st0 v R chain0 chain1 G1 s0 s P
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey hFit_rk hs0_align
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx28 hx29 hP hcont_err_2028 hcont_ok_2664

/-! ## 4. Composed V1 Ratchet Chain Segment (`+1856 -> +2664`) -/

/-- Envelope-parametric top-level V1 ratchet chain composition (`+1856 -> +2568 / +2028 /
    +2664`): composes `step_v1_chainFrom_1856_placed_ofEnv`,
    `step_v1_chain_reloc_and_addEpoch_1888_placed_ofEnv`, and
    `step_v1_chainRecvKey_1976_placed_ofEnv`. -/
theorem step_v1_ratchet_1856_to_2664_placed_ofEnv {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
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
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp)
    (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (hFit_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain pre_pb.versionNegotiation))
    (hFit_add : ∀ evs_cf chain0 G0 es,
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v.key = some es →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainAddEpochEnv (spqrHkdfWith F) ⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩))
    (hFit_rk : ∀ evs_cf chain0 G0 chain1 G1,
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩))
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
    (hcont_err_2568 : ∀ (evs_cf : List AllocEvent) (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
      BitVec.truncate 8 q0_err = spqrErrorTag e →
      s1.pc = spqrRecvPlacedEntry + 2568#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = noneCap → s1.readReg64 .x9 = w3_err →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
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
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_err_2028 : ∀ (evs_cf : List AllocEvent) (chain0 chain1 : Chain)
        (G0 G1 : ChainGhost) (err : Error) (w1_err w2_err w3_err : BitVec 64)
        (G1' : ChainGhost) (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
      (∀ r : BitVec 64,
        ((r + 8#64) ↦₆₄ w1_err) ⊢
          ((r + 8#64) ↦₈ spqrErrorTag err) ∗ memRegion (r + 9#64) 7) →
      s1.pc = spqrRecvPlacedEntry + 2028#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = w1_err →
      s1.readReg64 .x22 = w2_err → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = w3_err → s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents ((evs0 ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗ chainAt A.repAlloc (s0.sp - 232#64) G1' chain1 ∗
        memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok_2664 : ∀ (evs_cf : List AllocEvent) (chain0 chain1 chain2 : Chain)
        (G0 G1 G2 : ChainGhost) (rawKey : Bytes) (cap_rk ptr_rk : BitVec 64)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
      s1.pc = spqrRecvPlacedEntry + 2664#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = cap_rk →
      s1.readReg64 .x22 = ptr_rk → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length → s1.readReg64 .x25 = s0.sp - 3056#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents ((evs0 ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ chainAt A.repAlloc (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  refine step_v1_chainFrom_1856_placed_ofEnv evs0 hC st msg ret pre pre_pb w0 w1 kw0 kw1 kw2 kw3 sckaMsg v P_key R
    s0 s P hFit_cf hs0_align hsp4640_ne hpc hrun hsp htr
    hx0 hx1 hx2 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hcont_err_2568 ?_
  intro evs_cf chain0 G0 pad0 s1888 P1888 hevs_cf hcf _ hpc1888 hrun1888 hsp1888 htr1888
    hx8_1888 hx9_1888 hx19_1888 hx20_1888 hx21_1888 hx22_1888 hx23_1888 hx24_1888 hx25_1888
    hx26_1888 hx27_1888 hx28_1888 hx29_1888 hP1888
  refine step_v1_chain_reloc_and_addEpoch_1888_placed_ofEnv (evs0 ++ evs_cf) hC st msg ret pre pre_pb pb
    w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R chain0 G0 pad0 s0 s1888 P1888
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hfold_key
    (fun es hvk => hFit_add evs_cf chain0 G0 es hevs_cf hcf hvk) hs0_align
    hpc1888 hrun1888 hsp1888 htr1888 hx8_1888 hx9_1888 hx19_1888 hx20_1888 hx21_1888 hx22_1888
    hx23_1888 hx24_1888 hx25_1888 hx26_1888 hx27_1888 hx28_1888 hx29_1888 hP1888 ?_
  intro chain1 G1 s1976 P1976 hkey hpc1976 hrun1976 hsp1976 htr1976
    hx19_1976 hx20_1976 hx21_1976 hx22_1976 hx23_1976 hx28_1976 hx29_1976 hP1976
  exact step_v1_chainRecvKey_1976_placed_ofEnv
    ((evs0 ++ evs_cf) ++ v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key)
    hC st msg ret pre pre_pb pb w0 w1 sckaMsg st0 v R chain0 chain1 G1 s0 s1976 P1976
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey
    (hFit_rk evs_cf chain0 G0 chain1 G1 hevs_cf hcf hkey) hs0_align
    hpc1976 hrun1976 hsp1976 htr1976
    hx19_1976 hx20_1976 hx21_1976 hx22_1976 hx23_1976 hx28_1976 hx29_1976 hP1976
    (fun err w1_err w2_err w3_err G1' s1 P1 =>
      hcont_err_2028 evs_cf chain0 chain1 G0 G1 err w1_err w2_err w3_err G1' s1 P1 hevs_cf hcf hkey)
    (fun chain2 G2 rawKey cap_rk ptr_rk s1 P1 =>
      hcont_ok_2664 evs_cf chain0 chain1 chain2 G0 G1 G2 rawKey cap_rk ptr_rk s1 P1 hevs_cf hcf hkey)

theorem step_v1_ratchet_1856_to_2664_placed {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    (evs0 : List AllocEvent)
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp)
    (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        optEpochSecretAt A.repAlloc dst v.key)
    (hFit_cf : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (ChainFromAllocEnv pre_pb.chain pre_pb.versionNegotiation))
    (hFit_add : ∀ evs_cf chain0 G0 es,
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v.key = some es →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf) st_cost)
        (ChainAddEpochEnv (spqrHkdfWith F) ⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩))
    (hFit_rk : ∀ evs_cf chain0 G0 chain1 G1,
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) st_cost)
        (ChainRecvKeyEnv (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩))
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
    (hcont_err_2568 : ∀ (evs_cf : List AllocEvent) (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
      BitVec.truncate 8 q0_err = spqrErrorTag e →
      s1.pc = spqrRecvPlacedEntry + 2568#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = noneCap → s1.readReg64 .x9 = w3_err →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
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
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_err_2028 : ∀ (evs_cf : List AllocEvent) (chain0 chain1 : Chain)
        (G0 G1 : ChainGhost) (err : Error) (w1_err w2_err w3_err : BitVec 64)
        (G1' : ChainGhost) (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
      (∀ r : BitVec 64,
        ((r + 8#64) ↦₆₄ w1_err) ⊢
          ((r + 8#64) ↦₈ spqrErrorTag err) ∗ memRegion (r + 9#64) 7) →
      s1.pc = spqrRecvPlacedEntry + 2028#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = w1_err →
      s1.readReg64 .x22 = w2_err → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = w3_err → s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents ((evs0 ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗ chainAt A.repAlloc (s0.sp - 232#64) G1' chain1 ∗
        memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok_2664 : ∀ (evs_cf : List AllocEvent) (chain0 chain1 chain2 : Chain)
        (G0 G1 G2 : ChainGhost) (rawKey : Bytes) (cap_rk ptr_rk : BitVec 64)
        (s1 : State) (P1 : SepProp),
      ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
      s1.pc = spqrRecvPlacedEntry + 2664#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = cap_rk →
      s1.readReg64 .x22 = ptr_rk → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length → s1.readReg64 .x25 = s0.sp - 3056#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents ((evs0 ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ chainAt A.repAlloc (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_ratchet_1856_to_2664_placed_ofEnv (Env := SpqrRecvEnv st msg) evs0 hC
    st msg ret pre pre_pb pb w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R s0 s P
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hfold_key
    hFit_cf hFit_add hFit_rk hs0_align hsp4640_ne hpc hrun hsp htr
    hx0 hx1 hx2 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP
    hcont_err_2568 hcont_err_2028 hcont_ok_2664

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudget
