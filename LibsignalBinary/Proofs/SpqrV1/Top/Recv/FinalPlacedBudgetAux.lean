/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500PlacedBudget

/-!
# Budget-Threaded Per-Branch Obligations & Tails for `spqr::recv`

Mid-execution `FitsEnv` extension combinators, the per-branch budget/closure bundle
`SpqrRecvBranchHyps`, and proofs of the three version-branch tail contracts for `spqr::recv`
(Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudgetAux

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain Direction EpochSecret Error Message MlKem MsgPreamble PqRatchetState
   States V1Recv V1State VersionNegotiationPB chainFrom msgPreamble
   spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg spqrRecvStack)
open CryptoVerification.SpqrV1.ChainProofs (ChainGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS msgPreamble_epoch_beq_zero_false sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt
   sp_sub_4640_ne_zero sp_sub_4992_ne_zero spqrV1Recv_v1_chainFrom_err spqrV1Recv_v1_recvKey_err
   topResult_addEpoch_of_v1ChainAfterKey v1ChainAfterKey)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   fitsEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (ChainAddEpochEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbAllocEnv ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (ChainRecvKeyEnv chainRecvKeyEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromAllocEnv ChainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget (toDropContractsBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (InitInnerPlacedTailGen V0ChainPlacedTailGen V1RatchetPlacedTailLSGen)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7PlacedBudget (step_ordering_less_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part9PlacedBudget (step_ordering_greater_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudget
  (step_v1_ratchet_1532_to_1856_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudget
  (step_v1_ratchet_1856_to_2664_placed_ofEnv v1ChainAfterKeyEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudget
  (step_v1_ok_2664_to_ret_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500PlacedBudget
  (step_chainFrom_err_2568_placed_ofEnv step_recvKey_err_2028_placed_ofEnv)

export CryptoVerification.SpqrV1.Top.Recv
  (sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Mid-Execution `FitsEnv` Extension Combinators & Per-Branch Obligation Bundle -/

omit [LibsignalPlacement] in
/-- Discharge `FitsEnv MC lim (MC.stepEvents evs_pre st_cost) SubEnv` from entry `FitsEnv MC lim
    st_cost Env` whenever every `evs_sub` in `SubEnv` extends with some suffix `evs_suf` to an
    element of `Env`. -/
theorem fitsEnv_step_of_extend {MC : AllocCostModel} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env SubEnv : List AllocEvent → Prop} {evs_pre : List AllocEvent}
    (h0 : FitsEnv MC lim st_cost Env)
    (hext : ∀ evs_sub, SubEnv evs_sub → ∃ evs_suf, Env ((evs_pre ++ evs_sub) ++ evs_suf)) :
    FitsEnv MC lim (MC.stepEvents evs_pre st_cost) SubEnv := by
  intro evs_sub hsub
  obtain ⟨evs_suf, hEnv⟩ := hext evs_sub hsub
  have hfe := h0 _ hEnv
  rw [fitsEvents_append] at hfe
  exact ((fitsEvents_append MC lim evs_pre evs_sub st_cost).mp hfe.1).2

omit [LibsignalPlacement] in
/-- Specialization of `fitsEnv_step_of_extend` with empty suffix (`evs_suf = []`), matching
    `SeqEnv` left-inclusion (`Or.inl`). -/
theorem fitsEnv_step_of_prefix {MC : AllocCostModel} {lim : BudgetLimits} {st_cost : MC.σ}
    {Env SubEnv : List AllocEvent → Prop} {evs_pre : List AllocEvent}
    (h0 : FitsEnv MC lim st_cost Env)
    (hpre : ∀ evs_sub, SubEnv evs_sub → Env (evs_pre ++ evs_sub)) :
    FitsEnv MC lim (MC.stepEvents evs_pre st_cost) SubEnv :=
  fitsEnv_step_of_extend h0 fun evs_sub hsub =>
    ⟨[], by rw [List.append_nil]; exact hpre evs_sub hsub⟩

/-- Per-call branch budget (`FitsEnv`) and envelope-closure obligations for `spqr::recv` (`Block
    329`) at entry state `s0`, cost-model state `st_cost`, and target envelope `Env`. All
    concatenated event lists are normalized right-associatively (`a ++ b ++ c`). -/
structure SpqrRecvBranchHyps {MC : AllocCostModel}
    (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (InitEnv : InitInnerGhost → List AllocEvent → Prop)
    (FromPbEnv : V1State → List AllocEvent → Prop)
    (RecvEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop)
    (Env : List AllocEvent → Prop)
    (st msg : VecArg) (s0 : State) (st_cost : MC.σ) : Prop where
  /-- Early `msgPreamble` error exit emits `[]`. -/
  env_nil : Env []
  /-- Entry `FitsEnv` for `spqr::decode_state`. -/
  fit_dec : ∀ pre : MsgPreamble,
    msgPreamble msg.bytes = .ok pre →
    FitsEnv MC lim st_cost (DecodePreEnv ⟨st, s0.sp - 3056#64⟩)
  /-- `spqr::decode_state` + drop-only early exits (`decode_state` error, `vn = none`, `inner =
      none`, `version < minVersion`, invalid `vn.direction`). -/
  env_dec_free : ∀ (pre : MsgPreamble) (evs_dec evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_d)
  /-- `Ordering::Greater` (`pre.version > 1#8`): `FitsEnv` for `spqr::chain_from`. -/
  gt_fit_cf : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (evs_dec : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FitsEnv MC lim (MC.stepEvents evs_dec st_cost) (ChainFromAllocEnv pre_pb.chain (some vn))
  /-- `Ordering::Greater`: `FitsEnv` for `<Chain>::recv_key` at epoch `0`. -/
  gt_fit_rk : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (evs_dec evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_cf) st_cost)
      (ChainRecvKeyEnv (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
  /-- `Ordering::Greater`: `FitsEnv` for `<Chain>::into_pb`. -/
  gt_fit_into : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (evs_dec evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
      (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
    chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
    FitsEnv MC lim
      (MC.stepEvents
        (evs_dec ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩)
        st_cost)
      (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩)
  /-- `Ordering::Greater`: `FitsEnv` for `<PqRatchetState>::encode_to_vec`. -/
  gt_fit_enc : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (evs_dec evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
      (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost) (evs_into : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
    chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
    ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
    FitsEnv MC lim
      (MC.stepEvents
        (evs_dec ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_into)
        st_cost)
      (PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) })
  /-- `Ordering::Greater`: `Env` closure on `<Chain>::recv_key` error. -/
  gt_env_rk_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (evs_dec evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
      (e : Error) (evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
    chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .error (.err e) →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++ evs_d)
  /-- `Ordering::Greater`: `Env` closure on `<Chain>::recv_key` success. -/
  gt_env_rk_ok : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (evs_dec evs_cf : List AllocEvent) (chain0 : Chain) (G_c0 : ChainGhost)
      (chain1 : Chain) (rawKey : Bytes) (gChain : ChainGhost)
      (evs_into evs_enc evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 →
    chain0.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) →
    ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
    PqRatchetStateEncodeToVecEnv
      { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
      evs_enc →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_cf ++ chainRecvKeyEvents (spqrHkdfWith F)
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ ++
      evs_into ++ evs_enc ++ evs_d)
  /-- `Ordering::Less` (`pre.version < 1#8`): `FitsEnv` for `spqr::init_inner`. -/
  lt_fit_init : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (w1 : BitVec 64) (dir : Direction) (evs_dec : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    Direction.fromI32? vn.direction = some dir →
    FitsEnv MC lim (MC.stepEvents evs_dec st_cost)
      (InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩)
  /-- `Ordering::Less`: `FitsEnv` for `spqr::chain_from`. -/
  lt_fit_cf : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (w1 : BitVec 64) (dir : Direction) (evs_dec evs_init : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    Direction.fromI32? vn.direction = some dir →
    InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_init) st_cost)
      (ChainFromAllocEnv pre_pb.chain (some vn))
  /-- `Ordering::Less`: `FitsEnv` for `<Chain>::into_pb`. -/
  lt_fit_into : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (w1 : BitVec 64) (dir : Direction)
      (evs_dec evs_init evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    Direction.fromI32? vn.direction = some dir →
    InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_init ++ evs_cf) st_cost)
      (ChainIntoPbAllocEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩)
  /-- `Ordering::Less`: `Env` closure on `chain_from` error. -/
  lt_env_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (w1 : BitVec 64) (dir : Direction)
      (evs_dec evs_init evs_cf evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    Direction.fromI32? vn.direction = some dir →
    InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_init ++ evs_cf ++ evs_d)
  /-- `Ordering::Less`: `Env` closure on `chain_from` + `into_pb` path (note `init_inner` for
      `.v0` always returns `Err(UnknownVersion)` after `into_pb`). -/
  lt_env_ok : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
      (pb : V1State) (w1 : BitVec 64) (dir : Direction)
      (evs_dec evs_init evs_cf : List AllocEvent) (ch : Chain) (G : ChainGhost)
      (evs_into evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    Direction.fromI32? vn.direction = some dir →
    InitEnv ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ evs_init →
    ChainFromEnv pre_pb.chain (some vn) evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch →
    ChainIntoPbEnv ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩ evs_into →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_init ++ evs_cf ++ evs_into ++ evs_d)
  /-- `Ordering::Equal` (`pre.version = 1#8`): `FitsEnv` for `<States>::from_pb`. -/
  v1_fit_fpb : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (evs_dec evs_md : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_md) st_cost) (FromPbEnv pb)
  /-- `Ordering::Equal`: `Env` closure on `<States>::from_pb` error. -/
  v1_env_fpb_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (evs_dec evs_md evs_fpb evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_md ++ evs_fpb ++ evs_d)
  /-- `Ordering::Equal`: `FitsEnv` for `<States>::recv`. -/
  v1_fit_rcv : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (evs_dec evs_md evs_fpb : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_md ++ evs_fpb) st_cost)
      (RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩)
  /-- `Ordering::Equal`: `Env` closure on `<States>::recv` error. -/
  v1_env_rcv_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (evs_dec evs_md evs_fpb evs_rcv evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_d)
  /-- `Ordering::Equal`: `FitsEnv` for `spqr::chain_from` after `<States>::recv = .ok v`. -/
  v1_fit_cf : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (evs_dec evs_md evs_fpb evs_rcv : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok v →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv) st_cost)
      (ChainFromAllocEnv pre_pb.chain pre_pb.versionNegotiation)
  /-- `Ordering::Equal`: `Env` closure on `spqr::chain_from` error at `+2568`. -/
  v1_env_cf_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F)) (e : Error)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok v →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++ evs_d)
  /-- `Ordering::Equal`: `FitsEnv` for `<Chain>::add_epoch` when `v.key = some es`. -/
  v1_fit_add : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F)) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf : List AllocEvent)
      (chain0 : Chain) (G0 : ChainGhost) (es : EpochSecret),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok v →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v.key = some es →
    FitsEnv MC lim (MC.stepEvents (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf) st_cost)
      (ChainAddEpochEnv (spqrHkdfWith F)
        ⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩)
  /-- `Ordering::Equal`: `FitsEnv` for `<Chain>::recv_key` at `pre.epoch - 1`. -/
  v1_fit_rk : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F)) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf : List AllocEvent)
      (chain0 chain1 : Chain) (G0 G1 : ChainGhost),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok v →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
    FitsEnv MC lim
      (MC.stepEvents
        (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key)
        st_cost)
      (ChainRecvKeyEnv (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩)
  /-- `Ordering::Equal`: `Env` closure on `<Chain>::recv_key` error at `+2028`. -/
  v1_env_rk_err : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F)) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf : List AllocEvent)
      (chain0 chain1 : Chain) (G0 G1 : ChainGhost) (err : Error) (evs_d : List AllocEvent),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok v →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
    chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++
      v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key ++
      chainRecvKeyEvents (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩ ++
      evs_d)
  /-- `Ordering::Equal`: `FitsEnv` for `<States>::into_pb` at `+2664`. -/
  v1_fit_sip : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 st1 : States spqrPolyApi (spqrAuthApi F))
      (key : Option EpochSecret) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf : List AllocEvent)
      (chain0 chain1 chain2 : Chain) (G0 G1 : ChainGhost) (rawKey : Bytes),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok ⟨key, st1⟩ →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1 →
    chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
    FitsEnv MC lim
      (MC.stepEvents
        (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩)
        st_cost)
      (IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩)
  /-- `Ordering::Equal`: `FitsEnv` for `<Chain>::into_pb` at `+2676`. -/
  v1_fit_cip : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 st1 : States spqrPolyApi (spqrAuthApi F))
      (key : Option EpochSecret) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip : List AllocEvent)
      (chain0 chain1 chain2 : Chain) (G0 G1 G2 : ChainGhost) (rawKey : Bytes),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok ⟨key, st1⟩ →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1 →
    chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
    IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
    FitsEnv MC lim
      (MC.stepEvents
        (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩ ++
          evs_sip)
        st_cost)
      (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G2, chain2⟩)
  /-- `Ordering::Equal`: `FitsEnv` for `<PqRatchetState>::encode_to_vec` at `+2688`. -/
  v1_fit_enc : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 st1 : States spqrPolyApi (spqrAuthApi F))
      (key : Option EpochSecret) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip evs_cip : List AllocEvent)
      (chain0 chain1 chain2 : Chain) (G0 G1 G2 : ChainGhost) (rawKey : Bytes),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok ⟨key, st1⟩ →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1 →
    chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
    IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
    ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G2, chain2⟩ evs_cip →
    FitsEnv MC lim
      (MC.stepEvents
        (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++
          v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key ++
          chainRecvKeyEvents (spqrHkdfWith F)
            ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩ ++
          evs_sip ++ evs_cip)
        st_cost)
      (PqRatchetStateEncodeToVecEnv
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) })
  /-- `Ordering::Equal`: `Env` closure on full V1 ratchet `Ok` return. -/
  v1_env_ok : ∀ (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
      (sckaMsg : Message spqrPolyApi) (st0 st1 : States spqrPolyApi (spqrAuthApi F))
      (key : Option EpochSecret) (kw0 kw1 : BitVec 64)
      (evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip evs_cip evs_enc evs_d : List AllocEvent)
      (chain0 chain1 chain2 : Chain) (G0 G1 G2 : ChainGhost) (rawKey : Bytes),
    msgPreamble msg.bytes = .ok pre →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
    States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
    States.recv K st0 sckaMsg = .ok ⟨key, st1⟩ →
    DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
    FreeOnlyEvs evs_md →
    FromPbEnv pb evs_fpb →
    RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
    ChainFromEnv pre_pb.chain pre_pb.versionNegotiation evs_cf →
    chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
    v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1 →
    chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
    IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs_sip →
    ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 232#64, G2, chain2⟩ evs_cip →
    PqRatchetStateEncodeToVecEnv
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
      evs_enc →
    FreeOnlyEvs evs_d →
    Env (evs_dec ++ evs_md ++ evs_fpb ++ evs_rcv ++ evs_cf ++
      v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key ++
      chainRecvKeyEvents (spqrHkdfWith F)
        ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩ ++
      evs_sip ++ evs_cip ++ evs_enc ++ evs_d)

/-! ## 2. Discharging the 3 Version-Branch Tails (`Ordering::Greater`, `Less`, `Equal`) -/

/-- `Ordering::Greater` (`V0ChainPlacedTailGen` at `+496`) discharged from `SpqrRecvBranchHyps`
    via `step_ordering_greater_placed_ofEnv` (`Part9PlacedBudget.lean`). -/
theorem v0ChainPlacedTailGen_ok_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {st_cost : MC.σ} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hB : SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
      Env st msg s0 st_cost)
    (evs_dec : List AllocEvent) (hdec_env : DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec) :
    V0ChainPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R := by
  intro pre _remPtr pre_pb vn pb w0 w1 _w26 s P
    hpre _hrem hdec hvn hinner _hw0 _hw26 hmin hver_gt
    hpc hrun hsp htr hx19 hx20 hx21 _hx22 _hx23 _hx24 _hx26 hx27 hx28 hx29 hP
  exact step_ordering_greater_placed_ofEnv st_cost Env evs_dec hC
    st msg ret pre pre_pb vn pb w0 w1 hst_len hpre hdec hvn hinner hmin hver_gt
    s0 s P R
    (fun evs_d hd => hB.env_dec_free pre evs_dec evs_d hpre hdec_env hd)
    (hB.gt_fit_cf pre pre_pb vn pb evs_dec hpre hdec hvn hinner hmin hver_gt hdec_env)
    (fun evs_cf chain0 G_c0 hcf_env hcf => by
      simpa only [List.append_assoc] using
        hB.gt_fit_rk pre pre_pb vn pb evs_dec evs_cf chain0 G_c0
          hpre hdec hvn hinner hmin hver_gt hdec_env hcf_env hcf)
    (fun evs_cf chain0 G_c0 chain1 rawKey gChain hcf_env hcf hrk => by
      simpa only [List.append_assoc] using
        hB.gt_fit_into pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 chain1 rawKey gChain
          hpre hdec hvn hinner hmin hver_gt hdec_env hcf_env hcf hrk)
    (fun evs_cf chain0 G_c0 chain1 rawKey gChain evs_into hcf_env hcf hrk hinto => by
      simpa only [List.append_assoc] using
        hB.gt_fit_enc pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 chain1 rawKey gChain evs_into
          hpre hdec hvn hinner hmin hver_gt hdec_env hcf_env hcf hrk hinto)
    (fun evs_cf chain0 G_c0 e evs_d hcf_env hcf hrk hd => by
      simpa only [List.append_assoc] using
        hB.gt_env_rk_err pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 e evs_d
          hpre hdec hvn hinner hmin hver_gt hdec_env hcf_env hcf hrk hd)
    (fun evs_cf chain0 G_c0 chain1 rawKey gChain evs_into evs_enc evs_d hcf_env hcf hrk hinto henc hd => by
      simpa only [List.append_assoc] using
        hB.gt_env_rk_ok pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 chain1 rawKey gChain
          evs_into evs_enc evs_d
          hpre hdec hvn hinner hmin hver_gt hdec_env hcf_env hcf hrk hinto henc hd)
    hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx27 hx28 hx29 hP

/-- `Ordering::Less` (`InitInnerPlacedTailGen` at `+1076`) discharged from `SpqrRecvBranchHyps`
    via `step_ordering_less_placed_ofEnv` (`Part7PlacedBudget.lean`). -/
theorem initInnerPlacedTailGen_ok_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {st_cost : MC.σ} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hB : SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
      Env st msg s0 st_cost)
    (evs_dec : List AllocEvent) (hdec_env : DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec) :
    InitInnerPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R := by
  intro pre _remPtr pre_pb vn pb w0 w1 w26 s P
    hpre _hrem hdec hvn hinner _hw0 hw26 hmin hver_lt
    hpc hrun hsp htr hx19 hx20 _hx21 _hx22 _hx23 _hx24 hx25 hx26 _hx27 _hx28 hx29 hP
  exact step_ordering_less_placed_ofEnv st_cost Env evs_dec hC
    st msg ret pre pre_pb vn pb w0 w1 w26
    hst_len hpre hdec hvn hinner hw26 hmin hver_lt
    s0 s P R
    (fun evs_d hd => hB.env_dec_free pre evs_dec evs_d hpre hdec_env hd)
    (fun dir hdir =>
      hB.lt_fit_init pre pre_pb vn pb w1 dir evs_dec hpre hdec hvn hinner hmin hver_lt hdec_env hdir)
    (fun dir evs_init hdir hinit_env => by
      simpa only [List.append_assoc] using
        hB.lt_fit_cf pre pre_pb vn pb w1 dir evs_dec evs_init
          hpre hdec hvn hinner hmin hver_lt hdec_env hdir hinit_env)
    (fun dir evs_init evs_cf ch G hdir hinit_env hcf_env hcf => by
      simpa only [List.append_assoc] using
        hB.lt_fit_into pre pre_pb vn pb w1 dir evs_dec evs_init evs_cf ch G
          hpre hdec hvn hinner hmin hver_lt hdec_env hdir hinit_env hcf_env hcf)
    (fun dir evs_init evs_cf evs_d hdir hinit_env hcf_env hd => by
      simpa only [List.append_assoc] using
        hB.lt_env_err pre pre_pb vn pb w1 dir evs_dec evs_init evs_cf evs_d
          hpre hdec hvn hinner hmin hver_lt hdec_env hdir hinit_env hcf_env hd)
    (fun dir evs_init evs_cf ch G evs_into evs_d hdir hinit_env hcf_env hcf hinto hd => by
      simpa only [List.append_assoc] using
        hB.lt_env_ok pre pre_pb vn pb w1 dir evs_dec evs_init evs_cf ch G evs_into evs_d
          hpre hdec hvn hinner hmin hver_lt hdec_env hdir hinit_env hcf_env hcf hinto hd)
    hs0_align (sp_sub_4992_ne_zero hsp_lo) hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

/-- `Ordering::Equal` (`V1RatchetPlacedTailLSGen` at `+1532`) discharged from
    `SpqrRecvBranchHyps` by composing `step_v1_ratchet_1532_to_1856_placed_ofEnv`,
    `step_v1_ratchet_1856_to_2664_placed_ofEnv`, `step_chainFrom_err_2568_placed_ofEnv`,
    `step_recvKey_err_2028_placed_ofEnv`, and `step_v1_ok_2664_to_ret_placed_ofEnv`. -/
theorem v1RatchetPlacedTailGen_ok_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {st_cost : MC.σ} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64) (s0 : State) (R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hs0_align : s0.spAligned = true)
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hB : SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
      Env st msg s0 st_cost)
    (evs_dec : List AllocEvent) (hdec_env : DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec) :
    V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R := by
  intro pre remPtr pre_pb pb w0 w1 s P
    hpre hvalid hdec hinner _hw0 hmv hmin
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP
  have hep0 : (pre.epoch == 0#64) = false := msgPreamble_epoch_beq_zero_false hpre hmv
  have hsp4640_ne : s0.sp - 4640#64 ≠ 0#64 := sp_sub_4640_ne_zero hsp_lo
  refine step_v1_ratchet_1532_to_1856_placed_ofEnv Env evs_dec hC
    st msg ret pre remPtr pre_pb pb w0 w1 hst_len hpre hvalid hdec hinner hmv hmin s0 s P R
    (fun evs_d hd => hB.env_dec_free pre evs_dec evs_d hpre hdec_env hd)
    (fun evs_md hmd => by
      simpa only [List.append_assoc] using
        hB.v1_fit_fpb pre pre_pb pb evs_dec evs_md hpre hdec hinner hmv hmin hdec_env hmd)
    (fun evs_md evs_fpb evs_d hmd hfpb hd => by
      simpa only [List.append_assoc] using
        hB.v1_env_fpb_err pre pre_pb pb evs_dec evs_md evs_fpb evs_d
          hpre hdec hinner hmv hmin hdec_env hmd hfpb hd)
    (fun sckaMsg st0 evs_md evs_fpb hmsg hfrom hmd hfpb => by
      simpa only [List.append_assoc] using
        hB.v1_fit_rcv pre pre_pb pb sckaMsg st0 evs_dec evs_md evs_fpb
          hpre hdec hinner hmv hmin hmsg hfrom hdec_env hmd hfpb)
    (fun sckaMsg st0 evs_md evs_fpb evs_rcv evs_d hmsg hfrom hmd hfpb hrcv hd => by
      simpa only [List.append_assoc] using
        hB.v1_env_rcv_err pre pre_pb pb sckaMsg st0 evs_dec evs_md evs_fpb evs_rcv evs_d
          hpre hdec hinner hmv hmin hmsg hfrom hdec_env hmd hfpb hrcv hd)
    hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP ?_
  intro evs_md evs_fpb evs_rcv sckaMsg st0 v kw0 kw1 kw2 kw3 P_key s1 P1
    hmd hfpb hrcv hmsg hfrom hrecv hfold_key
    hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1
    hx26_1 hx27_1 hx28_1 hx29_1 hP1
  refine step_v1_ratchet_1856_to_2664_placed_ofEnv (Env := Env)
    (((evs_dec ++ evs_md) ++ evs_fpb) ++ evs_rcv) hC
    st msg ret pre pre_pb pb w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R s0 s1 P1
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hfold_key
    (by
      simpa only [List.append_assoc] using
        hB.v1_fit_cf pre pre_pb pb sckaMsg st0 v evs_dec evs_md evs_fpb evs_rcv
          hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv)
    (fun evs_cf chain0 G0 es hcf_env hcf hvk => by
      simpa only [List.append_assoc] using
        hB.v1_fit_add pre pre_pb pb sckaMsg st0 v kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf
          chain0 G0 es hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv
          hcf_env hcf hvk)
    (fun evs_cf chain0 G0 chain1 G1 hcf_env hcf hkey => by
      simpa only [List.append_assoc] using
        hB.v1_fit_rk pre pre_pb pb sckaMsg st0 v kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf
          chain0 chain1 G0 G1 hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv
          hcf_env hcf hkey)
    hs0_align hsp4640_ne
    hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1
    hx26_1 hx27_1 hx28_1 hx29_1 hP1
    ?_ ?_ ?_
  · intro evs_cf e q0_err w3_err s_err P_err hcf_env hcf htag_q0
      hpc_e hrun_e hsp_e htr_e _hx8_e _hx9_e hx19_e _hx20_e _hx21_e _hx22_e hx23_e hx24_e hx25_e
      _hx26_e _hx27_e hx28_e _hx29_e hP_err
    obtain ⟨herr, hnp⟩ :=
      spqrV1Recv_v1_chainFrom_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
    subst hP_err
    apply sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
    exact step_chainFrom_err_2568_placed_ofEnv A lim st_cost Env
      ((((evs_dec ++ evs_md) ++ evs_fpb) ++ evs_rcv) ++ evs_cf)
      (fun evs_d hd => by
        simpa only [List.append_assoc] using
          hB.v1_env_cf_err pre pre_pb pb sckaMsg st0 v e
            evs_dec evs_md evs_fpb evs_rcv evs_cf evs_d
            hpre hdec hinner hmv hmin hmsg hfrom hrecv hcf hdec_env hmd hfpb hrcv hcf_env hd)
      F K ext (toDropContractsBudget hC)
      st msg ret pre_pb w0 w1 sckaMsg v kw0 kw1 kw2 kw3 P_key hfold_key
      e q0_err w3_err herr htag_q0 s0 s_err _ R _ rfl hs0_align
      hpc_e hrun_e hsp_e htr_e hx19_e hx23_e hx24_e hx25_e hx28_e (by ac_rfl) hcl
  · intro evs_cf chain0 chain1 G0 G1 err w1_err w2_err w3_err G1' s_err P_err
      hcf_env hcf hkey hrk hw1_err
      hpc_e hrun_e hsp_e htr_e hx19_e hx21_e hx22_e hx23_e hx24_e hx26_e hx29_e hP_err
    obtain ⟨herr, hnp⟩ := spqrV1Recv_v1_recvKey_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
      (topResult_addEpoch_of_v1ChainAfterKey hkey) hrk
    subst hP_err
    apply sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
    exact step_recvKey_err_2028_placed_ofEnv A lim st_cost Env
      (((((evs_dec ++ evs_md) ++ evs_fpb) ++ evs_rcv) ++ evs_cf ++
        v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key) ++
        chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩)
      (fun evs_d hd => by
        simpa only [List.append_assoc] using
          hB.v1_env_rk_err pre pre_pb pb sckaMsg st0 v kw0 kw1
            evs_dec evs_md evs_fpb evs_rcv evs_cf chain0 chain1 G0 G1 err evs_d
            hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv hcf_env hcf hkey hrk hd)
      F K ext (toDropContractsBudget hC)
      st msg ret pre_pb w0 w1 sckaMsg v G1' chain1 err w1_err w2_err w3_err herr hw1_err
      s0 s_err _ R _ rfl hs0_align
      hpc_e hrun_e hsp_e htr_e hx19_e hx21_e hx22_e hx23_e hx24_e hx26_e hx29_e (by ac_rfl) hcl
  · intro evs_cf chain0 chain1 chain2 G0 G1 G2 rawKey cap_rk ptr_rk s_ok P_ok
      hcf_env hcf hkey hrk
      hpc_ok hrun_ok hsp_ok htr_ok hx19_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx26_ok hx29_ok hP_ok
    rcases v with ⟨key, st1⟩
    exact step_v1_ok_2664_to_ret_placed_ofEnv (Env := Env)
      (((((evs_dec ++ evs_md) ++ evs_fpb) ++ evs_rcv) ++ evs_cf ++
        v1ChainAfterKeyEvents (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key) ++
        chainRecvKeyEvents (spqrHkdfWith F)
          ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩)
      hC st msg ret pre pre_pb pb sckaMsg st0 st1 key chain0 chain1 chain2 G2 rawKey
      w0 w1 cap_rk ptr_rk hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf
      (topResult_addEpoch_of_v1ChainAfterKey hkey) hrk
      s0 s_ok P_ok R
      (by
        simpa only [List.append_assoc] using
          hB.v1_fit_sip pre pre_pb pb sckaMsg st0 st1 key kw0 kw1
            evs_dec evs_md evs_fpb evs_rcv evs_cf chain0 chain1 chain2 G0 G1 rawKey
            hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv hcf_env hcf hkey hrk)
      (fun evs_sip hsip => by
        simpa only [List.append_assoc] using
          hB.v1_fit_cip pre pre_pb pb sckaMsg st0 st1 key kw0 kw1
            evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip chain0 chain1 chain2 G0 G1 G2 rawKey
            hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv hcf_env hcf hkey hrk hsip)
      (fun evs_sip evs_cip hsip hcip => by
        simpa only [List.append_assoc] using
          hB.v1_fit_enc pre pre_pb pb sckaMsg st0 st1 key kw0 kw1
            evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip evs_cip chain0 chain1 chain2 G0 G1 G2 rawKey
            hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv hcf_env hcf hkey hrk hsip hcip)
      (fun evs_sip evs_cip evs_enc evs_d hsip hcip henc hd => by
        simpa only [List.append_assoc] using
          hB.v1_env_ok pre pre_pb pb sckaMsg st0 st1 key kw0 kw1
            evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip evs_cip evs_enc evs_d
            chain0 chain1 chain2 G0 G1 G2 rawKey
            hpre hdec hinner hmv hmin hmsg hfrom hrecv hdec_env hmd hfpb hrcv hcf_env hcf hkey hrk
            hsip hcip henc hd)
      hs0_align hpc_ok hrun_ok hsp_ok htr_ok
      hx19_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx26_ok hx29_ok hP_ok

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudgetAux
