/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import ProofLib.SepLogic.WPp

/-!
# Relocatable Callee Contract & `.rodata` Scaffolding for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Provides `.rodata` extraction/restoration helpers and discharges `SpqrSendPlacedContracts`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `.rodata` Bundle Introduction & Restoration Helpers (`spqrSendRoPlacedAt`) -/

/-- Introduce `spqrSendRoPlacedAt` into the precondition of a `SepWPp` obligation from
    `GF.Mul2U16.tokenInitPlacedAt ∗ P` under `LibsignalRoLoaded lsmpl s0.mem`. -/
theorem sepWPp_intro_spqrSendRoPlacedAt
    {prog : Program} {ret : BitVec 64} {s0 : State} (hro : LibsignalRoLoaded lsmpl s0.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s0 (spqrSendRoPlacedAt ∗ P) Q Qp) :
    SepWPp prog ret s0 (GF.Mul2U16.tokenInitPlacedAt ∗ P) Q Qp := by
  intro R0 hm hL
  have hm_assoc : s0.mem ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ (P ∗ R0) := by
    rwa [← sepConj_assoc]
  have hm' : s0.mem ⊨ (spqrSendRoPlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact lsro_spqrSendRoPlacedAt hro hm_assoc
  exact h R0 hm' hL

/-- Discard the read-only `.rodata` slices in `spqrSendRoPlacedAt`, recovering
    `GF.Mul2U16.tokenInitPlacedAt ∗ P`. -/
theorem spqrSendRoPlacedAt_restore {m : Memory} {P : SepProp}
    (hm : m ⊨ spqrSendRoPlacedAt ∗ P) :
    m ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ P := by
  have hm' :
      m ⊨ (spqrSendStatesJumpTablePlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗
           spqrSendDropJumpTablePlacedAt ∗
           Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
           statesFromPbJumpTablePlacedAt ∗
           statesIntoPbJumpTablePlacedAt ∗
           GF.UnacceleratedMul.reduceTablePlacedAt) ∗
          (GF.Mul2U16.tokenInitPlacedAt ∗ P) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [spqrSendRoPlacedAt]
    ac_rfl
  exact Satisfies.of_sep_right hm'

/-! ## 2. Cross-Block `withLsCodeRoLoaded` Transfer Combinators -/

/-- Transfer a `withLsCodeRoLoaded lsmpl spec` contract from block `j` to `callerProg` (block `i`). -/
theorem ls_subroutine_ok_cro_of_cro {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  keys_ls_subroutine_ok_of_block_cro h hi hj hj_unmut

/-- Lift a `withLsCodeLoaded lsmpl spec` contract on block `j` to `withLsCodeRoLoaded lsmpl spec`
    on `callerProg` (block `i`). -/
theorem ls_subroutine_ok_cro_of_cl {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  have h_cro_j : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono h
      (fun _ _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, withLsCodeLoaded] at hpre ⊢
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
        exact ⟨hpre.1.1, hpre.2⟩)
      (fun _ _ _ _ hpost => hpost)
  exact keys_ls_subroutine_ok_of_block_cro h_cro_j hi hj hj_unmut

/-- Lift a `withLsCallInv lsmpl spec` contract on block `j` to `withLsCodeRoLoaded lsmpl spec`
    on `callerProg` (block `i`). -/
theorem ls_subroutine_ok_cro_of_callInv {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCallInv lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  have h_cro_j : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono h
      (fun _ _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, withLsCallInv] at hpre ⊢
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hpre.1.2, hpre.1.1⟩, hpre.2⟩)
      (fun _ _ _ _ hpost => hpost)
  exact keys_ls_subroutine_ok_of_block_cro h_cro_j hi hj hj_unmut

/-- Lift a plain `spec` contract on block `j` to `withLsCodeRoLoaded lsmpl spec`
    on `callerProg` (block `i`). -/
theorem ls_subroutine_ok_cro_of_plain {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  ls_subroutine_ok_cro_of_cl (subroutine_ok_withLsCodeLoaded_of_plain h) hi hj hj_unmut

/-- Lift a plain `spec` contract on `blockProgram lsmpl j H` to `withLsCodeRoLoaded lsmpl spec`
    on `callerProg` (block `i`). -/
theorem ls_subroutine_ok_of_blockProgram_plain {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide)
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns := by decide +kernel) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  have h_cl : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec) :=
    subroutine_ok_withLsCodeLoaded_of_plain hcallee
  have h_cro : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono h_cl
      (fun _ _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, withLsCodeLoaded] at hpre ⊢
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
        exact ⟨hpre.1.1, hpre.2⟩)
      (fun _ _ _ _ hpost => hpost)
  exact ls_subroutine_ok_of_blockProgram_cro h_cro hi hj hj_unmut hext_j

/-! ## 3. CGU-Local Drop Glue (`Block 439`, `Block 446`) & `CliSpqrSendPeerSeams` Wiring -/

/-- `core::ptr::drop_in_place::<spqr::proto::pq_ratchet::Chain>` (`Block 439`) meets
    `withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)` on `spqrSendPlacedProg ext`. -/
theorem drop_proto_spqr_chain_placed_ok_x {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)) :=
  ls_subroutine_ok_cro_of_plain
    (CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_placed hA.dealloc)

/-- `core::ptr::drop_in_place::<[spqr::proto::pq_ratchet::chain::Epoch]> [local#1]` (`Block 446`)
    meets `withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec A)` on `spqrSendPlacedProg ext`. -/
theorem drop_chain_epoch_slice_local1_placed_ok_x {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec A)) :=
  ls_subroutine_ok_cro_of_plain
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed hA.dealloc)

/-- `<HeaderSent>::send_ek_chunk` (`Block 336`) meets `HeaderSentSendEkChunkPlacedOkX A C.F ext`. -/
theorem headerSent_send_ek_chunk_placed_ok_x {A : RustAlloc} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    HeaderSentSendEkChunkPlacedOkX A C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.headerSentSendEkChunk_ok

/-- `<Ct1Received>::send_ek_chunk` (`Block 345`) meets `Ct1ReceivedSendEkChunkPlacedOkX A C.F ext`. -/
theorem ct1Received_send_ek_chunk_placed_ok_x {A : RustAlloc} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    Ct1ReceivedSendEkChunkPlacedOkX A C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ct1ReceivedSendEkChunk_ok

/-- `<Ct1Sampled>::send_ct1_chunk` (`Block 335`) meets `Ct1SampledSendCt1ChunkPlacedOkX A C.F ext`. -/
theorem ct1Sampled_send_ct1_chunk_placed_ok_x {A : RustAlloc} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    Ct1SampledSendCt1ChunkPlacedOkX A C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ct1SampledSendCt1Chunk_ok

/-- `<EkReceivedCt1Sampled>::send_ct1_chunk` (`Block 344`) meets `EkReceivedCt1SampledSendCt1ChunkPlacedOkX A C.F ext`. -/
theorem ekReceivedCt1Sampled_send_ct1_chunk_placed_ok_x {A : RustAlloc} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkX A C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ekReceivedCt1SampledSendCt1Chunk_ok

/-- `<Ct2Sampled>::send_ct2_chunk` (`Block 354`) meets `Ct2SampledSendCt2ChunkPlacedOkX A C.F ext`. -/
theorem ct2Sampled_send_ct2_chunk_placed_ok_x {A : RustAlloc} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    Ct2SampledSendCt2ChunkPlacedOkX A C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ct2SampledSendCt2Chunk_ok

/-- `signal_session_coins_fill` (`Block 618`) meets `CoinsFillPlacedOkX ext`. -/
theorem coins_fill_placed_ok_x {A : RustAlloc} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    CoinsFillPlacedOkX ext :=
  ls_subroutine_ok_of_blockProgram_plain hSeams.coinsFill_ok

/-! ## 4. Constructing `SpqrSendPlacedContracts` from Placed Callee Contracts & `CliSpqrSendPeerSeams` -/

/-- Assemble `SpqrSendPlacedContracts canonicalV1InnerHeap A ctl C K ext` from placed callee contracts
    and `CliSpqrSendPeerSeams A C ext`. -/
theorem spqrSendPlacedContracts_of_okX
    {A : RustAlloc} {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hChainFromPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A)))
    (hChainAddEpoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith C.F) A)))
    (hChainSendKey : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith C.F) A)))
    (hChainIntoPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A)))
    (hAuthMacHdr : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec C.F A)))
    (hAuthUpdate : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec C.F A)))
    (hHkdfToVec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))))
    (hEncodeBytes : EncodeBytesPlacedOkX A ext)
    (hPolyNextChunk : PolyNextChunkPlacedOkX A ext)
    (hSeams : CliSpqrSendPeerSeams A C ext) :
    SpqrSendPlacedContracts canonicalV1InnerHeap A ctl C K ext where
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A
  alloc := hA
  coinsFill_ok := coins_fill_placed_ok_x hSeams
  decodeState_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.decodeState_ok
  statesFromPb_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.statesFromPb_ok
  statesIntoPb_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.statesIntoPb_ok
  chainFromPb_ok := hChainFromPb
  chainFromVn_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.chainFromVn_ok
  chainAddEpoch_ok := hChainAddEpoch
  chainSendKey_ok := hChainSendKey
  chainIntoPb_ok := hChainIntoPb
  messageSerialize_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.messageSerialize_ok
  encodeVarint_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.encodeVarint_ok
  authMacHdr_ok := hAuthMacHdr
  authUpdate_ok := hAuthUpdate
  hkdfToVec_ok := hHkdfToVec
  encodeBytes_ok := hEncodeBytes
  polyNextChunk_ok := hPolyNextChunk
  headerSentSendEkChunk_ok := headerSent_send_ek_chunk_placed_ok_x hSeams
  ct1ReceivedSendEkChunk_ok := ct1Received_send_ek_chunk_placed_ok_x hSeams
  ct1SampledSendCt1Chunk_ok := ct1Sampled_send_ct1_chunk_placed_ok_x hSeams
  ekReceivedCt1SampledSendCt1Chunk_ok := ekReceivedCt1Sampled_send_ct1_chunk_placed_ok_x hSeams
  ct2SampledSendCt2Chunk_ok := ct2Sampled_send_ct2_chunk_placed_ok_x hSeams
  dropProtoChain_ok := drop_proto_spqr_chain_placed_ok_x hA
  dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_placed_ok_x hA

end CryptoVerification.Cli.SpqrV1.Top.Send
