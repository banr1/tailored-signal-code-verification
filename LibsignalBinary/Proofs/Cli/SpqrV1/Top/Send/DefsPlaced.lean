/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced

/-!
# Relocatable Definitions, `.rodata` Bundle, & Callee Contracts for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Defines `[LibsignalPlacement]` entry/program abbreviations, `.rodata` table bundles, and
`SpqrSendPlacedContracts` for Block `427`.
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
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

/-- Rebased relocatable program for Block `427` (`spqr::send::<signal_session_ratchet::Coins>`)
    under `Rust.withPanics ext`. -/
noncomputable abbrev spqrSendPlacedProg (ext : String → Option (State → State)) : Program :=
  (blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext)

noncomputable abbrev cliSpqrSendPlacedProg (ext : String → Option (State → State)) : Program :=
  spqrSendPlacedProg ext

/-- Symbolic entry address of Block `427` (`spqr::send::<signal_session_ratchet::Coins>`). -/
noncomputable abbrev spqrSendPlacedEntry : BitVec 64 := (blkPl_427).base

noncomputable abbrev cliSpqrSendPlacedEntry : BitVec 64 := spqrSendPlacedEntry

/-- `.rodata` symbol name for the combined 64-byte jump-table block of
    `spqr::send::<signal_session_ratchet::Coins>` (Block `427`). -/
abbrev spqrSendRoSym : String :=
  "libsignal_cli_ratchet:.rodata.spqr::send::<libsignal_cli_ratchet::Coins>"

abbrev cliSpqrSendRoSym : String := spqrSendRoSym

/-- CLI `.rodata` symbol for `sckaKeyInfoPrefix` at Block `427` offsets `+1576`/`+1580`. -/
abbrev cliSpqrSendLanon29Sym : String :=
  "libsignal_cli_ratchet:.rodata..Lanon.29"

/-- CLI `.rodata` symbol for the 32-byte zero constant at Block `427` offsets `+1624`/`+1628`. -/
abbrev cliSpqrSendCst32Sym : String :=
  "libsignal_cli_ratchet:.rodata.cst32"

/-- Global log-filter zero invariant `lsLogFilterAddr ↦₆₄ 0#64`. -/
abbrev spqrLogLevelZeroPlacedAt : SepProp :=
  lsLogFilterAddr ↦₆₄ 0#64

/-- Read-only separation-logic assertion for jump table 1 (`22` bytes = 11 `u16` entries at `+0`). -/
def spqrSendStatesJumpTablePlacedAt : SepProp :=
  (lsρ spqrSendRoSym) ↦ᵣ spqrSendStatesJumpTableBytes

/-- Read-only separation-logic assertion for jump table 2 (`22` bytes = 11 `u16` entries at `+22`). -/
def spqrSendEncodeJumpTablePlacedAt : SepProp :=
  (lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes

/-- Read-only separation-logic assertion for jump table 3 (`20` bytes = 10 `u16` entries at `+44`). -/
def spqrSendDropJumpTablePlacedAt : SepProp :=
  (lsρ spqrSendRoSym + 44#64) ↦ᵣ spqrSendDropJumpTableBytes

/-- Bundle of all relocatable `.rodata` tables used by `spqr::send::<Coins>` (Block `427`) and its callees. -/
def spqrSendRoPlacedAt : SepProp :=
  spqrSendStatesJumpTablePlacedAt ∗
  spqrSendEncodeJumpTablePlacedAt ∗
  spqrSendDropJumpTablePlacedAt ∗
  v1StateJumpTablesPlacedAt ∗
  statesFromPbJumpTablePlacedAt ∗
  statesIntoPbJumpTablePlacedAt ∗
  reduceTablePlacedAt ∗
  tokenInitPlacedAt

/-- Unpacked 11-halfword (`↦₁₆ᵣ`) form of `spqrSendStatesJumpTablePlacedAt`. -/
theorem spqrSendStatesJumpTablePlacedAt_eq_words :
    spqrSendStatesJumpTablePlacedAt =
      spqrSendStatesJumpTableWordsAt (lsρ spqrSendRoSym) :=
  spqrSendStatesJumpTableBytes_eq (lsρ spqrSendRoSym)

/-! ## Leaf `PlacedOkX` Contracts on `spqrSendPlacedProg` (Block `427`) -/

/-- `<PolyEncoder as Encoder>::next_chunk` (Block `416`) on `spqrSendPlacedProg ext`. -/
def PolyNextChunkPlacedOkX (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 416)
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A))

/-- `<PolyEncoder as Encoder>::encode_bytes` (Block `417`) on `spqrSendPlacedProg ext`. -/
def EncodeBytesPlacedOkX (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 417)
    (withLsCodeRoLoaded lsmpl (encodeBytesSpecX A))

/-- `<HeaderSent>::send_ek_chunk` (Block `336`) on `spqrSendPlacedProg ext`. -/
def HeaderSentSendEkChunkPlacedOkX (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 336)
    (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec A F))

/-- `<Ct1Received>::send_ek_chunk` (Block `345`) on `spqrSendPlacedProg ext`. -/
def Ct1ReceivedSendEkChunkPlacedOkX (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 345)
    (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec A F))

/-- `<Ct1Sampled>::send_ct1_chunk` (Block `335`) on `spqrSendPlacedProg ext`. -/
def Ct1SampledSendCt1ChunkPlacedOkX (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 335)
    (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec A F))

/-- `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`) on `spqrSendPlacedProg ext`. -/
def EkReceivedCt1SampledSendCt1ChunkPlacedOkX (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 344)
    (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F))

/-- `<Ct2Sampled>::send_ct2_chunk` (Block `354`) on `spqrSendPlacedProg ext`. -/
def Ct2SampledSendCt2ChunkPlacedOkX (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 354)
    (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec A F))

/-- `signal_session_coins_fill` (Block `618`) on `spqrSendPlacedProg ext`. -/
def CoinsFillPlacedOkX (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 618)
    (withLsCodeRoLoaded lsmpl (spqrCoinsFillSpecPlaced spqrSendCalleeStack))

/-! ## Complete Relocatable Callee Contract Bundle `SpqrSendPlacedContracts` for Block `427` -/

/-- Bundle of all relocatable `[LibsignalPlacement]` callee contracts required by
    `spqr::send::<signal_session_ratchet::Coins>` (Block `427`). -/
structure SpqrSendPlacedContracts (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  /-- Bridge between `DecodeState.optProtoInnerStateAt H_inner` and `Drop.optProtoInnerStateAt`. -/
  h_inner_eq : ∀ a st, Top.DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st
  /-- Rust heap allocator + `memcpy` + `memcmp` contracts under `[LibsignalPlacement]`. -/
  alloc : AllocContractsPlaced A ext
  /-- `signal_session_coins_fill` (Block `618`). -/
  coinsFill_ok : CoinsFillPlacedOkX ext
  /-- `spqr::decode_state` (Block `325`). -/
  decodeState_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX H_inner A))
  /-- `<States>::from_pb` (Block `333`). -/
  statesFromPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A C.F))
  /-- `<States>::into_pb` (Block `334`). -/
  statesIntoPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A C.F))
  /-- `<Chain>::from_pb` (Block `364`). -/
  chainFromPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A))
  /-- `spqr::chain_from_version_negotiation` (Block `328`). -/
  chainFromVn_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith C.F) A))
  /-- `<Chain>::add_epoch` (Block `368`). -/
  chainAddEpoch_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith C.F) A))
  /-- `<Chain>::send_key` (Block `367`). -/
  chainSendKey_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith C.F) A))
  /-- `<Chain>::into_pb` (Block `365`). -/
  chainIntoPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A))
  /-- `<Message>::serialize` (Block `352`). -/
  messageSerialize_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi A))
  /-- `spqr::encode_varint` (Block `326`). -/
  encodeVarint_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A))
  /-- `<Authenticator>::mac_hdr` (Block `342`). -/
  authMacHdr_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec C.F A))
  /-- `<Authenticator>::update` (Block `341`). -/
  authUpdate_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec C.F A))
  /-- `spqr::kdf::hkdf_to_vec` (Block `378`). -/
  hkdfToVec_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F)))
  /-- `<PolyEncoder>::encode_bytes` (Block `417`). -/
  encodeBytes_ok : EncodeBytesPlacedOkX A ext
  /-- `<PolyEncoder as Encoder>::next_chunk` (Block `416`). -/
  polyNextChunk_ok : PolyNextChunkPlacedOkX A ext
  /-- Leaf `<HeaderSent>::send_ek_chunk` (Block `336`). -/
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkPlacedOkX A C.F ext
  /-- Leaf `<Ct1Received>::send_ek_chunk` (Block `345`). -/
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkPlacedOkX A C.F ext
  /-- Leaf `<Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkPlacedOkX A C.F ext
  /-- Leaf `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
  ekReceivedCt1SampledSendCt1Chunk_ok : EkReceivedCt1SampledSendCt1ChunkPlacedOkX A C.F ext
  /-- Leaf `<Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkPlacedOkX A C.F ext
  /-- `drop_glue::<proto::Chain> [local#2]` (Block `439`, CGU-local CLI counterpart of Block `136`). -/
  dropProtoChain_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A))
  /-- `drop_glue::<[chain::ChainEpoch]> [local#3]` (Block `446`, CGU-local CLI counterpart of Block `143`). -/
  dropChainEpochSlice_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec A))

end CryptoVerification.Cli.SpqrV1.Top.Send
