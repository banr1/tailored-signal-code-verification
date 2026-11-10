/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpers
public import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
public import LibsignalBinary.Proofs.SpqrV1.Auth.Update
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch

/-!
# Shared Definitions, Stack Layout, and Callee Contract Bundle for `spqr::send` (`0x3085c`)

**Checked by Lean.**

Defines stack frame constants (`spqrSendFrame = 8064`, `spqrSendCalleeStack = 123008`),
`spqrSendSavedRegs`, `optEpochSecretRegSlotAt`, `statesSendArmOffset` for jump table 1,
and the callee contract bundles `SpqrSendContracts` and `SpqrSendContractsExt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## Stack Frame Constants and Saved Callee-Saved Registers (`sp + 0x1f20 .. sp + 0x1f80`) -/

/-- Own stack frame of `spqr::send::<HookRng>` (`0x3085c`):
    `0x60` (`96`B saved registers) + `0x1f20` (`7,968`B local slots) = `0x1f80` (`8,064`B). -/
abbrev spqrSendFrame : Nat := 8064

/-- Remaining callee stack budget of `spqr::send::<HookRng>` (`2^17 - 8,064 = 123,008`B). -/
abbrev spqrSendCalleeStack : Nat := 123008

theorem spqrSendStack_eq : spqrSendStack = spqrSendCalleeStack + spqrSendFrame := by decide

/-- Saved callee-saved registers (`x29, x30, x28..x19`) at `[sp + 0x1f20 .. sp + 0x1f80)`
    (`sp = s0.sp - 0x1f80`, `sp + 0x1f20 = s0.sp - 0x60`). -/
def spqrSendSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 0x1f20#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp + 0x1f28#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 0x1f30#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp + 0x1f38#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 0x1f40#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp + 0x1f48#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 0x1f50#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp + 0x1f58#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 0x1f60#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp + 0x1f68#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 0x1f70#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp + 0x1f78#64) ↦₆₄ s0.readReg64 .x19)

theorem spqrSendSavedRegs_entails_memRegion (sp : BitVec 64) (s0 : State) :
    spqrSendSavedRegs sp s0 ⊢ memRegion (sp + 0x1f20#64) 96 := by
  unfold spqrSendSavedRegs
  have hcell (off : BitVec 64) (v : BitVec 64) :
      ((sp + off) ↦₆₄ v) ⊢ memRegion (sp + off) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + off) v
  rw [ProofLib.memRegion_split (sp + 0x1f20#64) 8 88 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64) 8 80 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64) 8 72 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp + 0x1f20#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (hcell _ _)))))))))))

theorem stackAt_spqrSend_split_96 (sp0 : BitVec 64) :
    stackAt sp0 spqrSendStack =
      stackAt (sp0 - 96#64) (spqrSendCalleeStack + 7968) ∗ cells (sp0 - 96#64) 12 := by
  have h := ProofLib.stackAt_split_cells sp0 (spqrSendCalleeStack + 7968) 12 (by decide)
  have h1 : spqrSendCalleeStack + 7968 + 8 * 12 = spqrSendStack := by decide
  rw [h1] at h
  exact h

theorem stackAt_spqrSend_split_frame (sp0 : BitVec 64) :
    stackAt (sp0 - 96#64) (spqrSendCalleeStack + 7968) =
      stackAt (sp0 - 8064#64) spqrSendCalleeStack ∗ memRegion (sp0 - 8064#64) 7968 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp0 - 96#64) - BitVec.ofNat 64 (spqrSendCalleeStack + 7968))
    spqrSendCalleeStack 7968 (by decide)]
  have h1 : (sp0 - 96#64) - BitVec.ofNat 64 (spqrSendCalleeStack + 7968) =
      (sp0 - 8064#64) - BitVec.ofNat 64 spqrSendCalleeStack := by
    change (sp0 - 96#64) - 130976#64 = (sp0 - 8064#64) - 123008#64
    bv_omega
  have h2 : (sp0 - 96#64) - BitVec.ofNat 64 (spqrSendCalleeStack + 7968) +
      BitVec.ofNat 64 spqrSendCalleeStack = sp0 - 8064#64 := by
    change (sp0 - 96#64) - 130976#64 + 123008#64 = sp0 - 8064#64
    bv_omega
  rw [h2, h1]

theorem stackAt_spqrSend_eq_callee_and_frame (sp0 : BitVec 64) :
    stackAt sp0 spqrSendStack =
      stackAt (sp0 - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (sp0 - 0x1f80#64) 0x1f20 ∗
      memRegion (sp0 - 0x1f80#64 + 0x1f20#64) 96 := by
  simp only [stackAt]
  have h1 := ProofLib.memRegion_split (sp0 - BitVec.ofNat 64 spqrSendStack)
    spqrSendCalleeStack 8064 (by decide)
  have h1' : spqrSendCalleeStack + 8064 = spqrSendStack := rfl
  rw [h1'] at h1
  have h2 := ProofLib.memRegion_split (sp0 - 0x1f80#64) 0x1f20 96 (by decide)
  have h2' : 0x1f20 + 96 = (8064 : Nat) := rfl
  rw [h2'] at h2
  have ha : (sp0 - 0x1f80#64) - BitVec.ofNat 64 spqrSendCalleeStack =
      sp0 - BitVec.ofNat 64 spqrSendStack := by
    change (sp0 - 8064#64) - 123008#64 = sp0 - 131072#64
    bv_omega
  have hb : (sp0 - BitVec.ofNat 64 spqrSendStack) + BitVec.ofNat 64 spqrSendCalleeStack =
      sp0 - 0x1f80#64 := by
    change (sp0 - 131072#64) + 123008#64 = sp0 - 8064#64
    bv_omega
  rw [h1, hb, ← ha, h2]

theorem stack_restore_spqrSend (sp0 : BitVec 64) (s0 : State) :
    stackAt (sp0 - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (sp0 - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (sp0 - 0x1f80#64) s0 ⊢
      stackAt sp0 spqrSendStack := by
  rw [stackAt_spqrSend_eq_callee_and_frame sp0]
  exact sepConj_mono_right (sepConj_mono_right (spqrSendSavedRegs_entails_memRegion (sp0 - 0x1f80#64) s0))

/-! ## Optional `epoch_secret` Register/Stack Layout (`sp + 0x1bc0`, `x21`, `x27`) -/

/-- Register+stack representation of `epoch_secret : Option<EpochSecret>` at the Phase 2 -> Phase 3
    join point (`0x314dc` / `0x31580`):
    - `x21 = cap` (`noneCap = -1` when `None`, `32 <= cap < 2^63` when `Some es`),
    - `x27 = ptr` (allocated buffer pointer when `Some es`),
    - `[sp + 0x1bc0] = es.secret.length` and `[sp + 0x1bc8] = es.epoch` when `Some es`
      (or `memRegion (sp + 0x1bc0) 16` when `None`). -/
def optEpochSecretRegSlotAt (A : RustAlloc) (sp x21 x27 : BitVec 64) :
    Option EpochSecret → SepProp
  | none =>
      ⌜x21 = LibsignalTripleRatchetRepr.noneCap⌝ ∗ memRegion (sp + 0x1bc0#64) 16
  | some es =>
      ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗
        ((sp + 0x1bc0#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
        ((sp + 0x1bc8#64) ↦₆₄ es.epoch) ∗
        vecU8Heap A x21 x27 es.secret

/-! ## Jump Table 1 Target Offsets (`0x309cc`) -/

/-- PC offset (in bytes from `spqrSendEntry b = b + 0x3085c`) jumped to by `br x10` at `0x309cc`
    for each of the 11 `States` variants. -/
def statesSendArmOffset {F : ShaCompress} :
    States spqrPolyApi (spqrAuthApi F) → BitVec 64
  | .keysUnsampled _ => 372#64          -- 0x309d0 (tag 2, idx 0, entry 0x0000)
  | .keysSampled _ => 1208#64           -- 0x30d14 (tag 3, idx 1, entry 0x00d1)
  | .headerSent _ => 960#64             -- 0x30c1c (tag 4, idx 2, entry 0x0093)
  | .ct1Received _ => 1040#64           -- 0x30c6c (tag 5, idx 3, entry 0x00a7)
  | .ekSentCt1Received _ => 924#64      -- 0x30bf8 (tag 6, idx 4, entry 0x008a)
  | .noHeaderReceived _ => 1284#64      -- 0x30d60 (tag 7, idx 5, entry 0x00e4)
  | .headerReceived _ => 1312#64        -- 0x30d7c (tag 8, idx 6, entry 0x00eb)
  | .ct1Sampled _ => 1128#64            -- 0x30cc4 (tag 1, idx 7, entry 0x00bd)
  | .ekReceivedCt1Sampled _ => 2460#64  -- 0x311f8 (tag 10, idx 8, entry 0x020a)
  | .ct1Acknowledged _ => 952#64        -- 0x30c14 (tag 11, idx 9, entry 0x0091)
  | .ct2Sampled _ => 2372#64            -- 0x311a0 (tag 12, idx 10, entry 0x01f4)

/-! ## `<PolyEncoder>::next_chunk` and Leaf `send_*_chunk` Contracts -/

/-- `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`) meets `(polyNextChunkSpec A img.base).inImage img`
    on `tripleRatchetProgAtExt img.base ext`. -/
def PolyNextChunkOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr polyNextChunkName)
    ((polyNextChunkSpec A img.base).inImage img)

def HeaderSentSendEkChunkOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentSendEkChunkName)
    ((headerSentSendEkChunkSpec A F img.base).inImage img)

def Ct1ReceivedSendEkChunkOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedSendEkChunkName)
    ((ct1ReceivedSendEkChunkSpec A F img.base).inImage img)

def Ct1SampledSendCt1ChunkOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1SampledSendCt1ChunkName)
    ((ct1SampledSendCt1ChunkSpec A F img.base).inImage img)

def EkReceivedCt1SampledSendCt1ChunkOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledSendCt1ChunkName)
    ((ekReceivedCt1SampledSendCt1ChunkSpec A F img.base).inImage img)

def Ct2SampledSendCt2ChunkOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledSendCt2ChunkName)
    ((ct2SampledSendCt2ChunkSpec A F img.base).inImage img)

/-! ## Callee Contract Bundles (`SpqrSendContracts`, `SpqrSendContractsExt`) -/

/-- Bundle of all `.rodata` tables used by `spqr::send::<HookRng>` (`0x3085c`) and its callees. -/
def spqrSendRoAt (b : BitVec 64) : SepProp :=
  spqrSendStatesJumpTableAt b ∗
  spqrSendEncodeJumpTableAt b ∗
  spqrSendDropJumpTableAt b ∗
  Prost.MessageMerge.v1StateJumpTablesAt b ∗
  statesFromPbJumpTableAt b ∗
  statesIntoPbJumpTableAt b ∗
  reduceTableAt b

/-- Bundle of all callee contracts and `.rodata` tables required by `spqr::send::<HookRng>` (`0x3085c`). -/
structure SpqrSendContracts (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  /-- Base alignment (`img.base &&& 0xfff#64 = 0#64`). -/
  base_aligned : img.base &&& 0xfff#64 = 0#64
  /-- `img` loads `libsignalSessionImage` (so `.rodata` jump tables are present under `ImgCallInv`). -/
  loads : Obj.Loads libsignalSessionImage img
  /-- Bridge between `DecodeState.optProtoInnerStateAt H_inner` and `Drop.optProtoInnerStateAt`. -/
  h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st
  /-- Rust heap allocator + `memcpy` + `memcmp` contracts. -/
  alloc : AllocContracts img.base A ext
  /-- `spqr::decode_state` (`0x5349c`). -/
  decodeState_ok : DecodeStateOkX H_inner img A ext
  /-- `<States>::from_pb` (`0x5a0a4`). -/
  statesFromPb_ok : StatesFromPbOkX img A C.F ext
  /-- `<States>::into_pb` (`0x5ce24`). -/
  statesIntoPb_ok : StatesIntoPbOkX img A C.F ext
  /-- `<Chain>::from_pb` (`0x60074`). -/
  chainFromPb_ok : ChainFromPbOkX img A ext
  /-- `spqr::chain_from_version_negotiation` (`0x545e4`). -/
  chainFromVn_ok : ChainFromVersionNegotiationOkX img (spqrHkdfWith C.F) A ext
  /-- `<Chain>::add_epoch` (`0x61004`). -/
  chainAddEpoch_ok : ChainAddEpochOkX img (spqrHkdfWith C.F) A ext
  /-- `<Chain>::send_key` (`0x60db0`). -/
  chainSendKey_ok : ChainSendKeyOkX img (spqrHkdfWith C.F) A ext
  /-- `<Chain>::into_pb` (`0x60514`). -/
  chainIntoPb_ok : ChainIntoPbOkX img A ext
  /-- `<Message>::serialize` (`0x5f784`). -/
  messageSerialize_ok : MessageSerializeOkX spqrPolyApi img A ext
  /-- `spqr::encode_varint` (`0x54040`). -/
  encodeVarint_ok : SpqrEncodeVarintOkX img A ext
  /-- `<Authenticator>::mac_hdr` (`0x69b0c`). -/
  authMacHdr_ok : AuthMacHdrOkX img C.F A ext
  /-- `<Authenticator>::update` (`0x69dbc`). -/
  authUpdate_ok : AuthUpdateOkX img C.F A ext
  /-- `spqr::kdf::hkdf_to_vec` (`0x66010`). -/
  hkdfToVec_ok : HkdfToVecOkX img A (spqrHkdfWith C.F) ext
  /-- `<PolyEncoder>::encode_bytes` (`0x6b560`). -/
  encodeBytes_ok : EncodeBytesOkX img A ext
  /-- `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`). -/
  polyNextChunk_ok : PolyNextChunkOkX img A ext
  /-- Leaf `<HeaderSent>::send_ek_chunk` (`0x5d860`). -/
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkOkX img A C.F ext
  /-- Leaf `<Ct1Received>::send_ek_chunk` (`0x5e250`). -/
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkOkX img A C.F ext
  /-- Leaf `<Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`). -/
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkOkX img A C.F ext
  /-- Leaf `<EkReceivedCt1Sampled>::send_ct1_chunk` (`0x5e1d0`). -/
  ekReceivedCt1SampledSendCt1Chunk_ok : EkReceivedCt1SampledSendCt1ChunkOkX img A C.F ext
  /-- Leaf `<Ct2Sampled>::send_ct2_chunk` (`0x5f9d4`). -/
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkOkX img A C.F ext
  /-- `drop_glue::<proto::Chain>` (`0x35530`). -/
  dropProtoChain_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropProtoSpqrChainName)
    (dropProtoSpqrChainSpec A)
  /-- `drop_glue::<[chain::Epoch]> [local#1]` (`0x35ec4`). -/
  dropChainEpochSlice_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name)
    (dropChainEpochSliceSpec A)

/-- Contract-parameterized (`*Ext`, `+ 16384` B extern-hook stack headroom) callee bundle for
    `spqr::send::<HookRng>` (`0x3085c`). -/
structure SpqrSendContractsExt (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  base_aligned : img.base &&& 0xfff#64 = 0#64
  loads : Obj.Loads libsignalSessionImage img
  h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st
  alloc : AllocContracts img.base A ext
  decodeState_ok : DecodeStateOkX H_inner img A ext
  statesFromPb_ok : StatesFromPbOkX img A C.F ext
  statesIntoPb_ok : StatesIntoPbOkX img A C.F ext
  chainFromPb_ok : ChainFromPbOkX img A ext
  chainFromVn_ok : ChainFromVersionNegotiationOkExt img (spqrHkdfWith C.F) A ext
  chainAddEpoch_ok : ChainAddEpochOkExt img (spqrHkdfWith C.F) A ext
  chainSendKey_ok : ChainSendKeyOkExt img (spqrHkdfWith C.F) A ext
  chainIntoPb_ok : ChainIntoPbOkX img A ext
  messageSerialize_ok : MessageSerializeOkX spqrPolyApi img A ext
  encodeVarint_ok : SpqrEncodeVarintOkX img A ext
  authMacHdr_ok : AuthMacHdrOkX img C.F A ext
  authUpdate_ok : AuthUpdateOkExt img C.F A ext
  hkdfToVec_ok : HkdfToVecOkExt img A (spqrHkdfWith C.F) ext
  encodeBytes_ok : EncodeBytesOkX img A ext
  polyNextChunk_ok : PolyNextChunkOkX img A ext
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkOkX img A C.F ext
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkOkX img A C.F ext
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkOkX img A C.F ext
  ekReceivedCt1SampledSendCt1Chunk_ok : EkReceivedCt1SampledSendCt1ChunkOkX img A C.F ext
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkOkX img A C.F ext
  dropProtoChain_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropProtoSpqrChainName)
    (dropProtoSpqrChainSpec A)
  dropChainEpochSlice_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name)
    (dropChainEpochSliceSpec A)

/-! ## Monotonicity Bridges (`*OkX → *OkExt`, `SpqrSendContracts.toExt`) -/

private theorem stackAt_split_grow (sp : BitVec 64) (nX nExt : Nat)
    (hle : nX ≤ nExt := by decide) (hbd : nExt ≤ 131072 := by decide) :
    stackAt sp nExt = memRegion (sp - BitVec.ofNat 64 nExt) (nExt - nX) ∗ stackAt sp nX := by
  have hbd' : nX + (nExt - nX) ≤ 2 ^ 64 := by omega
  have h := ProofLib.stackAt_split_bottom sp nX (nExt - nX) hbd'
  rwa [Nat.add_sub_of_le hle] at h

private theorem sub_ok_inImage_grow_stack {α : Type} {prog : Program} {img : Obj.Image}
    {entry : BitVec 64} {specX specExt : Spec α} (nX nExt : Nat)
    (hpre_imp : ∀ x s,
      specExt.pre x s ⊢
        specX.pre x s ∗ memRegion (s.sp - BitVec.ofNat 64 nExt) (nExt - nX))
    (hpost_imp : ∀ x s sf,
      specX.post x s sf ∗ memRegion (s.sp - BitVec.ofNat 64 nExt) (nExt - nX) ⊢
        specExt.post x s sf)
    (hpan_eq : ∀ x s sf, ∃ φ : Prop,
      specX.onPanic x s sf = (⌜φ⌝ ∗ anyHeap) ∧ specExt.onPanic x s sf = (⌜φ⌝ ∗ anyHeap))
    (hexit : ∀ x code s sf, specX.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ x s sf, specX.onOom x s sf = ⌜False⌝)
    (h : subroutine_ok prog entry (specX.inImage img)) :
    subroutine_ok prog entry (specExt.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F := memRegion (s0.sp - BitVec.ofNat 64 nExt) (nExt - nX)
  have hpre' : s0.mem ⊨ (specX.inImage img).pre x s0 ∗ (F ∗ R) := by
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specExt.pre x s0) ∗ R at hpre
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specX.pre x s0) ∗ (F ∗ R)
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (hpre_imp x s0))) ?_
    exact Entails.of_eq (by dsimp only [F]; ac_rfl)
  refine h.mono_outcome x (F ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    change sf.mem ⊨ specX.post x s0 sf ∗ (F ∗ R) at hpost
    change sf.mem ⊨ specExt.post x s0 sf ∗ R
    refine Satisfies.mono ?_ hpost
    exact Entails.trans (Entails.of_eq (by dsimp only [F]; ac_rfl))
      (sepConj_mono_left (hpost_imp x s0 sf))
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    obtain ⟨φ, hpX, hpE⟩ := hpan_eq x s0 sf
    change sf.mem ⊨ specX.onPanic x s0 sf ∗ (F ∗ R) at hpost
    change sf.mem ⊨ specExt.onPanic x s0 sf ∗ R
    rw [hpX] at hpost; rw [hpE]
    refine Satisfies.mono ?_ hpost
    exact Entails.trans
      (Entails.of_eq (show (⌜φ⌝ ∗ anyHeap) ∗ (F ∗ R) = (⌜φ⌝ ∗ (anyHeap ∗ F)) ∗ R by ac_rfl))
      (sepConj_mono_left (sepConj_mono_right (entails_anyHeap (anyHeap ∗ F))))
  · change sf.mem ⊨ specX.onExit x code s0 sf ∗ (F ∗ R) at hpost
    rw [hexit] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · change sf.mem ⊨ specX.onOom x s0 sf ∗ (F ∗ R) at hpost
    rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim

theorem hkdfToVecOkExt_of_okX {img : Obj.Image} {A : RustAlloc} {hkdf : HkdfFn}
    {ext : String → Option (State → State)} (h : HkdfToVecOkX img A hkdf ext) :
    HkdfToVecOkExt img A hkdf ext := by
  refine sub_ok_inImage_grow_stack extHookStack hkdfToVecStackExt ?_ ?_
    (fun _ s0 sf => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [hkdfToVecSpecExt, hkdfToVecSpec]
    rw [stackAt_split_grow s.sp extHookStack hkdfToVecStackExt]
    have hpure :
        (s.readReg64 .x8 = x.outVec ∧
          s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
          s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
          s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
          s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
          x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
          (¬x.saltRO ∨ x.salt.length ≤ 64) ∧
          (¬x.ikmRO ∨ x.ikm.length < 64) ∧
          32 ≤ x.info.length ∧ x.info.length < 55 ∧
          (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)) →
        (s.readReg64 .x8 = x.outVec ∧
          s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
          s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
          s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
          s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
          x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
          32 ≤ x.info.length ∧ x.info.length < 55 ∧
          (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)) := by
      rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, _, h11, h12, h13⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    exact Entails.trans (sepConj_mono_left (Entails.pure_mono hpure)) (Entails.of_eq (by ac_rfl))
  · intro x s sf; dsimp only [hkdfToVecSpecExt, hkdfToVecSpec]
    rw [stackAt_split_grow s.sp extHookStack hkdfToVecStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem authUpdateOkExt_of_okX {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AuthUpdateOkX img F A ext) :
    AuthUpdateOkExt img F A ext := by
  refine sub_ok_inImage_grow_stack authUpdateStackX authUpdateStackExt ?_ ?_
    (fun _ s0 sf => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [authUpdateSpecExt, authUpdateSpec]
    rw [stackAt_split_grow s.sp authUpdateStackX authUpdateStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [authUpdateSpecExt, authUpdateSpec]
    rw [stackAt_split_grow s.sp authUpdateStackX authUpdateStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem chainFromVnOkExt_of_okX {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainFromVersionNegotiationOkX img hkdf A ext) :
    ChainFromVersionNegotiationOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack chainFromVersionNegotiationStackX
    chainFromVersionNegotiationStackExt ?_ ?_
    (fun _ s0 sf => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [chainFromVersionNegotiationSpecExt, chainFromVersionNegotiationSpecX]
    rw [stackAt_split_grow s.sp chainFromVersionNegotiationStackX chainFromVersionNegotiationStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [chainFromVersionNegotiationSpecExt, chainFromVersionNegotiationSpecX]
    rw [stackAt_split_grow s.sp chainFromVersionNegotiationStackX chainFromVersionNegotiationStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem chainAddEpochOkExt_of_okX {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainAddEpochOkX img hkdf A ext) :
    ChainAddEpochOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack chainAddEpochStackX chainAddEpochStackExt ?_ ?_
    (fun x s0 sf => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [chainAddEpochSpecExt, chainAddEpochSpecX]
    rw [stackAt_split_grow s.sp chainAddEpochStackX chainAddEpochStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [chainAddEpochSpecExt, chainAddEpochSpecX]
    cases h_ae : Chain.addEpoch hkdf x.self x.epochSecret
    · dsimp only
      apply Entails.pure_left; exact False.elim
    · dsimp only
      rw [stackAt_split_grow s.sp chainAddEpochStackX chainAddEpochStackExt]
      exact Entails.of_eq (by ac_rfl)

theorem chainSendKeyOkExt_of_okX {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : ChainSendKeyOkX img hkdf A ext) :
    ChainSendKeyOkExt img hkdf A ext := by
  refine sub_ok_inImage_grow_stack chainSendKeyStackX chainSendKeyStackExt ?_ ?_
    (fun x s0 sf => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [chainSendKeySpecExt, chainSendKeySpecX]
    rw [stackAt_split_grow s.sp chainSendKeyStackX chainSendKeyStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [chainSendKeySpecExt, chainSendKeySpecX]
    rw [stackAt_split_grow s.sp chainSendKeyStackX chainSendKeyStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem SpqrSendContracts.toExt {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem} {ext : String → Option (State → State)}
    (h : SpqrSendContracts H_inner img A ctl C K ext) :
    SpqrSendContractsExt H_inner img A ctl C K ext where
  base_aligned := h.base_aligned
  loads := h.loads
  h_inner_eq := h.h_inner_eq
  alloc := h.alloc
  decodeState_ok := h.decodeState_ok
  statesFromPb_ok := h.statesFromPb_ok
  statesIntoPb_ok := h.statesIntoPb_ok
  chainFromPb_ok := h.chainFromPb_ok
  chainFromVn_ok := chainFromVnOkExt_of_okX h.chainFromVn_ok
  chainAddEpoch_ok := chainAddEpochOkExt_of_okX h.chainAddEpoch_ok
  chainSendKey_ok := chainSendKeyOkExt_of_okX h.chainSendKey_ok
  chainIntoPb_ok := h.chainIntoPb_ok
  messageSerialize_ok := h.messageSerialize_ok
  encodeVarint_ok := h.encodeVarint_ok
  authMacHdr_ok := h.authMacHdr_ok
  authUpdate_ok := authUpdateOkExt_of_okX h.authUpdate_ok
  hkdfToVec_ok := hkdfToVecOkExt_of_okX h.hkdfToVec_ok
  encodeBytes_ok := h.encodeBytes_ok
  polyNextChunk_ok := h.polyNextChunk_ok
  headerSentSendEkChunk_ok := h.headerSentSendEkChunk_ok
  ct1ReceivedSendEkChunk_ok := h.ct1ReceivedSendEkChunk_ok
  ct1SampledSendCt1Chunk_ok := h.ct1SampledSendCt1Chunk_ok
  ekReceivedCt1SampledSendCt1Chunk_ok := h.ekReceivedCt1SampledSendCt1Chunk_ok
  ct2SampledSendCt2Chunk_ok := h.ct2SampledSendCt2Chunk_ok
  dropProtoChain_ok := h.dropProtoChain_ok
  dropChainEpochSlice_ok := h.dropChainEpochSlice_ok

end CryptoVerification.SpqrV1.Top.Send
