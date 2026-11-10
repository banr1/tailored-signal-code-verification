/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.MessageKeyLoop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.ProloguePart1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.ProloguePart2

@[expose] public section

set_option autoImplicit false

/-!
# `prost::encoding::message::encode::<Chain, Vec<u8>>`

Verifies `encode::<Chain, Vec<u8>>` (`0x60`-byte frame): writes the length-delimited field key
`(tag << 3) | 2`, the `Chain::encoded_len` varint, and the `Chain` body (tags 1–4).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
  sepWPp_extract_vecU8Buf_le vecU8Buf_eq_open_one vecU8Buf_snoc_eq
open CryptoVerification.E2E.Record

/-- Rest of `chainAt A gc a` excluding `srk`, `priv`, and `ck`. -/
def chainAtRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys)

theorem chainAt_eq_fields (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a =
      vecGhostAt A gc.1.srk a ∗
      vecGhostAt A gc.1.priv (a + 24#64) ∗
      optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗
      chainAtRest A gc a := by
  unfold protoChainAt chainAtRest
  ac_rfl

theorem encChain_bound_seg1 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length +
      (bytesField 1 x.gc.1.srk.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

theorem encChain_bound_seg2 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes).length +
      (bytesField 2 x.gc.1.priv.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

theorem encChain_bound_seg3 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes).length +
      (msgField 3 (x.gc.2.chainKey.map encChainKey)).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

theorem encChain_bound_seg4 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)).length +
      ((x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

theorem encChain_final_bytes_eq (x : EncodeChainGhost) :
    (((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)) ++
      (x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) =
    x.bs ++ lenField x.tag (encChainMem x.gc) := by
  simp only [lenField, encChainMem, List.append_assoc]

/-- `encode::<Chain, Vec<u8>>` meets `encodeChainSpecX` given `encode_varint`,
`do_reserve_and_handle`, `Chain::encoded_len`, and `MessageKey::encoded_len`. -/
theorem encodeChain_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hchain : OkAtX img ext chainLenName (chainLenSpec A))
    (hmk : OkAtX img ext msgKeyLenName (msgKeyLenSpec A)) :
    OkAtX img ext encodeChainName (encodeChainSpecX A) := by
  apply subroutine_ok_of_sepWPpX
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeChainSpecX A).pre x s0, R, hpre, ?_⟩
  refine step_encChain_seg0 img A ext hEV hchain hpc hrun halign ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hlen
  refine step_encChain_seg1 img A ext hA hEV hDR
    x.v x.a cap1 ptr1 s0.sp x.gc.1.srk
    (x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length))
    (encChain_bound_seg1 x hlen)
    (x := x)
    (F := vecGhostAt A x.gc.1.priv (x.a + 24#64) ∗
      optChainKeyAt A x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1
    (by rw [chainAt_eq_fields]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
  refine step_encChain_seg2 img A ext hA hEV hDR
    x.v x.a cap2 ptr2 s0.sp x.gc.1.priv
    ((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes)
    (encChain_bound_seg2 x hlen)
    (x := x)
    (F := vecGhostAt A x.gc.1.srk x.a ∗
      optChainKeyAt A x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2
    (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3
  refine step_encChain_seg3 img A ext hA hEV hDR
    x.v x.a cap3 ptr3 s0.sp x.gc.1.ck x.gc.2.chainKey
    (((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes)
    (encChain_bound_seg3 x hlen)
    (x := x)
    (F := vecGhostAt A x.gc.1.srk x.a ∗
      vecGhostAt A x.gc.1.priv (x.a + 24#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3
    (by ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4
  refine step_encChain_seg4 img A ext hA hmk hEV hDR
    x.v x.a cap4 ptr4 s0.sp x.gc
    ((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey))
    (encChain_bound_seg4 x hlen)
    (x := x)
    (F := encChainSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4
    (by rw [chainAt_eq_fields]; ac_rfl) ?_
  intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5
  exact step_encChain_epilogue img A ext cap5 ptr5
    hpc5 hrun5 hsp5 halign htr5
    (by rw [encChain_final_bytes_eq x]; ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
