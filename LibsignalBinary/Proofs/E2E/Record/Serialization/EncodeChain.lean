/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoop
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLen
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`)

Proves `encodeChain_ok` and its relocatable `[LibsignalPlacement]` counterparts (block `12`):
appends outer field key `(tag << 3) | 2`, varint payload length from `Chain::encoded_len`, and the
inline `Chain` fields (tags 1–4) to the destination `Vec<u8>`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

/-- Portion of `protoChainAt` outside `srk`, `priv`, and `ck`. -/
private def chainAtRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys)

private theorem chainAt_eq_fields (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a =
      vecGhostAt A gc.1.srk a ∗
      vecGhostAt A gc.1.priv (a + 24#64) ∗
      optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗
      chainAtRest A gc a := by
  unfold protoChainAt chainAtRest
  ac_rfl

private theorem encChain_bound_seg1 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length +
      (bytesField 1 x.gc.1.srk.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg2 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes).length +
      (bytesField 2 x.gc.1.priv.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg3 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes).length +
      (msgField 3 (x.gc.2.chainKey.map encChainKey)).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg4 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)).length +
      ((x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_final_bytes_eq (x : EncodeChainGhost) :
    (((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)) ++
      (x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) =
    x.bs ++ lenField x.tag (encChainMem x.gc) := by
  simp only [lenField, encChainMem, List.append_assoc]

/-- `prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`) satisfies `encodeChainSpec`
given `encode_varint`, `do_reserve_and_handle`, `Chain::encoded_len`, and `MessageKey::encoded_len`. -/
theorem encodeChain_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (hchain : OkAt b C ctl abs chainLenName (chainLenSpec A))
    (hmk : OkAt b C ctl abs msgKeyLenName (msgKeyLenSpec A)) :
    OkAt b C ctl abs encodeChainName (encodeChainSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeChainSpec A).pre x s0, R, hpre, ?_⟩
  refine step_encChain_seg0 b C A ctl abs hEV hchain hpc hrun halign ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hlen
  refine step_encChain_seg1 b C A ctl abs hEV hDR
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
  refine step_encChain_seg2 b C A ctl abs hEV hDR
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
  refine step_encChain_seg3 b C A ctl abs hEV hDR
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
  refine step_encChain_seg4 b C A ctl abs hmk hEV hDR
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
  exact step_encChain_epilogue b C A ctl abs cap5 ptr5
    hpc5 hrun5 hsp5 halign htr5
    (by rw [encChain_final_bytes_eq x]; ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `12`) -/

section Placed

open CryptoVerification.E2E.Record.Placed

/-- Relocatable `encode::<Chain, Vec<u8>>` (block `12`) contract from callee and `memcpy`
contracts. -/
theorem encodeChain_placed_ok_of_contracts [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(withLsCodeLoaded lsmpl (encodeChainSpec A)).pre x s0, R, hpre, ?_⟩
  refine step_encChain_seg0_placed A H hEV hchain hpc hrun halign ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hlen
  refine step_encChain_seg1_placed A H hEV hDR hmc
    x.v x.a cap1 ptr1 s0.sp x.gc.1.srk
    (x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length))
    (encChain_bound_seg1 x hlen)
    (x := x)
    (F := vecGhostAt A x.gc.1.priv (x.a + 24#64) ∗
      optChainKeyAt A x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hcl1 hsp1 halign htr1 hx19_1 hx20_1
    (by rw [chainAt_eq_fields]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2
  refine step_encChain_seg2_placed A H hEV hDR hmc
    x.v x.a cap2 ptr2 s0.sp x.gc.1.priv
    ((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes)
    (encChain_bound_seg2 x hlen)
    (x := x)
    (F := vecGhostAt A x.gc.1.srk x.a ∗
      optChainKeyAt A x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc2 hrun2 hcl2 hsp2 halign htr2 hx19_2 hx20_2
    (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hcl3 hsp3 htr3 hx19_3 hx20_3
  refine step_encChain_seg3_placed A H hEV hDR hmc
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
    hpc3 hrun3 hcl3 hsp3 halign htr3 hx19_3 hx20_3
    (by ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hcl4 hsp4 htr4 hx19_4 hx20_4
  refine step_encChain_seg4_placed A H hmk hEV hDR hmc
    x.v x.a cap4 ptr4 s0.sp x.gc
    ((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey))
    (encChain_bound_seg4 x hlen)
    (x := x)
    (F := encChainSavedRegs s0.sp s0)
    hpc4 hrun4 hcl4 hsp4 halign htr4 hx19_4 hx20_4
    (by rw [chainAt_eq_fields]; ac_rfl) ?_
  intro s5 cap5 ptr5 hpc5 hrun5 _hcl5 hsp5 htr5
  exact step_encChain_epilogue_placed A H cap5 ptr5
    hpc5 hrun5 hsp5 halign htr5
    (by rw [encChain_final_bytes_eq x]; ac_rfl)

/-- Relocatable `encode::<Chain, Vec<u8>>` (block `12`) contract from primitive hook hypotheses. -/
theorem encodeChain_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)) :=
  encodeChain_placed_ok_of_contracts A H
    (encode_varint_placed_ok hshim halloc hrealloc hpanic)
    (do_reserve_placed_ok hshim halloc hrealloc hpanic)
    (chainLen_placed_ok A H)
    (subroutine_ok_withLsCodeLoaded_of_plain (msgKeyLen_placed_ok A H))
    hmc

/-- Relocatable `encode::<Chain, Vec<u8>>` (block `12`) contract from `PlacedSerializeHooks`. -/
theorem encodeChain_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hH : PlacedSerializeHooks A H) :
    subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec A)) :=
  encodeChain_placed_ok hH.shim hH.alloc hH.realloc hH.memcpy hH.panic_handle_error

end Placed

end CryptoVerification.E2E.Record.Serialization

