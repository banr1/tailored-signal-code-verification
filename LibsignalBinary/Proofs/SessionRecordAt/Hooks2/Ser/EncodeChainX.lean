/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXA
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXB

@[expose] public section

set_option autoImplicit false

/-!
# `prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`)

Assembles Segments 0–4 and the epilogue to prove the full subroutine contract of
`prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`, Block `12`) at `encodeChainStackX`
on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2

/-- Rest of `chainAt A gc a` excluding `srk`, `priv`, and `ck`. -/
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

theorem L1_EncodeChainX : True := trivial

theorem encodeChain_ok_ext (A : RustAlloc) (ext : String → Option (State → State)) {img : Obj.Image}
    (hC : SerContractsX img A ext) (hEV : EncodeVarintOkX img A ext) (hDR : DoReserveOkX img A ext)
    (hchain : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainLenName) (chainLenSpec A))
    (hmk : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr msgKeyLenName) (msgKeyLenSpec A)) :
    EncodeChainOkX img A ext := by
  apply subroutine_ok_inImage_of_sepWPpIn
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeChainSpecX A).pre x s0, R, hpre, ?_⟩
  refine step_encChain_seg0_x A ext hEV hchain hpc hrun halign ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hlen
  refine step_encChain_seg1_x A ext hC hEV hDR
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
  refine step_encChain_seg2_x A ext hC hEV hDR
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
  refine step_encChain_seg3_x A ext hC hEV hDR
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
  refine step_encChain_seg4_x A ext hC hmk hEV hDR
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
  exact step_encChain_epilogue_x A ext cap5 ptr5
    hpc5 hrun5 hsp5 halign htr5
    (by rw [encChain_final_bytes_eq x]; ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `12`) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Block `12` (`encode::<Chain, Vec<u8>>`) at `encodeChainStackX` under `[LibsignalPlacement]`. -/
theorem encodeChain_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A))) :
    EncodeChainPlacedOkX A H := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeChainSpecX A).pre x s0, R, hpre, ?_⟩
  refine step_encChain_seg0_placed_x A H hEV hchain hpc hrun halign ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hlen
  refine step_encChain_seg1_placed_x A H hC hEV hDR
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
  refine step_encChain_seg2_placed_x A H hC hEV hDR
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
  refine step_encChain_seg3_placed_x A H hC hEV hDR
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
  refine step_encChain_seg4_placed_x A H hC hmk hEV hDR
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
  exact step_encChain_epilogue_placed_x A H cap5 ptr5
    hpc5 hrun5 hsp5 halign htr5
    (by rw [encChain_final_bytes_eq x]; ac_rfl)

theorem encodeChain_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A))) :
    subroutine_ok callerProg (lsmpl.base 12) (withLsCl lsmpl (encodeChainSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeChain_placed_ok_ext A H hC hEV hDR hchain hmk)

end Placed

end CryptoVerification.E2E.Record.Serialization
