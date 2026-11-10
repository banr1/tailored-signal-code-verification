/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Loop
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget

/-!
# `VmPreserved` Distribution Loop for `<PolyEncoder as Encoder>::encode_bytes`

Strengthens the relocatable `[LibsignalPlacement]` distribution-loop lemmas (`+724..+668`) on
Block `417` with `VmPreserved` so `A.pool lim st` transports across the allocator-free loop.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.LoopBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement blkLib_eq_417 blkPC_417 blkPl_417)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (Point)
open CryptoVerification.SpqrV1.Poly (pointListPinAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (bytesAt distributeMsgChunksTotal)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (blk417_safeVm isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)

private noncomputable abbrev keep417 [LibsignalPlacement] : BitVec 64 → Bool :=
  ProofLib.progKeep ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics vmTrapHooks))

theorem encode_bytes_dist_load_chunk_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp msgPtr : BitVec 64) (msgRO : Bool) (c0 c1 : BitVec 8)
    (i totalChunks : Nat) (hi : i < 2 ^ 64)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 792#64) s
      (bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (i % 16) ∧
        sm.readReg64 .x27 = (c1 ++ c0).zeroExtend 64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 i ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dist_load_chunk_placed
      (ext := vmTrapHooks) s0 (ProofLib.stripS keep417 s) fsp msgPtr msgRO c0 c1 i totalChunks hi
      Frame hpc hrun hsp
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx22)
      (by simpa using hx23) (by simpa using hx24) (by simpa using hx25)
      htrace hvregs)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx8_m, hx27_m, hx19_m, hx20_m, hx22_m, hx23_m, hx24_m, hx25_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m,
        by simpa using hx8_m, by simpa using hx27_m, by simpa using hx19_m,
        by simpa using hx20_m, by simpa using hx22_m, by simpa using hx23_m,
        by simpa using hx24_m, by simpa using hx25_m, htr_m, hvr_m⟩

theorem encode_bytes_dist_step_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool) (c0 c1 : BitVec 8)
    (i totalChunks : Nat)
    (hilt : i < totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 totalChunks)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ i)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (if i + 1 = totalChunks then
        (blkPl_417).base + 668#64
       else
        (blkPl_417).base + 784#64)
      s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i [c0, c1] pts) ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr + 2#64 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (i + 1) ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dist_step_placed
      (A := A) (ext := vmTrapHooks) s0 (ProofLib.stripS keep417 s) fsp msgPtr hfsp_align
      msgRO c0 c1 i totalChunks hilt hmax pins pts hpins_len hpts_len hpins_cap hpts_bound
      Frame hpc hrun hsp
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx22)
      (by simpa using hx23) (by simpa using hx24) (by simpa using hx25)
      htrace hvregs)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx24_m, hx25_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m,
        by simpa using hx19_m, by simpa using hx20_m, by simpa using hx22_m,
        by simpa using hx23_m, by simpa using hx24_m, by simpa using hx25_m,
        htr_m, hvr_m⟩

theorem encode_bytes_dist_loop_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (msg : List (BitVec 8))
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (i totalChunks : Nat)
    (hrem_even : msg.length % 2 = 0)
    (hrem_pos : 0 < msg.length)
    (hi_rem : i + msg.length / 2 = totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 totalChunks)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ i)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr msg ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i msg pts) ∗
            bytesAt msgRO msgPtr msg ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dist_loop_placed
      (A := A) (ext := vmTrapHooks) msg s0 (ProofLib.stripS keep417 s) fsp msgPtr hfsp_align msgRO
      i totalChunks hrem_even hrem_pos hi_rem hmax pins pts hpins_len hpts_len hpins_cap hpts_bound
      Frame hpc hrun hsp
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx22)
      (by simpa using hx23) (by simpa using hx24) (by simpa using hx25)
      htrace hvregs)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m, by simpa using hx19_m, htr_m, hvr_m⟩

theorem encode_bytes_dist_entry_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (msg : List (BitVec 8))
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (heven : msg.length % 2 = 0)
    (hpos : 0 < msg.length)
    (hmax : msg.length < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 (msg.length / 2))
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 724#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 msg.length - 2#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr msg ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal 0 msg pts) ∗
            bytesAt msgRO msgPtr msg ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dist_entry_placed
      (A := A) (ext := vmTrapHooks) msg s0 (ProofLib.stripS keep417 s) fsp msgPtr hfsp_align msgRO
      heven hpos hmax pins pts hpins_len hpts_len hpins_cap hpts_bound Frame
      hpc hrun hsp
      (by simpa using hx8) (by simpa using hx19) (by simpa using hx20)
      htrace hvregs)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m, by simpa using hx19_m, htr_m, hvr_m⟩

end LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.LoopBudget
