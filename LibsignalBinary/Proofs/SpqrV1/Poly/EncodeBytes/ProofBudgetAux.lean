/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.LoopBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Alloc
import ProofLib.SepLogic.WP.Apply

/-!
# `VmPreserved` Non-Allocation Segments for `<PolyEncoder as Encoder>::encode_bytes`

Provides `VmPreserved`-strengthened `[LibsignalPlacement]` prologue, length-dispatch, header-store,
and `memcpy` finish lemmas for Block `417`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalPlacement blkLib_eq_417 blkPC_417 blkPl_417 lsρ)
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchet
  (sessionMemcpySpec)
open CryptoVerification.LibsignalSpqrV1 (NUM_POLYS Point)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly
  (encoderStatePinnedAt
   pointListPinAt polyEncoderIdxOff polyEncoderPadOff
   polyEncoderPadSize polyEncoderPinnedAt polyEncoderPointsTag polyEncoderSize
   polyEncoderVecsOff resultPolyEncoderAt resultPolyEncoderPinnedAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (align_pre bv384_toNat bv_add_add_lit encodeBytesStack
   length_pointHeadersBytes memRegion_464_split_560 memRegion_out_ok_open
   pointBufList pointHeadersBytes pointListPinAt_eq_bytes_bufs
   resultPolyEncoderPinnedAt_entails_resultPolyEncoderAt savedCells seq_clean
   sp_sub_16_add_8 sp_sub_24_add_8 sp_sub_32_add_8 sp_sub_40_add_8 sp_sub_48_add_8
   sp_sub_560_add_464 sp_sub_56_add_8 sp_sub_64_add_8 sp_sub_72_add_8 sp_sub_80_add_8
   sp_sub_88_add_8 sp_sub_96_add_16 sp_sub_96_add_24 sp_sub_96_add_32 sp_sub_96_add_40
   sp_sub_96_add_48 sp_sub_96_add_56 sp_sub_96_add_64 sp_sub_96_add_72 sp_sub_96_add_8
   sp_sub_96_add_80 sp_sub_96_add_88 sp_sub_96_add_96 sp_sub_96_sub_464
   stackAt_96_split_464)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (blk417_safeVm encode_bytes_epilogue_placed
   isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_add_add_lit BitVec.toNat_zero bv384_toNat
  sp_sub_96_sub_464 sp_sub_560_add_464 sp_sub_96_add_8 sp_sub_96_add_16 sp_sub_96_add_24
  sp_sub_96_add_32 sp_sub_96_add_40 sp_sub_96_add_48 sp_sub_96_add_56 sp_sub_96_add_64
  sp_sub_96_add_72 sp_sub_96_add_80 sp_sub_96_add_88 sp_sub_96_add_96 sp_sub_88_add_8
  sp_sub_80_add_8 sp_sub_72_add_8 sp_sub_64_add_8 sp_sub_56_add_8 sp_sub_48_add_8
  sp_sub_40_add_8 sp_sub_32_add_8 sp_sub_24_add_8 sp_sub_16_add_8
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_stub% "memcpy")

private noncomputable abbrev keep417 [LibsignalPlacement] : BitVec 64 → Bool :=
  ProofLib.progKeep ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics vmTrapHooks))

private theorem seq_vm_clean {P : Program} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP P mid s Pre (fun sm Pm => (Pm ⊢ P_mid) ∧ VmPreserved s sm ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP P target sm P_mid post) :
    SepWP P target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hvm, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem with_vm_cur {P : Program} {target : BitVec 64} {s s' : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (hk : VmPreserved s s' → SepWP P target s' Pre post)
    (hvm : VmPreserved s s' := by simp [wp_norm, arm64_norm]) :
    SepWP P target s' Pre post :=
  hk hvm

private theorem sepWP_rebase_vm_trans {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {target_pc : BitVec 64} {s0 s : State}
    {Pre P_mid : SepProp} {Q : State → Prop}
    (hvm0 : VmPreserved s0 s)
    (h : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ P_mid) ∧ VmPreserved s0 sm ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm1, hent, hQ⟩ => ⟨hent, hvm0.trans hvm1, hQ⟩

section Placed
variable [LibsignalPlacement]

theorem encode_bytes_prologue_placed {ext : String → Option (State → State)}
    (s0 : State) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_417).base) (hrun : s0.status = .Running) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 40#64) s0
      (stackAt s0.sp encodeBytesStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame) ∧
        VmPreserved s0 sm ∧
        sm.sp = s0.sp - 560#64 ∧ sm.readReg64 .x0 = s0.readReg64 .x0 ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧ sm.readReg64 .x21 = s0.readReg64 .x1 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hsaved : savedCells (ProofLib.stripS keep417 s0) = savedCells s0 := by
    unfold savedCells
    simp only [stripS_sp, stripS_readReg64]
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_prologue_placed
      (ext := vmTrapHooks) (ProofLib.stripS keep417 s0) Frame hsp0_align hpc hrun)
    fun sm Pm hvm ⟨hPm, hsp, hx0, hx19, hx21, htr, hvr⟩ =>
      ⟨by simpa only [hsaved, stripS_sp] using hPm, hvm,
       hsp, by simpa using hx0, by simpa using hx19, by simpa using hx21, htr, hvr⟩

theorem encode_bytes_dispatch_odd_placed {ext : String → Option (State → State)}
    (s : State) (n : Nat) (hodd : n % 2 != 0) (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 n) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 72#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ VmPreserved s sm ∧
        sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dispatch_odd_placed
      (ext := vmTrapHooks) (ProofLib.stripS keep417 s) n hodd P hpc hrun (by simpa using hx21))
    fun sm Pm hvm ⟨hPm, hsp, hx19, htr, hvr⟩ =>
      ⟨hPm, hvm, hsp, by simpa using hx19, htr, hvr⟩

theorem encode_bytes_dispatch_too_long_placed {ext : String → Option (State → State)}
    (s : State) (n : Nat) (heven : n % 2 = 0) (hgt : 1048576 < n) (hlt : n < 2 ^ 64)
    (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 n) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 52#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ VmPreserved s sm ∧
        sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dispatch_too_long_placed
      (ext := vmTrapHooks) (ProofLib.stripS keep417 s) n heven hgt hlt P hpc hrun (by simpa using hx21))
    fun sm Pm hvm ⟨hPm, hsp, hx19, htr, hvr⟩ =>
      ⟨hPm, hvm, hsp, by simpa using hx19, htr, hvr⟩

theorem encode_bytes_dispatch_empty_placed {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 496#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ VmPreserved s sm ∧
        sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x21 = 0#64 ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dispatch_empty_placed
      (ext := vmTrapHooks) (ProofLib.stripS keep417 s) P hpc hrun (by simpa using hx21))
    fun sm Pm hvm ⟨hPm, hsp, hx19, hx21', htr, hvr⟩ =>
      ⟨hPm, hvm, hsp, by simpa using hx19, by simpa using hx21', htr, hvr⟩

theorem encode_bytes_dispatch_nonempty_placed {ext : String → Option (State → State)}
    (s : State) (n : Nat) (heven : n % 2 = 0) (hpos : 2 ≤ n) (hle : n ≤ 1048576)
    (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 n) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 96#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ VmPreserved s sm ∧
        sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x0 ∧ sm.readReg64 .x21 = BitVec.ofNat 64 n ∧
        sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_dispatch_nonempty_placed
      (ext := vmTrapHooks) (ProofLib.stripS keep417 s) n heven hpos hle P hpc hrun (by simpa using hx21))
    fun sm Pm hvm ⟨hPm, hsp, hx19, hx20, hx21', htr, hvr⟩ =>
      ⟨hPm, hvm, hsp, by simpa using hx19, by simpa using hx20, by simpa using hx21', htr, hvr⟩

theorem encode_bytes_store_headers_empty_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 496#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 0#64) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s (memRegion (fsp + 72#64) 384 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ pointListPinAt A (fsp + 72#64) (List.replicate 16 ⟨0#64, 2#64⟩)
          (List.replicate 16 { value := [] }) ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_store_headers_empty_placed
      (A := A) (ext := vmTrapHooks) s0 (ProofLib.stripS keep417 s) fsp hfsp_align Frame
      hpc hrun hsp (by simpa using hx21) htrace hvregs)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m, by simpa using hx19_m, htr_m, hvr_m⟩

theorem encode_bytes_store_headers_nonempty_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (heven : msgLen % 2 = 0) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) (hp3 : p3 ≠ 0)
    (hp4 : p4 ≠ 0) (hp5 : p5 ≠ 0) (hp6 : p6 ≠ 0) (hp7 : p7 ≠ 0)
    (hp8 : p8 ≠ 0) (hp9 : p9 ≠ 0) (hp10 : p10 ≠ 0) (hp11 : p11 ≠ 0)
    (hp12 : p12 ≠ 0) (hp13 : p13 ≠ 0) (hp14 : p14 ≠ 0) (hp15 : p15 ≠ 0)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 476#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (hx23 : s.readReg64 .x23 = p8) (hx24 : s.readReg64 .x24 = p9)
    (hx25 : s.readReg64 .x25 = p10) (hx26 : s.readReg64 .x26 = p11)
    (hx27 : s.readReg64 .x27 = p12) (hx28 : s.readReg64 .x28 = p13)
    (hx22 : s.readReg64 .x22 = p14) (hx0 : s.readReg64 .x0 = p15)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let cap := BitVec.ofNat 64 (msgLen / 2)
    let pins : List VecPin :=
      [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩, ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
       ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩, ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 724#64) s
      (memRegion (fsp + 72#64) 384 ∗ (fsp ↦₆₄ v0) ∗
        ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
        ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
        (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗ (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
        (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗ (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
        (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗ (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
        (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗ (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
        (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗ (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
        (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗ (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
        (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗ (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
        (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗ (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ pointListPinAt A (fsp + 72#64) pins (List.replicate 16 { value := [] }) ∗ cells fsp 9 ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = BitVec.ofNat 64 msgLen - 2#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  intro cap pins
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_store_headers_nonempty_placed
      (A := A) (ext := vmTrapHooks) s0 (ProofLib.stripS keep417 s) fsp hfsp_align
      msgLen heven hpos hle v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
      hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 Frame
      hpc hrun hsp (by simpa using hx21)
      (by simpa using hx23) (by simpa using hx24) (by simpa using hx25) (by simpa using hx26)
      (by simpa using hx27) (by simpa using hx28) (by simpa using hx22) (by simpa using hx0)
      htrace hvregs)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8_m, hx19_m, hx20_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m, by simpa using hx8_m, by simpa using hx19_m, by simpa using hx20_m, htr_m, hvr_m⟩

theorem encode_bytes_finish_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (fsp out : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64) (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 668#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗ memRegion out polyEncoderSize ∗
        cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  subst hfsp
  have hlen_eq : pins.length = pts.length := by rw [hpins_len, hpts_len]
  have hbs_len : (pointHeadersBytes pins pts).length = 384 := by
    rw [length_pointHeadersBytes pins pts hlen_eq, hpts_len]
  have hfsp_align : ((s0.sp - 560#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  rw [pointListPinAt_eq_bytes_bufs A ((s0.sp - 560#64) + 72#64) pins pts hlen_eq]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_ok_open out))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro d0; apply SepWP.exists_left; intro d392
  rw [← hbs_len]
  refine seq_vm_clean (mid := (blkPl_417).base + 692#64)
    (P_mid := savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
      (resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗ Frame))
    (Q := fun sm => sm.sp = s0.sp - 560#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · have hmemcpy : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (lsρ "memcpy") (withVmPreserved sessionMemcpySpec) :=
      spqr_hook_ok_of_mem hmemcpy_sat
    simp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec] at hmemcpy
    wp_steps
    refine with_vm_cur (s := s) fun hvm1 => ?_
    wp_apply
    refine sepWP_rebase_vm_trans (hvm1.trans ‹VmPreserved _ _›) ?_
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp [arm64_norm, wp_norm], ?_,
        by simp [arm64_norm, wp_norm, hsp, htrace, hvregs, *]⟩
      have hres :
          (out ↦₆₄ 0#64) ∗ (((out + 8#64) ↦ₛ pointHeadersBytes pins pts) ∗ pointBufList A pins pts) ∗
            ((out + 392#64) ↦₃₂ 0#32) ∗ memRegion (out + 396#64) 4 ⊢
          resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) := by
        rw [← pointListPinAt_eq_bytes_bufs A (out + 8#64) pins pts hlen_eq]
        refine Entails.trans ?_
          (resultPolyEncoderPinnedAt_entails_resultPolyEncoderAt A ⟨pins⟩ out
            (.ok { idx := 0#32, s := .points pts }))
        dsimp only [resultPolyEncoderPinnedAt, polyEncoderPinnedAt, encoderStatePinnedAt,
          polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff,
          polyEncoderPadSize, NUM_POLYS]
        have hpure : (out ↦₆₄ 0#64) ⊢ ⌜pts.length = 16 ∧ pins.length = 16 ∧
            (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗ (out ↦₆₄ 0#64) :=
          Entails.pure_right ⟨hpts_len, hpins_len, hpts_bound⟩ (Entails.refl _)
        exact Entails.trans (sepConj_mono_left hpure) (Entails.of_eq (by sep_ac_rfl))
      have hstk :
          stackAt s.sp 4096 ∗ cells (s0.sp - 560#64) 9 ∗
            ((s0.sp - 488#64) ↦ₛ pointHeadersBytes pins pts) ∗ memRegion (s0.sp - 104#64) 8 ⊢
          stackAt (s0.sp - 96#64) (allocHookStack + 464) := by
        have h1 : ((s0.sp - 488#64) ↦ₛ pointHeadersBytes pins pts) ⊢ memRegion (s0.sp - 488#64) 384 := by
          rw [← hbs_len]; exact pointsToBytes_entails_memRegion _ _
        rw [stackAt_96_split_464 s0.sp, memRegion_464_split_560 s0.sp, ← hsp]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1))
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_right (sepConj_mono hstk (sepConj_mono_left hres)))
  · intro s1 hpc1 hrun1 hvm01 ⟨hsp1, htrace1, hvregs1⟩
    refine SepWP.mono
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (encode_bytes_epilogue_placed (ext := ext) s0 s1
          (resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗ Frame)
          hsp0_align hpc1 hrun1 hsp1 htrace1 hvregs1))
      fun sf Pf _hpcf _hrunf ⟨hPf, hvm1f, hcs, hspf, htrf⟩ =>
        ⟨by simpa only [sepConj_assoc] using hPf, hvm01.trans hvm1f, hcs, hspf, htrf⟩

theorem encode_bytes_empty_body_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (fsp out : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (hpc : s.pc = (blkPl_417).base + 496#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = 0#64)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗ stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out
          (.ok { idx := 0#32, s := .points (List.replicate 16 { value := [] }) }) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]; exact ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  have hhdr := encode_bytes_store_headers_empty_placed (A := A) (ext := ext) s0 s fsp hfsp_align
    (cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗
      stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗ Frame)
    hpc hrun hsp hx21 htrace hvregs
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_vm_clean hhdr ?_)
  intro s1 hpc1 hrun1 hvm01 ⟨hsp1, hx19_1, htr1, hvr1⟩
  have hpins_len : (List.replicate 16 (⟨0#64, 2#64⟩ : VecPin)).length = 16 := by simp
  have hpts_len : (List.replicate 16 ({ value := [] } : Point)).length = 16 := by simp
  have hpts_bound : ∀ pt ∈ (List.replicate 16 ({ value := [] } : Point)),
      pt.value.length ≤ 0x0555555555555555 := by
    intro pt hpt; rw [List.mem_replicate] at hpt; rcases hpt with ⟨_, rfl⟩; simp
  have hfin := encode_bytes_finish_ok_placed (A := A) hmemcpy_sat s0 s1 fsp out hfsp
    (List.replicate 16 ⟨0#64, 2#64⟩) (List.replicate 16 { value := [] })
    hpins_len hpts_len hpts_bound Frame hsp0_align hpc1 hrun1 hsp1 (by rw [hx19_1, hx19]) htr1 hvr1
  refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hfin)
    fun sf Pf _hpcf _hrunf ⟨hPf, hvm1f, hcs, hspf, htrf⟩ =>
      ⟨hPf, hvm01.trans hvm1f, hcs, hspf, htrf⟩

end Placed

end LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudgetAux
