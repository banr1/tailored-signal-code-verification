/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 5 (`NoHeaderReceived`, `+1344`) — Part B

Relocatable Block-`333` header validation (`+1344`), early error paths, and `Authenticator`
cloning and input-buffer deallocation (`+3744 -> +6064`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm]
  v5b_cond_ls_none2Cap v5b_cond_ls_noneCap

/-! ## Entry Header Check (`+1344 -> +3744 | +1396`) & Early Error Paths (`v5b_*_placed`) -/

/-- Entry header check (`+1344 -> +3744`) when `receivingHdr = none` (`w8 = noneCap`). -/
theorem v5b_step_1344_to_3744_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (z224 : BitVec 64) (z232 : BitVec 32)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1344#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3744#64) s
      (v5a_pbAHeadersAt pbA noneCap w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗
        ((fsp + 232#64) ↦₃₂ z232) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗
          ((fsp + 232#64) ↦₃₂ d36) ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = w88 ∧
        sm.readReg64 .x9 = w96 ∧
        sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w64 ∧
        sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = noneCap ∧
        sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x25 = d32.zeroExtend 64 ∧
        sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = w24 ∧
        TraceCalleeSaved sm s0) := by
  have hm := v5a_pbAHeadersAt_entails_224 pbA noneCap w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96
  rw [v5a_pbAHeadersAt_eq] at hm ⊢
  simp only [sepConj_assoc]
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc hm ⊢
  change s.pc = (blkPl_333).base + 1344#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 3744#64) s _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000005#64) ∗
       ((pbA + 8#64) ↦₆₄ 18446744073709551615#64) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
       ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₃₂ d32) ∗ ((pbA + 36#64) ↦₃₂ d36) ∗
       ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
       ((pbA + 64#64) ↦₆₄ w64) ∗ ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
       ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
       memRegion (pbA + 104#64) 120) ∗
      (((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_left hm
  · wp_done

/-- Entry header check (`+1344 -> +3744`) when `receivingHdr = some d` (`w8.toNat < 2^63`) and `d32 = 48#32`. -/
theorem v5b_step_1344_to_3744_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (w8 w16 w24 : BitVec 64) (d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (z224 : BitVec 64) (z232 : BitVec 32)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw8_lt : w8.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1344#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3744#64) s
      (v5a_pbAHeadersAt pbA w8 w16 w24 48#32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗
        ((fsp + 232#64) ↦₃₂ z232) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗
          ((fsp + 232#64) ↦₃₂ d36) ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = w88 ∧
        sm.readReg64 .x9 = w96 ∧
        sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w64 ∧
        sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w8 ∧
        sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x25 = (48#32).zeroExtend 64 ∧
        sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = w24 ∧
        TraceCalleeSaved sm s0) := by
  have hw8_ne : (w8 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw8_lt)
  have hm := v5a_pbAHeadersAt_entails_224 pbA w8 w16 w24 48#32 d36 w40 w48 w56 w64 w72 w80 w88 w96
  rw [v5a_pbAHeadersAt_eq] at hm ⊢
  simp only [sepConj_assoc]
  change s.pc = (blkPl_333).base + 1344#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 3744#64) s _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000005#64) ∗
       ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
       ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₃₂ 48#32) ∗ ((pbA + 36#64) ↦₃₂ d36) ∗
       ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
       ((pbA + 64#64) ↦₆₄ w64) ∗ ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
       ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
       memRegion (pbA + 104#64) 120) ∗
      (((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_left hm
  · wp_done

/-- Entry header check (`+1344 -> +1396`) when `receivingHdr = some d` (`w8.toNat < 2^63`) and `d32 ≠ 48#32`. -/
theorem v5b_step_1344_to_1396_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (z224 : BitVec 64) (z232 : BitVec 32)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw8_lt : w8.toNat < 2 ^ 63)
    (hd32_ne : d32 ≠ 48#32)
    (hpc : s.pc = lsmpl.base 333 + 1344#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1396#64) s
      (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗
        ((fsp + 232#64) ↦₃₂ z232) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗
          ((fsp + 232#64) ↦₃₂ d36) ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w8 ∧
        sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x28 = w24 ∧
        TraceCalleeSaved sm s0) := by
  have hw8_ne : (w8 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw8_lt)
  have hd32_sub_ne : ((d32.zeroExtend 64).extractLsb' 0 32 - 48#32 == 0#32) = false := by
    apply beq_false_of_ne
    intro heq
    apply hd32_ne
    have h1 : (d32.zeroExtend 64).extractLsb' 0 32 = d32 := by bv_kernel
    rw [h1] at heq
    bv_omega
  have hm := v5a_pbAHeadersAt_entails_224 pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96
  rw [v5a_pbAHeadersAt_eq] at hm ⊢
  simp only [sepConj_assoc]
  change s.pc = (blkPl_333).base + 1344#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1396#64) s _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000005#64) ∗
       ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
       ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₃₂ d32) ∗ ((pbA + 36#64) ↦₃₂ d36) ∗
       ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
       ((pbA + 64#64) ↦₆₄ w64) ∗ ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
       ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
       memRegion (pbA + 104#64) 120) ∗
      (((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_left hm
  · wp_done

/-- Early `MsgDecode` error path `+1396 -> +4256 -> +6428` when `w48 = none2Cap` (`uc = none`). -/
theorem v5b_step_1396_uc_none_to_6428_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 1396#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = none2Cap)
    (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6428#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x28 = ptsLen) := by
  dsimp only [none2Cap, BitVec.ofNat_eq_ofNat] at hpc hx24 ⊢
  change s.pc = (blkPl_333).base + 1396#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6428#64) s P _
  wp_steps
  wp_done

/-- Early `MsgDecode` error path `+1396 -> +4256 -> +6428` when `w48 = noneCap` (`auth = none`). -/
theorem v5b_step_1396_auth_none_to_6428_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 1396#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = noneCap)
    (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6428#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x28 = ptsLen) := by
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc hx24 ⊢
  change s.pc = (blkPl_333).base + 1396#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6428#64) s P _
  wp_steps
  wp_done

/-- Early `MsgDecode` error path `+1396..+1460 -> +4256 -> +6428` when `auth = some authPb` (`c1 < 2^63`):
deallocates `c1, p1` (`x24, x26`) and `c2, p2` (`x21, x10`), sets `x27 = 2#64`, and reaches `+6428`. -/
theorem v5b_step_1396_auth_some_to_6428_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen c1 p1 c2 p2 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1396#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx10 : s.readReg64 .x10 = p2)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1)
    (hx26 : s.readReg64 .x26 = p1)
    (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6428#64) s
      (vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x28 = ptsLen) := by
  have hdealloc := v5a_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  have hult := v5b_c1_add_two_uge_two hc1_lt
  change s.pc = (blkPl_333).base + 1396#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6428#64) s _ _
  refine Drop.seq_clean (mid := (blkPl_333).base + 1436#64)
    (P_mid := vecCapPtrDealloc A c2 p2 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x10 = p2 ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
      sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hc1 : (c1 == 0#64) = true
    · simp only [hc1, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hc1_f : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      simp only [hc1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_steps
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx10_1, hx19_1, hx21_1, hx22_1, hx23_1, hx28_1, htrace1⟩
    dsimp only [vecCapPtrDealloc]
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hc2_f : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hc2_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_steps
      wp_done

/-- Error path `+3744..+3756 -> +6420` when `x24 = none2Cap` (`uc = none`). -/
theorem v5b_step_3744_uc_none_to_6420_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 3744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = none2Cap)
    (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6420#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧
        sm.readReg64 .x28 = ptsLen) := by
  dsimp only [none2Cap, BitVec.ofNat_eq_ofNat] at hpc hx24 ⊢
  change s.pc = (blkPl_333).base + 3744#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6420#64) s P _
  wp_steps
  wp_done

/-- Error path `+3744..+3756 -> +6420` when `x24 = noneCap` (`auth = none`). -/
theorem v5b_step_3744_auth_none_to_6420_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 3744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = noneCap)
    (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6420#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧
        sm.readReg64 .x28 = ptsLen) := by
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc hx24 ⊢
  change s.pc = (blkPl_333).base + 3744#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6420#64) s P _
  wp_steps
  wp_done

/-! ## `Authenticator` Cloning & Original Buffer Deallocation (`+3744 -> +4264..+6064`) -/

/-- Execution segment `+3744 -> +4276` when `c1.toNat < 2 ^ 63`: branches at `+3748` (`b.ls +4264`) and stores
`p2` at `[fsp + 200]`, `ep` at `[fsp + 152]`, and `l2` at `[fsp + 216]`. -/
theorem v5b_step_3744_to_4276_auth_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l2 ep p2 l1 c2 ptsPtr ptsCap c1 d32_64 p1 ptsLen : BitVec 64)
    (z152 z200 z216 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 3744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = l2)
    (hx9 : s.readReg64 .x9 = ep)
    (hx10 : s.readReg64 .x10 = p2)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = l1)
    (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1)
    (hx25 : s.readReg64 .x25 = d32_64)
    (hx26 : s.readReg64 .x26 = p1)
    (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4276#64) s
      (((fsp + 152#64) ↦₆₄ z152) ∗
        ((fsp + 200#64) ↦₆₄ z200) ∗
        ((fsp + 216#64) ↦₆₄ z216) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 152#64) ↦₆₄ ep) ∗
          ((fsp + 200#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = l2 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = l1 ∧
        sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x22 = ptsPtr ∧
        sm.readReg64 .x23 = ptsCap ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = d32_64 ∧
        sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x28 = ptsLen ∧
        TraceCalleeSaved sm s0) := by
  have hls := v5b_c1_cmn3_ls_true hc1_lt
  change s.pc = (blkPl_333).base + 3744#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4276#64) s _ _
  wp_steps
  wp_done

/-- Clones `authPb.rootKey` at `+4276 -> +5964`:
produces a newly allocated `vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey`
stored at `[fsp + 208] ↦₆₄ p1_new` and weakens the original buffer to
`vecCapPtrDealloc A c1 p1` (or panics on OOM via `+11596`). -/
theorem v5b_clone_rootKey_4276_to_5964_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out p1 c1 c2 l2 ptsPtr ptsCap ptsLen d32_64 v208 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4276#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = l2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 rootKey.length)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5964#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A c1 p1 rootKey ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A c1 p1 ∗
            A.pool ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x8 = l2 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 rootKey.length ∧
          sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = ptsPtr ∧
          sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x24 = c1 ∧
          sm.readReg64 .x25 = d32_64 ∧
          sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have h208 : (s0.sp - 2400#64) + 208#64 = s0.sp - 2192#64 := by bv_omega
  have h216 : (s0.sp - 2400#64) + 216#64 = s0.sp - 2184#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A c1 p1 rootKey ∗ A.pool ∗ Rest =
      ⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
       (if c1 = 0#64 then emp
        else A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
          memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
       A.pool ∗ Rest) := by
    unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hr_le, hr_cap, _⟩ => ?_
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with rfl | hr_pos
  ·
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20_1 ⊢
    apply SepWPp.of_sepWP_ret
    refine v5b_sepWP_exists_post 1#64 ?_
    change s1.pc = (blkPl_333).base + 4276#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5964#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h208]
      have hv0 := vecU8Payload_zero A
      have hite := v5b_ite_nil_entails_vecCapPtrDealloc A c1 p1
      refine Entails.trans
        (Entails.of_eq (show _ =
          emp ∗
          (if c1 = 0#64 then emp
           else A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ ([] : List (BitVec 8))) ∗
             memRegion (p1 + 0#64) (c1.toNat - 0)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ((s0.sp - 2192#64) ↦₆₄ 1#64) ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hv0 (sepConj_mono_left hite)) (Entails.of_eq (by ac_rfl))
    · wp_done
  ·
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc1_ne : c1 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hlay : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.shim : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustNoAllocShimSym) sessionShimSpec)
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.alloc : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustAllocSym) (rustAllocSpec A))
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.memcpy : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrMemcpySym) sessionMemcpySpec)
    simp only [sessionMemcpySpec] at hmc
    have hoom_step := v5a_states_from_pb_oom_11596_placed hA s0
    simp only [hc1_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hmc hoom_step hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4276#64 at hpc1
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5964#64) s1 _ _ _
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 4300#64)
    wp_steps
    wp_apply
    wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_call halloc (rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    ·
      simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v5a_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v5a_sepWPp_seq_clean
        (mid := (blkPl_333).base + 11596#64)
        (P_mid :=
          A.pool ∗ stackAt sf.sp allocHookStack ∗
            memRegion (s0.sp - 7552#64) 1056 ∗
            ((s0.sp - 2192#64) ↦₆₄ v208) ∗
            ((s0.sp - 2184#64) ↦₆₄ l2) ∗
            A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
            memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro s3 hpc3 hrun3 htr3
        exact hoom_step s3 _ _ R _ hpc3 hrun3 htr3
    ·
      simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v5a_pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v5b_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h208, h216]
        have hst := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp_sf1] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) rootKey hr_pos hr_lt63 hoom
        have hv_old := v5b_live_bytes_entails_vecCapPtrDealloc A c1 p1 rootKey hc1_ne hr_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf_1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) rootKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ rootKey)) ∗
            (A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
              memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
            (((s0.sp - 2192#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
             ((s0.sp - 2184#64) ↦₆₄ l2) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done

/-- Clones `authPb.macKey` at `+5964 -> +6020`:
produces a newly allocated `vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey`
stored at `[fsp + 136] ↦₆₄ p2_new` and weakens the original buffer to
`vecCapPtrDealloc A c2 p2` (or panics on OOM via `+11596`). -/
theorem v5b_clone_macKey_5964_to_6020_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out p1 p2 c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 v136 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5964#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = BitVec.ofNat 64 macKey.length)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = l1)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6020#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
        vecU8Payload A c2 p2 macKey ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
            vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A c2 p2 ∗
            A.pool ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = l1 ∧
          sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = ptsPtr ∧
          sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x24 = c1 ∧
          sm.readReg64 .x25 = d32_64 ∧
          sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have h136 : (s0.sp - 2400#64) + 136#64 = s0.sp - 2264#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have hpure :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
        vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest =
      ⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
       (if c2 = 0#64 then emp
        else A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
          memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
       A.pool ∗ Rest) := by
    unfold vecU8Payload; ac_rfl
  rw [hpure]
  refine SepWPp.pure_left fun ⟨hm_le, hm_cap, _⟩ => ?_
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with rfl | hm_pos
  ·
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx8_1 ⊢
    apply SepWPp.of_sepWP_ret
    refine v5b_sepWP_exists_post 1#64 ?_
    change s1.pc = (blkPl_333).base + 5964#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6020#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [h136, h200]
      have hv0 := vecU8Payload_zero A
      have hite := v5b_ite_nil_entails_vecCapPtrDealloc A c2 p2
      refine Entails.trans
        (Entails.of_eq (show _ =
          emp ∗
          (if c2 = 0#64 then emp
           else A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ ([] : List (BitVec 8))) ∗
             memRegion (p2 + 0#64) (c2.toNat - 0)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ((s0.sp - 2264#64) ↦₆₄ 1#64) ∗
           ((s0.sp - 2200#64) ↦₆₄ p2) ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hv0 (sepConj_mono_left hite)) (Entails.of_eq (by ac_rfl))
    · wp_done
  ·
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hc2_ne : c2 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hlay : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.shim : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustNoAllocShimSym) sessionShimSpec)
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.alloc : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrRustAllocSym) (rustAllocSpec A))
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec := by
      simpa only [lsProg_333, blkPl_333] using
        (spqr_hook_ok_of_mem hA.memcpy : subroutine_ok (lsProg_333 (Rust.withPanics ext))
          (lsρ spqrMemcpySym) sessionMemcpySpec)
    simp only [sessionMemcpySpec] at hmc
    have hoom_step := v5a_states_from_pb_oom_11596_placed hA s0
    simp only [hc2_ne, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
    simp only [sepConj_assoc]
    dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hmc hoom_step hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5964#64 at hpc1
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6020#64) s1 _ _ _
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 5988#64)
    wp_steps
    wp_apply
    wp_steps
    nth_rw 1 [← hsp1]; nth_rw 1 [← h_1]
    wp_call halloc (macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    ·
      simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte]
      rw [v5a_pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      have htr_sf1 : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace]; simp only [wp_norm, arm64_norm, *]
      refine v5a_sepWPp_seq_clean
        (mid := (blkPl_333).base + 11596#64)
        (P_mid :=
          A.pool ∗ stackAt sf.sp allocHookStack ∗
            memRegion (s0.sp - 7552#64) 1056 ∗
            ((s0.sp - 2264#64) ↦₆₄ v136) ∗
            ((s0.sp - 2200#64) ↦₆₄ p2) ∗
            A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
            memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length) ∗ Rest)
        (Q_regs := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro s3 hpc3 hrun3 htr3
        exact hoom_step s3 _ _ R _ hpc3 hrun3 htr3
    ·
      simp only [BitVec.ofNat_eq_ofNat, hoom, ↓reduceIte, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      rw [v5a_pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine v5b_sepWP_exists_post (sf_1.readReg64 (Reg.gpr 0#5)) ?_
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [h136, h200]
        have hst := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp_sf1] at hst
        have hv_new := vecU8Payload_pos A (sf_1.readReg64 (Reg.gpr 0#5)) macKey hm_pos hm_lt63 hoom
        have hv_old := v5b_live_bytes_entails_vecCapPtrDealloc A c2 p2 macKey hc2_ne hm_le
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt sf_1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (A.live (sf_1.readReg64 (Reg.gpr 0#5)) macKey.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ macKey)) ∗
            (A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
              memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
            (((s0.sp - 2264#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
             ((s0.sp - 2200#64) ↦₆₄ p2) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono hst (sepConj_mono hv_new (sepConj_mono_left hv_old))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done

/-- Deallocates the original `rootKey` (`c1, p1`) and `macKey` (`c2, p2`) buffers at
`+6020 -> +6064`, loading `x27 = [fsp + 208]` (`p1_new`). -/
theorem v5b_dealloc_old_auth_6020_to_6064_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out p1 p2 p1_new c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6020#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = l1)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6064#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
          (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = l1 ∧
        sm.readReg64 .x22 = ptsPtr ∧
        sm.readReg64 .x23 = ptsCap ∧
        sm.readReg64 .x25 = d32_64 ∧
        sm.readReg64 .x27 = p1_new ∧
        sm.readReg64 .x28 = ptsLen ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v5a_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  rw [v5b_stackAt_encoderFromPb_split_7552 s0.sp]
  change s1.pc = (blkPl_333).base + 6020#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6064#64) s1 _ _
  refine EncoderFromPb.seq_clean
    (mid := (blkPl_333).base + 6044#64)
    (P_mid :=
      memRegion (s0.sp - 7552#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
      (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
      vecCapPtrDealloc A c2 p2 ∗
      A.pool ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x20 = l1 ∧
      s2.readReg64 .x21 = c2 ∧
      s2.readReg64 .x22 = ptsPtr ∧
      s2.readReg64 .x23 = ptsCap ∧
      s2.readReg64 .x25 = d32_64 ∧
      s2.readReg64 .x27 = p1_new ∧
      s2.readReg64 .x28 = ptsLen ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    by_cases hc1 : (c1 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp1]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
    dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
    by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre (by simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done
    · wp_steps; wp_apply
      refine EncoderFromPb.align_pre (by rw [hsp2]; simp only [arm64_norm]; exact Entails.of_eq (by ac_rfl)) ?_
      wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlaced
  (v5b_step_1344_to_3744_none_placed
   v5b_step_1344_to_3744_some_placed
   v5b_step_1344_to_1396_err_placed
   v5b_step_1396_uc_none_to_6428_placed
   v5b_step_1396_auth_none_to_6428_placed
   v5b_step_1396_auth_some_to_6428_placed
   v5b_step_3744_uc_none_to_6420_placed
   v5b_step_3744_auth_none_to_6420_placed
   v5b_step_3744_to_4276_auth_some_placed
   v5b_clone_rootKey_4276_to_5964_placed
   v5b_clone_macKey_5964_to_6020_placed
   v5b_dealloc_old_auth_6020_to_6064_placed)

end CryptoVerification.SpqrV1.States.FromPb
