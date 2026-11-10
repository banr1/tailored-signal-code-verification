/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hse3` -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  fnOff_drop_poly16
  fnOff_drop_proto_poly_encoder
  fnOff_drop_poly_encoder_local2
  fnOff_drop_ek_sent
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

open CryptoVerification.SpqrV1.Alloc
attribute [local simp, local arm64_norm, local wp_norm] v2hse3_bv_add_add_lit
attribute [local simp, local arm64_norm, local wp_norm] v2hse3_x23_add_193_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hse3_x25_add_65_sext

namespace Ext4K

/-- At `+9328` (`0x5c514: b.eq 0x5cbb4`), when `s1.pstate = addsPState64 noneCap 1#64`
(`receivingCt1 = none`), takes `b.eq +11024`, drops `[Poly; 16]` at `fsp + 1400`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`. -/
theorem v2hse3_none_dec_9328_to_9228
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11024#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = fsp + 1392#64 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9328 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx26_2, htr2⟩
    exact v2hsd_cleanup_11024_to_9228 hA s0 s2 fsp out ca1 pa1 ca2 pa2 ca3 pa3 enc Frame
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 htr2

/-- At `+9388`, when `resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err)` holds,
loads `noneCap` from `[sp, #0x760]`, stores `noneCap` to `[sp, #0xd8]` (`fsp + 216#64`),
takes `b.eq +11240`, drops `enc` at `fsp + 1392` and `uc` at `fsp + 1264` via
`v2hsd_cleanup_11240_to_9228`, and reaches `+9228` with `x23 = 0#64`. -/
theorem v2hse3_err_dec_9388_to_9228
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (fsp out w216_old : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (err : PolynomialError) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A (fsp + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 216#64) ↦₆₄ noneCap) ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v2hse3_resultPolyDecoder_err_entails_tag_392 A fsp err))) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11240#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      unchunkedEkSentAt A (fsp + 1264#64) uc ∗
      A.pool ∗
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 216#64) ↦₆₄ noneCap) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9388 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hm400 := v2hse3_1888_tag_392_to_memRegion_400 fsp 18446744073709551615#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1888#64) ↦₆₄ 18446744073709551615#64) ∗
         memRegion (fsp + 1896#64) 392) ∗
        (stackAt fsp encoderFromPbStack ∗
         polyEncoderAt A (fsp + 1392#64) enc ∗
         unchunkedEkSentAt A (fsp + 1264#64) uc ∗
         A.pool ∗
         (((fsp + 216#64) ↦₆₄ 18446744073709551615#64) ∗ Frame)) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm400) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have h11240 := v2hsd_cleanup_11240_to_9228 hA s0 s2 fsp out enc uc
      (memRegion (fsp + 1888#64) 400 ∗ ((fsp + 216#64) ↦₆₄ noneCap) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 htr2
    exact SepWP.mono h11240 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
