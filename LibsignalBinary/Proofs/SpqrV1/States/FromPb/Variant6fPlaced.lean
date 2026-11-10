/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6dPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part F

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant6f.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6dPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
  v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  v6hr_stackRest10000 v6hr_decHeap epilogueStackSlots epilogueStackGaps epilogueOutFull
  resultChunkedStatesAt statesFromPbSavedCells vecU8Payload
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## 1. Exit, Epilogue, and Clone Glue for `HeaderReceived` -/

theorem v6hr_exit_err_10324_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out ptsPtr ptsCap : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10324#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap 2#64)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .msgDecode)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10396#64) s1
        ((if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
              ((ptsCap.toNat - pts.length) * 24)) ∗
          A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
           memRegion (s0.sp - 2160#64) 2064 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ Rest))
        (fun sm Pm =>
          (Pm ⊢ A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
             v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
             memRegion (s0.sp - 2160#64) 2064 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ Rest)) ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out ptsPtr ptsCap 2#64) :=
    v6hr_states_from_pb_dealloc_proto_decoder_10324_placed hA s0 s1 (s0.sp - 2400#64)
      out ptsPtr ptsCap 2#64 pts
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
       memRegion (s0.sp - 2160#64) 2064 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ Rest)
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq h1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, _, _, hx25_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl))
      (sepConj_mono_left hst)) ?_
  have hx25_b : (s2.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
    rw [hx25_2]; rfl
  exact v6hr_states_from_pb_err_10396_placed (A := A) (F := F) s0 s2 out
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 .msgDecode (A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx25_b htr2

theorem v6hr_exit_err_10316_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out ptsPtr x25_val : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64)
    (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr noneCap x25_val) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.seq
    (v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed s0 s1 (s0.sp - 2400#64)
      out ptsPtr x25_val _ hpc1 hrun1 hpres1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, _, _, hx25_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hx25_b : (s2.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx25_2, hx25_1]; rfl
  exact v6hr_states_from_pb_err_10396_placed (A := A) (F := F) s0 s2 out
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx25_b htr2

theorem v6hr_exit_err_10316_some_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64)
    (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap x25_val)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10396#64) s1
        ((if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
              ((ptsCap.toNat - pts.length) * 24)) ∗
          A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
           memRegion (s0.sp - 2160#64) 2064 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ Rest))
        (fun sm Pm =>
          (Pm ⊢ A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
             v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
             memRegion (s0.sp - 2160#64) 2064 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ Rest)) ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out ptsPtr ptsCap x25_val) :=
    v6hr_states_from_pb_dealloc_some_proto_decoder_10316_placed hA s0 s1 (s0.sp - 2400#64)
      out ptsPtr ptsCap x25_val pts
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
       memRegion (s0.sp - 2160#64) 2064 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ Rest)
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq h1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, _, _, hx25_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl))
      (sepConj_mono_left hst)) ?_
  have hx25_b : (s2.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx25_2, hx25_1]; rfl
  exact v6hr_states_from_pb_err_10396_placed (A := A) (F := F) s0 s2 out
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx25_b htr2

set_option maxHeartbeats 800000 in
theorem v6hr_step_10000_ok_to_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 p0 p1_new p2_new ep p2 w120 ptsPtr : BitVec 64)
    (d184 d200 : BitVec 32)
    (rootKey macKey hdrBytes : List (BitVec 8))
    (dec : PolyDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hhdr : hdrBytes.length = 64)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (polyDecoderAt A ((s0.sp - 2400#64) + 1888#64) dec ∗
        (v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 ptsPtr ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
         (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
          memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A c0 p0 hdrBytes ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.headerReceived
              { uc := { epoch := ep, auth := { rootKey := rootKey, macKey := macKey }, hdr := hdrBytes },
                receiving_ek := dec })) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (sepConj_mono (v6hr_polyDecoderAt_unpack A ((s0.sp - 2400#64) + 1888#64) dec)
      (sepConj_mono_left
        (v6hr_stack_10000_ok_entails s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
          (BitVec.ofNat 64 macKey.length) w120 ptsPtr))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u160
  apply ProofLib.SepWP.exists_left; intro d172
  apply ProofLib.SepWP.exists_left; intro uq608
  apply ProofLib.SepWP.exists_left; intro uq624
  apply ProofLib.SepWP.exists_left; intro uq640
  apply ProofLib.SepWP.exists_left; intro uq656
  apply ProofLib.SepWP.exists_left; intro uq672
  apply ProofLib.SepWP.exists_left; intro uq688
  apply ProofLib.SepWP.exists_left; intro uq704
  apply ProofLib.SepWP.exists_left; intro uq720
  apply ProofLib.SepWP.exists_left; intro uq736
  apply ProofLib.SepWP.exists_left; intro uq752
  apply ProofLib.SepWP.exists_left; intro uq768
  apply ProofLib.SepWP.exists_left; intro uq784
  apply ProofLib.SepWP.exists_left; intro uq800
  apply ProofLib.SepWP.exists_left; intro uq816
  apply ProofLib.SepWP.exists_left; intro u832
  apply ProofLib.SepWP.exists_left; intro uq848
  apply ProofLib.SepWP.exists_left; intro u864
  apply ProofLib.SepWP.exists_left; intro u880
  apply ProofLib.SepWP.exists_left; intro u888
  apply ProofLib.SepWP.exists_left; intro dw
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        v6hr_decHeap A dec dw ∗
        (v6hr_decWordsAt ((s0.sp - 2400#64) + 1888#64) dw ∗
         (((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         v6hr_stagingSlotsPre (s0.sp - 2400#64) u160 d172 p2 w120 ptsPtr
           uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
           u832 uq848 u864 u880 u888 ∗
         v6hr_stackRest10000 (s0.sp - 2400#64) ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A c0 p0 hdrBytes ∗ Rest) by ac_rfl))
      (Entails.trans (sepConj_mono_left (v6hr_decHeap_w0_lt A dec dw))
        (Entails.of_eq (by rw [sepConj_assoc])))) ?_
  apply ProofLib.SepWP.pure_elim; intro hw0_lt
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hstep1 := v6hr_step_10000_ok_to_8180_placed (ext := ext) s0 s1 (s0.sp - 2400#64)
    out c0 p0 64#64 (BitVec.ofNat 64 rootKey.length) p1_new
    (BitVec.ofNat 64 macKey.length) p2_new ep dw
    u160 d172 p2 w120 ptsPtr
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u888
    (v6hr_stackRest10000 (s0.sp - 2400#64) ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
     vecU8Payload A c0 p0 hdrBytes ∗
     v6hr_decHeap A dec dw ∗ Rest)
    hfsp_align hw0_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s2 P2 hpc2 hrun2
    ⟨hP2, hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2,
     hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo, hx27_mid, hx27_hi, hx4_2, hx5_2, hx21_2,
     hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx19_2, hx23_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  have h8180_st := v6hr_stack_8180_entails (s0.sp - 2400#64) 64#64 ep p2_new p0
    (BitVec.ofNat 64 macKey.length) p1_new dw
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         v6hr_stagingSlotsPost (s0.sp - 2400#64) dw p1_new ∗
         v6hr_decWordsAt ((s0.sp - 2400#64) + 1888#64) dw ∗
         v6hr_stackRest10000 (s0.sp - 2400#64)) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A c0 p0 hdrBytes ∗
         v6hr_decHeap A dec dw ∗ Rest) by ac_rfl))
      (sepConj_mono_left h8180_st)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d92
  apply ProofLib.SepWP.exists_left; intro w104_s
  apply ProofLib.SepWP.exists_left; intro w112_s
  apply ProofLib.SepWP.exists_left; intro w120_s
  apply ProofLib.SepWP.exists_left; intro w192
  apply ProofLib.SepWP.exists_left; intro bs240
  apply ProofLib.SepWP.exists_left; intro q576
  apply ProofLib.SepWP.exists_left; intro w592
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (states_from_pb_epilogue_8180_placed hA.memcpy s0 s2 out
        d92 ((EncoderFromPb.loByte dw.g0.w56).zeroExtend 32)
        w104_s w112_s w120_s dw.g4.u360 w192 p1_new dw.g4.u392 dw.g3.u344
        bs240.val bs240.property q576 w592
        dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
        dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
        dw.g3.u304 (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72) (dw.g1.w72 >>> 8)
        (unshiftWord dw.g0.w32 (EncoderFromPb.loByte dw.g0.w40)) (dw.g0.w40 >>> 8)
        (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32
        (vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A c0 p0 hdrBytes ∗
         v6hr_decHeap A dec dw ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2) ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨?_, hsp_f, hcs_f, htr_f⟩
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2,
      hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo, hx27_mid, hx27_hi, hx4_2, hx5_2, hx21_2,
      hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2] at hPf
  have hok_out := v6hr_epilogueOutFull_entails_ok A (F := F) out c0 p0 p1_new p2_new ep
    rootKey macKey hdrBytes dec dw
    (s2.readReg64 .x28) w192 (s2.readReg64 .x16) w104_s w112_s w120_s
    (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property
    (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32 hhdr
  refine Entails.trans hPf ?_
  refine Entails.trans
    (Entails.of_eq (show _ =
      (epilogueOutFull out 8#64
        (BitVec.ofNat 64 rootKey.length) p1_new (BitVec.ofNat 64 rootKey.length)
        (BitVec.ofNat 64 macKey.length) p2_new (BitVec.ofNat 64 macKey.length)
        c0 p0 64#64 ep dw.g0.w0
        (dw.g0.w8.extractLsb' 0 8) (dw.g0.w8.extractLsb' 8 32)
        (dw.g0.w8.extractLsb' 40 16) (dw.g0.w8.extractLsb' 56 8)
        dw.g0.w16 dw.g0.w24 (EncoderFromPb.loByte dw.g0.w32)
        (unshiftWord dw.g0.w32 (EncoderFromPb.loByte dw.g0.w40))
        (overlapWord7 (unshiftWord dw.g0.w32 (EncoderFromPb.loByte dw.g0.w40)) (dw.g0.w40 >>> 8))
        dw.g0.w48
        (((EncoderFromPb.loByte dw.g0.w56).zeroExtend 32).setWidth 8)
        (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72)
        (overlapWord7 ((v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72).extractLsb' 64 64) (dw.g1.w72 >>> 8))
        dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
        dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
        dw.g3.u304 dw.g3.u312 dw.g3.u320 dw.g3.u328 dw.g3.u336 dw.g3.u344
        dw.g4.u352 dw.g4.u360 dw.g4.u368 dw.g4.u376 dw.g4.u384 dw.g4.u392
        (s2.readReg64 .x28) w192 (s2.readReg64 .x16) w104_s w112_s w120_s
        (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240.val (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32 ∗
       vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
       vecU8Payload A c0 p0 hdrBytes ∗
       v6hr_decHeap A dec dw) ∗
      Rest ∗ stackAt s0.sp statesFromPbStack by ac_rfl))
    (sepConj_mono_left hok_out)

theorem v6hr_step_3760_to_9936_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 : BitVec 64)
    (d112 d116 : BitVec 32)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1
      (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
      epoch w88 w104 d112 d116 w120) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecU8Payload A c1 p1 rootKey ∗
        vecU8Payload A c2 p2 macKey ∗
        A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ (p1_new p2_new : BitVec 64) (d184' : BitVec 32),
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 epoch p2_new p0 d184' p1_new d116 p2
              (BitVec.ofNat 64 macKey.length) w120 w96 ∗
            vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧
          sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = w104 ∧
          sm.readReg64 .x24 = p1_new >>> 8 ∧
          sm.readReg64 .x25 = p1_new ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 rootKey.length ∧
          sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = w88 ∧
          TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hstep1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 3796#64) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          vecU8Payload A c1 p1 rootKey ∗
          vecU8Payload A c2 p2 macKey ∗
          A.pool ∗ Rest)
        (fun s2 P2 =>
          (P2 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 v128 v136 v144 d184 v192 d200 v208 v216 w120 w96 ∗
            vecU8Payload A c1 p1 rootKey ∗
            vecU8Payload A c2 p2 macKey ∗
            A.pool ∗ Rest) ∧
          v6hr_Regs1508 s0 s2 out c0 p0 64#64 c1 p1
            (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
            epoch w88 w104 d112 d116 w120 ∧
          s2.readReg64 .x27 = c0) := by
    unfold v6hr_lowStackAt
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (v6hr_step_3760_to_3796_placed s0 s1 out c0 p0 c1 p1 (BitVec.ofNat 64 rootKey.length)
          c2 p2 (BitVec.ofNat 64 macKey.length) epoch w88 w104 d112 d116 w120 v80 v224
          (((s0.sp - 2272#64) ↦₆₄ v128) ∗ ((s0.sp - 2264#64) ↦₆₄ v136) ∗
           ((s0.sp - 2256#64) ↦₆₄ v144) ∗ ((s0.sp - 2216#64) ↦₃₂ d184) ∗
           ((s0.sp - 2208#64) ↦₆₄ v192) ∗ ((s0.sp - 2200#64) ↦₃₂ d200) ∗
           ((s0.sp - 2192#64) ↦₆₄ v208) ∗ ((s0.sp - 2184#64) ↦₆₄ v216) ∗
           ((s0.sp - 2168#64) ↦₆₄ w96) ∗ v6hr_lowStackGaps s0.sp ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           vecU8Payload A c1 p1 rootKey ∗ vecU8Payload A c2 p2 macKey ∗ A.pool ∗ Rest)
          hsp0_align hc0 hc1 hpc1 hrun1 hregs1))
  refine v6hr_sepWPp_seq_clean hstep1 ?_
  intro s2 hpc2 hrun2 ⟨hregs2, _⟩
  rcases hregs2 with ⟨hsp2, hx8_2, hx9_2, _, hx11_2, hx12_2, hx13_2, hx14_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
  rw [v6hr_lowStackAt_eq_fsp]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (v6hr_sepWPp_bind
      (v6hr_clone_rootKey_3796_to_8812_placed hA s0 s2
        out c0 p0 c1 p1 c2 p2 (BitVec.ofNat 64 macKey.length) epoch w88 w104 w120
        v128 v144 v192 v208 d112 d116 d184 d200 rootKey
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ w96) ∗
         v6hr_lowStackGaps s0.sp ∗
         vecU8Payload A c2 p2 macKey ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx8_2 hx9_2 hx11_2 hx12_2 hx13_2 hx14_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2) ?_)
  intro s3 P3 hpc3 hrun3 ⟨p1_new, d184', hP3, hsp3, hx11_3, hx12_3, hx19_3, hx20_3,
    hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx28_3, htr3⟩
  refine SepWPp.weaken_pre hP3 ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (v6hr_sepWPp_bind
      (v6hr_clone_macKey_8812_to_9852_placed hA s0 s3
        out c0 c1 p1 (BitVec.ofNat 64 rootKey.length) c2 p2 w88 w104
        v136 v216 d112 d116 macKey
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ epoch) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184') ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ w96) ∗
         v6hr_lowStackGaps s0.sp ∗
         vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecCapPtrDealloc A c1 p1 ∗ Rest)
        hsp0_align hpc3 hrun3 hsp3 hx11_3 hx12_3 hx19_3 hx20_3 hx21_3 hx22_3
        hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 htr3) ?_)
  intro s4 P4 hpc4 hrun4 ⟨p2_new, hP4, hsp4, hx11_4, hx12_4, hx19_4, hx21_4, hx22_4,
    hx23_4, hx24_4, hx26_4, hx27_4, hx28_4, htr4⟩
  refine SepWPp.weaken_pre hP4 ?_
  apply SepWPp.of_sepWP_ret
  refine v6hr_sepWP_exists_post p1_new (v6hr_sepWP_exists_post p2_new (v6hr_sepWP_exists_post d184' ?_))
  rw [v6hr_lowStackAt_eq_fsp]
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
      (v6hr_dealloc_auth_9852_to_9936_placed hA s0 s4
        out c0 c1 p1 p1_new (BitVec.ofNat 64 rootKey.length) c2 p2 w88 w104 d112 d116
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ epoch) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184') ∗
         (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ w96) ∗
         v6hr_lowStackGaps s0.sp ∗
         vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗ Rest)
        hsp0_align hpc4 hrun4 hsp4 hx11_4 hx12_4 hx19_4 hx21_4 hx22_4 hx23_4
        hx24_4 hx26_4 hx27_4 hx28_4 htr4))

theorem v6hr_step_9936_dec_none_to_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State)
    (out c0 p0 p1_new p2_new ep p2 w120 w96 : BitVec 64)
    (d184 d200 : BitVec 32)
    (rootKey macKey hdrBytes : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
          (BitVec.ofNat 64 macKey.length) w120 w96 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A c0 p0 hdrBytes ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 w96 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A c0 p0 hdrBytes ∗
         A.pool ∗ Rest) by ac_rfl))
      (Entails.trans (sepConj_mono_left (v6hr_vecU8Payload_cap_lt A _ p1_new rootKey))
        (Entails.of_eq (by rw [sepConj_assoc])))) ?_
  apply ProofLib.SepWP.pure_elim; rintro ⟨_, hl1⟩
  refine SepWP.seq
    (v6hr_step_9936_dec_none_to_10416_placed s0 s1 out c0 p1_new (BitVec.ofNat 64 rootKey.length) _
      hl1 hpc1 hrun1 hsp1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  rw [v6hr_lowStackAt_eq_fsp]
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.seq
      (v6hr_dealloc_cloned_10416_to_10396_placed hA s0 s2
        out c0 p0 (BitVec.ofNat 64 rootKey.length) p1_new
        (BitVec.ofNat 64 macKey.length) p2_new
        rootKey macKey hdrBytes
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₃₂ d200) ∗
         (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ w96) ∗
         v6hr_lowStackGaps s0.sp ∗
         memRegion (s0.sp - 2160#64) 2064 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx26_2 hx27_2 htr2) ?_)
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx25_3, htr3⟩
  refine SepWP.weaken_pre hP3 ?_
  have hx25_b : (s3.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx25_3]; rfl
  have herr := v6hr_states_from_pb_err_10396_placed (A := A) (F := F) (ext := ext) s0 s3 out
    64#64 ep p2_new p0 d184 p1_new d200 p2 (BitVec.ofNat 64 macKey.length) w120 w96
    .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx25_b htr3
  rw [v6hr_lowStackAt_eq_fsp] at herr
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) herr

set_option maxHeartbeats 800000 in
theorem v6hr_step_9936_dec_some_to_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hdec : DecoderFromPbPlacedOkExt A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 : BitVec 64)
    (d184 : BitVec 32)
    (authPb : ProtoAuthenticator) (hdrBytes : List (BitVec 8))
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hhdr : hdrBytes.length = 64)
    (heq_pts : decPb.ptsNeeded = 576#32)
    (h1 : (pbToProtoPolyDecoder decPb).pts.length ≤ ptsCap.toNat)
    (h2 : ptsCap.toNat * 24 < 2 ^ 63)
    (h3 : ptsPtr ≠ 0#64)
    (hw120 : EncoderFromPb.loByte w120 = boolByte (pbToProtoPolyDecoder decPb).isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = (pbToProtoPolyDecoder decPb).ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = (pbToProtoPolyDecoder decPb).polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
          (pbToProtoPolyDecoder decPb).polys p2
          (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        vecU8Payload A c0 p0 hdrBytes ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
             ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.headerReceived
                  { uc := some { hdr := hdrBytes, auth := some authPb, epoch := ep },
                    receivingEk := some decPb }) }) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  refine SepWPp.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
           (pbToProtoPolyDecoder decPb).polys p2
           (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         vecU8Payload A c0 p0 hdrBytes ∗
         (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
              ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
         A.pool ∗ Rest) by ac_rfl))
      (Entails.trans
        (sepConj_mono (v6hr_vecU8Payload_cap_lt A _ p1_new authPb.rootKey)
          (sepConj_mono_left (v6hr_memRegion_2064_split_9936 s0.sp)))
        (Entails.of_eq (by rw [sepConj_assoc])))) ?_
  refine SepWPp.pure_left fun ⟨_, hl1⟩ => ?_
  rw [v6hr_lowStackAt_eq_fsp]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (v6hr_sepWPp_bind
      (v6hr_step_9936_dec_some_to_10000_placed hdec s0 s1 hcl1 out c0 p1_new
        (BitVec.ofNat 64 authPb.rootKey.length) ptsCap ptsPtr w120
        (pbToProtoPolyDecoder decPb)
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₃₂ (pbToProtoPolyDecoder decPb).polys) ∗
         (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
         v6hr_lowStackGaps s0.sp ∗
         (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
          memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         vecU8Payload A c0 p0 hdrBytes ∗ Rest)
        hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx23_1
        hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  refine SepWPp.weaken_pre hP2 ?_
  apply SepWPp.of_sepWP_ret
  cases hres : decoderFromPbResult (pbToProtoPolyDecoder decPb) with
  | error e =>
    rw [v6hr_from_pb_hdr_eq64_dec_err F hdrBytes authPb ep decPb e heq_pts hhdr hres]
    refine SepWP.seq
      (v6hr_step_10000_err_to_10492_placed s0 s2 out c0 p1_new
        (BitVec.ofNat 64 authPb.rootKey.length) e _
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx26_2 hx27_2 htr2) ?_
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx21_3, hx26_3, hx27_3, htr3⟩
    refine SepWP.weaken_pre hP3 ?_
    have hunsplit := v6hr_memRegion_2064_unsplit_9936 s0.sp
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          (memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
           memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
            memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
           (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
           vecU8Payload A c0 p0 hdrBytes ∗ A.pool ∗
           ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
            (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗
            (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₃₂ (pbToProtoPolyDecoder decPb).polys) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
            v6hr_lowStackGaps s0.sp ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl))
        (sepConj_mono_left hunsplit)) ?_
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq
        (v6hr_dealloc_cloned_10492_to_10396_placed hA s0 s3
          out c0 p0 (BitVec.ofNat 64 authPb.rootKey.length) p1_new
          (BitVec.ofNat 64 authPb.macKey.length) p2_new
          authPb.rootKey authPb.macKey hdrBytes
          (memRegion (s0.sp - 2160#64) 2064 ∗
           (((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
           (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗
           (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₃₂ (pbToProtoPolyDecoder decPb).polys) ∗
           (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
           v6hr_lowStackGaps s0.sp ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx26_3 hx27_3 htr3) ?_)
    intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx25_4, htr4⟩
    refine SepWP.weaken_pre hP4 ?_
    have hx25_b : (s4.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx25_4]; rfl
    have herr := v6hr_states_from_pb_err_10396_placed (A := A) (F := F) (ext := ext) s0 s4 out
      64#64 ep p2_new p0 d184 p1_new (pbToProtoPolyDecoder decPb).polys p2
      (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr .stateDecode (A.pool ∗ Rest)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx25_b htr4
    rw [v6hr_lowStackAt_eq_fsp] at herr
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) herr
  | ok dec =>
    rw [v6hr_from_pb_hdr_eq64_dec_ok F hdrBytes authPb ep decPb dec heq_pts hhdr hres]
    dsimp only [resultPolyDecoderFromPbAt]
    have hok := v6hr_step_10000_ok_to_exit_placed (F := F) hA s0 s2
      out c0 p0 p1_new p2_new ep p2 w120 ptsPtr
      d184 (pbToProtoPolyDecoder decPb).polys
      authPb.rootKey authPb.macKey hdrBytes dec (A.pool ∗ Rest)
      hsp0_align hhdr hpc2 hrun2 hsp2 hx19_2 hx21_2 hx26_2 hx27_2 htr2
    rw [v6hr_lowStackAt_eq_fsp] at hok
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hok

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlaced
  (v6hr_exit_err_10324_placed
   v6hr_exit_err_10316_none_placed
   v6hr_exit_err_10316_some_placed
   v6hr_step_10000_ok_to_exit_placed
   v6hr_step_3760_to_9936_placed
   v6hr_step_9936_dec_none_to_exit_placed
   v6hr_step_9936_dec_some_to_exit_placed)

end CryptoVerification.SpqrV1.States.FromPb
