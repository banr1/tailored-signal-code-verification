/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant5d`

Lifts `Variant5d.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

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
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.FromPb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode

theorem v5_err_6420_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out w8 w16 w24 w40 : BitVec 64) (d32 d36 : BitVec 32)
    (receivingHdr : Option PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6420#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : v5a_Saved6428Preserved s0 s1 (s0.sp - 2400#64) out w16 w8 0#64)
    (hx28_1 : s1.readReg64 .x28 = w24) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (v5a_optProtoPolyDecoderHeap A (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases receivingHdr with
  | none =>
    dsimp only [Option.map, v5a_optProtoPolyDecoderHeap]
    apply ProofLib.SepWP.pure_elim; intro hw8; subst hw8
    have h6500 := v5a_states_from_pb_dealloc_none_proto_decoder_6420
      s0 s1 (s0.sp - 2400#64) out w16 0#64
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))
      hpc1 hrun1 hpres1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (EncoderFromPb.seq_clean h6500 ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, _, _, hx27_2, htr2⟩
    have hx27_byte : (s2.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx27_2]; rfl
    exact v5a_states_from_pb_err_6500 s0 s2 out .stateDecode (A.pool ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx27_byte htr2
  | some decPb =>
    dsimp only [Option.map, v5a_optProtoPolyDecoderHeap, pbToProtoPolyDecoder]
    rw [sepConj_assoc]
    apply ProofLib.SepWP.pure_elim
    rintro ⟨hw24, _, _, hpts_le, hpts_cap_lt, _, _⟩
    rw [hw24] at hx28_1
    have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
    have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    refine SepWP.weaken_pre
      (Entails.trans (sepConj_mono_right (sepConj_mono_left hst_split))
        (Entails.of_eq (show _ =
          (if w8 = 0#64 then emp
           else A.live w16 (w8.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 w16 decPb.pts ∗
             memRegion (w16 + BitVec.ofNat 64 (decPb.pts.length * 24))
               ((w8.toNat - decPb.pts.length) * 24)) ∗
          A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by ac_rfl))) ?_
    have h6500 := Ext4K.v5a_states_from_pb_dealloc_some_proto_decoder_6420
      hA s0 s1 (s0.sp - 2400#64) out w16 w8 0#64 decPb.pts
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx28_1
    refine EncoderFromPb.seq_clean h6500 ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, _, _, hx27_2, htr2⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗
           memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
          (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl))
        (Entails.trans (sepConj_mono_left hst_join)
          (Entails.of_eq (show _ =
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
            (A.pool ∗ Rest) by ac_rfl)))) ?_
    have hx27_byte : (s2.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx27_2]; rfl
    exact v5a_states_from_pb_err_6500 s0 s2 out .stateDecode (A.pool ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx27_byte htr2

theorem v5_err_1396_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived)
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = w72) (hx22_1 : s1.readReg64 .x22 = w16)
    (hx23_1 : s1.readReg64 .x23 = w8) (hx24_1 : s1.readReg64 .x24 = w48)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .msgDecode)) ∗
          (A.pool ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  let P_after_uc : SepProp :=
    v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest
  have h6428 : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6428#64) s1
      (v5a_optProtoUcHeap A uc w48 w56 w64 w72 w80 w88 w96 ∗ P_after_uc)
      (fun sm Pm =>
        (Pm ⊢ P_after_uc) ∧
        v5a_Saved6428Preserved s0 sm (s0.sp - 2400#64) out w16 w8 2#64 ∧
        sm.readReg64 .x28 = w24) := by
    cases uc with
    | none =>
      dsimp only [v5a_optProtoUcHeap]
      apply ProofLib.SepWP.pure_elim; intro hw48; rw [hw48] at hx24_1
      exact v5b_step_1396_uc_none_to_6428 s0 s1 (s0.sp - 2400#64) out w16 w8 w24 P_after_uc
        hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
    | some ucVal =>
      rcases ucVal with ⟨ep, optAuth⟩
      cases optAuth with
      | none =>
        dsimp only [v5a_optProtoUcHeap]
        apply ProofLib.SepWP.pure_elim; rintro ⟨hw48, _⟩; rw [hw48] at hx24_1
        exact v5b_step_1396_auth_none_to_6428 s0 s1 (s0.sp - 2400#64) out w16 w8 w24 P_after_uc
          hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
      | some authPb =>
        dsimp only [v5a_optProtoUcHeap, P_after_uc]
        rw [sepConj_assoc]
        apply ProofLib.SepWP.pure_elim; intro _
        have hd1 := v5a_vecU8Heap_entails_dealloc A authPb.rootKey w48 w56 w64
        have hd2 := v5a_vecU8Heap_entails_dealloc A authPb.macKey w72 w80 w88
        have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
        have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ =
              v5a_vecU8Heap A authPb.rootKey w48 w56 w64 ∗
              v5a_vecU8Heap A authPb.macKey w72 w80 w88 ∗
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              (v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
               memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl))
            (sepConj_mono hd1 (sepConj_mono hd2 (sepConj_mono_left hst_split)))) ?_
        rw [sepConj_assoc]
        apply ProofLib.SepWP.pure_elim; rintro ⟨_, _, hw48_lt, _⟩
        refine SepWP.weaken_pre
          (Entails.of_eq (show _ =
            ⌜w88 = BitVec.ofNat 64 authPb.macKey.length ∧
              authPb.macKey.length ≤ w72.toNat ∧ w72.toNat < 2 ^ 63 ∧ w80 ≠ 0#64⌝ ∗
            (vecCapPtrDealloc A w48 w56 ∗ vecCapPtrDealloc A w72 w80 ∗ A.pool ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
              v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
              memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
              memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
        apply ProofLib.SepWP.pure_elim; intro _
        have hstep := Ext4K.v5b_step_1396_auth_some_to_6428 hA s0 s1
          (s0.sp - 2400#64) out w16 w8 w24 w48 w56 w72 w80
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
           memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ Rest)
          hfsp_align hw48_lt hpc1 hrun1 hsp1 hx10_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 htr1
        refine SepWP.mono hstep ?_
        intro sm Pm _ _ ⟨hPm, hpres, hx28_m⟩
        refine ⟨Entails.trans hPm ?_, hpres, hx28_m⟩
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt (s0.sp - 2400#64) allocHookStack ∗
             memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
            (v5a_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder decPb)) w8 w16 w24 d32 d36 w40 ∗
             memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl))
          (Entails.trans (sepConj_mono_left hst_join) (Entails.of_eq (by ac_rfl)))
  refine EncoderFromPb.seq_clean h6428 ?_
  intro s2 hpc2 hrun2 ⟨hpres2, hx28_2⟩
  dsimp only [P_after_uc, v5a_optProtoPolyDecoderHeap, pbToProtoPolyDecoder]
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim
  rintro ⟨hw24, _, _, hpts_le, hpts_cap_lt, _, _⟩
  rw [hw24] at hx28_2
  have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (Entails.trans (sepConj_mono_right (sepConj_mono_left hst_split))
      (Entails.of_eq (show _ =
        (if w8 = 0#64 then emp
         else A.live w16 (w8.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 w16 decPb.pts ∗
           memRegion (w16 + BitVec.ofNat 64 (decPb.pts.length * 24))
             ((w8.toNat - decPb.pts.length) * 24)) ∗
        A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by ac_rfl))) ?_
  have h6500 := Ext4K.v5a_states_from_pb_dealloc_proto_decoder_6428
    hA s0 s2 (s0.sp - 2400#64) out w16 w8 2#64 decPb.pts
    (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 2304 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
    hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hpres2 hx28_2
  refine EncoderFromPb.seq_clean h6500 ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, _, _, hx27_3, htr3⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗
         memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hst_join)
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest) by ac_rfl)))) ?_
  have hx27_byte : (s3.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
    rw [hx27_3]; rfl
  exact v5a_states_from_pb_err_6500 s0 s3 out .msgDecode (A.pool ∗ Rest)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_byte htr3

theorem v5_err_6520_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out p1_new p2_new l1 l2 ep w200 w224 : BitVec 64) (d232 : BitVec 32)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6520#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = l1)
    (hx27_1 : s1.readReg64 .x27 = p1_new) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        vecU8Payload A l1 p1_new rootKey ∗ vecU8Payload A l2 p2_new macKey ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hd1 := v10_vecU8Payload_entails_vecCapPtrDealloc A l1 p1_new rootKey
  have hd2 := v10_vecU8Payload_entails_vecCapPtrDealloc A l2 p2_new macKey
  have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  let R_stack : SepProp :=
    memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
    memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
    (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
    (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
    memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecU8Payload A l1 p1_new rootKey ∗ vecU8Payload A l2 p2_new macKey ∗
        ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
         A.pool ∗ memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by ac_rfl))
      (Entails.trans (sepConj_mono hst_split (sepConj_mono hd1 (sepConj_mono_left hd2)))
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
          vecCapPtrDealloc A l1 p1_new ∗ vecCapPtrDealloc A l2 p2_new ∗
          A.pool ∗ R_stack by dsimp only [R_stack]; ac_rfl)))) ?_
  have h6500 := Ext4K.v5c_dealloc_cloned_auth_6520_to_6500 hA s0 s1
    (s0.sp - 2400#64) out p1_new p2_new l1 l2 R_stack
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx27_1 htr1
  refine EncoderFromPb.seq_clean h6500 ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, htr2⟩
  have h224 := v5_memRegion_224_join_auth (s0.sp - 2400#64) p2_new ep w200 p1_new l2
  have h2304 := v5b_memRegion_2304_join_224_232 (s0.sp - 2400#64) w224 d232
  dsimp only [R_stack]
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗
         memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        ((memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
          memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗
          (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2)) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
        (statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl))
      (Entails.trans
        (sepConj_mono hst_join (sepConj_mono_left (Entails.trans (sepConj_mono_left h224) h2304)))
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest) by ac_rfl)))) ?_
  have hx27_byte : (s2.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx27_2]; rfl
  exact v5a_states_from_pb_err_6500 s0 s2 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx27_byte htr2

theorem v5_auth_some_3744_to_6064
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep : BitVec 64)
    (authPb : ProtoAuthenticator) (Rest R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6064#64) s1
      (v5a_optProtoUcHeap A (some { auth := some authPb, epoch := ep }) w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        ∃ p1_new p2_new : BitVec 64,
          authPb.rootKey.length < 2 ^ 63 ∧ authPb.macKey.length < 2 ^ 63 ∧
          (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
            memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
            memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
            vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
            vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
            A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x27 = p1_new ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  dsimp only [v5a_optProtoUcHeap]
  refine SepWPp.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        ⌜w96 = ep⌝ ∗ v5a_vecU8Heap A authPb.rootKey w48 w56 w64 ∗
        v5a_vecU8Heap A authPb.macKey w72 w80 w88 ∗ memRegion (s0.sp - 2400#64) 224 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Rest) by ac_rfl))
      (sepConj_mono_right
        (sepConj_mono (v5_vecU8Heap_dup_bounds A authPb.rootKey w48 w56 w64)
          (sepConj_mono (v5_vecU8Heap_dup_bounds A authPb.macKey w72 w80 w88)
            (sepConj_mono_left (v5_memRegion_224_split_auth (s0.sp - 2400#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun z216 => SepWPp.exists_elim fun z208 =>
    SepWPp.exists_elim fun z200 => SepWPp.exists_elim fun z152 =>
    SepWPp.exists_elim fun z136 => ?_
  refine SepWPp.pure_left fun hw96 => ?_
  refine SepWPp.pure_left fun ⟨hw64, hr_lt63, hw48_lt⟩ => ?_
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜w88 = BitVec.ofNat 64 authPb.macKey.length ∧
        authPb.macKey.length < 2 ^ 63 ∧ w72.toNat < 2 ^ 63⌝ ∗
      ((((s0.sp - 2400#64) + 152#64) ↦₆₄ z152) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ z200) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ z216) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ z208) ∗
        vecU8Payload A w48 w56 authPb.rootKey ∗ A.pool ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗
        vecU8Payload A w72 w80 authPb.macKey ∗ memRegion (s0.sp - 2400#64) 136 ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
        Rest)) by ac_rfl)) ?_
  refine SepWPp.pure_left fun ⟨hw88, hm_lt63, _⟩ => ?_
  have hl1_lt : (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr_lt63
  rw [hw96] at hx9_1; rw [hw64] at hx20_1; rw [hw88] at hx8_1
  have h4276 := v5b_step_3744_to_4276_auth_some s0 s1
    (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.macKey.length) ep w80
    (BitVec.ofNat 64 authPb.rootKey.length) w72 ptsPtr ptsCap w48 d32_64 w56 ptsLen
    z152 z200 z216
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ z208) ∗
     vecU8Payload A w48 w56 authPb.rootKey ∗ A.pool ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗
     vecU8Payload A w72 w80 authPb.macKey ∗ memRegion (s0.sp - 2400#64) 136 ∗
     memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest)
    hfsp_align hw48_lt hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
    hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1
  refine v5a_sepWPp_seq_clean h4276 ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ z208) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
      vecU8Payload A w48 w56 authPb.rootKey ∗ A.pool ∗
      ((((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ vecU8Payload A w72 w80 authPb.macKey ∗
       memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest) by ac_rfl)) ?_
  have h5964 := Ext4K.v5b_clone_rootKey_4276_to_5964 hA s0 s2
    out w56 w48 w72 (BitVec.ofNat 64 authPb.macKey.length) ptsPtr ptsCap ptsLen d32_64 z208
    authPb.rootKey
    ((((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ vecU8Payload A w72 w80 authPb.macKey ∗
     memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest) R
    hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2
  refine v5_sepWPp_seq h5964 ?_
  intro s3 P3 hpc3 hrun3 ⟨p1_new, hP3, hsp3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx28_3, htr3⟩
  refine SepWPp.weaken_pre
    (Entails.trans hP3
      (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ vecU8Payload A w72 w80 authPb.macKey ∗ A.pool ∗
        ((((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecCapPtrDealloc A w48 w56 ∗ memRegion (s0.sp - 2400#64) 136 ∗
         memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
         Rest) by ac_rfl))) ?_
  have h6020 := Ext4K.v5b_clone_macKey_5964_to_6020 hA s0 s3
    out w56 w80 w48 w72 (BitVec.ofNat 64 authPb.rootKey.length) ptsPtr ptsCap ptsLen d32_64 z136
    authPb.macKey
    ((((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecCapPtrDealloc A w48 w56 ∗ memRegion (s0.sp - 2400#64) 136 ∗
     memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
     Rest) R
    hsp0_align hpc3 hrun3 hsp3 hx8_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 htr3
  refine v5_sepWPp_seq h6020 ?_
  intro s4 P4 hpc4 hrun4 ⟨p2_new, hP4, hsp4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx28_4, htr4⟩
  apply SepWPp.of_sepWP_ret
  refine SepWP.weaken_pre
    (Entails.trans hP4
      (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ vecCapPtrDealloc A w48 w56 ∗
        vecCapPtrDealloc A w72 w80 ∗ A.pool ∗
        ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest) by ac_rfl))) ?_
  have h6064 := Ext4K.v5b_dealloc_old_auth_6020_to_6064 hA s0 s4
    out w56 w80 p1_new w48 w72 (BitVec.ofNat 64 authPb.rootKey.length) ptsPtr ptsCap ptsLen d32_64
    ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecU8Payload A (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
     memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx28_4 htr4
  refine SepWP.mono h6064 ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m, htr_m⟩
  refine ⟨p1_new, p2_new, hr_lt63, hm_lt63, hl1_lt, ?_, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m, htr_m⟩
  exact Entails.trans hPm (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb.Ext4K
