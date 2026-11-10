/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9d
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbExt
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant9d`

Lifts `Variant9d` (`AllocContracts` -> `AllocContracts4K`) inside
`CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.States.FromPb

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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

theorem v9_sub_ok_ct1_sent_from_pb
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 15272#64)
      (ct1SentFromPbSpec A F) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 15272) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_ct1_sent_from_pb (by decide))
    (CryptoVerification.SpqrV1.Unchunked.Ext4K.ct1_sent_from_pb_ok_ext (b := b) (A := A) (F := F) (ext := ext) hA)

section StepLemmas

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  v9_x25_add_209
  v9_x25_add_209_sext
  v9_pbA_add_145
  v9_x21_add_57
  v9_x21_add_57_sext
  v9_x24_add_9
  v9_x24_add_9_sext
  v9_x21_add_15
  v9_x21_add_15_sext
  v9_x21_add_39
  v9_x21_add_39_sext
  v9_fsp_add_247_sext
  v9_bv_add_add_lit

end StepLemmas

/-- From `+5368` (`dealloc_proto_decoder_5368`) through `+7084` (`err_7084`) to `s0.x30`
    when `receivingEk = some d` is still live in `v9_optProtoPolyDecoderHeap`. -/
theorem v9_tail_5368_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (d : ProtoPolynomialDecoder) (err : LibsignalSpqrV1.Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A (some d) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
      (Entails.of_eq (show _ =
        (if w0 = 0#64 then emp
         else A.live w8 (w0.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 d.pts ∗
           memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
  refine v9_seq_err_7084 s0 s fsp out pbA _ err hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_dealloc_proto_decoder_5368 hA s0 s fsp out w8 w0 x28_val d.pts
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hle hcap hpc hrun hpres hx22))
    (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

/-- From `+5360` (`dealloc_none/some_proto_decoder_5360`) through `+7084` (`err_7084`) to `s0.x30`
    for arbitrary `optDec : Option ProtoPolynomialDecoder`. -/
theorem v9_tail_5360_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (err : LibsignalSpqrV1.Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optDec with
  | none =>
    dsimp only [v9_optProtoPolyDecoderHeap]
    apply SepWP.pure_elim; rintro rfl
    refine v9_seq_err_7084 s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (SepWP.strengthen_entails_const ?_
        (v9_states_from_pb_dealloc_none_proto_decoder_5360 s0 s fsp out w8 x28_val
          (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hpc hrun hpres))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    subst hfsp_eq; exact Entails.of_eq (by ac_rfl)
  | some d =>
    dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
        (Entails.of_eq (show _ =
          (if w0 = 0#64 then emp
           else A.live w8 (w0.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 d.pts ∗
             memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    refine v9_seq_err_7084 s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (SepWP.strengthen_entails_const ?_
        (v9_states_from_pb_dealloc_some_proto_decoder_5360 hA s0 s fsp out w8 w0 x28_val d.pts
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hfsp_align hle hcap hpc hrun hpres hx22))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    subst hfsp_eq
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
      memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
    exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

/-- From `+6904` (`drop_uc_6904`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_6904_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6904#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr) (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap) (hx13 : s.readReg64 .x13 = ct1Cap)
    (hx14 : s.readReg64 .x14 = ct1Ptr) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ A.pool ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗
    vecCapPtrDealloc A hdrCap hdrPtr ∗ vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗
    A.pool ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_seq_err_7084 s0 s fsp out pbA _ .stateDecode hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_drop_uc_6904 hA s0 s fsp out rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
         memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 72 ∗ ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗
     memRegion (s0.sp - 2400#64 + 80#64) 48 ∗ ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗
     memRegion (s0.sp - 2400#64 + 136#64) 8 ∗ ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗ memRegion (s0.sp - 2400#64 + 160#64) 2144) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_6904_entails_2304 (s0.sp - 2400#64) esPtr esCap hdrPtr hdrCap))

/-- From `+8588` (`drop_uc_8588`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_8588_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8588#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
        memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
     ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗ A.pool ∗
     memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
    ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
    vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗ vecCapPtrDealloc A hdrCap hdrPtr ∗
    vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗ A.pool ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
     memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_seq_err_7084 s0 s fsp out pbA _ .stateDecode hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_drop_uc_8588 hA s0 s fsp out rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
         memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 48 ∗ ((s0.sp - 2400#64 + 48#64) ↦₆₄ ct1Cap) ∗
     ((s0.sp - 2400#64 + 56#64) ↦₆₄ rkCap) ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗ memRegion (s0.sp - 2400#64 + 80#64) 48 ∗
     ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗ ((s0.sp - 2400#64 + 136#64) ↦₆₄ mkPtr) ∗
     ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗
     memRegion (s0.sp - 2400#64 + 160#64) 40 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ct1Ptr) ∗
     memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ mkCap) ∗
     memRegion (s0.sp - 2400#64 + 224#64) 2080) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_8588_entails_2304 (s0.sp - 2400#64)
      ct1Cap rkCap esPtr esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap))

/-- From `+3044` (after `decoderFromPb` returns) to `s0.x30`. -/
theorem v9_tail_3044_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (d : PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64) (hx25 : s.readReg64 .x25 = esLen)
    (hx26 : s.readReg64 .x26 = rkLen) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (match decoderFromPbResult (pbToProtoPolyDecoder d) with
             | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := (dec : spqrPolyApi.PolyDecoder) })
             | .error _ => .error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases decoderFromPbResult (pbToProtoPolyDecoder d) with
  | error err =>
    refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8588#64)
      (v9_step_3044_err_to_8588 s0 s fsp out rkPtr err _
        hfsp_align hpc hrun hsp hx19 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx28_1, htr1⟩
    refine SepWP.weaken_pre ?_
      (v9_tail_8588_to_ret hA s0 s1 fsp out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
        hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1)
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen)) ∗
       (((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 8 ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 28) ∗
       (memRegion (fsp + 224#64) 16 ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16)) ∗
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
       ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
       ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
       memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
       v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (v9_memRegion_3044_collapse_err fsp mkLen hdrLen
      (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch
      ((EncoderFromPb.loByte ct1Len).zeroExtend 32))) (Entails.of_eq (by ac_rfl))
  | ok dec =>
    dsimp only [resultPolyDecoderFromPbAt]
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_left (v9_polyDecoderAt_relocate A (fsp + 1888#64) (out + 136#64) dec))
      (Entails.of_eq (show _ =
        (∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
          ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧ EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
            (((out + 136#64) ↦ₛ bs.val) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
             (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec)⌝ ∗
          ((fsp + 1888#64) ↦ₛ bs.val) ∗ (((fsp + 1888#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((fsp + 1888#64) + 392#64) ↦₆₄ w392) ∗ P_heap) ∗
        (memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
         memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641) ∗
        (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
         ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
         ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
         ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
         ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v9_memRegion_3044_split_ok fsp))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun w888 => ProofLib.SepWP.exists_left fun w880 =>
      ProofLib.SepWP.exists_left fun w864 => ProofLib.SepWP.exists_left fun q848 =>
      ProofLib.SepWP.exists_left fun w832 => ProofLib.SepWP.exists_left fun q816 =>
      ProofLib.SepWP.exists_left fun q800 => ProofLib.SepWP.exists_left fun q784 =>
      ProofLib.SepWP.exists_left fun q768 => ProofLib.SepWP.exists_left fun q752 =>
      ProofLib.SepWP.exists_left fun q736 => ProofLib.SepWP.exists_left fun q720 =>
      ProofLib.SepWP.exists_left fun q704 => ProofLib.SepWP.exists_left fun q688 =>
      ProofLib.SepWP.exists_left fun q672 => ProofLib.SepWP.exists_left fun q656 =>
      ProofLib.SepWP.exists_left fun q640 => ProofLib.SepWP.exists_left fun q624 =>
      ProofLib.SepWP.exists_left fun q608 => ProofLib.SepWP.exists_left fun w592 =>
      ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w232 =>
      ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w208 =>
      ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
      ProofLib.SepWP.exists_left fun w160 => ProofLib.SepWP.exists_left fun w120 =>
      ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
      ProofLib.SepWP.exists_left fun d92 => ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun w392 => ProofLib.SepWP.exists_left fun P_heap => ?_
    apply SepWP.pure_elim; rintro ⟨hw0_lt, _, hreloc⟩
    wp_conv_pre => rw [v9_bs384_eq_decCells bs.val bs.property (fsp + 1888#64)]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
      ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
      ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
      ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
      ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
      ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
      ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
      ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
      ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
      ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
      ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
      ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
      ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
      v9_decCellsAt (fsp + 1888#64) bs.val ∗
      ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 2280#64) ↦₆₄ w392) ∗
      (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗ memRegion (fsp + 100#64) 4 ∗
       memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 255#64) 313 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗
       memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗
       memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
       v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
    refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64)
      (v9_step_3044_ok_to_8180 s0 s fsp out
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
        w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 (BitVec.ofNat 64 dec.ptsNeeded) w392 d172
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 bs.val _
        hfsp_align hw0_lt hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1,
      hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
      hx28_1, hx30_1, htr1⟩
    have hpre8180 :
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗ ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 120#64) ↦₆₄ w392) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
        ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
        ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗
        ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
        ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
        ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
        ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
        ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
        ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
        ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
        ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
        ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
        ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
        ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
        ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
        v9_decCellsAt (fsp + 1888#64) bs.val ∗ ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 2280#64) ↦₆₄ w392) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗ memRegion (fsp + 100#64) 4 ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 255#64) 313 ∗
         memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗
         memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) ⊢
        (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
        (((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)) ∗
         ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16)) ∗
         ((fsp + 1920#64) ↦₆₄ v9_wordAt bs.val 32) ∗ memRegion (fsp + 1928#64) 376) ∗
        (memRegion fsp 92 ∗ memRegion (fsp + 96#64) 8 ∗ memRegion (fsp + 128#64) 32 ∗
         memRegion (fsp + 200#64) 8 ∗ memRegion (fsp + 216#64) 8 ∗ memRegion (fsp + 895#64) 993) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) := by
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 313) ∗
        (v9_decCellsAt (fsp + 1888#64) bs.val ∗ ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
         ((fsp + 2280#64) ↦₆₄ w392) ∗ memRegion (fsp + 2288#64) 16) ∗
        ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗ memRegion (fsp + 64#64) 8 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
          ((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 4) ∗
         (((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 4) ∗
         (((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap)) ∗
         ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         (memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952)) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      exact sepConj_mono (v9_loBytes7_64_313_entails_bs328 fsp
        (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch)
        (sepConj_mono (v9_fsp_1888_entails_epilogue fsp (BitVec.ofNat 64 dec.ptsNeeded) w392 bs.val bs.property)
          (sepConj_mono_left (v9_fsp_8180_gaps_collapse fsp mkLen ct1Cap rkCap esPtr hdrLen
            esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap ((EncoderFromPb.loByte ct1Len).zeroExtend 32))))
    refine SepWP.weaken_pre hpre8180 ?_
    subst hfsp_eq; rw [sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro bs240
    have hep := states_from_pb_epilogue_8180 hA s0 s1 out
      d92 ((EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32)
      (v9_wordAt bs.val 376) (BitVec.ofNat 64 dec.ptsNeeded) w392
      (v9_wordAt bs.val 312) (v9_wordAt bs.val 360) rkPtr
      (v9_wordAt bs.val 344) (v9_wordAt bs.val 296) bs240.val bs240.property q576 w592
      (v9_quadAt bs.val 32) (v9_quadAt bs.val 48) (v9_quadAt bs.val 64) (v9_quadAt bs.val 80)
      (v9_quadAt bs.val 96) (v9_quadAt bs.val 112) (v9_quadAt bs.val 128) (v9_quadAt bs.val 144)
      (v9_quadAt bs.val 160) (v9_quadAt bs.val 176) (v9_quadAt bs.val 192) (v9_quadAt bs.val 208)
      (v9_quadAt bs.val 224) (v9_quadAt bs.val 240) (v9_wordAt bs.val 256)
      (v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24))
      (v9_wordAt bs.val 24 >>> 8) (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))
      (uc.epoch >>> 8) (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
      (v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
         esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool)
      hsp0_align hpc1 hrun1 hsp1 hx6_1 hx19_1 hx23_1 htr1
    rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
        hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
        hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
    refine SepWP.weaken_pre (by unfold epilogueStackSlots epilogueStackGaps; exact Entails.of_eq (by ac_rfl))
      (SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ => ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩)
    have hb96 : (esLen.extractLsb' 0 32).setWidth 8 = esLen.extractLsb' 0 8 := by bv_kernel
    have hd97 : (esLen >>> 8).extractLsb' 0 32 = esLen.extractLsb' 8 32 := by bv_kernel
    have hh101 : (((esLen >>> 8) >>> 32).setWidth 32).setWidth 16 = esLen.extractLsb' 40 16 := by bv_kernel
    have hb103 : (((esLen >>> 8) >>> 48).setWidth 32).setWidth 8 = esLen.extractLsb' 56 8 := by bv_kernel
    have hb120 : ((EncoderFromPb.loByte ct1Len).zeroExtend 32).setWidth 8 = EncoderFromPb.loByte ct1Len :=
      v9_zext32_setWidth8 (EncoderFromPb.loByte ct1Len)
    rw [hb96, hd97, hh101, hb103, hb120]
    have hreloc' :
        ((out + 136#64) ↦ₛ bs.val) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec := by
      simpa only [v9_bv_add_add_lit, Nat.reduceAdd] using hreloc
    have hout := v9_epilogueOutFull_entails_ct1Acknowledged A (F := F) out
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc bs.val bs.property w392 dec P_heap hreloc'
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property
      (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hout)

end CryptoVerification.SpqrV1.States.FromPb.Ext4K
