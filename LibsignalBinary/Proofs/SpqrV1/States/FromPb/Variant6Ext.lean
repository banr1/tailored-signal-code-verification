/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fExt

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant6`

Lifts `Variant6.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
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
  v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  v6hr_stackRest10000 v6hr_decHeap epilogueStackSlots epilogueStackGaps epilogueOutFull
  resultChunkedStatesAt statesFromPbSavedCells vecU8Payload

theorem v6hr_lowStack_err_3760_auth_none_to_10316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v6hr_lowStackAt s0.sp w24 v128 v136 (if (c0 == 0#64) = true then v144 else p0)
            d184 v192 d200 v208 v216 w120 w96 ∗
          A.pool ∗ Rest) ∧
        (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
        sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (Ext4K.v6hr_err_3760_auth_none_to_10316 hA s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104
        d112 d116 w120 v80 v144 v224
        (((s0.sp - 2272#64) ↦₆₄ v128) ∗ ((s0.sp - 2264#64) ↦₆₄ v136) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨hP, hx25, hpres, hx23⟩
  exact ⟨Entails.trans hP (Entails.of_eq (by ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A c0 p0 ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v6hr_lowStackAt s0.sp w24 v128 v136 (if (c0 == 0#64) = true then v144 else p0)
            d184 v192 d200 v208 v216 w120 w96 ∗
          A.pool ∗ Rest) ∧
        (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
        sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (Ext4K.v6hr_err_3760_hdr_ne64_auth_some_to_10316 hA s0 s1
        out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104
        d112 d116 w120 v80 v144 v224
        (((s0.sp - 2272#64) ↦₆₄ v128) ∗ ((s0.sp - 2264#64) ↦₆₄ v136) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hc1 hw24 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨hP, hx25, hpres, hx23⟩
  exact ⟨Entails.trans hP (Entails.of_eq (by ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_lowStack_err_1520_auth_none_to_10324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A c0 p0 ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          A.pool ∗ Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
        sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (Ext4K.v6hr_err_1520_auth_none_to_10324 hA s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104
        d112 d116 w120
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨hP, hpres, hx23⟩
  exact ⟨Entails.trans hP (Entails.of_eq (by ac_rfl)), hpres, hx23⟩

theorem v6hr_lowStack_err_1520_auth_some_to_10324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A c0 p0 ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗
        A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          A.pool ∗ Rest) ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
        sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (Ext4K.v6hr_err_1520_auth_some_to_10324 hA s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104
        d112 d116 w120
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hc1 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨hP, hpres, hx23⟩
  exact ⟨Entails.trans hP (Entails.of_eq (by ac_rfl)), hpres, hx23⟩

theorem states_from_pb_headerReceived_1464
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.HeaderReceived)
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (_hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.headerReceived s)) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerReceived s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  apply v6hr_sepWPp_to_sat
  apply v6hr_sepWPp_post_reassoc (P1 :=
    resultChunkedStatesAt A (F := F) out
      (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerReceived s) }) ∗
    (A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) ∗
    stackAt s0.sp statesFromPbStack) (by ac_rfl)
  rw [v6hr_optProtoInnerStateAt_headerReceived A pbA s]
  refine SepWPp.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        memRegion (s0.sp - 2400#64) 2304 ∗
        (optProtoPolynomialDecoderAt A (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
         optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) s.uc ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000006#64) ∗
         memRegion (pbA + 128#64) 96 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
      (sepConj_mono_left (v6hr_memRegion_2304_entails_lowStackAt s0.sp))) ?_
  simp only [sepExists_sepConj_left]
  refine v6hr_sepWPp_exists_left fun v80 => v6hr_sepWPp_exists_left fun v128 =>
    v6hr_sepWPp_exists_left fun v136 => v6hr_sepWPp_exists_left fun v144 =>
    v6hr_sepWPp_exists_left fun d184 => v6hr_sepWPp_exists_left fun v192 =>
    v6hr_sepWPp_exists_left fun d200 => v6hr_sepWPp_exists_left fun v208 =>
    v6hr_sepWPp_exists_left fun v216 => v6hr_sepWPp_exists_left fun v224 =>
    v6hr_sepWPp_exists_left fun v232 => ?_
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      optProtoPolynomialDecoderAt A (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
      (optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) s.uc ∗
       v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
       memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000006#64) ∗ memRegion (pbA + 128#64) 96 ∗
       statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
  rcases s with ⟨uc, receivingEk⟩
  dsimp only
  cases receivingEk with
  | none =>
    dsimp only [Option.map]
    refine SepWPp.weaken_pre (sepConj_mono_left (v6hr_dec_none_unpack A pbA)) ?_
    simp only [sepExists_sepConj_left]
    refine v6hr_sepWPp_exists_left fun w96 => v6hr_sepWPp_exists_left fun w104 =>
      v6hr_sepWPp_exists_left fun d112 => v6hr_sepWPp_exists_left fun d116 =>
      v6hr_sepWPp_exists_left fun w120 => ?_
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) uc ∗
        (((pbA + 88#64) ↦₆₄ noneCap) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
         ((pbA + 104#64) ↦₆₄ w104) ∗ ((pbA + 112#64) ↦₃₂ d112) ∗
         ((pbA + 116#64) ↦₃₂ d116) ∗ ((pbA + 120#64) ↦₆₄ w120) ∗
         v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x8000000000000006#64) ∗ memRegion (pbA + 128#64) 96 ∗
         statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    cases uc with
    | none =>
      rw [v6hr_from_pb_uc_none_dec_none F]
      apply SepWPp.of_sepWP_ret
      refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_none_unpack A pbA)) ?_
      simp only [sepExists_sepConj_left]
      refine ProofLib.SepWP.exists_left fun w16 => ProofLib.SepWP.exists_left fun w24 =>
        ProofLib.SepWP.exists_left fun w32 => ProofLib.SepWP.exists_left fun w40 =>
        ProofLib.SepWP.exists_left fun w48 => ProofLib.SepWP.exists_left fun w56 =>
        ProofLib.SepWP.exists_left fun w64 => ProofLib.SepWP.exists_left fun w72 =>
        ProofLib.SepWP.exists_left fun w80 => ?_
      refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
        (SepWP.seq
          (v6hr_lowStack_load_headers_1464_none_to_3760 s0 s1 out pbA
            noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 d112 d116 w120
            v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
            (memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             statesFromPbJumpTableAt b ∗ A.pool)
            hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
      intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
      refine SepWP.weaken_pre hP2
        (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_err_3760_uc_none_to_10316 s0 s2 out
              w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
              (memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
              hsp0_align hpc2 hrun2 hregs2) ?_))
      intro s3 P3 hpc3 hrun3 ⟨hP3, hpres3, _⟩
      refine SepWP.weaken_pre hP3
        (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (v6hr_exit_err_10316_none (A := A) (F := F) s0 s3 out w96 0#64
            v80 v128 v136 v144 d184 v192 d200 v208 v216 w120 w96
            (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
            hsp0_align hpc3 hrun3 rfl hpres3))
    | some ucVal =>
      rcases ucVal with ⟨epoch, authOpt, hdr⟩
      cases authOpt with
      | none =>
        rw [v6hr_from_pb_auth_none_dec_none F hdr epoch]
        apply SepWPp.of_sepWP_ret
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_none_unpack' A pbA hdr epoch)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
          ProofLib.SepWP.exists_left fun w40 => ProofLib.SepWP.exists_left fun w48 =>
          ProofLib.SepWP.exists_left fun w56 => ProofLib.SepWP.exists_left fun w64 =>
          ProofLib.SepWP.exists_left fun w72 => ?_
        refine v6hr_sepWP_pure_left fun ⟨_, hc0⟩ => ?_
        refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_load_headers_1464_none_to_3760 s0 s1 out pbA
              c0 p0 (BitVec.ofNat 64 hdr.length) noneCap w40 w48 w56 w64 w72 epoch w96 w104 d112 d116 w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
              (vecCapPtrDealloc A c0 p0 ∗ memRegion (s0.sp - 2160#64) 2064 ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
              hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
        intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
        refine SepWP.weaken_pre hP2
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (SepWP.seq
              (Ext4K.v6hr_lowStack_err_3760_auth_none_to_10316 hA s0 s2 out
                c0 p0 (BitVec.ofNat 64 hdr.length) w40 w48 w56 w64 w72 epoch noneCap w96 w104 d112 d116 w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                (memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                hsp0_align hc0 hpc2 hrun2 hregs2) ?_))
        intro s3 P3 hpc3 hrun3 ⟨hP3, hx25_3, hpres3, _⟩
        refine SepWP.weaken_pre hP3
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (v6hr_exit_err_10316_none (A := A) (F := F) s0 s3 out w96 (s3.readReg64 .x25)
              (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
              d184 v192 d200 v208 v216 w120 w96
              (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
              hsp0_align hpc3 hrun3 hx25_3 hpres3))
      | some authPb =>
        refine SepWPp.weaken_pre (sepConj_mono_left (v6hr_uc_auth_some_unpack' A pbA hdr authPb epoch)) ?_
        simp only [sepExists_sepConj_left]
        refine v6hr_sepWPp_exists_left fun c0 => v6hr_sepWPp_exists_left fun p0 =>
          v6hr_sepWPp_exists_left fun c1 => v6hr_sepWPp_exists_left fun p1 =>
          v6hr_sepWPp_exists_left fun c2 => v6hr_sepWPp_exists_left fun p2 => ?_
        refine v6hr_sepWPp_pure_left fun ⟨⟨hc0_le, hc0⟩, ⟨_, hc1⟩⟩ => ?_
        by_cases hlen : hdr.length = 64
        · rw [v6hr_from_pb_hdr_eq64_dec_none F hdr authPb epoch hlen]
          have hlen_bv : BitVec.ofNat 64 hdr.length = 64#64 := by rw [hlen]
          rw [hlen_bv]
          refine SepWPp.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
            (v6hr_sepWPp_seq_clean
              (v6hr_lowStack_load_headers_1464_none_to_3760 s0 s1 out pbA
                c0 p0 64#64 c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch w96 w104 d112 d116 w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecU8Payload A c0 p0 hdr ∗ vecU8Payload A c1 p1 authPb.rootKey ∗
                 vecU8Payload A c2 p2 authPb.macKey ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                 stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
                 memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 hpc2 hrun2 hregs2
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (v6hr_sepWPp_bind
              (Ext4K.v6hr_step_3760_to_9936 hA s0 s2
                out c0 p0 c1 p1 c2 p2 epoch noneCap w96 w104 w120 d112 d116
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                authPb.rootKey authPb.macKey
                (vecU8Payload A c0 p0 hdr ∗ memRegion pbA optProtoInnerStateSize ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                 memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                hsp0_align hc0 hc1 hpc2 hrun2 hregs2) ?_)
          intro s3 P3 hpc3 hrun3 ⟨p1_new, p2_new, d184', hP3, hsp3, _, _, hx19_3, _,
            hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
          refine SepWPp.weaken_pre hP3
            (SepWPp.of_sepWP_ret
              (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
                (Ext4K.v6hr_step_9936_dec_none_to_exit (F := F) hA s0 s3
                  out c0 p0 p1_new p2_new epoch p2 w120 w96 d184' d116
                  authPb.rootKey authPb.macKey hdr
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hpc3 hrun3 hsp3 hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3)))
        · rw [v6hr_from_pb_hdr_ne64_dec_none F hdr authPb epoch hlen]
          have hw24 := v6hr_ofNat_len_beq_64_false hlen hc0_le hc0
          apply SepWPp.of_sepWP_ret
          refine SepWP.weaken_pre
            (sepConj_mono_left
              (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr)
                (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c1 p1 authPb.rootKey)
                  (sepConj_mono_left (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c2 p2 authPb.macKey))))) ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_none_to_3760 s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch w96 w104 d112 d116 w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A c0 p0 ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (SepWP.seq
                (Ext4K.v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316 hA s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch noneCap w96 w104 d112 d116 w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hc0 hc1 hw24 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨hP3, hx25_3, hpres3, _⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (v6hr_exit_err_10316_none (A := A) (F := F) s0 s3 out w96 (s3.readReg64 .x25)
                (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                d184 v192 d200 v208 v216 w120 w96
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                hsp0_align hpc3 hrun3 hx25_3 hpres3))
  | some decPb =>
    dsimp only [Option.map]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v6hr_dec_some_unpack A pbA (pbToProtoPolyDecoder decPb))) ?_
    simp only [sepExists_sepConj_left]
    refine v6hr_sepWPp_exists_left fun ptsCap => v6hr_sepWPp_exists_left fun ptsPtr =>
      v6hr_sepWPp_exists_left fun w120 => ?_
    refine v6hr_sepWPp_pure_left fun ⟨hpts_le, hpts_cap_lt, hpts_ne, hw120⟩ => ?_
    have hw88 : ptsCap.toNat < 2 ^ 63 := by omega
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) uc ∗
        (((pbA + 88#64) ↦₆₄ ptsCap) ∗ ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length) ∗
         ((pbA + 112#64) ↦₃₂ (pbToProtoPolyDecoder decPb).ptsNeeded) ∗
         ((pbA + 116#64) ↦₃₂ (pbToProtoPolyDecoder decPb).polys) ∗
         ((pbA + 120#64) ↦₆₄ w120) ∗
         (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
              ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
         v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x8000000000000006#64) ∗ memRegion (pbA + 128#64) 96 ∗
         statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    by_cases heq_pts : decPb.ptsNeeded = 576#32
    · have heq_pts' : (pbToProtoPolyDecoder decPb).ptsNeeded = 576#32 := heq_pts
      rw [heq_pts']
      cases uc with
      | none =>
        rw [v6hr_from_pb_uc_none_dec_some F decPb heq_pts]
        apply SepWPp.of_sepWP_ret
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_none_unpack A pbA)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun w16 => ProofLib.SepWP.exists_left fun w24 =>
          ProofLib.SepWP.exists_left fun w32 => ProofLib.SepWP.exists_left fun w40 =>
          ProofLib.SepWP.exists_left fun w48 => ProofLib.SepWP.exists_left fun w56 =>
          ProofLib.SepWP.exists_left fun w64 => ProofLib.SepWP.exists_left fun w72 =>
          ProofLib.SepWP.exists_left fun w80 => ?_
        refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_load_headers_1464_some_eq_to_3760 s0 s1 out pbA
              noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
              (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
              (pbToProtoPolyDecoder decPb).polys w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
              ((if ptsCap = 0#64 then emp
                else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                  arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                    ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
               memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               statesFromPbJumpTableAt b ∗ A.pool)
              hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
        intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
        refine SepWP.weaken_pre hP2
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_err_3760_uc_none_to_10316 s0 s2 out
                w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
                (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                576#32 (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                (memRegion pbA optProtoInnerStateSize ∗
                 (if ptsCap = 0#64 then emp
                  else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hpc2 hrun2 hregs2) ?_))
        intro s3 P3 hpc3 hrun3 ⟨hP3, hpres3, hx23_3⟩
        refine SepWP.weaken_pre hP3
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (Ext4K.v6hr_exit_err_10316_some (A := A) (F := F) hA s0 s3 out ptsPtr ptsCap 0#64
              (pbToProtoPolyDecoder decPb).pts
              v80 v128 v136 v144 d184 v192 d200 v208 v216 w120 ptsPtr
              (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
              hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 rfl hpres3 hx23_3))
      | some ucVal =>
        rcases ucVal with ⟨epoch, authOpt, hdr⟩
        cases authOpt with
        | none =>
          rw [v6hr_from_pb_auth_none_dec_some F hdr epoch decPb heq_pts]
          apply SepWPp.of_sepWP_ret
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_none_unpack' A pbA hdr epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun w40 => ProofLib.SepWP.exists_left fun w48 =>
            ProofLib.SepWP.exists_left fun w56 => ProofLib.SepWP.exists_left fun w64 =>
            ProofLib.SepWP.exists_left fun w72 => ?_
          refine v6hr_sepWP_pure_left fun ⟨_, hc0⟩ => ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_some_eq_to_3760 s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) noneCap w40 w48 w56 w64 w72 epoch
                ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A c0 p0 ∗
                 (if ptsCap = 0#64 then emp
                  else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (SepWP.seq
                (Ext4K.v6hr_lowStack_err_3760_auth_none_to_10316 hA s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) w40 w48 w56 w64 w72 epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  576#32 (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗
                   (if ptsCap = 0#64 then emp
                    else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hc0 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨hP3, hx25_3, hpres3, hx23_3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (Ext4K.v6hr_exit_err_10316_some (A := A) (F := F) hA s0 s3 out ptsPtr ptsCap (s3.readReg64 .x25)
                (pbToProtoPolyDecoder decPb).pts
                (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                d184 v192 d200 v208 v216 w120 ptsPtr
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hx25_3 hpres3 hx23_3))
        | some authPb =>
          refine SepWPp.weaken_pre (sepConj_mono_left (v6hr_uc_auth_some_unpack' A pbA hdr authPb epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine v6hr_sepWPp_exists_left fun c0 => v6hr_sepWPp_exists_left fun p0 =>
            v6hr_sepWPp_exists_left fun c1 => v6hr_sepWPp_exists_left fun p1 =>
            v6hr_sepWPp_exists_left fun c2 => v6hr_sepWPp_exists_left fun p2 => ?_
          refine v6hr_sepWPp_pure_left fun ⟨⟨hc0_le, hc0⟩, ⟨_, hc1⟩⟩ => ?_
          by_cases hlen : hdr.length = 64
          · have hlen_bv : BitVec.ofNat 64 hdr.length = 64#64 := by rw [hlen]
            rw [hlen_bv]
            refine SepWPp.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
              (v6hr_sepWPp_seq_clean
                (v6hr_lowStack_load_headers_1464_some_eq_to_3760 s0 s1 out pbA
                  c0 p0 64#64 c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                  (vecU8Payload A c0 p0 hdr ∗ vecU8Payload A c1 p1 authPb.rootKey ∗
                   vecU8Payload A c2 p2 authPb.macKey ∗
                   (if ptsCap = 0#64 then emp
                    else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                   statesFromPbJumpTableAt b ∗ A.pool)
                  hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
            intro s2 hpc2 hrun2 hregs2
            refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
              (v6hr_sepWPp_bind
                (Ext4K.v6hr_step_3760_to_9936 hA s0 s2
                  out c0 p0 c1 p1 c2 p2 epoch ptsCap ptsPtr
                  (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length) w120
                  576#32 (pbToProtoPolyDecoder decPb).polys
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  authPb.rootKey authPb.macKey
                  (vecU8Payload A c0 p0 hdr ∗
                   (if ptsCap = 0#64 then emp
                    else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hc0 hc1 hpc2 hrun2 hregs2) ?_)
            intro s3 P3 hpc3 hrun3 ⟨p1_new, p2_new, d184', hP3, hsp3, hx11_3, hx12_3, hx19_3, hx23_3,
              hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
            rw [← heq_pts'] at hx11_3
            refine SepWPp.weaken_pre hP3
              (SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
                (Ext4K.v6hr_step_9936_dec_some_to_exit (F := F) hA hdec s0 s3
                  out c0 p0 p1_new p2_new epoch p2 ptsCap ptsPtr w120 d184'
                  authPb hdr decPb
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hlen heq_pts hpts_le hpts_cap_lt hpts_ne hw120
                  hpc3 hrun3 hsp3 hx11_3 hx12_3 hx19_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3))
          · rw [v6hr_from_pb_hdr_ne64_dec_some F hdr authPb epoch decPb heq_pts hlen]
            have hw24 := v6hr_ofNat_len_beq_64_false hlen hc0_le hc0
            apply SepWPp.of_sepWP_ret
            refine SepWP.weaken_pre
              (sepConj_mono_left
                (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr)
                  (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c1 p1 authPb.rootKey)
                    (sepConj_mono_left (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c2 p2 authPb.macKey))))) ?_
            refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
              (SepWP.seq
                (v6hr_lowStack_load_headers_1464_some_eq_to_3760 s0 s1 out pbA
                  c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                  (vecCapPtrDealloc A c0 p0 ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗
                   (if ptsCap = 0#64 then emp
                    else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                   statesFromPbJumpTableAt b ∗ A.pool)
                  hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
            intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
            refine SepWP.weaken_pre hP2
              (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
                (SepWP.seq
                  (Ext4K.v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316 hA s0 s2 out
                    c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                    c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                    ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                    576#32 (pbToProtoPolyDecoder decPb).polys w120
                    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                    (memRegion pbA optProtoInnerStateSize ∗
                     (if ptsCap = 0#64 then emp
                      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                        memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                          ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                     memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                     memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                    hsp0_align hc0 hc1 hw24 hpc2 hrun2 hregs2) ?_))
            intro s3 P3 hpc3 hrun3 ⟨hP3, hx25_3, hpres3, hx23_3⟩
            refine SepWP.weaken_pre hP3
              (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
                (Ext4K.v6hr_exit_err_10316_some (A := A) (F := F) hA s0 s3 out ptsPtr ptsCap (s3.readReg64 .x25)
                  (pbToProtoPolyDecoder decPb).pts
                  (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                  d184 v192 d200 v208 v216 w120 ptsPtr
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hx25_3 hpres3 hx23_3))
    · rw [v6hr_from_pb_ptsNeeded_ne F uc decPb heq_pts]
      have hd112 : ((pbToProtoPolyDecoder decPb).ptsNeeded == 576#32) = false :=
        beq_false_of_ne heq_pts
      apply SepWPp.of_sepWP_ret
      cases uc with
      | none =>
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_none_unpack A pbA)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun w16 => ProofLib.SepWP.exists_left fun w24 =>
          ProofLib.SepWP.exists_left fun w32 => ProofLib.SepWP.exists_left fun w40 =>
          ProofLib.SepWP.exists_left fun w48 => ProofLib.SepWP.exists_left fun w56 =>
          ProofLib.SepWP.exists_left fun w64 => ProofLib.SepWP.exists_left fun w72 =>
          ProofLib.SepWP.exists_left fun w80 => ?_
        refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_load_headers_1464_some_ne_to_1520 s0 s1 out pbA
              noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
              (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
              (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
              ((if ptsCap = 0#64 then emp
                else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                  arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                    ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
               memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               statesFromPbJumpTableAt b ∗ A.pool)
              hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
        intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
        refine SepWP.weaken_pre hP2
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_err_1520_uc_none_to_10324 s0 s2 out
                w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
                (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                (memRegion pbA optProtoInnerStateSize ∗
                 (if ptsCap = 0#64 then emp
                  else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hpc2 hrun2 hregs2) ?_))
        intro s3 P3 hpc3 hrun3 ⟨hP3, hpres3, hx23_3⟩
        refine SepWP.weaken_pre hP3
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (Ext4K.v6hr_exit_err_10324 (A := A) (F := F) hA s0 s3 out ptsPtr ptsCap
              (pbToProtoPolyDecoder decPb).pts
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 ptsPtr
              (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
              hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hpres3 hx23_3))
      | some ucVal =>
        rcases ucVal with ⟨epoch, authOpt, hdr⟩
        cases authOpt with
        | none =>
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_none_unpack' A pbA hdr epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun w40 => ProofLib.SepWP.exists_left fun w48 =>
            ProofLib.SepWP.exists_left fun w56 => ProofLib.SepWP.exists_left fun w64 =>
            ProofLib.SepWP.exists_left fun w72 => ?_
          refine v6hr_sepWP_pure_left fun ⟨_, hc0⟩ => ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_some_ne_to_1520 s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) noneCap w40 w48 w56 w64 w72 epoch
                ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A c0 p0 ∗
                 (if ptsCap = 0#64 then emp
                  else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (SepWP.seq
                (Ext4K.v6hr_lowStack_err_1520_auth_none_to_10324 hA s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) w40 w48 w56 w64 w72 epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗
                   (if ptsCap = 0#64 then emp
                    else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hc0 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨hP3, hpres3, hx23_3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (Ext4K.v6hr_exit_err_10324 (A := A) (F := F) hA s0 s3 out ptsPtr ptsCap
                (pbToProtoPolyDecoder decPb).pts
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 ptsPtr
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hpres3 hx23_3))
        | some authPb =>
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_some_unpack' A pbA hdr authPb epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun c1 => ProofLib.SepWP.exists_left fun p1 =>
            ProofLib.SepWP.exists_left fun c2 => ProofLib.SepWP.exists_left fun p2 => ?_
          refine v6hr_sepWP_pure_left fun ⟨⟨_, hc0⟩, ⟨_, hc1⟩⟩ => ?_
          refine SepWP.weaken_pre
            (sepConj_mono_left
              (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr)
                (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c1 p1 authPb.rootKey)
                  (sepConj_mono_left (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c2 p2 authPb.macKey))))) ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_some_ne_to_1520 s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A c0 p0 ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗
                 (if ptsCap = 0#64 then emp
                  else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTableAt b ∗ A.pool)
                hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (SepWP.seq
                (Ext4K.v6hr_lowStack_err_1520_auth_some_to_10324 hA s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗
                   (if ptsCap = 0#64 then emp
                    else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b)
                  hsp0_align hc0 hc1 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨hP3, hpres3, hx23_3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
              (Ext4K.v6hr_exit_err_10324 (A := A) (F := F) hA s0 s3 out ptsPtr ptsCap
                (pbToProtoPolyDecoder decPb).pts
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 ptsPtr
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
                hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hpres3 hx23_3))

end CryptoVerification.SpqrV1.States.FromPb.Ext4K
