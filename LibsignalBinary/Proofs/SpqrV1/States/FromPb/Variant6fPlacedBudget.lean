/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part F

Proves the Variant 6 `Authenticator` key-clone phase (`+3760 -> +9936`) and decoder-branch exit
tails (`+9936 -> ret`) under `RustCliAllocBudget M`, re-exporting error exits and `Ok` epilogue
steps from `Variant6fPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator States pbToProtoPolyDecoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (boolByte resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved decoderFromPbResult resultChunkedStatesAt spqrErrorByte
   statesFromPbSavedCells statesFromPbStack v1_bv_add_add_lit v1_bv_sub_sub_lit
   v6hr_Regs1508 v6hr_from_pb_hdr_eq64_dec_err v6hr_from_pb_hdr_eq64_dec_ok
   v6hr_lowStackAt v6hr_lowStackAt_eq_fsp v6hr_lowStackGaps
   v6hr_memRegion_2064_split_9936 v6hr_memRegion_2064_unsplit_9936 v6hr_vecU8Payload_cap_lt)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   fitsEvents_append rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
  (v6hr_sub_ok_dealloc_of_placedHooks v6hr_sub_ok_dealloc_placed)

export Variant6fPlacedBudgetAux
  (V6hrAuthCloneEnv fitsEvents_authClone_of_fitsEnv fromPbDecEnv_append_freeOnly
   v6hr_exit_err_10324_of_sub_placed v6hr_exit_err_10324_of_placedHooks
   v6hr_exit_err_10324_placed
   v6hr_exit_err_10316_none_placed v6hr_exit_err_10316_none_placed_budget
   v6hr_exit_err_10316_some_of_sub_placed v6hr_exit_err_10316_some_of_placedHooks
   v6hr_exit_err_10316_some_placed
   v6hr_step_10000_ok_to_8180_placed
   v6hr_step_10000_ok_to_exit_of_sub_placed v6hr_step_10000_ok_to_exit_of_placedHooks
   v6hr_step_10000_ok_to_exit_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
  resultChunkedStatesAt statesFromPbSavedCells vecU8Payload
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## 3. Key Clone & Input `ProtoAuthenticator` Cleanup (`+3760 -> +9936`) -/

theorem v6hr_step_3760_to_9936_of_placedHooks_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 : BitVec 64)
    (d112 d116 : BitVec 32)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64) (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1
      (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
      epoch w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (p1_new p2_new : BitVec 64) (d184' : BitVec 32),
          V6hrAuthCloneEnv rootKey macKey evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 epoch p2_new p0 d184' p1_new d116 p2
              (BitVec.ofNat 64 macKey.length) w120 w96 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
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
          TraceCalleeSaved sm s0) := by
  obtain ⟨hfits_r, hfits_m⟩ :=
    (fitsEvents_append M lim (authKeyCloneEvents rootKey) (authKeyCloneEvents macKey) st).mp hfits
  have hstep1 :
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 3796#64) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          vecU8Payload A.repAlloc c1 p1 rootKey ∗
          vecU8Payload A.repAlloc c2 p2 macKey ∗
          A.pool lim st s1 ∗ Rest)
        (fun s2 P2 =>
          (P2 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 v128 v136 v144 d184 v192 d200 v208 v216 w120 w96 ∗
            vecU8Payload A.repAlloc c1 p1 rootKey ∗
            vecU8Payload A.repAlloc c2 p2 macKey ∗
            A.pool lim st s2 ∗ Rest) ∧
          v6hr_Regs1508 s0 s2 out c0 p0 64#64 c1 p1
            (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
            epoch w88 w104 d112 d116 w120 ∧
          s2.readReg64 .x27 = c0) := by
    unfold v6hr_lowStackAt
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (Variant6bPlacedBudget.v6hr_step_3760_to_3796_placed_budget A lim st s0 s1
          out c0 p0 c1 p1 (BitVec.ofNat 64 rootKey.length)
          c2 p2 (BitVec.ofNat 64 macKey.length) epoch w88 w104 d112 d116 w120 v80 v224
          (((s0.sp - 2272#64) ↦₆₄ v128) ∗ ((s0.sp - 2264#64) ↦₆₄ v136) ∗
           ((s0.sp - 2256#64) ↦₆₄ v144) ∗ ((s0.sp - 2216#64) ↦₃₂ d184) ∗
           ((s0.sp - 2208#64) ↦₆₄ v192) ∗ ((s0.sp - 2200#64) ↦₃₂ d200) ∗
           ((s0.sp - 2192#64) ↦₆₄ v208) ∗ ((s0.sp - 2184#64) ↦₆₄ v216) ∗
           ((s0.sp - 2168#64) ↦₆₄ w96) ∗ v6hr_lowStackGaps s0.sp ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           vecU8Payload A.repAlloc c1 p1 rootKey ∗ vecU8Payload A.repAlloc c2 p2 macKey ∗ Rest)
          hsp0_align hc0 hc1 hpc1 hrun1 hregs1) ?_)
    intro s2 P2 _ _ ⟨hP2, _, hregs2, hx27_2⟩
    exact ⟨Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)), hregs2, hx27_2⟩
  refine SepWP.seq hstep1 ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hregs2, _⟩
  rcases hregs2 with ⟨hsp2, hx8_2, hx9_2, _, hx11_2, hx12_2, hx13_2, hx14_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  rw [v6hr_lowStackAt_eq_fsp]
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq
      (Variant6cPlacedBudget.v6hr_clone_rootKey_3796_to_8812_of_placedHooks hA st s0 s2
        out c0 p0 c1 p1 c2 p2 (BitVec.ofNat 64 macKey.length) epoch w88 w104 w120
        v128 v144 v192 v208 d112 d116 d184 d200 rootKey
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ w96) ∗
         v6hr_lowStackGaps s0.sp ∗
         vecU8Payload A.repAlloc c2 p2 macKey ∗ Rest)
        hfits_r hsp0_align hpc2 hrun2 hsp2 hx8_2 hx9_2 hx11_2 hx12_2 hx13_2 hx14_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2) ?_)
  intro s3 P3 hpc3 hrun3 ⟨p1_new, d184', hP3, hsp3, hx11_3, hx12_3, hx19_3, hx20_3,
    hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx28_3, htr3⟩
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq
      (Variant6cPlacedBudget.v6hr_clone_macKey_8812_to_9852_of_placedHooks hA
        (M.stepEvents (authKeyCloneEvents rootKey) st) s0 s3
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
         vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecCapPtrDealloc A.repAlloc c1 p1 ∗ Rest)
        hfits_m hsp0_align hpc3 hrun3 hsp3 hx11_3 hx12_3 hx19_3 hx20_3 hx21_3 hx22_3
        hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 htr3) ?_)
  intro s4 P4 hpc4 hrun4 ⟨p2_new, hP4, hsp4, hx11_4, hx12_4, hx19_4, hx21_4, hx22_4,
    hx23_4, hx24_4, hx26_4, hx27_4, hx28_4, htr4⟩
  refine SepWP.weaken_pre hP4 ?_
  have hdealloc := Variant6cPlacedBudget.v6hr_dealloc_auth_9852_to_9936_of_placedHooks hA
    (M.stepEvents (authKeyCloneEvents macKey) (M.stepEvents (authKeyCloneEvents rootKey) st))
    s0 s4 out c0 c1 p1 p1_new (BitVec.ofNat 64 rootKey.length) c2 p2 w88 w104 d112 d116
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
     vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗ Rest)
    hsp0_align hpc4 hrun4 hsp4 hx11_4 hx12_4 hx19_4 hx21_4 hx22_4 hx23_4
    hx24_4 hx26_4 hx27_4 hx28_4 htr4
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hdealloc ?_)
  intro sm Pm _ _ ⟨evs_free, hevs_free, hPm, hregs_m⟩
  refine ⟨authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey ++ evs_free,
    p1_new, p2_new, d184', ⟨evs_free, hevs_free, rfl⟩, ?_, hregs_m⟩
  rw [v6hr_lowStackAt_eq_fsp,
      LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
      LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v6hr_step_3760_to_9936_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 : BitVec 64)
    (d112 d116 : BitVec 32)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64) (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1
      (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
      epoch w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (p1_new p2_new : BitVec 64) (d184' : BitVec 32),
          V6hrAuthCloneEnv rootKey macKey evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 epoch p2_new p0 d184' p1_new d116 p2
              (BitVec.ofNat 64 macKey.length) w120 w96 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
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
          TraceCalleeSaved sm s0) :=
  v6hr_step_3760_to_9936_of_placedHooks_sepWP hA.toPlacedBudget st s0 s1
    out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 d112 d116
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 rootKey macKey Rest
    hfits hsp0_align hc0 hc1 hpc1 hrun1 hregs1

theorem v6hr_step_3760_to_9936_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 : BitVec 64)
    (d112 d116 : BitVec 32)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64) (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1
      (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
      epoch w88 w104 d112 d116 w120) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (p1_new p2_new : BitVec 64) (d184' : BitVec 32),
          V6hrAuthCloneEnv rootKey macKey evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 epoch p2_new p0 d184' p1_new d116 p2
              (BitVec.ofNat 64 macKey.length) w120 w96 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
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
      Qp :=
  SepWPp.of_sepWP_ret
    (v6hr_step_3760_to_9936_of_placedHooks_sepWP hA st s0 s1
      out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 d112 d116
      v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 rootKey macKey Rest
      hfits hsp0_align hc0 hc1 hpc1 hrun1 hregs1)

theorem v6hr_step_3760_to_9936_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 : BitVec 64)
    (d112 d116 : BitVec 32)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64) (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1
      (BitVec.ofNat 64 rootKey.length) c2 p2 (BitVec.ofNat 64 macKey.length)
      epoch w88 w104 d112 d116 w120) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (p1_new p2_new : BitVec 64) (d184' : BitVec 32),
          V6hrAuthCloneEnv rootKey macKey evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp 64#64 epoch p2_new p0 d184' p1_new d116 p2
              (BitVec.ofNat 64 macKey.length) w120 w96 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
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
      Qp :=
  SepWPp.of_sepWP_ret
    (v6hr_step_3760_to_9936_placed_sepWP hA st s0 s1
      out c0 p0 c1 p1 c2 p2 epoch w88 w96 w104 w120 d112 d116
      v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 rootKey macKey Rest
      hfits hsp0_align hc0 hc1 hpc1 hrun1 hregs1)

/-! ## 4. Decoder Branch & Full Exit (`+9936 -> ret`) -/

theorem v6hr_step_9936_dec_none_to_exit_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 p1_new p2_new ep p2 w120 w96 : BitVec 64)
    (d184 d200 : BitVec 32)
    (rootKey macKey hdrBytes : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
          (BitVec.ofNat 64 macKey.length) w120 w96 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 w96 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
         A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (v6hr_vecU8Payload_cap_lt A.repAlloc _ p1_new rootKey))
        (Entails.of_eq (by rw [sepConj_assoc])))) ?_
  apply ProofLib.SepWP.pure_elim; rintro ⟨_, hl1⟩
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq
      (Variant6ePlacedBudget.v6hr_step_9936_dec_none_to_10416_placed_budget A lim st s0 s1
        out c0 p1_new (BitVec.ofNat 64 rootKey.length)
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 w96 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗ Rest)
        hl1 hpc1 hrun1 hsp1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, _, hsp2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  rw [v6hr_lowStackAt_eq_fsp]
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq
      (Variant6cPlacedBudget.v6hr_dealloc_cloned_10416_to_10396_of_sub_placed hdealloc_ok st s0 s2
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
  intro s3 P3 hpc3 hrun3 ⟨evs, hevs, hP3, hsp3, hx19_3, hx25_3, htr3⟩
  refine SepWP.weaken_pre hP3 ?_
  have hx25_b : (s3.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx25_3]; rfl
  have herr := Variant6aPlacedBudget.v6hr_states_from_pb_err_10396_placed_budget
    A lim (M.stepEvents evs st) (F := F) (ext := ext) s0 s3 out
    64#64 ep p2_new p0 d184 p1_new d200 p2 (BitVec.ofNat 64 macKey.length) w120 w96
    .stateDecode Rest hsp0_align hpc3 hrun3 hsp3 hx19_3 hx25_b htr3
  rw [v6hr_lowStackAt_eq_fsp] at herr
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono herr ?_)
  intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
  exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v6hr_step_9936_dec_none_to_exit_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ) (s0 s1 : State)
    (out c0 p0 p1_new p2_new ep p2 w120 w96 : BitVec 64)
    (d184 d200 : BitVec 32)
    (rootKey macKey hdrBytes : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
          (BitVec.ofNat 64 macKey.length) w120 w96 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_step_9936_dec_none_to_exit_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA) st s0 s1
    out c0 p0 p1_new p2_new ep p2 w120 w96 d184 d200 rootKey macKey hdrBytes Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

theorem v6hr_step_9936_dec_none_to_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ) (s0 s1 : State)
    (out c0 p0 p1_new p2_new ep p2 w120 w96 : BitVec 64)
    (d184 d200 : BitVec 32)
    (rootKey macKey hdrBytes : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
          (BitVec.ofNat 64 macKey.length) w120 w96 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_step_9936_dec_none_to_exit_of_sub_placed (v6hr_sub_ok_dealloc_placed hA) st s0 s1
    out c0 p0 p1_new p2_new ep p2 w120 w96 d184 d200 rootKey macKey hdrBytes Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

set_option maxHeartbeats 800000 in
theorem v6hr_step_9936_dec_some_to_exit_of_placedHooks_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 : BitVec 64)
    (d184 : BitVec 32)
    (authPb : ProtoAuthenticator) (hdrBytes : List (BitVec 8))
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (heq_pts : decPb.ptsNeeded = 576#32)
    (h1 : (pbToProtoPolyDecoder decPb).pts.length ≤ ptsCap.toNat)
    (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte (pbToProtoPolyDecoder decPb).isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = (pbToProtoPolyDecoder decPb).ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = (pbToProtoPolyDecoder decPb).polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
          (pbToProtoPolyDecoder decPb).polys p2
          (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
             ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder decPb) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.headerReceived
                    { uc := some { hdr := hdrBytes, auth := some authPb, epoch := ep },
                      receivingEk := some decPb }) }) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
           (pbToProtoPolyDecoder decPb).polys p2
           (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
         (if ptsCap = 0#64 then emp
          else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
              ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
         A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
      (Entails.trans
        (sepConj_mono (v6hr_vecU8Payload_cap_lt A.repAlloc _ p1_new authPb.rootKey)
          (sepConj_mono_left (v6hr_memRegion_2064_split_9936 s0.sp)))
        (Entails.of_eq (by rw [sepConj_assoc])))) ?_
  apply ProofLib.SepWP.pure_elim; rintro ⟨_, hl1⟩
  rw [v6hr_lowStackAt_eq_fsp]
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq
      (Variant6ePlacedBudget.v6hr_step_9936_dec_some_to_10000_placed_sepWP hdec st s0 s1 hcl1
        out c0 p1_new (BitVec.ofNat 64 authPb.rootKey.length) ptsCap ptsPtr w120
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
         vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗ Rest)
        hfits hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx23_1
        hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_)
  intro s2 P2 hpc2 hrun2 ⟨evs1, henv1, hP2, hsp2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  cases hres : decoderFromPbResult (pbToProtoPolyDecoder decPb) with
  | error e =>
    rw [v6hr_from_pb_hdr_eq64_dec_err F hdrBytes authPb ep decPb e heq_pts hhdr hres]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.seq
        (Variant6ePlacedBudget.v6hr_step_10000_err_to_10492_placed_budget A lim
          (M.stepEvents evs1 st) s0 s2 out c0 p1_new
          (BitVec.ofNat 64 authPb.rootKey.length) e
          (memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
           (((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
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
           vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
           vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
           vecU8Payload A.repAlloc c0 p0 hdrBytes ∗ Rest)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx26_2 hx27_2 htr2) ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, _, hsp3, hx19_3, hx21_3, hx26_3, hx27_3, htr3⟩
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
           vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
           vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
           vecU8Payload A.repAlloc c0 p0 hdrBytes ∗ A.pool lim (M.stepEvents evs1 st) s3 ∗
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
            memRegion out chunkedStatesSize ∗ Rest)) by sep_ac_rfl))
        (sepConj_mono_left hunsplit)) ?_
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.seq
        (Variant6cPlacedBudget.v6hr_dealloc_cloned_10492_to_10396_of_placedHooks hA
          (M.stepEvents evs1 st) s0 s3
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
    intro s4 P4 hpc4 hrun4 ⟨evs2, hevs2, hP4, hsp4, hx19_4, hx25_4, htr4⟩
    refine SepWP.weaken_pre hP4 ?_
    have hx25_b : (s4.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx25_4]; rfl
    have herr := Variant6aPlacedBudget.v6hr_states_from_pb_err_10396_placed_budget
      A lim (M.stepEvents evs2 (M.stepEvents evs1 st)) (F := F) (ext := ext) s0 s4 out
      64#64 ep p2_new p0 d184 p1_new (pbToProtoPolyDecoder decPb).polys p2
      (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr .stateDecode Rest
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx25_b htr4
    rw [v6hr_lowStackAt_eq_fsp] at herr
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono herr ?_)
    intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
    refine ⟨evs1 ++ evs2, fromPbDecEnv_append_freeOnly henv1 hevs2, ?_, hsp_f, hcs_f, htr_f⟩
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
  | ok dec =>
    rw [v6hr_from_pb_hdr_eq64_dec_ok F hdrBytes authPb ep decPb dec heq_pts hhdr hres]
    dsimp only [resultPolyDecoderFromPbAt]
    have hok := v6hr_step_10000_ok_to_exit_of_placedHooks (F := F) hA (M.stepEvents evs1 st) s0 s2
      out c0 p0 p1_new p2_new ep p2 w120 ptsPtr
      d184 (pbToProtoPolyDecoder decPb).polys
      authPb.rootKey authPb.macKey hdrBytes dec Rest
      hsp0_align hhdr hpc2 hrun2 hsp2 hx19_2 hx21_2 hx26_2 hx27_2 htr2
    rw [v6hr_lowStackAt_eq_fsp] at hok
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hok ?_)
    intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
    exact ⟨evs1, henv1, hPf, hsp_f, hcs_f, htr_f⟩

theorem v6hr_step_9936_dec_some_to_exit_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 : BitVec 64)
    (d184 : BitVec 32)
    (authPb : ProtoAuthenticator) (hdrBytes : List (BitVec 8))
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (heq_pts : decPb.ptsNeeded = 576#32)
    (h1 : (pbToProtoPolyDecoder decPb).pts.length ≤ ptsCap.toNat)
    (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte (pbToProtoPolyDecoder decPb).isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = (pbToProtoPolyDecoder decPb).ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = (pbToProtoPolyDecoder decPb).polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
          (pbToProtoPolyDecoder decPb).polys p2
          (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
             ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder decPb) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.headerReceived
                    { uc := some { hdr := hdrBytes, auth := some authPb, epoch := ep },
                      receivingEk := some decPb }) }) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_step_9936_dec_some_to_exit_of_placedHooks_sepWP (F := F) hA.toPlacedBudget hdec st s0 s1 hcl1
    out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 d184 authPb hdrBytes decPb Rest
    hfits hsp0_align hhdr heq_pts h1 h2 h3 hw120 hpc1 hrun1 hsp1
    hx11_1 hx12_1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

theorem v6hr_step_9936_dec_some_to_exit_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 : BitVec 64)
    (d184 : BitVec 32)
    (authPb : ProtoAuthenticator) (hdrBytes : List (BitVec 8))
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (heq_pts : decPb.ptsNeeded = 576#32)
    (h1 : (pbToProtoPolyDecoder decPb).pts.length ≤ ptsCap.toNat)
    (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte (pbToProtoPolyDecoder decPb).isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = (pbToProtoPolyDecoder decPb).ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = (pbToProtoPolyDecoder decPb).polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
          (pbToProtoPolyDecoder decPb).polys p2
          (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
             ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder decPb) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.headerReceived
                    { uc := some { hdr := hdrBytes, auth := some authPb, epoch := ep },
                      receivingEk := some decPb }) }) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      Qp :=
  SepWPp.of_sepWP_ret
    (v6hr_step_9936_dec_some_to_exit_of_placedHooks_sepWP (F := F) hA hdec st s0 s1 hcl1
      out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 d184 authPb hdrBytes decPb Rest
      hfits hsp0_align hhdr heq_pts h1 h2 h3 hw120 hpc1 hrun1 hsp1
      hx11_1 hx12_1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1)

theorem v6hr_step_9936_dec_some_to_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 : BitVec 64)
    (d184 : BitVec 32)
    (authPb : ProtoAuthenticator) (hdrBytes : List (BitVec 8))
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (heq_pts : decPb.ptsNeeded = 576#32)
    (h1 : (pbToProtoPolyDecoder decPb).pts.length ≤ ptsCap.toNat)
    (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte (pbToProtoPolyDecoder decPb).isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = (pbToProtoPolyDecoder decPb).ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = (pbToProtoPolyDecoder decPb).polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8) (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new
          (pbToProtoPolyDecoder decPb).polys p2
          (BitVec.ofNat 64 authPb.macKey.length) w120 ptsPtr ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
             ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv (pbToProtoPolyDecoder decPb) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.headerReceived
                    { uc := some { hdr := hdrBytes, auth := some authPb, epoch := ep },
                      receivingEk := some decPb }) }) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      Qp :=
  SepWPp.of_sepWP_ret
    (v6hr_step_9936_dec_some_to_exit_placed_sepWP (F := F) hA hdec st s0 s1 hcl1
      out c0 p0 p1_new p2_new ep p2 ptsCap ptsPtr w120 d184 authPb hdrBytes decPb Rest
      hfits hsp0_align hhdr heq_pts h1 h2 h3 hw120 hpc1 hrun1 hsp1
      hx11_1 hx12_1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudget
