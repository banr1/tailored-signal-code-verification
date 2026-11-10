/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2
import ProofLib.SepLogic.WPp

/-!
# Relocatable V1 Ratchet `<Message>::deserialize` Steps & `.rodata` Helpers for `spqr::recv`

Relocatable pre/post `<Message>::deserialize` steppers (`+1532..+1568`) and `.rodata` exposure
lemmas for `spqr::recv` (Block `329`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `+1532..+1568`: Placed `Message::deserialize` Pre/Post Steps -/

/-- Pre-call step `+1532 -> lsmpl.base 351`: sets `x0 = s0.sp - 3056#64`, `x1 = pre.epoch`, `x2
    = remPtr`, `x3 = BitVec.ofNat 64 pre.remaining.length`, `x25 = s0.sp - 4640#64`, and `x30 =
    spqrRecvPlacedEntry + 1556#64`. -/
theorem step_pre_msgDeserialize_1532_placed (ext : String → Option (State → State))
    (s0 s : State) (pre : MsgPreamble) (remPtr : BitVec 64) (P : SepProp)
    (hs0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1532#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr) :
    SepWP (spqrRecvPlacedProg ext) (lsmpl.base 351) s P
      (fun sf Pf =>
        Pf = P ∧
        sf.sp = s0.sp - 4992#64 ∧
        TraceVRegs sf s ∧
        sf.readReg64 .x0 = s0.sp - 3056#64 ∧
        sf.readReg64 .x1 = pre.epoch ∧
        sf.readReg64 .x2 = remPtr ∧
        sf.readReg64 .x3 = BitVec.ofNat 64 pre.remaining.length ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = pre.epoch ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
        sf.readReg64 .x24 = remPtr ∧
        sf.readReg64 .x25 = s0.sp - 4640#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = spqrRecvPlacedEntry + 1556#64) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨rfl, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [spqrRecvPlacedEntry, arm64_norm, *]⟩

/-- Post-call error step `+1556 -> +2060` when `Message.deserialize spqrPolyApi pre.epoch
    pre.remaining = .error err`: reads `0xff#8` from `s0.sp - 3048#64` (`[sp, #1944]`) and takes
    `b.eq +2060`. -/
theorem step_post_msgDeserialize_err_1556_placed (ext : String → Option (State → State))
    (s0 s : State) (Rest : SepProp)
    (hs0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1556#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64) :
    SepWP (spqrRecvPlacedProg ext) (spqrRecvPlacedEntry + 2060#64) s
      (((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest)
      (fun sf Pf =>
        Pf = (((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest) ∧
        sf.sp = s0.sp - 4992#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        TraceVRegs sf s) := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨rfl, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩

/-- Post-call ok step `+1556 -> +1568` when `tag ≠ 0xff#8`: reads `tag` from `s0.sp - 3048#64`
    (`[sp, #1944]`), does not branch to `+2060`, and reaches `+1568` with `(sf.readReg64
    .x8).truncate 8 = tag`. -/
theorem step_post_msgDeserialize_ok_1556_placed (ext : String → Option (State → State))
    (s0 s : State) (tag : BitVec 8) (Rest : SepProp)
    {post : State → SepProp → Prop}
    (hs0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1556#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htag : tag ≠ 0xff#8)
    (hnext : ∀ sf : State,
      sf.pc = spqrRecvPlacedEntry + 1568#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 4992#64 →
      TraceVRegs sf s →
      (sf.readReg64 .x8).truncate 8 = tag →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) sf
        (((s0.sp - 3048#64) ↦₈ tag) ∗ Rest) post) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s
      (((s0.sp - 3048#64) ↦₈ tag) ∗ Rest) post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have htag_eq := tag_zeroExtend_beq_255_false htag
  have htag_cond := tag_zeroExtend_sub_255_beq_0_false htag
  have htag_ne := tag_zeroExtend_sub_255_bne_0_true htag
  have htrunc : ((tag.zeroExtend 32).zeroExtend 64).truncate 8 = tag := by
    revert tag; bv_kernel
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  wp_steps
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

/-! ## 2. Placed `.rodata` Exposure Lemmas -/

theorem spqrRecvRoPlacedAt_expose_statesFromPb :
    spqrRecvRoPlacedAt ⊢
      statesFromPbJumpTablePlacedAt ∗
      (∃∗ P_ro : SepProp, ⌜statesFromPbJumpTablePlacedAt ∗ P_ro ⊢ spqrRecvRoPlacedAt⌝ ∗ P_ro) := by
  unfold spqrRecvRoPlacedAt
  refine Entails.trans
    (Entails.of_eq (show
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt =
      statesFromPbJumpTablePlacedAt ∗
        (Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
          statesRecvRoPlacedAt ∗
          statesIntoPbJumpTablePlacedAt) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

theorem spqrRecvRoPlacedAt_expose_statesRecv :
    spqrRecvRoPlacedAt ⊢
      statesRecvRoPlacedAt ∗
      (∃∗ P_ro : SepProp, ⌜statesRecvRoPlacedAt ∗ P_ro ⊢ spqrRecvRoPlacedAt⌝ ∗ P_ro) := by
  unfold spqrRecvRoPlacedAt
  refine Entails.trans
    (Entails.of_eq (show
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt =
      statesRecvRoPlacedAt ∗
        (Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗
          statesIntoPbJumpTablePlacedAt) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
