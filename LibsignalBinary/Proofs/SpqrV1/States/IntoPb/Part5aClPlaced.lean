/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbClPlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5a `withLsCodeLoaded`: Arm 8 (`States.ekReceivedCt1Sampled`)

Relocatable `[LibsignalPlacement]` verification of Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`)
with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` (Block `375`) and Block `334`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States.IntoPb.Placed

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-- Auxiliary reference state overriding only `x30` (`lr`) so `SepWPp` CPS steps can stop at an
    intermediate PC `lr` and sequence with `sepWPp_seq_mid_lscl`. -/
def statesIntoPbSetLr (s0 : State) (lr : BitVec 64) : State :=
  s0.writeReg64 (Reg.gpr 30#5) lr

theorem statesIntoPbSetLr_lr (s0 : State) (lr : BitVec 64) :
    (statesIntoPbSetLr s0 lr).readReg64 .x30 = lr := by
  simp [statesIntoPbSetLr, wp_norm]

/-- Step 5 (`+2324 -> +2340` in Block `334`) with `withLsCodeLoaded` on `<PolyEncoder>::into_pb`. -/
theorem ekReceivedCt1Sampled_step_2324_to_2340_cl_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sm.pc = (blkPl_334).base + 2340#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = len_ct1 →
      sm.readReg64 .x22 = ptr_new →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      LibsignalCodeLoaded lsmpl sm.mem →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
          ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
          ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
          ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
         protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
         memRegion (stA + 8#64) polyEncoderSize ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A (stA + 8#64) enc ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  refine statesIntoPb_seq_sepWP_cl
    (mid := lsmpl.base 375)
    (P' :=
      memRegion (s0.sp - 1232#64) 56 ∗
      polyEncoderAt A (stA + 8#64) enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Post := fun sm =>
      sm.sp = s0.sp - 1520#64 ∧
      sm.readReg64 .x29 = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = stA ∧
      sm.readReg64 .x21 = len_ct1 ∧
      sm.readReg64 .x22 = ptr_new ∧
      sm.readReg64 .x27 = s0.sp - 1360#64 ∧
      sm.readReg64 .x28 = epoch ∧
      sm.readReg64 .x0 = s0.sp - 1232#64 ∧
      sm.readReg64 .x1 = stA + 8#64 ∧
      sm.readReg64 .x30 = (blkPl_334).base + 2340#64 ∧
      TraceCalleeSaved sm s0)
    hcl ?_ ?_
  · wp_steps
    wp_done
  · intro s_call hpc_call hrun_call hcl_call ⟨hsp_c, hx29_c, hx19_c, hx20_c, hx21_c, hx22_c,
      hx27_c, hx28_c, hx0_c, hx1_c, hx30_c, htr_c⟩
    have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
    exact call_encoderIntoPb_expose_cl_placed henc_cl
      (s0.sp - 1232#64) (stA + 8#64) enc
      hcl_call hpc_call hrun_call hsp_c hfsp_align hx30_c htr_c hx0_c hx1_c
      (by change _ = (memRegion (s0.sp - 1232#64) 56 ∗ polyEncoderAt A (stA + 8#64) enc ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame; ac_rfl)
      (fun sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm hcc htrm hclm => by
        refine SepWPp.weaken_pre ?_
          (hnext sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm
            (hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c)
            (hcc.1.trans hx19_c)
            (hcc.2.1.trans hx20_c)
            (hcc.2.2.1.trans hx21_c)
            (hcc.2.2.2.1.trans hx22_c)
            (hcc.2.2.2.2.2.2.2.2.1.trans hx27_c)
            (hcc.2.2.2.2.2.2.2.2.2.1.trans hx28_c)
            htrm hclm)
        exact Entails.of_eq (by simp only [arm64_norm]))

set_option maxHeartbeats 800000 in
/-- Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`, jump table index `8` -> `+1644` in Block `334`)
    with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` (`Block 375`) and Block `334`. -/
theorem states_into_pb_ekReceivedCt1Sampled_cl_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlaced A ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec A F (.ekReceivedCt1Sampled s))) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesIntoPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.ekReceivedCt1Sampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp_placed s0 s0 out stA (.ekReceivedCt1Sampled s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkReceivedCt1Sampled_expose A stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro a0
  apply SepWPp.exists_elim; intro a1
  apply SepWPp.exists_elim; intro a2
  apply SepWPp.exists_elim; intro a3
  apply SepWPp.exists_elim; intro a4
  apply SepWPp.exists_elim; intro a5
  apply SepWPp.exists_elim; intro es0
  apply SepWPp.exists_elim; intro es1
  apply SepWPp.exists_elim; intro es2
  apply SepWPp.exists_elim; intro ek0
  apply SepWPp.exists_elim; intro ek1
  apply SepWPp.exists_elim; intro ek2
  apply SepWPp.exists_elim; intro cap_ct1
  apply SepWPp.exists_elim; intro ptr_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 10#64) ∗
      polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
      ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
      ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A es0 es1 es2 s.uc.es ∗
      vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 10#64) ∗
       (statesIntoPbJumpTablePlacedAt ∗
        memRegion out optProtoInnerStateSize ∗
        polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
        ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
        ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗
        vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
        memRegion (stA + 536#64) 392 ∗ A.pool)) by ac_rfl]
  apply SepWPp.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60_placed (ext := ext) s0 out stA 10#64
    (statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP_cl hcl0 hpro fun s1 hpc1 hrun1 hcl1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [@ProofLib.memRegion_split' (s0.sp - 1520#64) (s0.sp - 1512#64) 8 1416 1424
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (Drop.pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWPp.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 10#64) ∗
          (statesIntoPbJumpTablePlacedAt ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗
           vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 10#64) ∗
           statesIntoPbJumpTablePlacedAt ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A es0 es1 es2 s.uc.es ∗
           vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool) by ac_rfl]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w8
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w88
  apply SepWPp.exists_elim; intro w96
  apply SepWPp.exists_elim; intro w104
  apply SepWPp.exists_elim; intro w112
  apply SepWPp.exists_elim; intro w120
  apply SepWPp.exists_elim; intro w128
  apply SepWPp.exists_elim; intro w136
  apply SepWPp.exists_elim; intro w144
  apply SepWPp.exists_elim; intro w152
  apply SepWPp.exists_elim; intro w160
  apply SepWPp.exists_elim; intro w168
  apply SepWPp.exists_elim; intro w176
  apply SepWPp.exists_elim; intro w184
  apply SepWPp.exists_elim; intro w192
  apply SepWPp.exists_elim; intro w200
  apply SepWPp.exists_elim; intro w208
  apply SepWPp.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
         ∃∗ t4 : BitVec 64, ∃∗ t5 : BitVec 64, ∃∗ t6 : BitVec 64, ∃∗ t7 : BitVec 64,
         ∃∗ t8 : BitVec 64, ∃∗ t9 : BitVec 64, ∃∗ t10 : BitVec 64, ∃∗ t11 : BitVec 64,
         ∃∗ t12 : BitVec 64, ∃∗ t13 : BitVec 64, ∃∗ t14 : BitVec 64, ∃∗ t15 : BitVec 64,
         ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
           ekReceivedScratchCells s0.sp
             t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
           memRegion (s0.sp - 1232#64) 56 ∗
           memRegion (s0.sp - 1176#64) 696 ∗
           memRegion (s0.sp - 432#64) 128 ∗
           memRegion (s0.sp - 208#64) 112) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ekReceived_scratch_split s0.sp))
  refine SepWPp.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro t0
  apply SepWPp.exists_elim; intro t1
  apply SepWPp.exists_elim; intro t2
  apply SepWPp.exists_elim; intro t3
  apply SepWPp.exists_elim; intro t4
  apply SepWPp.exists_elim; intro t5
  apply SepWPp.exists_elim; intro t6
  apply SepWPp.exists_elim; intro t7
  apply SepWPp.exists_elim; intro t8
  apply SepWPp.exists_elim; intro t9
  apply SepWPp.exists_elim; intro t10
  apply SepWPp.exists_elim; intro t11
  apply SepWPp.exists_elim; intro t12
  apply SepWPp.exists_elim; intro t13
  apply SepWPp.exists_elim; intro t14
  apply SepWPp.exists_elim; intro t15
  apply SepWPp.exists_elim; intro u0
  apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2
  apply SepWPp.exists_elim; intro u3
  apply SepWPp.exists_elim; intro u4
  apply SepWPp.exists_elim; intro u5
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply SepWPp.exists_elim; intro v3
  apply SepWPp.exists_elim; intro v4
  apply SepWPp.exists_elim; intro v5
  have hstep2 := ekReceivedCt1Sampled_step_60_to_1760_placed (ext := ext) s0 s1 out stA
    a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool)
    hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine statesIntoPb_seq_sepWP_cl hcl1
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep2) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx23_2, hx24_2,
    hx26_2, hx27_2, hx28_2, htr2⟩
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  let Frame_clone : SepProp :=
    ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
    ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
    ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
    ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
    ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
    ekReceivedScratchCells s0.sp
      a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
      u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
    memRegion (s0.sp - 1232#64) 56 ∗
    memRegion (s0.sp - 1176#64) 696 ∗
    memRegion (s0.sp - 432#64) 128 ∗
    memRegion (s0.sp - 208#64) 112 ∗
    memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
    epilogueStagingCells s0.sp
      w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
    statesIntoPbSavedCells s0 ∗
    (stA ↦₆₄ 10#64) ∗
    statesIntoPbJumpTablePlacedAt ∗
    memRegion out optProtoInnerStateSize ∗
    polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
    ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
    ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A es0 es1 es2 s.uc.es ∗
    vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
    memRegion (stA + 536#64) 392
  let s_ref2252 := statesIntoPbSetLr s0 ((blkPl_334).base + 2252#64)
  have hclone0 := ekReceivedCt1Sampled_step_1760_to_2252_placed
    (Q := fun sm Pm =>
      ∃ ptr_new : BitVec 64,
        (Pm ⊢ vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
                (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
              vecCapPtrDealloc A cap_ct1 ptr_ct1 ∗
              A.pool ∗ stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame_clone) ∧
        sm.sp = s0.sp - 1520#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = stA ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 s.uc.ct1.length ∧
        sm.readReg64 .x22 = ptr_new ∧
        sm.readReg64 .x23 = cap_ct1 ∧
        sm.readReg64 .x24 = ptr_ct1 ∧
        sm.readReg64 .x26 = s0.sp - 480#64 ∧
        sm.readReg64 .x27 = s0.sp - 1360#64 ∧
        sm.readReg64 .x28 = s.uc.epoch ∧
        TraceCalleeSaved sm s0)
    hA s_ref2252 s2 out stA cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1 Frame_clone R
    hsp0_align hlen hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx23_2 hx24_2
    hx26_2 hx27_2 hx28_2 htr2
    (fun sm ptr_new hpcm hrunm hspm hx29m hx19m hx20m hx21m hx22m hx23m hx24m
        hx26m hx27m hx28m htrm => by
      rw [statesIntoPbSetLr_lr]
      exact SepWPp.done hpcm hrunm ⟨ptr_new, Entails.refl _, hspm, hx29m, hx19m, hx20m,
        hx21m, hx22m, hx23m, hx24m, hx26m, hx27m, hx28m, htrm⟩)
  rw [statesIntoPbSetLr_lr] at hclone0
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [Frame_clone]; ac_rfl))
    (DecoderPb.sepWPp_seq_mid_lscl hcl2 hclone0 fun s3 P3 hpc3 hrun3 hcl3
      ⟨ptr_new, hent3, hsp3, hx29_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
       hx26_3, hx27_3, hx28_3, htr3⟩ =>
      SepWPp.weaken_pre hent3 ?_)
  dsimp only [Frame_clone]
  have hstep4 := ekReceivedCt1Sampled_step_2252_to_2324_placed hA s0 s3 out stA
    cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct1 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  refine statesIntoPb_seq_sepWP_cl hcl3
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep4) ?_
  intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx22_4, hx27_4, hx28_4, htr4⟩
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  refine SepWPp.weaken_pre ?_
    (ekReceivedCt1Sampled_step_2324_to_2340_cl_placed henc_cl s0 s4 out stA ptr_new
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.sending_ct1
      (((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ekReceivedScratchCells s0.sp
         a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTablePlacedAt ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392)
      R hcl4 hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hx20_4 hx21_4 hx22_4 hx27_4 hx28_4 htr4 ?_)
  · rw [← hrecomb_stack]
    exact Entails.of_eq (by ac_rfl)
  intro s5 e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5
    hx27_5 hx28_5 htr5 _hcl5
  have hstep6 := ekReceivedCt1Sampled_step_2340_to_1544_placed (ext := ext) s0 s5 out stA ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    e0 e1 e2 e3 e4 e5 e6
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion (stA + 8#64) polyEncoderSize ∗
     A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5 hx27_5 hx28_5 htr5
  refine DecoderPb.SepWPp.seq_clean
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep6) ?_
  intro s6 hpc6 hrun6 ⟨hsp6, hx29_6, hx19_6, hx21_6, hx22_6, htr6⟩
  have hscratch := ekReceivedScratchCells_entails_memRegions s0.sp
    es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
  have hstA := stA_ekReceivedCt1Sampled_entails_928 stA
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
  have hpre_epi :
      ekReceivedScratchCells s0.sp
        es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
       ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
       ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
       ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTablePlacedAt ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
    refine Entails.trans (Entails.of_eq (show _ =
      (ekReceivedScratchCells s0.sp
         es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112) ∗
      ((stA ↦₆₄ 10#64) ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         es0 es1 es2 ek0 ek1 ek2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch e0 e1 e2 e3 e4 e5 e6
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A es0 es1 es2 s.uc.es ∗
       vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by ac_rfl)
  apply SepWPp.of_sepWP_ret
  have hep := states_into_pb_epilogue_placed (ext := ext) s0 s6 out
    es0 es1 es2 ek0 ek1 ek2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 htr6
  rw [hx22_6, hx21_6] at hep
  unfold StatesIntoPbPlacedPost
  refine SepWP.strengthen_entails_const ?_ (SepWP.weaken_pre hpre_epi hep)
  have hout := outWords28_entails_ekReceivedCt1Sampled A out
    es0 es1 es2 ek0 ek1 ek2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       (1#64 <<< 63 ||| 8#64)
       es0 es1 es2 ek0 ek1 ek2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       e0 e1 e2 e3 e4 e5 e6
       w192 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A es0 es1 es2 s.uc.es ∗
     vecU8Heap A ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by ac_rfl)) ?_
  exact sepConj_mono_left hout

end CryptoVerification.SpqrV1.States.IntoPb
