/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5d `withLsCodeLoaded`: Arm 7 Call Steps

Relocatable `[LibsignalPlacement]` call step lemmas (`+2100 -> +2116` and `+2116 -> +2128` in
Block `334`) for Arm 7 (`States.ct1Sampled`) with `withLsCodeLoaded` on `<PolyEncoder>::into_pb`
(Block `375`) and `<PolyDecoder>::into_pb` (Block `377`).
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

/-- Step 4 (`+2100 -> +2116` in Block `334`) with `withLsCodeLoaded`:
    call `<PolyEncoder>::into_pb(s0.sp - 1232, stA)` and thread `LibsignalCodeLoaded`. -/
theorem ct1Sampled_step_2100_to_2116_cl_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sm.pc = (blkPl_334).base + 2116#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = len_ct1 →
      sm.readReg64 .x23 = s0.sp - 1360#64 →
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
         memRegion stA polyEncoderSize ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A stA enc ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  refine statesIntoPb_seq_sepWP_cl
    (mid := lsmpl.base 375)
    (P' :=
      memRegion (s0.sp - 1232#64) 56 ∗
      polyEncoderAt A stA enc ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Post := fun sm =>
      sm.sp = s0.sp - 1520#64 ∧
      sm.readReg64 .x29 = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = stA ∧
      sm.readReg64 .x21 = ptr_new ∧
      sm.readReg64 .x22 = len_ct1 ∧
      sm.readReg64 .x23 = s0.sp - 1360#64 ∧
      sm.readReg64 .x27 = s0.sp - 1360#64 ∧
      sm.readReg64 .x28 = epoch ∧
      sm.readReg64 .x0 = s0.sp - 1232#64 ∧
      sm.readReg64 .x1 = stA ∧
      sm.readReg64 .x30 = (blkPl_334).base + 2116#64 ∧
      TraceCalleeSaved sm s0)
    hcl ?_ ?_
  · wp_steps
    wp_done
  · intro s_call hpc_call hrun_call hcl_call ⟨hsp_c, hx29_c, hx19_c, hx20_c, hx21_c, hx22_c,
      hx23_c, hx27_c, hx28_c, hx0_c, hx1_c, hx30_c, htr_c⟩
    have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
    exact call_encoderIntoPb_expose_cl_placed henc_cl
      (s0.sp - 1232#64) stA enc
      hcl_call hpc_call hrun_call hsp_c hfsp_align hx30_c htr_c hx0_c hx1_c
      (by change _ = (memRegion (s0.sp - 1232#64) 56 ∗ polyEncoderAt A stA enc ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame; ac_rfl)
      (fun sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm hcc htrm hclm => by
        refine SepWPp.weaken_pre ?_
          (hnext sm e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm
            (hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c)
            (hcc.1.trans hx19_c)
            (hcc.2.1.trans hx20_c)
            (hcc.2.2.1.trans hx21_c)
            (hcc.2.2.2.1.trans hx22_c)
            (hcc.2.2.2.2.1.trans hx23_c)
            (hcc.2.2.2.2.2.2.2.2.1.trans hx27_c)
            (hcc.2.2.2.2.2.2.2.2.2.1.trans hx28_c)
            htrm hclm)
        exact Entails.of_eq (by simp only [arm64_norm]))

/-- Step 5 (`+2116 -> +2128` in Block `334`) with `withLsCodeLoaded`:
    call `<PolyDecoder>::into_pb(s0.sp - 1176, stA + 528)`. -/
theorem ct1Sampled_step_2116_to_2128_cl_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (s0 s : State) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (dec : PolyDecoder)
    (Frame R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx23 : s.readReg64 .x23 = s0.sp - 1360#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (d0 d1 d2 d3 d4 : BitVec 64),
      sm.pc = (blkPl_334).base + 2128#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = len_ct1 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
          ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
          ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
         protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 dec.intoPb ∗
         memRegion (stA + 528#64) polyDecoderSize ∗
         A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1176#64) 40 ∗
       polyDecoderAt A (stA + 528#64) dec ∗
       A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q (StatesIntoPbPanic s0 R) := by
  rcases htrace with ⟨htrace, hvregs⟩
  refine statesIntoPb_seq_sepWP_cl
    (mid := lsmpl.base 377)
    (P' :=
      memRegion (s0.sp - 1176#64) 40 ∗
      polyDecoderAt A (stA + 528#64) dec ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
    (Post := fun sm =>
      sm.sp = s0.sp - 1520#64 ∧
      sm.readReg64 .x29 = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = ptr_new ∧
      sm.readReg64 .x22 = len_ct1 ∧
      sm.readReg64 .x27 = s0.sp - 1360#64 ∧
      sm.readReg64 .x28 = epoch ∧
      sm.readReg64 .x0 = s0.sp - 1176#64 ∧
      sm.readReg64 .x1 = stA + 528#64 ∧
      sm.readReg64 .x30 = (blkPl_334).base + 2128#64 ∧
      TraceCalleeSaved sm s0)
    hcl ?_ ?_
  · wp_steps
    wp_done
  · intro s_call hpc_call hrun_call hcl_call ⟨hsp_c, hx29_c, hx19_c, hx21_c, hx22_c,
      hx27_c, hx28_c, hx0_c, hx1_c, hx30_c, htr_c⟩
    have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
    exact call_decoderIntoPb_expose_cl_placed hdec_cl
      (s0.sp - 1176#64) (stA + 528#64) dec
      hcl_call hpc_call hrun_call hsp_c hfsp_align hx30_c htr_c hx0_c hx1_c
      (by change _ = (memRegion (s0.sp - 1176#64) 40 ∗ polyDecoderAt A (stA + 528#64) dec ∗
            A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame; ac_rfl)
      (fun sm d0 d1 d2 d3 d4 hpcm hrunm hspm hcc htrm => by
        refine SepWPp.weaken_pre ?_
          (hnext sm d0 d1 d2 d3 d4 hpcm hrunm hspm
            (hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c)
            (hcc.1.trans hx19_c)
            (hcc.2.2.1.trans hx21_c)
            (hcc.2.2.2.1.trans hx22_c)
            (hcc.2.2.2.2.2.2.2.2.1.trans hx27_c)
            (hcc.2.2.2.2.2.2.2.2.2.1.trans hx28_c)
            htrm)
        exact Entails.of_eq (by simp only [arm64_norm]))

end CryptoVerification.SpqrV1.States.IntoPb
