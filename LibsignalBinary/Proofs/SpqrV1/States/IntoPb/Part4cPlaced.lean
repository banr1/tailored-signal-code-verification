/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Placed
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Placed
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4c
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 4c Placed: Arm 4 (`States.ekSentCt1Received`)

Relocatable `[LibsignalPlacement]` verification of Arm 4 (`States.ekSentCt1Received`, tag `6`,
`+0 -> +60 -> +140 -> +160 -> +252 -> +1544 -> ret`) on Block `334`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
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

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-- Step 1 (`+60 -> +156` in Block `334`): jump-table dispatch for tag `6#64` (index `4` -> `+140`) and setup
    for `memcpy(sp + 0xa0, stA + 8, 504)` at `+156`. -/
theorem states_into_pb_ekSentCt1Received_pre1_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (blkPl_334).base + 60#64)
    (hrun : s1.status = .Running)
    (hsp : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 6#64)
    (htr : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s1
      (statesIntoPbJumpTablePlacedAt ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ statesIntoPbJumpTablePlacedAt ∗ Rest) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (blkPl_334).base + 160#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        (s2.readReg64 .x2).toNat = 504 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x28 = s0.sp - 256#64 ∧
        s2.readReg64 .x26 = s0.sp - 480#64 ∧
        s2.readReg64 .x21 = s0.sp - 1360#64 ∧
        s2.readReg64 .x20 = stA ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0) := by
  rcases htr with ⟨htr, hvregs⟩
  dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

/-- Step 2 (`+160 -> +248` in Block `334`). -/
theorem states_into_pb_ekSentCt1Received_pre2_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s2 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s2.pc = (blkPl_334).base + 160#64)
    (hrun : s2.status = .Running)
    (hsp : s2.sp = s0.sp - 1520#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s2.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s2.readReg64 .x26 = s0.sp - 480#64)
    (hx21 : s2.readReg64 .x21 = s0.sp - 1360#64)
    (hx20 : s2.readReg64 .x20 = stA)
    (hx19 : s2.readReg64 .x19 = out)
    (htr : TraceCalleeSaved s2 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s2
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
       ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
       cells (s0.sp - 256#64) 18 ∗
       Rest)
      (fun s3 P3 =>
        (P3 ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
           ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
           ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
          ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
           ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
           ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
           ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
           ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗
          Rest) ∧
        s3.sp = s0.sp - 1520#64 ∧
        s3.readReg64 .x30 = (blkPl_334).base + 252#64 ∧
        s3.readReg64 .x0 = s0.sp - 376#64 ∧
        s3.readReg64 .x1 = s0.sp - 1256#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64 ∧
        s3.readReg64 .x26 = s0.sp - 480#64 ∧
        s3.readReg64 .x20 = epoch ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have h160_48 :
      ((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
      ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
      ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5) ⊢
      memRegion (s0.sp - 160#64) 48 := by
    rw [ProofLib.memRegion_cells (s0.sp - 160#64) 6 (by decide)]
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  rename_i m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17
  refine SepWP.strengthen_entails_const (P₁ :=
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
     ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
     ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
    ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
    (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
     ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
     ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
     ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
     ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
     ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
    (((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
     ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
     ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5)) ∗
    Rest)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h160_48)))) ?_
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Step 3 (`+252 -> +356 -> +1544 -> ret` in Block `334`). -/
theorem states_into_pb_ekSentCt1Received_post_placed [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 dec0 dec1 dec2 dec3 dec4 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (blkPl_334).base + 252#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29_f : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx26_f : sf.readReg64 .x26 = s0.sp - 480#64)
    (hx20_f : sf.readReg64 .x20 = s.uc.epoch)
    (hx19_f : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗
       cells (s0.sp - 480#64) 13 ∗
       cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
        ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
        ((s0.sp - 344#64) ↦₆₄ dec4) ∗
        protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
        memRegion (s0.sp - 1256#64) polyDecoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
        ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
        ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
        ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
        ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 856#64) 376 ∗
       memRegion (s0.sp - 336#64) 32 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 6#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
       memRegion (stA + 104#64) 408 ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
       memRegion (stA + 512#64) 416 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (StatesIntoPbPostPlaced A s0 out stA (.ekSentCt1Received s)) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  rename_i u0 u1 u2 u3 u4 u5
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hstep : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) sf
      ((((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
        ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
        ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
        ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
        ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
        ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
        ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
        ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
        ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
        ((s0.sp - 1368#64) ↦₆₄ w184)) ∗
       (((s0.sp - 480#64) ↦₆₄ c0) ∗ ((s0.sp - 472#64) ↦₆₄ c1) ∗
        ((s0.sp - 464#64) ↦₆₄ c2) ∗ ((s0.sp - 456#64) ↦₆₄ c3) ∗
        ((s0.sp - 448#64) ↦₆₄ c4) ∗ ((s0.sp - 440#64) ↦₆₄ c5) ∗
        ((s0.sp - 432#64) ↦₆₄ c6) ∗ ((s0.sp - 424#64) ↦₆₄ c7) ∗
        ((s0.sp - 416#64) ↦₆₄ c8) ∗ ((s0.sp - 408#64) ↦₆₄ c9) ∗
        ((s0.sp - 400#64) ↦₆₄ c10) ∗ ((s0.sp - 392#64) ↦₆₄ c11) ∗
        ((s0.sp - 384#64) ↦₆₄ c12)) ∗
       (((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
        ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
        ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5)) ∗
       (((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
        ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
        ((s0.sp - 344#64) ↦₆₄ dec4) ∗
        protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
        memRegion (s0.sp - 1256#64) polyDecoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
        ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
        ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
        ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
        ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 856#64) 376 ∗
       memRegion (s0.sp - 336#64) 32 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 6#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
       memRegion (stA + 104#64) 408 ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
       memRegion (stA + 512#64) 416 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            k0 k1 k2 d0 d1 d2
            a1 a2 a3 a4 a5 s.uc.epoch
            dec0 dec1 dec2 dec3 dec4
            w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A k0 k1 k2 s.uc.dk ∗
           vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTablePlacedAt ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x8000000000000004#64 ∧
        s2.readReg64 .x21 = a0 ∧
        TraceCalleeSaved s2 s0) := by
    have hrejoin880 :
        memRegion (s0.sp - 1360#64) 96 ∗
        ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (s0.sp - 1256#64) polyDecoderSize ∗
        memRegion (s0.sp - 856#64) 376 ⊢
        memRegion (s0.sp - 1360#64) 880 := by
      change memRegion (s0.sp - 1360#64) 96 ∗
        ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (s0.sp - 1256#64) 400 ∗
        memRegion (s0.sp - 856#64) 376 ⊢
        memRegion (s0.sp - 1360#64) 880
      rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 96) (k := 784)
            (b' := s0.sp - 1264#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 1264#64) (n := 8) (k := 776)
            (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 1256#64) (n := 400) (k := 376)
            (b' := s0.sp - 856#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
    have hrejoin176 :
        (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
         ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
         ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
         ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
         ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
         ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
         ((s0.sp - 384#64) ↦₆₄ s.uc.epoch) ∗
         ((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
         ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
         ((s0.sp - 344#64) ↦₆₄ dec4)) ∗
        memRegion (s0.sp - 336#64) 32 ⊢
        memRegion (s0.sp - 480#64) 176 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 144) (k := 32)
            (b' := s0.sp - 336#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 480#64) 18 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right k0 (Entails.sepExists_right k1
        (Entails.sepExists_right k2 (Entails.sepExists_right d0
          (Entails.sepExists_right d1 (Entails.sepExists_right d2
            (Entails.sepExists_right a0 (Entails.sepExists_right a1
              (Entails.sepExists_right a2 (Entails.sepExists_right a3
                (Entails.sepExists_right a4 (Entails.sepExists_right a5
                  (Entails.sepExists_right s.uc.epoch (Entails.sepExists_right dec0
                    (Entails.sepExists_right dec1 (Entails.sepExists_right dec2
                      (Entails.sepExists_right dec3 (Entails.sepExists_right dec4
                        (Entails.refl _))))))))))))))))))
    have hrejoin160 :
        (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
         ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
         ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
         ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
         ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
         ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
        memRegion (s0.sp - 160#64) 48 ∗
        memRegion (s0.sp - 112#64) 16 ⊢
        memRegion (s0.sp - 256#64) 160 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 96) (k := 64)
            (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 48) (k := 16)
            (b' := s0.sp - 112#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 256#64) 12 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right k0 (Entails.sepExists_right k1
        (Entails.sepExists_right k2 (Entails.sepExists_right d0
          (Entails.sepExists_right d1 (Entails.sepExists_right d2
            (Entails.sepExists_right a0 (Entails.sepExists_right a1
              (Entails.sepExists_right a2 (Entails.sepExists_right a3
                (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))))))))
    have hstA := stA_ekSentCt1Received_entails_928 stA a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2
    refine SepWP.strengthen_entails_const (P₁ :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        k0 k1 k2 d0 d1 d2
        a1 a2 a3 a4 a5 s.uc.epoch
        dec0 dec1 dec2 dec3 dec4
        w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 96 ∗
       ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1256#64) polyDecoderSize ∗
       memRegion (s0.sp - 856#64) 376) ∗
      ((((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
        ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
        ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
        ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
        ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
        ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
        ((s0.sp - 384#64) ↦₆₄ s.uc.epoch) ∗
        ((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
        ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
        ((s0.sp - 344#64) ↦₆₄ dec4)) ∗
       memRegion (s0.sp - 336#64) 32) ∗
      ((((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
        ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
        ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
        ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
        ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
       ((stA ↦₆₄ 6#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
         ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
         ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
        memRegion (stA + 104#64) 408 ∗
        memRegion (stA + 512#64) 416) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hrejoin880
          (sepConj_mono hrejoin176
            (sepConj_mono hrejoin160
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left hstA)))))))))))) ?_
    dsimp only [epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpcf ⊢
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (Drop.seq_clean hstep fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_)
  have hep := states_into_pb_epilogue_placed (ext := ext) s0 s2 out
    k0 k1 k2 d0 d1 d2
    a1 a2 a3 a4 a5 s.uc.epoch
    dec0 dec1 dec2 dec3 dec4
    w152 w160 w168 w176 w184 0#64 w200 w208 w216
    (protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.dk ∗
     vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  unfold StatesIntoPbPostPlaced
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_ekSentCt1Received A out
    k0 k1 k2 d0 d1 d2 a0 a1 a2 a3 a4 a5 dec0 dec1 dec2 dec3 dec4
    w152 w160 w168 w176 w184 0#64 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000004#64
      k0 k1 k2 d0 d1 d2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      dec0 dec1 dec2 dec3 dec4
      w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
     protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.dk ∗
     vecU8Heap A d0 d1 d2 s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by ac_rfl)) ?_
  exact sepConj_mono_left hout

set_option maxHeartbeats 800000 in
/-- Verifies `<States>::into_pb` (Block `334`) on `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (s : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec A F (.ekSentCt1Received s)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.ekSentCt1Received s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp_placed s0 s0 out stA (.ekSentCt1Received s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkSentCt1Received_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
         ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
         ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
          (stA ↦₆₄ 6#64) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
           ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
           ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
          (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A (stA + 112#64) s.receiving_ct2) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          vecU8Heap A k0 k1 k2 s.uc.dk ∗
          vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
          memRegion (stA + 512#64) 416) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 6#64) ∗
        ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
          ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
          ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
          ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
          ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
          ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
         (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
          polyDecoderAt A (stA + 112#64) s.receiving_ct2) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         vecU8Heap A k0 k1 k2 s.uc.dk ∗
         vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
         memRegion (stA + 512#64) 416 ∗
         memRegion out optProtoInnerStateSize ∗
         statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro a0
    apply Entails.sepExists_elim; intro a1
    apply Entails.sepExists_elim; intro a2
    apply Entails.sepExists_elim; intro a3
    apply Entails.sepExists_elim; intro a4
    apply Entails.sepExists_elim; intro a5
    apply Entails.sepExists_elim; intro k0
    apply Entails.sepExists_elim; intro k1
    apply Entails.sepExists_elim; intro k2
    apply Entails.sepExists_elim; intro d0
    apply Entails.sepExists_elim; intro d1
    apply Entails.sepExists_elim; intro d2
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right k0 (Entails.sepExists_right k1
            (Entails.sepExists_right k2 (Entails.sepExists_right d0
              (Entails.sepExists_right d1 (Entails.sepExists_right d2 ?_)))))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpull ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 =>
    SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
    SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun d0 =>
    SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 => ?_
  have hpro := states_into_pb_prologue_60_placed (ext := ext) s0 out stA 6#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
      ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
      ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
     (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 112#64) s.receiving_ct2) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.dk ∗
     vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP_placed hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  rw [stack_1416_split_ekSentCt1Received s0.sp]
  have hpre1 := states_into_pb_ekSentCt1Received_pre1_placed (ext := ext) s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 504 ∗
     memRegion (s0.sp - 856#64) 376 ∗
     cells (s0.sp - 480#64) 13 ∗
     memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗
     memRegion (s0.sp - 336#64) 32 ∗
     cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 18 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 6#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
      ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
      ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
     (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 112#64) s.receiving_ct2) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.dk ∗
     vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP_placed hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ k0) ∗ ((a + 56#64) ↦₆₄ k1) ∗ ((a + 64#64) ↦₆₄ k2) ∗
    ((a + 72#64) ↦₆₄ d0) ∗ ((a + 80#64) ↦₆₄ d1) ∗ ((a + 88#64) ↦₆₄ d2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (a + 8#64) s.receiving_ct2
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
       ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
       ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 96#64) =
      (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (stA + 112#64) s.receiving_ct2) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 96#64) =
      (((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (s0.sp - 1256#64) s.receiving_ct2) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 96#64 = stA + 104#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_placed hmemcpy_raw
    (k := 96) (m := 408) (n := 504) (off := 96#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words12 a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2)
    (Relocatable.epoch_polyDecoderAt A s.uc.epoch s.receiving_ct2)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 856#64) 376 ∗
      cells (s0.sp - 480#64) 13 ∗
      memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗
      memRegion (s0.sp - 336#64) 32 ∗
      cells (s0.sp - 304#64) 6 ∗
      cells (s0.sp - 256#64) 18 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 6#64) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk ∗
      vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
      memRegion (stA + 512#64) 416 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_ekSentCt1Received_pre2_placed (ext := ext) s0 s3 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A (s0.sp - 1256#64) s.receiving_ct2 ∗
     memRegion (stA + 104#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 856#64) 376 ∗
     cells (s0.sp - 480#64) 13 ∗
     memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗
     memRegion (s0.sp - 336#64) 32 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 6#64) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.dk ∗
     vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP_placed hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4⟩ => ?_)
  refine call_decoderIntoPb_expose_placed hdec_raw (s0.sp - 376#64) (s0.sp - 1256#64) s.receiving_ct2
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗
      cells (s0.sp - 480#64) 13 ∗
      cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
       ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
       ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
       ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
       ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
       ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 96 ∗
      ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 856#64) 376 ∗
      memRegion (s0.sp - 336#64) 32 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 6#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
       ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
       ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
      memRegion (stA + 104#64) 408 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk ∗
      vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
      memRegion (stA + 512#64) 416 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4
    (by ac_rfl)
    fun sf dec0 dec1 dec2 dec3 dec4 hpcf hrunf hspf hcsf htrf => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_ekSentCt1Received_post_placed (ext := ext) A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 dec0 dec1 dec2 dec3 dec4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
