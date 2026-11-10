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
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 3 Placed: Arm 1 (`States.keysSampled`)

Relocatable (`[LibsignalPlacement]`) proof of Arm 1 (`States.keysSampled`, tag `3`,
`+0 -> +60 -> +896 -> +1000 -> +1544 -> ret`) in Block `334`.
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
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_add_lit
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Arm 1: `States.keysSampled` (`+0 -> +60 -> +896 -> +1000 -> +1544 -> ret`) -/

theorem states_into_pb_keysSampled_pre_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_334).base + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 3#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) s1
      (memRegion (s0.sp - 480#64) 96 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       (stA ↦₆₄ 3#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
       ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
       ((stA + 504#64) ↦₆₄ epoch) ∗
       statesIntoPbJumpTablePlacedAt ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
           ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
           ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
           ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
           ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
           ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
           memRegion (s0.sp - 256#64) 160 ∗
           (stA ↦₆₄ 3#64) ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
           ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
           ((stA + 504#64) ↦₆₄ epoch) ∗
           statesIntoPbJumpTablePlacedAt ∗
           Rest)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (blkPl_334).base + 1000#64 ∧
        s2.readReg64 .x0 = s0.sp - 1256#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x27 = s0.sp - 1360#64 ∧
        s2.readReg64 .x21 = epoch ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h160 : memRegion (s0.sp - 256#64) 160 =
      cells (s0.sp - 256#64) 6 ∗ memRegion (s0.sp - 208#64) 112 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 48) (k := 112)
          (b' := s0.sp - 208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 256#64) 6 (by decide)]
  have hrejoin160 :
      (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
       ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
       ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 208#64) 112 ⊢
      memRegion (s0.sp - 256#64) 160 := by
    rw [h160]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  refine SepWP.strengthen_entails_const (P₁ :=
    ((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
    ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
    ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
    ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
    ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
    ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
    ((((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
      ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
      ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
     memRegion (s0.sp - 208#64) 112) ∗
    (stA ↦₆₄ 3#64) ∗
    ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
    ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
    ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
    ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
    ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
    ((stA + 504#64) ↦₆₄ epoch) ∗
    statesIntoPbJumpTablePlacedAt ∗
    Rest)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hrejoin160))))))))))))) ?_
  rw [ProofLib.memRegion_cells (s0.sp - 480#64) 12 (by decide), h160]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_pull_exists
  dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
    BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem states_into_pb_keysSampled_post_placed [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (blkPl_334).base + 1000#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : sf.readReg64 .x27 = s0.sp - 1360#64)
    (hx21 : sf.readReg64 .x21 = s.uc.epoch)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗
       memRegion (s0.sp - 1360#64) 104 ∗
       cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 1256#64) ↦₆₄ e0) ∗ ((s0.sp - 1248#64) ↦₆₄ e1) ∗
        ((s0.sp - 1240#64) ↦₆₄ e2) ∗ ((s0.sp - 1232#64) ↦₆₄ e3) ∗
        ((s0.sp - 1224#64) ↦₆₄ e4) ∗ ((s0.sp - 1216#64) ↦₆₄ e5) ∗
        ((s0.sp - 1208#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       ((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
       ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
       ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
       ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
       ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
       ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
       memRegion (s0.sp - 384#64) 80 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1200#64) 720 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 3#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
       ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
       ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.ek ∗
       vecU8Heap A d0 d1 d2 s.uc.dk ∗
       memRegion (stA + 512#64) 416 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (StatesIntoPbPostPlaced A s0 out stA (.keysSampled s)) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [ProofLib.memRegion_cells (s0.sp - 1360#64) 13 (by decide)]
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
       (((s0.sp - 1360#64) ↦₆₄ c0) ∗ ((s0.sp - 1352#64) ↦₆₄ c1) ∗
        ((s0.sp - 1344#64) ↦₆₄ c2) ∗ ((s0.sp - 1336#64) ↦₆₄ c3) ∗
        ((s0.sp - 1328#64) ↦₆₄ c4) ∗ ((s0.sp - 1320#64) ↦₆₄ c5) ∗
        ((s0.sp - 1312#64) ↦₆₄ c6) ∗ ((s0.sp - 1304#64) ↦₆₄ c7) ∗
        ((s0.sp - 1296#64) ↦₆₄ c8) ∗ ((s0.sp - 1288#64) ↦₆₄ c9) ∗
        ((s0.sp - 1280#64) ↦₆₄ c10) ∗ ((s0.sp - 1272#64) ↦₆₄ c11) ∗
        ((s0.sp - 1264#64) ↦₆₄ c12)) ∗
       (((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
        ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
        ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5)) ∗
       (((s0.sp - 1256#64) ↦₆₄ e0) ∗ ((s0.sp - 1248#64) ↦₆₄ e1) ∗
        ((s0.sp - 1240#64) ↦₆₄ e2) ∗ ((s0.sp - 1232#64) ↦₆₄ e3) ∗
        ((s0.sp - 1224#64) ↦₆₄ e4) ∗ ((s0.sp - 1216#64) ↦₆₄ e5) ∗
        ((s0.sp - 1208#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       ((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
       ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
       ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
       ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
       ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
       ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
       memRegion (s0.sp - 384#64) 80 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1200#64) 720 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 3#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
       ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
       ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.ek ∗
       vecU8Heap A d0 d1 d2 s.uc.dk ∗
       memRegion (stA + 512#64) 416 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            k0 k1 k2 d0 d1 d2
            a1 a2 a3 a4 a5 s.uc.epoch e0 e1
            e2 e3 e4 e5 e6 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A k0 k1 k2 s.uc.ek ∗
           vecU8Heap A d0 d1 d2 s.uc.dk ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTablePlacedAt ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x8000000000000001#64 ∧
        s2.readReg64 .x21 = a0 ∧
        TraceCalleeSaved s2 s0) := by
    have hrejoin880 :
        (((s0.sp - 1360#64) ↦₆₄ k0) ∗ ((s0.sp - 1352#64) ↦₆₄ k1) ∗
         ((s0.sp - 1344#64) ↦₆₄ k2) ∗ ((s0.sp - 1336#64) ↦₆₄ d0) ∗
         ((s0.sp - 1328#64) ↦₆₄ d1) ∗ ((s0.sp - 1320#64) ↦₆₄ d2) ∗
         ((s0.sp - 1312#64) ↦₆₄ a0) ∗ ((s0.sp - 1304#64) ↦₆₄ a1) ∗
         ((s0.sp - 1296#64) ↦₆₄ a2) ∗ ((s0.sp - 1288#64) ↦₆₄ a3) ∗
         ((s0.sp - 1280#64) ↦₆₄ a4) ∗ ((s0.sp - 1272#64) ↦₆₄ a5) ∗
         ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
         ((s0.sp - 1256#64) ↦₆₄ e0) ∗ ((s0.sp - 1248#64) ↦₆₄ e1) ∗
         ((s0.sp - 1240#64) ↦₆₄ e2) ∗ ((s0.sp - 1232#64) ↦₆₄ e3) ∗
         ((s0.sp - 1224#64) ↦₆₄ e4) ∗ ((s0.sp - 1216#64) ↦₆₄ e5) ∗
         ((s0.sp - 1208#64) ↦₆₄ e6)) ∗
        memRegion (s0.sp - 1200#64) 720 ⊢
        memRegion (s0.sp - 1360#64) 880 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 160) (k := 720)
            (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 1360#64) 20 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right k0 (Entails.sepExists_right k1
        (Entails.sepExists_right k2 (Entails.sepExists_right d0
          (Entails.sepExists_right d1 (Entails.sepExists_right d2
            (Entails.sepExists_right a0 (Entails.sepExists_right a1
              (Entails.sepExists_right a2 (Entails.sepExists_right a3
                (Entails.sepExists_right a4 (Entails.sepExists_right a5
                  (Entails.sepExists_right s.uc.epoch (Entails.sepExists_right e0
                    (Entails.sepExists_right e1 (Entails.sepExists_right e2
                      (Entails.sepExists_right e3 (Entails.sepExists_right e4
                        (Entails.sepExists_right e5 (Entails.sepExists_right e6
                          (Entails.refl _))))))))))))))))))))
    have hrejoin176 :
        (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
         ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
         ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
         ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
         ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
         ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5)) ∗
        memRegion (s0.sp - 384#64) 80 ⊢
        memRegion (s0.sp - 480#64) 176 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 96) (k := 80)
            (b' := s0.sp - 384#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 480#64) 12 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right k0 (Entails.sepExists_right k1
        (Entails.sepExists_right k2 (Entails.sepExists_right d0
          (Entails.sepExists_right d1 (Entails.sepExists_right d2
            (Entails.sepExists_right a0 (Entails.sepExists_right a1
              (Entails.sepExists_right a2 (Entails.sepExists_right a3
                (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))))))))
    have hstA := stA_sendEk_enc_entails_928 stA 3#64 a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 s.uc.epoch
    refine SepWP.strengthen_entails_const (P₁ :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        k0 k1 k2 d0 d1 d2
        a1 a2 a3 a4 a5 s.uc.epoch e0 e1
        e2 e3 e4 e5 e6 w168 w176 w184
        0#64 w200 w208 w216 ∗
      ((((s0.sp - 1360#64) ↦₆₄ k0) ∗ ((s0.sp - 1352#64) ↦₆₄ k1) ∗
        ((s0.sp - 1344#64) ↦₆₄ k2) ∗ ((s0.sp - 1336#64) ↦₆₄ d0) ∗
        ((s0.sp - 1328#64) ↦₆₄ d1) ∗ ((s0.sp - 1320#64) ↦₆₄ d2) ∗
        ((s0.sp - 1312#64) ↦₆₄ a0) ∗ ((s0.sp - 1304#64) ↦₆₄ a1) ∗
        ((s0.sp - 1296#64) ↦₆₄ a2) ∗ ((s0.sp - 1288#64) ↦₆₄ a3) ∗
        ((s0.sp - 1280#64) ↦₆₄ a4) ∗ ((s0.sp - 1272#64) ↦₆₄ a5) ∗
        ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
        ((s0.sp - 1256#64) ↦₆₄ e0) ∗ ((s0.sp - 1248#64) ↦₆₄ e1) ∗
        ((s0.sp - 1240#64) ↦₆₄ e2) ∗ ((s0.sp - 1232#64) ↦₆₄ e3) ∗
        ((s0.sp - 1224#64) ↦₆₄ e4) ∗ ((s0.sp - 1216#64) ↦₆₄ e5) ∗
        ((s0.sp - 1208#64) ↦₆₄ e6)) ∗
       memRegion (s0.sp - 1200#64) 720) ∗
      ((((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
        ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
        ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
        ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
        ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
        ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 384#64) 80) ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.ek ∗
       vecU8Heap A d0 d1 d2 s.uc.dk ∗
       ((stA ↦₆₄ 3#64) ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
        ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
        ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (stA + 512#64) 416) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hrejoin880
          (sepConj_mono hrejoin176
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_left hstA)))))))))))) ?_
    dsimp only [epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpcf ⊢
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (Drop.seq_clean hstep fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_)
  have hep := states_into_pb_epilogue_placed (ext := ext) s0 s2 out
    k0 k1 k2 d0 d1 d2
    a1 a2 a3 a4 a5 s.uc.epoch e0 e1
    e2 e3 e4 e5 e6 w168 w176 w184
    0#64 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.ek ∗
     vecU8Heap A d0 d1 d2 s.uc.dk ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  unfold StatesIntoPbPostPlaced
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_keysSampled A out
    k0 k1 k2 d0 d1 d2
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    w168 w176 w184 0#64 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000001#64
      k0 k1 k2 d0 d1 d2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      e0 e1 e2 e3 e4 e5 e6
      w168 w176 w184 0#64 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.ek ∗
     vecU8Heap A d0 d1 d2 s.uc.dk) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by ac_rfl)) ?_
  exact sepConj_mono_left hout

theorem states_into_pb_keysSampled_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec A))
    (s : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec A F (.keysSampled s)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.keysSampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp_placed s0 s0 out stA (.keysSampled s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (chunkedKeysSampled_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
         ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
         ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
          (stA ↦₆₄ 3#64) ∗
          polyEncoderAt A (stA + 8#64) s.sending_hdr ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
          ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
          ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
          ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
          ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          vecU8Heap A k0 k1 k2 s.uc.ek ∗
          vecU8Heap A d0 d1 d2 s.uc.dk ∗
          memRegion (stA + 512#64) 416) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 3#64) ∗
        (polyEncoderAt A (stA + 8#64) s.sending_hdr ∗
         ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
         ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
         ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         vecU8Heap A k0 k1 k2 s.uc.ek ∗
         vecU8Heap A d0 d1 d2 s.uc.dk ∗
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
  have hpro := states_into_pb_prologue_60_placed (ext := ext) s0 out stA 3#64
    (polyEncoderAt A (stA + 8#64) s.sending_hdr ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
     ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
     ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.ek ∗
     vecU8Heap A d0 d1 d2 s.uc.dk ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP_placed hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 104 ∗
      memRegion (s0.sp - 1256#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 1200#64) 720 ∗
      memRegion (s0.sp - 480#64) 96 ∗
      memRegion (s0.sp - 384#64) 80 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    change memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 104 ∗
      memRegion (s0.sp - 1256#64) 56 ∗
      memRegion (s0.sp - 1200#64) 720 ∗
      memRegion (s0.sp - 480#64) 96 ∗
      memRegion (s0.sp - 384#64) 80 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 104) (k := 1160)
          (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1256#64) (n := 56) (k := 1104)
          (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 720) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 96) (k := 288)
          (b' := s0.sp - 384#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 384#64) (n := 80) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  have hpre_step := states_into_pb_keysSampled_pre_placed (ext := ext) s0 s1 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 s.uc.epoch
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 104 ∗
     memRegion (s0.sp - 1256#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 1200#64) 720 ∗
     memRegion (s0.sp - 384#64) 80 ∗
     cells (s0.sp - 304#64) 6 ∗
     statesIntoPbSavedCells s0 ∗
     polyEncoderAt A (stA + 8#64) s.sending_hdr ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.ek ∗
     vecU8Heap A d0 d1 d2 s.uc.dk ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP_placed hpre_step fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  refine call_encoderIntoPb_expose_placed henc_raw (s0.sp - 1256#64) (stA + 8#64) s.sending_hdr
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 (by sep_focus)
    (fun sf e0 e1 e2 e3 e4 e5 e6 hpcf hrunf hspf hcsf htrf => ?_)
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_2
  have hx21_f : sf.readReg64 .x21 = s.uc.epoch := hcsf.2.2.1.trans hx21_2
  have hx27_f : sf.readReg64 .x27 = s0.sp - 1360#64 := hcsf.2.2.2.2.2.2.2.2.1.trans hx27_2
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_keysSampled_post_placed (ext := ext) A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 e0 e1 e2 e3 e4 e5 e6
    hsp0_align hpcf hrunf hspf hx29_f hx27_f hx21_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
