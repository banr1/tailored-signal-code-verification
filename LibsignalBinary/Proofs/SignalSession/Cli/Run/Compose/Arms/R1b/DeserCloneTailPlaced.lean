/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTail
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Relocatable Stage 4b (`opk` Stack Staging and Buffer Deallocations) of Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.DeserCloneTail` (`0x25f4 → 0x27bc`) on
Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

def r1b_opkStage2At (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0e0 w0e4 w9 s2_w9 c9 : BitVec 32)
    (w13 s2_w13 c13 : BitVec 16)
    (w15 w23 s2_w23 c23 : BitVec 64)
    (b31 s2_b31 c31 : BitVec 8) : SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
    ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
    ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
    ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
    memRegion (fsp + 0x1d0#64) 0x18 ∗
    ((fsp + 0x1e8#64) ↦₆₄ c23) ∗
    ((fsp + 0x1f0#64) ↦₈ c31) ∗
    memRegion (fsp + 0x1f1#64) 7 ∗
    ((fsp + 0x1f8#64) ↦₃₂ c9) ∗
    ((fsp + 0x1fc#64) ↦₁₆ c13) ∗
    memRegion (fsp + 0x1fe#64) 2 ∗
    Wire.sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 ∗
    memRegion (fsp + 0x207#64) 0x19 ∗
    ((fsp + 0x220#64) ↦₆₄ w23) ∗
    ((fsp + 0x228#64) ↦₈ b31) ∗
    memRegion (fsp + 0x229#64) 0x37 ∗
    memRegion (fsp + 0x2c0#64) 0x40 ∗
    ((fsp + 0x300#64) ↦₃₂ s2_w9) ∗
    ((fsp + 0x304#64) ↦₁₆ s2_w13) ∗
    memRegion (fsp + 0x306#64) 0x1a ∗
    ((fsp + 0x320#64) ↦₆₄ s2_w23) ∗
    ((fsp + 0x328#64) ↦₈ s2_b31) ∗
    memRegion (fsp + 0x329#64) 0x57 ∗
    Wire.sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 ∗
    memRegion (fsp + 0x387#64) 0x31 ∗
    Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
    memRegion (fsp + 0x3bf#64) 0x19 ∗
    ((fsp + 0x3d8#64) ↦₃₂ w9) ∗
    ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
    memRegion (fsp + 0x3de#64) 0xf2

private theorem r1b_stage1Spk_open_stage2 (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
    ∃∗ s2_b0 : BitVec 8, ∃∗ s2_b1 : BitVec 8, ∃∗ s2_b2 : BitVec 8, ∃∗ s2_b3 : BitVec 8,
    ∃∗ s2_b4 : BitVec 8, ∃∗ s2_b5 : BitVec 8, ∃∗ s2_b6 : BitVec 8,
    ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
    ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
    ∃∗ s2_w9 : BitVec 32, ∃∗ c9 : BitVec 32,
    ∃∗ s2_w13 : BitVec 16, ∃∗ c13 : BitVec 16,
    ∃∗ s2_w23 : BitVec 64, ∃∗ c23 : BitVec 64,
    ∃∗ s2_b31 : BitVec 8, ∃∗ c31 : BitVec 8,
      r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
        b0 b1 b2 b3 b4 b5 b6
        s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
        c0 c1 c2 c3 c4 c5 c6
        w0e0 w0e4 w9 s2_w9 c9 w13 s2_w13 c13 w15 w23 s2_w23 c23 b31 s2_b31 c31 := by
  dsimp only [r1b_opkStage1SpkAt]
  have h1d0 : memRegion (fsp + 0x1d0#64) 0x50 =
      memRegion (fsp + 0x1d0#64) 0x18 ∗
        memRegion (fsp + 0x1e8#64) 8 ∗ memRegion (fsp + 0x1f0#64) 1 ∗
        memRegion (fsp + 0x1f1#64) 7 ∗ memRegion (fsp + 0x1f8#64) 4 ∗
        memRegion (fsp + 0x1fc#64) 2 ∗ memRegion (fsp + 0x1fe#64) 2 ∗
        memRegion (fsp + 0x200#64) 7 ∗ memRegion (fsp + 0x207#64) 0x19 := by
    rw [r1b_split_region fsp 0x1d0 0x18 0x38,
      r1b_split_region fsp 0x1e8 8 0x30,
      r1b_split_region fsp 0x1f0 1 0x2f,
      r1b_split_region fsp 0x1f1 7 0x28,
      r1b_split_region fsp 0x1f8 4 0x24,
      r1b_split_region fsp 0x1fc 2 0x22,
      r1b_split_region fsp 0x1fe 2 0x20,
      r1b_split_region fsp 0x200 7 0x19]
  have h2c0 : memRegion (fsp + 0x2c0#64) 0xf8 =
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 2 ∗
        memRegion (fsp + 0x306#64) 0x1a ∗ memRegion (fsp + 0x320#64) 8 ∗
        memRegion (fsp + 0x328#64) 1 ∗ memRegion (fsp + 0x329#64) 0x57 ∗
        memRegion (fsp + 0x380#64) 7 ∗ memRegion (fsp + 0x387#64) 0x31 := by
    rw [r1b_split_region fsp 0x2c0 0x40 0xb8,
      r1b_split_region fsp 0x300 4 0xb4,
      r1b_split_region fsp 0x304 2 0xb2,
      r1b_split_region fsp 0x306 0x1a 0x98,
      r1b_split_region fsp 0x320 8 0x90,
      r1b_split_region fsp 0x328 1 0x8f,
      r1b_split_region fsp 0x329 0x57 0x38,
      r1b_split_region fsp 0x380 7 0x31]
  rw [h1d0, h2c0,
    ProofLib.memRegion_eight (fsp + 0x1e8#64),
    ProofLib.memRegion_one (fsp + 0x1f0#64),
    ProofLib.memRegion_four (fsp + 0x1f8#64),
    ProofLib.memRegion_two (fsp + 0x1fc#64),
    ProofLib.memRegion_four (fsp + 0x300#64),
    ProofLib.memRegion_two (fsp + 0x304#64),
    ProofLib.memRegion_eight (fsp + 0x320#64),
    ProofLib.memRegion_one (fsp + 0x328#64)]
  refine Entails.trans
    (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (r1b_memRegion7_to_head7 (fsp + 0x200#64))
        (r1b_memRegion7_to_head7 (fsp + 0x380#64))) (by r1b_ac)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s2_b31 =>
    Entails.sepExists_elim fun s2_w23 =>
    Entails.sepExists_elim fun s2_w13 =>
    Entails.sepExists_elim fun s2_w9 =>
    Entails.sepExists_elim fun c13 =>
    Entails.sepExists_elim fun c9 =>
    Entails.sepExists_elim fun c31 =>
    Entails.sepExists_elim fun c23 =>
    Entails.sepExists_elim fun s2_b0 =>
    Entails.sepExists_elim fun s2_b1 =>
    Entails.sepExists_elim fun s2_b2 =>
    Entails.sepExists_elim fun s2_b3 =>
    Entails.sepExists_elim fun s2_b4 =>
    Entails.sepExists_elim fun s2_b5 =>
    Entails.sepExists_elim fun s2_b6 =>
    Entails.sepExists_elim fun c0 =>
    Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun c5 =>
    Entails.sepExists_elim fun c6 => ?_
  refine Entails.sepExists_right s2_b0 (Entails.sepExists_right s2_b1
    (Entails.sepExists_right s2_b2 (Entails.sepExists_right s2_b3
    (Entails.sepExists_right s2_b4 (Entails.sepExists_right s2_b5
    (Entails.sepExists_right s2_b6 (Entails.sepExists_right c0
    (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4
    (Entails.sepExists_right c5 (Entails.sepExists_right c6
    (Entails.sepExists_right s2_w9 (Entails.sepExists_right c9
    (Entails.sepExists_right s2_w13 (Entails.sepExists_right c13
    (Entails.sepExists_right s2_w23 (Entails.sepExists_right c23
    (Entails.sepExists_right s2_b31 (Entails.sepExists_right c31 ?_)))))))))))))))))))))
  dsimp only [r1b_opkStage2At]
  exact Entails.of_eq (by r1b_ac)

private theorem r1b_stage2_close_stage3 (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0e0 w0e4 w9 s2_w9 c9 : BitVec 32)
    (w13 s2_w13 c13 : BitVec 16)
    (w15 w23 s2_w23 c23 : BitVec 64)
    (b31 s2_b31 c31 : BitVec 8) :
    r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6
      s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
      c0 c1 c2 c3 c4 c5 c6
      w0e0 w0e4 w9 s2_w9 c9 w13 s2_w13 c13 w15 w23 s2_w23 c23 b31 s2_b31 c31 ⊢
    r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
      c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 := by
  dsimp only [r1b_opkStage2At, r1b_opkStage3At]
  have h220 :
      ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
        memRegion (fsp + 0x229#64) 0x37 ⊢
        memRegion (fsp + 0x220#64) 0x40 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (r1b_cell8_to_region _ _)) (by r1b_ac)) ?_
    simp only [sepConj_assoc]
    rw [r1b_join_region fsp 0x228 1 0x37, r1b_join_region fsp 0x220 8 0x38]
    exact Entails.of_eq (by r1b_ac)
  have h2c0 :
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        ((fsp + 0x300#64) ↦₃₂ s2_w9) ∗ ((fsp + 0x304#64) ↦₁₆ s2_w13) ∗
        memRegion (fsp + 0x306#64) 0x1a ∗
        ((fsp + 0x320#64) ↦₆₄ s2_w23) ∗ ((fsp + 0x328#64) ↦₈ s2_b31) ∗
        memRegion (fsp + 0x329#64) 0x57 ∗
        Wire.sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 ∗
        memRegion (fsp + 0x387#64) 0x31 ∗
        Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
        memRegion (fsp + 0x3bf#64) 0x19 ∗
        ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
        memRegion (fsp + 0x3de#64) 0xf2 ⊢
        memRegion (fsp + 0x2c0#64) 0x210 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo16_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (r1b_cell8_to_region _ _)
              (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
                (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (pointsTo16_entails_memRegion _ _)))))))) (by r1b_ac)) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 2 ∗
        memRegion (fsp + 0x306#64) 0x1a ∗
        memRegion (fsp + 0x320#64) 8 ∗ memRegion (fsp + 0x328#64) 1 ∗
        memRegion (fsp + 0x329#64) 0x57 ∗
        memRegion (fsp + 0x380#64) 7 ∗ memRegion (fsp + 0x387#64) 0x31 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 by r1b_ac)) ?_
    rw [r1b_join_region fsp 0x3dc 2 0xf2,
      r1b_join_region fsp 0x3d8 4 0xf4,
      r1b_join_region fsp 0x3bf 0x19 0xf8,
      r1b_join_region fsp 0x3b8 7 0x111,
      r1b_join_region fsp 0x387 0x31 0x118,
      r1b_join_region fsp 0x380 7 0x149,
      r1b_join_region fsp 0x329 0x57 0x150,
      r1b_join_region fsp 0x328 1 0x1a7,
      r1b_join_region fsp 0x320 8 0x1a8,
      r1b_join_region fsp 0x306 0x1a 0x1b0,
      r1b_join_region fsp 0x304 2 0x1ca,
      r1b_join_region fsp 0x300 4 0x1cc,
      r1b_join_region fsp 0x2c0 0x40 0x1d0]
    exact Entails.refl _
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono h220 h2c0) (by r1b_ac)

set_option maxHeartbeats 800000 in
/-- Relocatable Stage-2 to Stage-3 copy (`0x2744 → 0x277c`) and buffer deallocations (`0x277c → 0x27bc`). -/
theorem r1b_tail_2744_placed [LibsignalPlacement] {S : RunSem} {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8}
    {c0_in c1_in c2_in c3_in c4_in c5_in c6_in : BitVec 8}
    {w0e0 w0e4 w9 s2_w9 c9_in : BitVec 32}
    {w13 s2_w13 c13_in : BitVec 16}
    {w15 w23 s2_w23 c23_in : BitVec 64}
    {b31 s2_b31 c31_in : BitVec 8}
    {opkFlag kpkId : BitVec 32}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x2744)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64)
    (hx27 : s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ sf : State,
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x27bc →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 →
      sf.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
            s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
            w0e0 w0e4 s2_w9 s2_w13 w15 s2_w23 s2_b31 ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6
          s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
          c0_in c1_in c2_in c3_in c4_in c5_in c6_in
          w0e0 w0e4 w9 s2_w9 c9_in w13 s2_w13 c13_in w15 w23 s2_w23 c23_in b31 s2_b31 c31_in ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 regBs ∗
        ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  intro fsp
  change s.readReg64 (.gpr 24#5) = fsp + 0x380#64 at hx24
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx26; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal380 : (fsp + 0x380#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x380#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal200 : (fsp + 0x200#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x200#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal300 : (fsp + 0x300#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x300#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal304 : (fsp + 0x304#64) &&& 1#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x304#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
  have hal320 : (fsp + 0x320#64) &&& 7#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x320#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
  have hal1f8 : (fsp + 0x1f8#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x1f8#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal1fc : (fsp + 0x1fc#64) &&& 1#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x1fc#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
  have hal1e8 : (fsp + 0x1e8#64) &&& 7#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x1e8#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
  let _ := hal; let _ := hal380; let _ := hal200; let _ := hal300; let _ := hal304
  let _ := hal320; let _ := hal1f8; let _ := hal1fc; let _ := hal1e8
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 0x2744#64 at hpc0
  dsimp only [r1b_opkStage2At, Wire.sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2748) hst.inv
  rw [runPcPlaced_eq]
  have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  have hflip380 :
      ((fsp + 0x380#64) ↦₃₂ (s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0)) ∗
        ((fsp + 0x384#64) ↦₈ s2_b4) ∗ ((fsp + 0x385#64) ↦₈ s2_b5) ∗
        ((fsp + 0x386#64) ↦₈ s2_b6) ⊢
      ((fsp + 0x380#64) ↦₈ s2_b0) ∗ ((fsp + 0x381#64) ↦₈ s2_b1) ∗
        ((fsp + 0x382#64) ↦₈ s2_b2) ∗
        ((fsp + 0x383#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3)) := by
    have heq := Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64)
      s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
    dsimp only [Wire.sevenBytesHeadAt, Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hflip380 (by r1b_ac) ?_
  simp only [sepConj_assoc]
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2758) hinv1
  rw [runPcPlaced_eq]
  have hpc : sm1.pc = (blkPl_579).base + 0x2748#64 := by simp [hsm1, arm64_norm]
  have hrun : sm1.status = .Running := by simp [hsm1, arm64_norm, hst.run]
  have hsp : sm1.sp = fsp := by simpa [hsm1, arm64_norm] using hst.sp
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
    first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx24
  let _ := hx24_1
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  have hw200 : (((((s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0).zeroExtend 64).truncate 32) : BitVec 32)) =
      (s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0) := by bv_bits
  let _ := hw200
  set_option linter.unusedSimpArgs false in
  try simp only [hsm1, arm64_norm, hw200]
  have hflip200 :
      ((fsp + 0x200#64) ↦₃₂ (s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0)) ∗
        ((fsp + 0x204#64) ↦₈ c4_in) ∗ ((fsp + 0x205#64) ↦₈ c5_in) ∗
        ((fsp + 0x206#64) ↦₈ c6_in) ⊢
      ((fsp + 0x200#64) ↦₈ s2_b0) ∗ ((fsp + 0x201#64) ↦₈ s2_b1) ∗
        ((fsp + 0x202#64) ↦₈ s2_b2) ∗
        ((fsp + 0x203#64) ↦₃₂ (c6_in ++ c5_in ++ c4_in ++ s2_b3)) := by
    have heq := Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x200#64)
      s2_b0 s2_b1 s2_b2 s2_b3 c4_in c5_in c6_in
    dsimp only [Wire.sevenBytesHeadAt, Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hflip200 (by r1b_ac) ?_
  simp only [sepConj_assoc]
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x277c) hinv2
  rw [runPcPlaced_eq]
  have hpc : sm2.pc = (blkPl_579).base + 0x2758#64 := by simp [hsm2, hsm1, arm64_norm]
  have hrun : sm2.status = .Running := by simp [hsm2, arm64_norm, hst.run]
  have hsp : sm2.sp = fsp := by simpa [hsm2, hsm1, arm64_norm] using hst.sp
  have hx11_2 : sm2.readReg64 (.gpr 11#5) = fsp + 0x104#64 := by
    simp [hsm2, hsm1, arm64_norm]
  let _ := hx11_2
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
  have hw203 : (((((s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3).zeroExtend 64).truncate 32) : BitVec 32)) =
      (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3) := by bv_bits
  have hw1fc_a : (((s2_w13.zeroExtend 64).truncate 16) : BitVec 16) = s2_w13 := by bv_bits
  have hw1fc_b : ((((s2_w13.zeroExtend 32).zeroExtend 64).truncate 16) : BitVec 16) = s2_w13 := by bv_bits
  have hw1f0_a : (((s2_b31.zeroExtend 64).truncate 8) : BitVec 8) = s2_b31 := by bv_bits
  have hw1f0_b : ((((s2_b31.zeroExtend 32).zeroExtend 64).truncate 8) : BitVec 8) = s2_b31 := by bv_bits
  have hw1f8 : (((s2_w9.zeroExtend 64).truncate 32) : BitVec 32) = s2_w9 := by bv_bits
  let _ := hw203; let _ := hw1fc_a; let _ := hw1fc_b
  let _ := hw1f0_a; let _ := hw1f0_b; let _ := hw1f8
  set_option linter.unusedSimpArgs false in
  try simp only [hsm2, hsm1, arm64_norm, hw203, hw1fc_a, hw1fc_b, hw1f0_a, hw1f0_b, hw1f8]
  have hback200 :
      ((fsp + 0x200#64) ↦₈ s2_b0) ∗ ((fsp + 0x201#64) ↦₈ s2_b1) ∗
        ((fsp + 0x202#64) ↦₈ s2_b2) ∗
        ((fsp + 0x203#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3)) ⊢
      Wire.sevenBytesHeadAt (fsp + 0x200#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 := by
    have heq := (Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x200#64)
      s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6).symm
    dsimp only [Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  have hback380 :
      ((fsp + 0x380#64) ↦₈ s2_b0) ∗ ((fsp + 0x381#64) ↦₈ s2_b1) ∗
        ((fsp + 0x382#64) ↦₈ s2_b2) ∗
        ((fsp + 0x383#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3)) ⊢
      Wire.sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 := by
    have heq := (Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64)
      s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6).symm
    dsimp only [Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  have hback3b8 :
      ((fsp + 0x3b8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((fsp + 0x3bc#64) ↦₈ b4) ∗ ((fsp + 0x3bd#64) ↦₈ b5) ∗
        ((fsp + 0x3be#64) ↦₈ b6) ⊢
      Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 := by
    dsimp only [Wire.sevenBytesHeadAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac)
    (sepConj_mono hback200 (sepConj_mono hback380 hback3b8)) (by r1b_ac) ?_
  have hclose_s3 := r1b_stage2_close_stage3 fsp spkW0 spkW8 spkW16 spkW24
    b0 b1 b2 b3 b4 b5 b6
    s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
    s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
    w0e0 w0e4 w9 s2_w9 s2_w9 w13 s2_w13 s2_w13 w15 w23 s2_w23 s2_w23 b31 s2_b31 s2_b31
  dsimp only [r1b_opkStage2At] at hclose_s3
  refine r1b_sepWPp_frame (by r1b_ac) hclose_s3 (by r1b_ac) ?_
  generalize hS3 : r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
    s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 w0e0 w0e4 s2_w9 s2_w13 w15 s2_w23 s2_b31 = stage3
  have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm3 0x277c := hok.of_step
    { pc := by rw [runPcPlaced_eq]; simp [hsm3, hsm2, hsm1, arm64_norm]
      run := by simp [hsm3, hsm2, hsm1, arm64_norm, hst.run]
      sp := by simpa [hsm3, hsm2, hsm1, arm64_norm] using hst.sp
      fp := by simpa [hsm3, hsm2, hsm1, arm64_norm] using hst.fp
      inv := hinv3
      vregs := by simpa [calleeSavedVRegs, hsm3, hsm2, hsm1, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
    (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
    (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
  have hsm3_run : sm3.status = .Running := hok3.st.run
  have hsm3_sp : sm3.sp = fsp := hok3.st.sp
  let _ := hsm3_run; let _ := hsm3_sp
  have hx8_3 : sm3.readReg64 (.gpr 8#5) = kpkCap := by simp [hsm3, hsm2, hsm1, arm64_norm]
  have hx23_3 : sm3.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 := by
    first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx23
  have hx25_3 : sm3.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 := by
    first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx25
  have hx26_3 : sm3.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 := by
    first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx26
  have hx27_3 : sm3.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 := by
    first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx27
  have hx28_3 : sm3.readReg64 (.gpr 28#5) = 64#64 := by
    first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx28
  let _ := hx8_3; let _ := hx23_3; let _ := hx25_3; let _ := hx26_3; let _ := hx27_3; let _ := hx28_3
  have hpc3 : sm3.pc = (blkPl_579).base + 0x277c#64 := by simp [hsm3, hsm2, hsm1, arm64_norm]
  clear hsm3 hsm2 hsm1
  suffices h2790 : ∀ sf4 : State,
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf4 0x2790 →
      sf4.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf4.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf4.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf4.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
      sf4.readReg64 (.gpr 28#5) = 64#64 →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf4
        (stage3 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 regBs ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0) by
    by_cases hkpk0 : kpkCap = 0#64
    · subst hkpk0
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2790) hinv3
      rw [runPcPlaced_eq]
      have hpc := hpc3
      have hrun := hok3.st.run; have hsp : sm3.sp = fsp := hok3.st.sp
      (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
      have hcap0 := r1b_ownedBytes_cap0_emp A kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs
      refine r1b_sepWPp_frame (by r1b_ac) hcap0 (by r1b_ac) ?_
      exact h2790 sm4
        (hok3.of_step
          { pc := by rw [runPcPlaced_eq]; simp [hsm4, arm64_norm]
            run := by simp [hsm4, arm64_norm, hok3.st.run]
            sp := by simpa [hsm4, arm64_norm] using hok3.st.sp
            fp := by simpa [hsm4, arm64_norm] using hok3.st.fp
            inv := hinv4
            vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hok3.st.vregs
            spAligned := hst.spAligned }
          (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
          (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
          (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm]))
        (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx23_3)
        (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx25_3)
        (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx26_3)
        (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx27_3)
        (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx28_3)
    · have hbeq : (kpkCap == 0#64) = false := beq_false_of_ne hkpk0
      let _ := hbeq
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
        (mid := lsρ lsRustDeallocSymCli) hinv3
      have hpc := hpc3
      have hrun := hok3.st.run; have hsp : sm3.sp = fsp := hok3.st.sp
      (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_call_frame <|
        r1b_call_dealloc_ownedBytes_placed (cap := kpkCap) (ptr := kpkPtr)
          (len := BitVec.ofNat 64 kpkBs.length) (bs := kpkBs)
          hh hbnd hinv4
          (by simp [hsm4, arm64_norm])
          (by simp [hsm4, arm64_norm, hok3.st.run])
          (by simpa [hsm4, arm64_norm] using hok3.st.sp)
          (by simpa [hsm4, arm64_norm] using hok3.st.fp)
          (by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hok3.st.vregs)
          hst.spAligned (retOff := 0x2790)
          (by rw [runPcPlaced_eq]; simp [hsm4, arm64_norm])
          (by simp [hsm4, arm64_norm])
          (by simp [hsm4, arm64_norm])
          (by simp [hsm4, arm64_norm])
          hkpk0 hpanic (fun sf4 hin4 hcs4 hfs4 htr4 => ?_)
      exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
        (h2790 sf4
          (hok3.after_call
            (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
            (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
            (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
            hin4 hcs4 (congrArg FsState.files hfs4) htr4)
          (hcs4.2.2.2.2.1.trans (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx23_3))
          (hcs4.2.2.2.2.2.2.1.trans (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx25_3))
          (hcs4.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx26_3))
          (hcs4.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx27_3))
          (hcs4.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm4, arm64_norm]; done) | simpa [hsm4, arm64_norm] using hx28_3)))
  intro sf4 hok4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4
  have hsf4_run : sf4.status = .Running := hok4.st.run
  have hsf4_sp : sf4.sp = fsp := hok4.st.sp
  let _ := hsf4_run; let _ := hsf4_sp
  let _ := hx23_4; let _ := hx25_4; let _ := hx26_4; let _ := hx27_4; let _ := hx28_4
  suffices h27a4 : ∀ sf5 : State,
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf5 0x27a4 →
      sf5.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf5.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf5.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf5.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
      sf5.readReg64 (.gpr 28#5) = 64#64 →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf5
        (stage3 ∗
          ownedBytes A regCap regPtr 4#64 regBs ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0) by
    have hpc4 := hok4.st.pc
    change sf4.pc = (blkPl_579).base + 0x2790#64 at hpc4
    by_cases hspk0 : spkCap = 0#64
    · subst hspk0
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x27a4) hok4.st.inv
      rw [runPcPlaced_eq]
      have hpc := hpc4; have hrun := hok4.st.run; have hsp : sf4.sp = fsp := hok4.st.sp
      (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => ?_
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hcap0 := r1b_ownedBytes_cap0_emp A spkPtr (BitVec.ofNat 64 spkBs.length) spkBs
      refine r1b_sepWPp_frame (by r1b_ac) hcap0 (by r1b_ac) ?_
      exact h27a4 sm5
        (hok4.of_step
          { pc := by rw [runPcPlaced_eq]; simp [hsm5, arm64_norm]
            run := by simp [hsm5, arm64_norm, hok4.st.run]
            sp := by simpa [hsm5, arm64_norm] using hok4.st.sp
            fp := by simpa [hsm5, arm64_norm] using hok4.st.fp
            inv := hinv5
            vregs := by simpa [calleeSavedVRegs, hsm5, arm64_norm] using hok4.st.vregs
            spAligned := hst.spAligned }
          (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
          (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
          (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm]))
        (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx23_4)
        (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx25_4)
        (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx26_4)
        (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx27_4)
        (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx28_4)
    · have hbeq : (spkCap == 0#64) = false := beq_false_of_ne hspk0
      let _ := hbeq
      apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
        (mid := lsρ lsRustDeallocSymCli) hok4.st.inv
      have hpc := hpc4; have hrun := hok4.st.run; have hsp : sf4.sp = fsp := hok4.st.sp
      (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => ?_
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_call_frame <|
        r1b_call_dealloc_ownedBytes_placed (cap := spkCap) (ptr := spkPtr)
          (len := BitVec.ofNat 64 spkBs.length) (bs := spkBs)
          hh hbnd hinv5
          (by simp [hsm5, arm64_norm])
          (by simp [hsm5, arm64_norm, hok4.st.run])
          (by simpa [hsm5, arm64_norm] using hok4.st.sp)
          (by simpa [hsm5, arm64_norm] using hok4.st.fp)
          (by simpa [calleeSavedVRegs, hsm5, arm64_norm] using hok4.st.vregs)
          hst.spAligned (retOff := 0x27a4)
          (by rw [runPcPlaced_eq]; simp [hsm5, arm64_norm])
          (by simp [hsm5, arm64_norm])
          (by simp [hsm5, arm64_norm])
          (by simp [hsm5, arm64_norm])
          hspk0 hpanic (fun sf5 hin5 hcs5 hfs5 htr5 => ?_)
      exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
        (h27a4 sf5
          (hok4.after_call
            (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
            (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
            (by simp [hsm5, arm64_norm]) (by simp [hsm5, arm64_norm])
            hin5 hcs5 (congrArg FsState.files hfs5) htr5)
          (hcs5.2.2.2.2.1.trans (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx23_4))
          (hcs5.2.2.2.2.2.2.1.trans (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx25_4))
          (hcs5.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx26_4))
          (hcs5.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx27_4))
          (hcs5.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm5, arm64_norm]; done) | simpa [hsm5, arm64_norm] using hx28_4)))
  intro sf5 hok5 hx23_5 hx25_5 hx26_5 hx27_5 hx28_5
  have hsf5_run : sf5.status = .Running := hok5.st.run
  have hsf5_sp : sf5.sp = fsp := hok5.st.sp
  let _ := hsf5_run; let _ := hsf5_sp
  let _ := hx23_5; let _ := hx25_5; let _ := hx26_5; let _ := hx27_5; let _ := hx28_5
  have hpc5 := hok5.st.pc
  change sf5.pc = (blkPl_579).base + 0x27a4#64 at hpc5
  by_cases hreg0 : regCap = 0#64
  · subst hreg0
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x27bc) hok5.st.inv
    rw [runPcPlaced_eq]
    have hpc := hpc5; have hrun := hok5.st.run; have hsp : sf5.sp = fsp := hok5.st.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm6 hsm6 hinv6 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hcap0 := r1b_ownedBytes_cap0_emp A regPtr 4#64 regBs
    refine r1b_sepWPp_frame (by r1b_ac) hcap0 (by r1b_ac) ?_
    refine MainHops.sepWPp_weaken_pre (Entails.of_eq (by rw [← hS3]; try r1b_ac))
      (hk sm6
        (hok5.of_step
          { pc := by rw [runPcPlaced_eq]; simp [hsm6, arm64_norm]
            run := by simp [hsm6, arm64_norm, hok5.st.run]
            sp := by simpa [hsm6, arm64_norm] using hok5.st.sp
            fp := by simpa [hsm6, arm64_norm] using hok5.st.fp
            inv := hinv6
            vregs := by simpa [calleeSavedVRegs, hsm6, arm64_norm] using hok5.st.vregs
            spAligned := hst.spAligned }
          (by simp [hsm6, arm64_norm]) (by simp [hsm6, arm64_norm])
          (by simp [hsm6, arm64_norm]) (by simp [hsm6, arm64_norm])
          (by simp [hsm6, arm64_norm]) (by simp [hsm6, arm64_norm]))
        (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx23_5)
        (by simp only [hsm6, arm64_norm])
        (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx25_5)
        (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx26_5)
        (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx28_5))
  · have hbeq : (regCap == 0#64) = false := beq_false_of_ne hreg0
    let _ := hbeq
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
      (mid := lsρ lsRustDeallocSymCli) hok5.st.inv
    have hpc := hpc5; have hrun := hok5.st.run; have hsp : sf5.sp = fsp := hok5.st.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm6 hsm6 hinv6 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hx24_6 : sm6.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 := by
      simp only [hsm6, arm64_norm]
    refine r1b_call_frame <|
      r1b_call_dealloc_ownedBytes_placed (cap := regCap) (ptr := regPtr) (len := 4#64) (bs := regBs)
        hh hbnd hinv6
        (by simp [hsm6, arm64_norm])
        (by simp [hsm6, arm64_norm, hok5.st.run])
        (by simpa [hsm6, arm64_norm] using hok5.st.sp)
        (by simpa [hsm6, arm64_norm] using hok5.st.fp)
        (by simpa [calleeSavedVRegs, hsm6, arm64_norm] using hok5.st.vregs)
        hst.spAligned (retOff := 0x27bc)
        (by rw [runPcPlaced_eq]; simp [hsm6, arm64_norm])
        (by simp [hsm6, arm64_norm])
        (by simp [hsm6, arm64_norm])
        (by simp [hsm6, arm64_norm])
        hreg0 hpanic (fun sf6 hin6 hcs6 hfs6 htr6 => ?_)
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by rw [← hS3]; try r1b_ac))
      (hk sf6
        (hok5.after_call
          (by simp [hsm6, arm64_norm]) (by simp [hsm6, arm64_norm])
          (by simp [hsm6, arm64_norm]) (by simp [hsm6, arm64_norm])
          (by simp [hsm6, arm64_norm]) (by simp [hsm6, arm64_norm])
          hin6 hcs6 (congrArg FsState.files hfs6) htr6)
        (hcs6.2.2.2.2.1.trans (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx23_5))
        (hcs6.2.2.2.2.2.1.trans hx24_6)
        (hcs6.2.2.2.2.2.2.1.trans (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx25_5))
        (hcs6.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx26_5))
        (hcs6.2.2.2.2.2.2.2.2.2.1.trans (by first | (simp [hsm6, arm64_norm]; done) | simpa [hsm6, arm64_norm] using hx28_5)))

set_option maxHeartbeats 800000 in
/-- Relocatable Stage 4b step (`0x25f4 → 0x27bc`): stages `opk` into Stage-3 stack slots and frees `kpkBs`, `spkBs`, and `regBs`. -/
theorem r1b_step_tail_25f4_placed [LibsignalPlacement] {S : RunSem} {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {kpkId v11c : BitVec 32}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {opk : Option (BitVec 32 × PublicKey)}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x25f4)
    (hopk_sem : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
        splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
        v11c = opkId ∧
        opkPk.bytes.toList = Wire.pkBytesOf b0 b1 b2 b3 b4 b5 b6
          (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31))
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ (sf : State)
        (c0 c1 c2 c3 c4 c5 c6 : BitVec 8) (c9 : BitVec 32) (c13 : BitVec 16)
        (c23 : BitVec 64) (c31 : BitVec 8),
      let opkFlag : BitVec 32 := if opk.isSome then 1#32 else 0#32
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x27bc →
      (∀ p, opk = some p → v11c = p.1 ∧
        p.2.bytes.toList = Wire.pkBytesOf c0 c1 c2 c3 c4 c5 c6
          (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 →
      sf.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
            c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 regBs ∗
        ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  intro fsp
  change s.readReg64 (.gpr 24#5) = fsp + 0x380#64 at hx24
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  let _ := hal
  refine r1b_sepWPp_frame (by r1b_ac)
    (r1b_stage1Spk_open_stage2 fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun s2_b0 => SepWPp.exists_elim fun s2_b1 =>
    SepWPp.exists_elim fun s2_b2 => SepWPp.exists_elim fun s2_b3 =>
    SepWPp.exists_elim fun s2_b4 => SepWPp.exists_elim fun s2_b5 =>
    SepWPp.exists_elim fun s2_b6 =>
    SepWPp.exists_elim fun c0_in => SepWPp.exists_elim fun c1_in =>
    SepWPp.exists_elim fun c2_in => SepWPp.exists_elim fun c3_in =>
    SepWPp.exists_elim fun c4_in => SepWPp.exists_elim fun c5_in =>
    SepWPp.exists_elim fun c6_in =>
    SepWPp.exists_elim fun s2_w9 => SepWPp.exists_elim fun c9_in =>
    SepWPp.exists_elim fun s2_w13 => SepWPp.exists_elim fun c13_in =>
    SepWPp.exists_elim fun s2_w23 => SepWPp.exists_elim fun c23_in =>
    SepWPp.exists_elim fun s2_b31 => SepWPp.exists_elim fun c31_in => ?_
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 0x25f4#64 at hpc0
  rcases hopk_sem with ⟨rfl, rfl⟩ |
      ⟨_opkId, _opkKey, _opkPk, _hne_nil, h63, hsp_o, _hd_o, rfl, hv11c, hbytes⟩
  ·
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2744) hst.inv
    rw [runPcPlaced_eq]
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    exact r1b_tail_2744_placed (opkFlag := 0#32) hh hbnd
      (hok.of_step
        { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
          run := by simp [hsm, arm64_norm, hst.run]
          sp := by simpa [hsm, arm64_norm] using hst.sp
          fp := by simpa [hsm, arm64_norm] using hst.fp
          inv := hinv_m
          vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
          spAligned := hst.spAligned }
        (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]))
      (by first | (simp [hsm, arm64_norm]; done) | simpa [hsm, arm64_norm] using hx23)
      (by change _ = fsp + 0x380#64; first | (simp [hsm, arm64_norm]; done) | simpa [hsm, arm64_norm] using hx24)
      (by first | (simp [hsm, arm64_norm]; done) | simpa [hsm, arm64_norm] using hx25)
      (by simp [hsm, arm64_norm])
      (by first | (simp [hsm, arm64_norm]; done) | simpa [hsm, arm64_norm] using hx27)
      (by first | (simp [hsm, arm64_norm]; done) | simpa [hsm, arm64_norm] using hx28)
      hpanic fun sf hok_f hx23_f hx24_f hx25_f hx26_f hx28_f =>
        hk sf s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 s2_w9 s2_w13 s2_w23 s2_b31
          hok_f (fun _ hp => by cases hp) hx23_f hx24_f hx25_f hx26_f hx28_f
  ·
    have h4len : 4 ≤ opkBs.length := by
      have ⟨_, _, hlen_o⟩ := r1b_splitId_bytes hsp_o; omega
    have hne0 : (BitVec.ofNat 64 opkBs.length == 0#64) = false := by
      apply beq_false_of_ne
      intro heq
      have hn : (BitVec.ofNat 64 opkBs.length).toNat = 0 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at hn
      omega
    have hal3b8 : (fsp + 0x3b8#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x3b8#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal380 : (fsp + 0x380#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x380#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal3d8 : (fsp + 0x3d8#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x3d8#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal3dc : (fsp + 0x3dc#64) &&& 1#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x3dc#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
    have hal220 : (fsp + 0x220#64) &&& 7#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x220#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
    have hal300 : (fsp + 0x300#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x300#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal304 : (fsp + 0x304#64) &&& 1#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x304#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
    have hal320 : (fsp + 0x320#64) &&& 7#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x320#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
    let _ := hne0
    let _ := hal3b8; let _ := hal380; let _ := hal3d8; let _ := hal3dc
    let _ := hal220; let _ := hal300; let _ := hal304; let _ := hal320
    dsimp only [r1b_opkStage2At, Wire.sevenBytesHeadAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x25fc) hst.inv
    rw [runPcPlaced_eq]
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
    have hflip3b8 :
        ((fsp + 0x3b8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((fsp + 0x3bc#64) ↦₈ b4) ∗ ((fsp + 0x3bd#64) ↦₈ b5) ∗
          ((fsp + 0x3be#64) ↦₈ b6) ⊢
        ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
          ((fsp + 0x3ba#64) ↦₈ b2) ∗
          ((fsp + 0x3bb#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) := by
      have heq := Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6
      dsimp only [Wire.sevenBytesHeadAt, Wire.sevenBytesTailAt] at heq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
      rw [heq]; exact Entails.refl _
    refine r1b_sepWPp_frame (by r1b_ac) hflip3b8 (by r1b_ac) ?_
    simp only [sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2610) hinv1
    rw [runPcPlaced_eq]
    have hpc : sm1.pc = (blkPl_579).base + 0x25fc#64 := by simp [hsm1, arm64_norm]
    have hrun : sm1.status = .Running := by simp [hsm1, arm64_norm, hst.run]
    have hsp : sm1.sp = fsp := by simpa [hsm1, arm64_norm] using hst.sp
    have hx24_1 : sm1.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
      first | (simp [hsm1, arm64_norm]; done) | simpa [hsm1, arm64_norm] using hx24
    let _ := hx24_1
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
    have hw380 : (((((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).truncate 32) : BitVec 32)) =
        (b3 ++ b2 ++ b1 ++ b0) := by bv_bits
    let _ := hw380
    try simp only [hsm1, arm64_norm, hw380]
    have hflip380 :
        ((fsp + 0x380#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((fsp + 0x384#64) ↦₈ s2_b4) ∗ ((fsp + 0x385#64) ↦₈ s2_b5) ∗
          ((fsp + 0x386#64) ↦₈ s2_b6) ⊢
        ((fsp + 0x380#64) ↦₈ b0) ∗ ((fsp + 0x381#64) ↦₈ b1) ∗
          ((fsp + 0x382#64) ↦₈ b2) ∗
          ((fsp + 0x383#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ b3)) := by
      have heq := Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64)
        b0 b1 b2 b3 s2_b4 s2_b5 s2_b6
      dsimp only [Wire.sevenBytesHeadAt, Wire.sevenBytesTailAt] at heq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
      rw [heq]; exact Entails.refl _
    refine r1b_sepWPp_frame (by r1b_ac) hflip380 (by r1b_ac) ?_
    simp only [sepConj_assoc]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2744) hinv2
    rw [runPcPlaced_eq]
    have hpc : sm2.pc = (blkPl_579).base + 0x2610#64 := by simp [hsm2, hsm1, arm64_norm]
    have hrun : sm2.status = .Running := by simp [hsm2, hsm1, arm64_norm, hst.run]
    have hsp : sm2.sp = fsp := by simpa [hsm2, hsm1, arm64_norm] using hst.sp
    have hx24_2 : sm2.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
      first | (simp [hsm2, hsm1, arm64_norm]; done) | simpa [hsm2, hsm1, arm64_norm] using hx24
    let _ := hx24_2
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hw383 : (((((b6 ++ b5 ++ b4 ++ b3).zeroExtend 64).truncate 32) : BitVec 32)) =
        (b6 ++ b5 ++ b4 ++ b3) := by bv_bits
    have hw304_a : (((w13.zeroExtend 64).truncate 16) : BitVec 16) = w13 := by bv_bits
    have hw304_b : ((((w13.zeroExtend 32).zeroExtend 64).truncate 16) : BitVec 16) = w13 := by bv_bits
    have hw300 : (((w9.zeroExtend 64).truncate 32) : BitVec 32) = w9 := by bv_bits
    have hw328_a : (((b31.zeroExtend 64).truncate 8) : BitVec 8) = b31 := by bv_bits
    have hw328_b : ((((b31.zeroExtend 32).zeroExtend 64).truncate 8) : BitVec 8) = b31 := by bv_bits
    let _ := hw383; let _ := hw304_a; let _ := hw304_b
    let _ := hw300; let _ := hw328_a; let _ := hw328_b
    try simp only [hsm2, hsm1, arm64_norm, hw383, hw304_a, hw304_b, hw300, hw328_a, hw328_b]
    have hback380 :
        ((fsp + 0x380#64) ↦₈ b0) ∗ ((fsp + 0x381#64) ↦₈ b1) ∗
          ((fsp + 0x382#64) ↦₈ b2) ∗
          ((fsp + 0x383#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
        Wire.sevenBytesHeadAt (fsp + 0x380#64) b0 b1 b2 b3 b4 b5 b6 := by
      have heq := (Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64) b0 b1 b2 b3 b4 b5 b6).symm
      dsimp only [Wire.sevenBytesTailAt] at heq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
      rw [heq]; exact Entails.refl _
    have hback3b8 :
        ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
          ((fsp + 0x3ba#64) ↦₈ b2) ∗
          ((fsp + 0x3bb#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
        Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 := by
      have heq := (Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6).symm
      dsimp only [Wire.sevenBytesTailAt] at heq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
      rw [heq]; exact Entails.refl _
    have hback200 :
        ((fsp + 0x200#64) ↦₃₂ (c3_in ++ c2_in ++ c1_in ++ c0_in)) ∗
          ((fsp + 0x204#64) ↦₈ c4_in) ∗ ((fsp + 0x205#64) ↦₈ c5_in) ∗
          ((fsp + 0x206#64) ↦₈ c6_in) ⊢
        Wire.sevenBytesHeadAt (fsp + 0x200#64) c0_in c1_in c2_in c3_in c4_in c5_in c6_in := by
      dsimp only [Wire.sevenBytesHeadAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.refl _
    refine r1b_sepWPp_frame (by r1b_ac)
      (sepConj_mono hback380 (sepConj_mono hback3b8 hback200)) (by r1b_ac) ?_
    have hfold :
        (memRegion fsp 0x0e0 ∗
          ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
          ((fsp + 0x0e8#64) ↦₆₄ w15) ∗ ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
          ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗ ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
          ((fsp + 0x108#64) ↦₆₄ spkW0) ∗ memRegion (fsp + 0x1d0#64) 0x18 ∗
          ((fsp + 0x1e8#64) ↦₆₄ c23_in) ∗ ((fsp + 0x1f0#64) ↦₈ c31_in) ∗
          memRegion (fsp + 0x1f1#64) 7 ∗ ((fsp + 0x1f8#64) ↦₃₂ c9_in) ∗
          ((fsp + 0x1fc#64) ↦₁₆ c13_in) ∗ memRegion (fsp + 0x1fe#64) 2 ∗
          Wire.sevenBytesHeadAt (fsp + 0x200#64) c0_in c1_in c2_in c3_in c4_in c5_in c6_in ∗
          memRegion (fsp + 0x207#64) 0x19 ∗
          ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
          memRegion (fsp + 0x229#64) 0x37 ∗ memRegion (fsp + 0x2c0#64) 0x40 ∗
          ((fsp + 0x300#64) ↦₃₂ w9) ∗ ((fsp + 0x304#64) ↦₁₆ w13) ∗
          memRegion (fsp + 0x306#64) 0x1a ∗
          ((fsp + 0x320#64) ↦₆₄ w23) ∗ ((fsp + 0x328#64) ↦₈ b31) ∗
          memRegion (fsp + 0x329#64) 0x57 ∗
          Wire.sevenBytesHeadAt (fsp + 0x380#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (fsp + 0x387#64) 0x31 ∗
          Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (fsp + 0x3bf#64) 0x19 ∗
          ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
          memRegion (fsp + 0x3de#64) 0xf2) ⊢
        r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6
          b0 b1 b2 b3 b4 b5 b6
          c0_in c1_in c2_in c3_in c4_in c5_in c6_in
          w0e0 w0e4 w9 w9 c9_in w13 w13 c13_in w15 w23 w23 c23_in b31 b31 c31_in := by
      dsimp only [r1b_opkStage2At]; exact Entails.of_eq (by r1b_ac)
    refine r1b_sepWPp_frame (by r1b_ac) hfold (by r1b_ac) ?_
    exact r1b_tail_2744_placed (opkFlag := 1#32) hh hbnd
      (hok.of_step
        { pc := by rw [runPcPlaced_eq]; simp [hsm3, hsm2, hsm1, arm64_norm]
          run := by simp [hsm3, hsm2, hsm1, arm64_norm, hst.run]
          sp := by simpa [hsm3, hsm2, hsm1, arm64_norm] using hst.sp
          fp := by simpa [hsm3, hsm2, hsm1, arm64_norm] using hst.fp
          inv := hinv3
          vregs := by simpa [calleeSavedVRegs, hsm3, hsm2, hsm1, arm64_norm] using hst.vregs
          spAligned := hst.spAligned }
        (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
        (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
        (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm]))
      (by first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx23)
      (by change _ = fsp + 0x380#64; first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx24)
      (by simp [hsm3, hsm2, hsm1, arm64_norm])
      (by simp [hsm3, hsm2, hsm1, arm64_norm])
      (by first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx27)
      (by first | (simp [hsm3, hsm2, hsm1, arm64_norm]; done) | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx28)
      hpanic fun sf hok_f hx23_f hx24_f hx25_f hx26_f hx28_f =>
        hk sf b0 b1 b2 b3 b4 b5 b6 w9 w13 w23 b31 hok_f
          (fun p hp => by
            injection hp with hp'
            subst hp'
            exact ⟨hv11c, hbytes⟩)
          hx23_f hx24_f hx25_f hx26_f hx28_f

end CryptoVerification.SignalSession.Cli.RunCompose
