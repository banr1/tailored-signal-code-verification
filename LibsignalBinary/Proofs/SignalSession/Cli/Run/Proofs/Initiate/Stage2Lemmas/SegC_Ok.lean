/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Fetch
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 2 Segment C Step C1 (`0x0584 → 0x0650`): Key Unpacking and Staging

Provides Stage 2 scratch-region partition lemmas, layout-independent callee address helpers, and
`segC_step1_unpack` (`+1412 → +1616`), which reassembles `(kp.pk, kp.sk)` and stages the ephemeral,
identity, and signed pre-key slices before cloning `pqspkB`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).symtab = s.symtab := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem symtab_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).symtab = s.symtab := by cases s; rfl

/-! ## Shared stack and overlap helpers -/

theorem layoutOk_1568_1 : LayoutOk 1568 1 := by
  unfold LayoutOk
  exact ⟨by decide, ⟨0, rfl⟩, by decide⟩

theorem layoutOk_16_8 : LayoutOk 16 8 := by
  unfold LayoutOk
  exact ⟨by decide, ⟨3, rfl⟩, by decide⟩

theorem extHookStack_le_sub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    extHookStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : extHookStack ≤ 516880 := by decide
  omega

theorem coinsFillStack_le_sub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    cliCoinsFillStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : cliCoinsFillStack ≤ 516880 := by decide
  omega

theorem isSameAccountStack_le_sub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    Pqxdh.WireEntries.isSameAccountDistinctStack ≤
      stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : Pqxdh.WireEntries.isSameAccountDistinctStack ≤
      516880 := by decide
  omega

theorem sub_frame_le_63 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 63 := by omega

theorem sub_frame_le_64 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 64 := by omega

theorem stackAt_sub_split_need (sp : BitVec 64) {fStk need : Nat}
    (hle : need ≤ fStk) (hhi : fStk ≤ 2 ^ 64) :
    stackAt sp fStk =
      memRegion (sp - BitVec.ofNat 64 fStk) (fStk - need) ∗ stackAt sp need := by
  have h1 := ProofLib.stackAt_split_bottom sp need (fStk - need) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

private theorem unpack32_pack (b0 b1 b2 b3 : BitVec 8) :
    unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
  dsimp only [unpack32]
  exact congrArg₂ List.cons (by bv_bits)
    (congrArg₂ List.cons (by bv_bits)
      (congrArg₂ List.cons (by bv_bits)
        (congrArg₂ List.cons (by bv_bits) rfl)))

private theorem pt8_singleton (p : BitVec 64) (v : BitVec 8) :
    (p ↦ₛ [v]) = (p ↦₈ v) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem sevenHi_eq_sevenLo (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
      ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) =
    (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) := by
  have hl : [b0, b1, b2, b3, b4, b5, b6] =
      [b0] ++ [b1] ++ [b2] ++ unpack32 (b6 ++ b5 ++ b4 ++ b3) := by
    rw [unpack32_pack]; rfl
  have hr : [b0, b1, b2, b3, b4, b5, b6] =
      unpack32 (b3 ++ b2 ++ b1 ++ b0) ++ [b4] ++ [b5] ++ [b6] := by
    rw [unpack32_pack]; rfl
  have h1 : (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6]) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
      ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) := by
    conv => lhs; rw [hl]
    simp only [List.append_assoc, pointsToBytes_append, List.length_singleton,
      BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo32_eq_pointsToBytes, pt8_singleton]
  have h2 : (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6]) =
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) := by
    conv => lhs; rw [hr]
    simp only [List.append_assoc, pointsToBytes_append, unpack32_length, List.length_singleton,
      BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo32_eq_pointsToBytes, pt8_singleton]
  exact h1.symm.trans h2

theorem sevenHi_to_Lo (sp k k1 k2 k3 k4 k5 k6 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (h1 : k + 1#64 = k1 := by rfl) (h2 : k + 2#64 = k2 := by rfl) (h3 : k + 3#64 = k3 := by rfl)
    (h4 : k + 4#64 = k4 := by rfl) (h5 : k + 5#64 = k5 := by rfl) (h6 : k + 6#64 = k6 := by rfl) :
    ((sp + k) ↦₈ b0) ∗ ((sp + k1) ↦₈ b1) ∗ ((sp + k2) ↦₈ b2) ∗
      ((sp + k3) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) =
    ((sp + k) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp + k4) ↦₈ b4) ∗ ((sp + k5) ↦₈ b5) ∗ ((sp + k6) ↦₈ b6) := by
  subst h1 h2 h3 h4 h5 h6
  have h := sevenHi_eq_sevenLo (sp + k) b0 b1 b2 b3 b4 b5 b6
  simpa only [BitVec.add_assoc] using h

theorem sevenHi_of_memRegion7 (a : BitVec 64) :
    memRegion a 7 ⊢
      ∃∗ b6 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b4 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b2 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
        ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) := by
  rw [mr_split a (a + 1#64) 1 6 7 rfl rfl,
      mr_split (a + 1#64) (a + 2#64) 1 5 6 rfl (by bv_omega),
      mr_split (a + 2#64) (a + 3#64) 1 4 5 rfl (by bv_omega),
      mr_split (a + 3#64) (a + 4#64) 1 3 4 rfl (by bv_omega),
      mr_split (a + 4#64) (a + 5#64) 1 2 3 rfl (by bv_omega),
      mr_split (a + 5#64) (a + 6#64) 1 1 2 rfl (by bv_omega),
      memRegion_1_eq_exists a, memRegion_1_eq_exists (a + 1#64),
      memRegion_1_eq_exists (a + 2#64), memRegion_1_eq_exists (a + 3#64),
      memRegion_1_eq_exists (a + 4#64), memRegion_1_eq_exists (a + 5#64),
      memRegion_1_eq_exists (a + 6#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b6 => Entails.sepExists_elim fun b5 =>
    Entails.sepExists_elim fun b4 => Entails.sepExists_elim fun b3 =>
    Entails.sepExists_elim fun b2 => Entails.sepExists_elim fun b1 =>
    Entails.sepExists_elim fun b0 => ?_
  have hbytes :
      ((a ↦₈ b0) ∗ (((a + 1#64) ↦₈ b1) ∗ (((a + 2#64) ↦₈ b2) ∗ (((a + 3#64) ↦₈ b3) ∗
        (((a + 4#64) ↦₈ b4) ∗ (((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6))))))) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
        ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
    have hl : [b0, b1, b2, b3, b4, b5, b6] =
        [b0] ++ [b1] ++ [b2] ++ unpack32 (b6 ++ b5 ++ b4 ++ b3) := by
      rw [unpack32_pack]; rfl
    have hL : (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6]) =
        ((a ↦₈ b0) ∗ (((a + 1#64) ↦₈ b1) ∗ (((a + 2#64) ↦₈ b2) ∗ (((a + 3#64) ↦₈ b3) ∗
          (((a + 4#64) ↦₈ b4) ∗ (((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6))))))) := by
      have hc : [b0, b1, b2, b3, b4, b5, b6] =
          [b0] ++ ([b1] ++ ([b2] ++ ([b3] ++ ([b4] ++ ([b5] ++ [b6]))))) := rfl
      conv => lhs; rw [hc]
      simp only [pointsToBytes_append, List.length_singleton, BitVec.add_assoc, BitVec.reduceAdd,
        pt8_singleton]
    have hR : (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6]) =
        ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
          ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
      conv => lhs; rw [hl]
      simp only [List.append_assoc, pointsToBytes_append, List.length_singleton,
        BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo32_eq_pointsToBytes, pt8_singleton]
    exact hL.symm.trans hR
  rw [hbytes]
  refine Entails.sepExists_right b6 ?_
  refine Entails.sepExists_right b5 ?_
  refine Entails.sepExists_right b4 ?_
  refine Entails.sepExists_right b3 ?_
  refine Entails.sepExists_right b2 ?_
  refine Entails.sepExists_right b1 ?_
  exact Entails.sepExists_right b0 (Entails.refl _)

theorem sevenHi_entails_mr7 (a : BitVec 64) (b0 b1 b2 : BitVec 8) (v3 : BitVec 32) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ v3)) ⊢
      memRegion a 7 := by
  refine mr_fold a (a + 1#64) 1 6 7 (mr_of_u8 _ _) ?_ rfl rfl
  refine mr_fold (a + 1#64) (a + 2#64) 1 5 6 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
  exact mr_fold (a + 2#64) (a + 3#64) 1 4 5 (mr_of_u8 _ _) (mr_of_u32 _ _) rfl (by bv_omega)

theorem sevenHi_to_Lo_rest (sp o0 o1 o2 o3 o4 o5 o6 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp)
    (h1 : o0 + 1#64 = o1 := by rfl) (h2 : o0 + 2#64 = o2 := by rfl)
    (h3 : o0 + 3#64 = o3 := by rfl) (h4 : o0 + 4#64 = o4 := by rfl)
    (h5 : o0 + 5#64 = o5 := by rfl) (h6 : o0 + 6#64 = o6 := by rfl) :
    ((sp + o0) ↦₈ b0) ∗ ((sp + o1) ↦₈ b1) ∗ ((sp + o2) ↦₈ b2) ∗
      ((sp + o3) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest =
    ((sp + o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp + o4) ↦₈ b4) ∗ ((sp + o5) ↦₈ b5) ∗ ((sp + o6) ↦₈ b6) ∗ rest := by
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (sevenHi_to_Lo sp o0 o1 o2 o3 o4 o5 o6 b0 b1 b2 b3 b4 b5 b6 h1 h2 h3 h4 h5 h6)

theorem sevenLo_entails_mr7 (a : BitVec 64) (v0 : BitVec 32) (b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ v0) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) ⊢
      memRegion a 7 := by
  refine mr_fold a (a + 4#64) 4 3 7 (mr_of_u32 _ _) ?_ rfl rfl
  refine mr_fold (a + 4#64) (a + 5#64) 1 2 3 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
  exact mr_fold (a + 5#64) (a + 6#64) 1 1 2 (mr_of_u8 _ _) (mr_of_u8 _ _) rfl (by bv_omega)

theorem mr_32_eq_words4 (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  apply Entails.antisymm
  · rw [mr_split a (a + 8#64) 8 24 32 rfl rfl,
        mr_split (a + 8#64) (a + 16#64) 8 16 24 rfl (by bv_omega),
        mr_split (a + 16#64) (a + 24#64) 8 8 16 rfl (by bv_omega),
        memRegion_8_eq_exists a, memRegion_8_eq_exists (a + 8#64),
        memRegion_8_eq_exists (a + 16#64), memRegion_8_eq_exists (a + 24#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.refl _
  · refine Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
      Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
    refine mr_fold a (a + 8#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl rfl
    refine mr_fold (a + 8#64) (a + 16#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    exact mr_fold (a + 16#64) (a + 24#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)

theorem words4_entails_mr32 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ⊢
      memRegion a 32 := by
  refine mr_fold a (a + 8#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl rfl
  refine mr_fold (a + 8#64) (a + 16#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  exact mr_fold (a + 16#64) (a + 24#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)

theorem mr_opk_32_eq (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ v6 : BitVec 8, ∃∗ v5 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v2 : BitVec 8, ∃∗ v1 : BitVec 16, ∃∗ v0 : BitVec 32,
        (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₁₆ v1) ∗ ((a + 6#64) ↦₈ v2) ∗
        ((a + 7#64) ↦₆₄ v3) ∗ ((a + 15#64) ↦₆₄ v4) ∗ ((a + 23#64) ↦₆₄ v5) ∗
        ((a + 31#64) ↦₈ v6) := by
  rw [mr_split a (a + 4#64) 4 28 32 rfl rfl,
      mr_split (a + 4#64) (a + 6#64) 2 26 28 rfl (by bv_omega),
      mr_split (a + 6#64) (a + 7#64) 1 25 26 rfl (by bv_omega),
      mr_split (a + 7#64) (a + 15#64) 8 17 25 rfl (by bv_omega),
      mr_split (a + 15#64) (a + 23#64) 8 9 17 rfl (by bv_omega),
      mr_split (a + 23#64) (a + 31#64) 8 1 9 rfl (by bv_omega),
      memRegion_4_eq_exists a,
      memRegion_2_eq_exists (a + 4#64),
      memRegion_1_eq_exists (a + 6#64),
      memRegion_8_eq_exists (a + 7#64),
      memRegion_8_eq_exists (a + 15#64),
      memRegion_8_eq_exists (a + 23#64),
      memRegion_1_eq_exists (a + 31#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem mr_opk_32_entails (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ v6 : BitVec 8, ∃∗ v5 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v2 : BitVec 8, ∃∗ v1 : BitVec 16, ∃∗ v0 : BitVec 32,
        (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₁₆ v1) ∗ ((a + 6#64) ↦₈ v2) ∗
        ((a + 7#64) ↦₆₄ v3) ∗ ((a + 15#64) ↦₆₄ v4) ∗ ((a + 23#64) ↦₆₄ v5) ∗
        ((a + 31#64) ↦₈ v6) :=
  Entails.of_eq (mr_opk_32_eq a)

theorem opkFlag_none {α : Type} :
    (if (none : Option α).isSome then 1#32 else 0#32) = 0#32 ∧
      (if (none : Option α).isSome then 1#32 else 0#32).truncate 8 = 0#8 :=
  ⟨rfl, rfl⟩

theorem opkFlag_some {α : Type} (v : α) :
    (if (some v).isSome then 1#32 else 0#32) = 1#32 ∧
      (if (some v).isSome then 1#32 else 0#32).truncate 8 = 1#8 :=
  ⟨rfl, rfl⟩

/-- Untouched Stage 2 scratch windows in `[sp + 0x5ba, sp + initLocalsSize)`. -/
def scratch5baGaps (sp : BitVec 64) : SepProp :=
  memRegion (sp + 1466#64) 6 ∗
    memRegion (sp + 1488#64) 376 ∗
    memRegion (sp + 1888#64) 16 ∗
    memRegion (sp + 1936#64) 400 ∗
    memRegion (sp + 2368#64) 128 ∗
    memRegion (sp + 2528#64) 1536 ∗
    memRegion (sp + 4128#64) 1504 ∗
    memRegion (sp + 5704#64) 1608

theorem scratch5ba_split (sp : BitVec 64) :
    memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (sp + 1472#64) 16 ∗
      memRegion (sp + 1864#64) 24 ∗
      memRegion (sp + 1904#64) 32 ∗
      memRegion (sp + 2336#64) 32 ∗
      memRegion (sp + 2496#64) 32 ∗
      memRegion (sp + 4064#64) 64 ∗
      memRegion (sp + 5632#64) 72 ∗
      scratch5baGaps sp := by
  have heq0 : sp + 0x5ba#64 = sp + 1466#64 := rfl
  have heqN : initLocalsSize - 0x5ba = 5846 := rfl
  rw [heq0, heqN,
      mr_split (sp + 1466#64) (sp + 1472#64) 6 5840 5846 rfl (by bv_omega),
      mr_split (sp + 1472#64) (sp + 1488#64) 16 5824 5840 rfl (by bv_omega),
      mr_split (sp + 1488#64) (sp + 1864#64) 376 5448 5824 rfl (by bv_omega),
      mr_split (sp + 1864#64) (sp + 1888#64) 24 5424 5448 rfl (by bv_omega),
      mr_split (sp + 1888#64) (sp + 1904#64) 16 5408 5424 rfl (by bv_omega),
      mr_split (sp + 1904#64) (sp + 1936#64) 32 5376 5408 rfl (by bv_omega),
      mr_split (sp + 1936#64) (sp + 2336#64) 400 4976 5376 rfl (by bv_omega),
      mr_split (sp + 2336#64) (sp + 2368#64) 32 4944 4976 rfl (by bv_omega),
      mr_split (sp + 2368#64) (sp + 2496#64) 128 4816 4944 rfl (by bv_omega),
      mr_split (sp + 2496#64) (sp + 2528#64) 32 4784 4816 rfl (by bv_omega),
      mr_split (sp + 2528#64) (sp + 4064#64) 1536 3248 4784 rfl (by bv_omega),
      mr_split (sp + 4064#64) (sp + 4128#64) 64 3184 3248 rfl (by bv_omega),
      mr_split (sp + 4128#64) (sp + 5632#64) 1504 1680 3184 rfl (by bv_omega),
      mr_split (sp + 5632#64) (sp + 5704#64) 72 1608 1680 rfl (by bv_omega)]
  unfold scratch5baGaps
  ac_rfl

/-- Bundle fields in `cliBundleAt` left untouched across Stage 2. -/
def cliBundleRestAt (a : BitVec 64) (b : BundleV) (spkSigPtr kpkSigPtr : BitVec 64) : SepProp :=
  (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
    (spkSigPtr ↦ₛ b.spkSig) ∗
    ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
    ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
    (kpkSigPtr ↦ₛ b.kpkSig) ∗
    ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
    ((a + 152#64) ↦₃₂ b.regId) ∗
    ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2

def cliBundleBodyAt (a : BitVec 64) (b : BundleV) (spkSigPtr kpkSigPtr kpkPtr : BitVec 64)
    (opkId : BitVec 32) : SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
    ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
    ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
    ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
    ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (a + 157#64) 32) ∗
    cliBundleRestAt a b spkSigPtr kpkSigPtr

theorem cliBundleAt_eq_body (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr =
      ∃∗ opkId : BitVec 32,
        ⌜b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
          ∀ p, b.opk = some p → opkId = p.1⌝ ∗
        cliBundleBodyAt a b spkSigPtr kpkSigPtr kpkPtr opkId := by
  unfold cliBundleAt cliBundleBodyAt cliBundleRestAt
  dsimp only
  congr 1
  funext opkId
  ac_rfl

theorem cliBundleBody_entails (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) (opkId : BitVec 32)
    (hpure : b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
      ∀ p, b.opk = some p → opkId = p.1) :
    cliBundleBodyAt a b spkSigPtr kpkSigPtr kpkPtr opkId ⊢
      cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr := by
  rw [cliBundleAt_eq_body]
  exact Entails.sepExists_right opkId (Entails.pure_right hpure (Entails.refl _))

theorem stage3KeySlotsAt_none (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId : BitVec 32) (hnone : b.opk = none) :
    ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
      memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ 0#32) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
      ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
      ((fsp + 0x438#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x439#64) 32 ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x45a#64) 6 =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  unfold stage3KeySlotsAt
  dsimp only
  rw [hnone]
  rfl

theorem stage3KeySlotsAt_some (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId id : BitVec 32) (k : PublicKey) (hsome : b.opk = some (id, k)) :
    ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
      memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ 1#32) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
      ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
      ((fsp + 0x438#64) ↦₈ 1#8) ∗
      ((fsp + 0x439#64) ↦ₛ k.bytes.toList) ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x45a#64) 6 =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  unfold stage3KeySlotsAt
  dsimp only
  rw [hsome]
  rfl

theorem stage2Mem_eq_sp (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (stk : Nat)
    {s0 s : State} (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    stage2Mem A img x stk s0 =
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      coinsCursorAt img x.coinsP x.coins 0 ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      logOff img ∗ A.pool ∗ initSaved s0 ∗
      memRegion s.sp 0x78 ∗ memRegion (s.sp + 120#64) 8 ∗ memRegion (s.sp + 0x80#64) 0x50 ∗
      initArgsAt img s.sp x s0 ∗
      memRegion (s.sp + 296#64) 32 ∗
      memRegion (s.sp + 0x148#64) 0x150 ∗
      memRegion (s.sp + 664#64) 456 ∗
      memRegion (s.sp + 0x460#64) 0x158 ∗
      ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (s.sp + 1472#64) 16 ∗
      memRegion (s.sp + 1864#64) 24 ∗
      memRegion (s.sp + 1904#64) 32 ∗
      memRegion (s.sp + 2336#64) 32 ∗
      memRegion (s.sp + 2496#64) 32 ∗
      memRegion (s.sp + 4064#64) 64 ∗
      memRegion (s.sp + 5632#64) 72 ∗
      scratch5baGaps s.sp ∗
      stackAt s.sp (stk - cliInitiateFrame) := by
  unfold stage2Mem
  dsimp only
  rw [← hsp,
      mr_split s.sp (s.sp + 120#64) 120 88 208 rfl rfl,
      mr_split (s.sp + 120#64) (s.sp + 128#64) 8 80 88 rfl (by bv_omega),
      mr_split (s.sp + 296#64) (s.sp + 328#64) 32 1136 1168 rfl (by bv_omega),
      mr_split (s.sp + 328#64) (s.sp + 664#64) 336 800 1136 rfl (by bv_omega),
      mr_split (s.sp + 664#64) (s.sp + 1120#64) 456 344 800 rfl (by bv_omega),
      scratch5ba_split s.sp]
  ac_rfl

/-! ## Layout-independent callee address helpers -/

theorem shim_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr shimName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2") := by
  have h0 := cliInitiate_fnOff
  have h1 := rustNoAllocShim_stub
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, shimName, h0, h1]
  bv_omega

theorem alloc_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr allocName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc") := by
  have h0 := cliInitiate_fnOff
  have h1 := rustAlloc_stub
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, allocName, h0, h1]
  bv_omega

theorem memcpy_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr memcpyName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy") := by
  have h0 := cliInitiate_fnOff
  have h1 := memcpy_stub
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, memcpyName, h0, h1]
  bv_omega

theorem handleError_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr handleErrorName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::raw_vec::handle_error") := by
  have h0 := cliInitiate_fnOff
  have h1 := handleError_stub
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h0, h1]
  bv_omega

theorem dealloc_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr deallocName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc") := by
  have h0 := cliInitiate_fnOff
  have h1 := rustDealloc_stub
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, deallocName, h0, h1]
  bv_omega

theorem isSameAccount_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr cliIsSameAccountName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName -
        bv% (ls_rel% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"
          "libsignal_cli_handshake::initiate") := by
  have h0 := cliInitiate_fnOff
  have h1 := cliIsSameAccount_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h0, h1]
  bv_omega

theorem coinsFill_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr cliCoinsFillName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill") := by
  have h0 := cliInitiate_fnOff
  have h1 := cliCoinsFill_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h0, h1]
  bv_omega

theorem derivePubKeyBytes_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr cliDerivePubKeyBytesName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName -
        bv% (ls_rel% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"
          "libsignal_cli_handshake::initiate") := by
  have h0 := cliInitiate_fnOff
  have h1 : libsignalSessionCode.fnOff cliDerivePubKeyBytesName =
      num% (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
      (ls_lemma% fnOff "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h0, h1]
  bv_omega

theorem staticSecretDrop_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr staticSecretDropName =
      (tripleRatchetProgAtExt b ext).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop") := by
  have h0 := cliInitiate_fnOff
  have h1 := staticSecretDrop_stub
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h0, h1]
  bv_omega

/-! ## Step C1 (`0x0584 → 0x0650`): `IdentityKeyPair` and key staging -/

theorem inInitiateExt_of_step {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s sm : State} {k0 k1 : Nat}
    (hctrl : InInitiateExt img ext s0 s k0)
    (hpc : sm.pc = initPcExt img ext k1)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hsym : sm.symtab = s.symtab)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s)
    (hkf : s.mem.KeepsFrozen sm.mem)
    (hfiles : sm.fs.files = s.fs.files) :
    InInitiateExt img ext s0 sm k1 :=
  { pc := hpc
    run := hrun
    sp := hsp.trans hctrl.sp
    fp := hfp.trans hctrl.fp
    x19 := hx19.trans hctrl.x19
    files0 := hfiles.trans hctrl.files0
    inv := imgCallInv_of_keepsFrozen hctrl.inv hkf hsym
    vregs := hvregs.trans hctrl.vregs
    spAligned := hctrl.spAligned }

theorem inInitiate_of_step {img : Obj.Image} {W : CliHooks} {s0 s sm : State} {k0 k1 : Nat}
    (hctrl : InInitiate img W s0 s k0)
    (hpc : sm.pc = initPc img W k1)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hsym : sm.symtab = s.symtab)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s)
    (hkf : s.mem.KeepsFrozen sm.mem)
    (hfiles : sm.fs.files = s.fs.files) :
    InInitiate img W s0 sm k1 :=
  { pc := hpc
    run := hrun
    sp := hsp.trans hctrl.sp
    fp := hfp.trans hctrl.fp
    x19 := hx19.trans hctrl.x19
    files0 := hfiles.trans hctrl.files0
    inv := imgCallInv_of_keepsFrozen hctrl.inv hkf hsym
    vregs := hvregs.trans hctrl.vregs
    spAligned := hctrl.spAligned }

theorem words4_to_slice_rest {bs : List (BitVec 8)} {a a1 a2 a3 : BitVec 64}
    {w0 w1 w2 w3 : BitVec 64}
    (h : a ↦ₛ bs = (a ↦₆₄ w0) ∗ (a1 ↦₆₄ w1) ∗ (a2 ↦₆₄ w2) ∗ (a3 ↦₆₄ w3))
    (rest : SepProp) :
    (a ↦₆₄ w0) ∗ (a1 ↦₆₄ w1) ∗ (a2 ↦₆₄ w2) ∗ (a3 ↦₆₄ w3) ∗ rest =
      (a ↦ₛ bs) ∗ rest := by
  simpa only [sepConj_assoc] using (congrArg (· ∗ rest) h).symm

theorem entails_by_focus {Full Sub Target F Goal : SepProp}
    (hfoc : Full ⊢ Sub ∗ F) (h : Sub ⊢ Target) (hrest : Target ∗ F ⊢ Goal) :
    Full ⊢ Goal :=
  Entails.trans hfoc (Entails.trans (sepConj_mono_left h) hrest)

set_option maxHeartbeats 1600000 in
/-- Stage 2 Step C1 (`+1412 → +1616`, `initProgExt`): reassembles `(kp.pk, kp.sk)` at
`[fsp + 776 .. 840)`, stages key slices onto the stack, and prepares `x.kpkPtr` (`1568` bytes) for
`pqspkB` cloning. -/
theorem segC_step1_unpack_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8} {u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s 0x0584)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = u1)
    (hx27 : s.readReg64 (.gpr 27#5) = u2)
    (hx25 : s.readReg64 (.gpr 25#5) = u3)
    (hx28 : s.readReg64 (.gpr 28#5) = u4)
    (hx24 : s.readReg64 (.gpr 24#5) = u5)
    (hx21 : s.readReg64 (.gpr 21#5) = u6)
    (hkpLo : ∀ a : BitVec 64,
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
        ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
        (a ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((a + 32#64) ↦ₛ kp.privateKey.bytes.toList.take 7))
    (hkpHi : ∀ a : BitVec 64,
      (a ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
        ((a + 7#64) ↦₆₄ u5) ∗ ((a + 15#64) ↦₆₄ u6) ∗
        ((a + 23#64) ↦₆₄ u7) ∗ ((a + 31#64) ↦₈ b63) =
        (a ↦ₛ kp.privateKey.bytes.toList))
    (hekPkLen : ekAPk.length = 32)
    (hekSkLen : ekASk.length = 32)
    (hk : ∀ sm : State,
      sm.pc = initPcExt img ext 0x0650 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.readReg64 .fp = s.readReg64 .fp →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.symtab = s.symtab →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 20#5) = x.kpkPtr →
      sm.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sm.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sm.readReg64 (.gpr 25#5) = 1568#64 →
      sm.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      post sm
        (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          memRegion (s.sp + 696#64) 72 ∗
          ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          memRegion (s.sp + 1864#64) 24 ∗
          ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
          ((s.sp + 5664#64) ↦ₛ ekASk) ∗
          ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
          ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          F)) :
    SepWP (initProgExt img ext) (initPcExt img ext 0x0650) s
      (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        ((s.sp + 696#64) ↦ₛ ekASk) ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        memRegion (s.sp + 776#64) 64 ∗
        ((s.sp + 1864#64) ↦₆₄ u7) ∗
        ((s.sp + 1872#64) ↦₈ b63) ∗
        memRegion (s.sp + 1873#64) 7 ∗
        ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
        ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
        memRegion (s.sp + 1887#64) 1 ∗
        memRegion (s.sp + 1904#64) 32 ∗
        memRegion (s.sp + 2336#64) 32 ∗
        memRegion (s.sp + 2496#64) 32 ∗
        memRegion (s.sp + 4064#64) 64 ∗
        memRegion (s.sp + 5632#64) 64 ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
        ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        F)
      post (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    1412 204
  clear hfn
  obtain ⟨ekp0, ekp1, ekp2, ekp3, hekp⟩ := exists_keyWords4_of_len32 hekPkLen
  obtain ⟨eks0, eks1, eks2, eks3, heks⟩ := exists_keyWords4_of_len32 hekSkLen
  obtain ⟨kpp0, kpp1, kpp2, kpp3, hkpp⟩ :=
    exists_keyWords4_of_len32 (bs := kp.identityKey.publicKey.bytes.toList)
      kp.identityKey.publicKey.bytes.property
  obtain ⟨kps0, kps1, kps2, kps3, hkps⟩ :=
    exists_keyWords4_of_len32 (bs := kp.privateKey.bytes.toList) kp.privateKey.bytes.property
  obtain ⟨spk0, spk1, spk2, spk3, hspk⟩ :=
    exists_keyWords4_of_len32 (bs := x.bundle.spk.bytes.toList) x.bundle.spk.bytes.property
  obtain ⟨idk0, idk1, idk2, idk3, hidk⟩ :=
    exists_keyWords4_of_len32 (bs := x.bundle.idKey.publicKey.bytes.toList)
      x.bundle.idKey.publicKey.bytes.property
  have hpc : s.pc = (initProgExt img ext).fnAddr cliInitiateName + 1412#64 := hctrl.pc
  have hrun : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  have h776_split :
      memRegion (s.sp + 776#64) 64 ⊢
        (∃∗ db63 : BitVec 8,
         ∃∗ q7 : BitVec 64, ∃∗ q6 : BitVec 64, ∃∗ q5 : BitVec 64,
         ∃∗ q4 : BitVec 64, ∃∗ q3 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q1 : BitVec 64,
         ∃∗ d6 : BitVec 8, ∃∗ d5 : BitVec 8, ∃∗ d4 : BitVec 8, ∃∗ d3 : BitVec 8,
         ∃∗ d2 : BitVec 8, ∃∗ d1 : BitVec 8, ∃∗ d0 : BitVec 8,
           ((s.sp + 776#64) ↦₈ d0) ∗ ((s.sp + 777#64) ↦₈ d1) ∗ ((s.sp + 778#64) ↦₈ d2) ∗
           ((s.sp + 779#64) ↦₃₂ (d6 ++ d5 ++ d4 ++ d3)) ∗
           ((s.sp + 783#64) ↦₆₄ q1) ∗ ((s.sp + 791#64) ↦₆₄ q2) ∗
           ((s.sp + 799#64) ↦₆₄ q3) ∗ ((s.sp + 807#64) ↦₆₄ q4) ∗
           ((s.sp + 815#64) ↦₆₄ q5) ∗ ((s.sp + 823#64) ↦₆₄ q6) ∗
           ((s.sp + 831#64) ↦₆₄ q7) ∗ ((s.sp + 839#64) ↦₈ db63)) := by
    rw [mr_split (s.sp + 776#64) (s.sp + 783#64) 7 57 64 rfl (by bv_omega),
        mr_split (s.sp + 783#64) (s.sp + 791#64) 8 49 57 rfl (by bv_omega),
        mr_split (s.sp + 791#64) (s.sp + 799#64) 8 41 49 rfl (by bv_omega),
        mr_split (s.sp + 799#64) (s.sp + 807#64) 8 33 41 rfl (by bv_omega),
        mr_split (s.sp + 807#64) (s.sp + 815#64) 8 25 33 rfl (by bv_omega),
        mr_split (s.sp + 815#64) (s.sp + 823#64) 8 17 25 rfl (by bv_omega),
        mr_split (s.sp + 823#64) (s.sp + 831#64) 8 9 17 rfl (by bv_omega),
        mr_split (s.sp + 831#64) (s.sp + 839#64) 8 1 9 rfl (by bv_omega),
        memRegion_8_eq_exists (s.sp + 783#64), memRegion_8_eq_exists (s.sp + 791#64),
        memRegion_8_eq_exists (s.sp + 799#64), memRegion_8_eq_exists (s.sp + 807#64),
        memRegion_8_eq_exists (s.sp + 815#64), memRegion_8_eq_exists (s.sp + 823#64),
        memRegion_8_eq_exists (s.sp + 831#64), memRegion_1_eq_exists (s.sp + 839#64)]
    refine Entails.trans (sepConj_mono_left (sevenHi_of_memRegion7 (s.sp + 776#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    exact Entails.refl _
  refine SepWP.weaken_pre
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (Entails.refl _)
              (sepConj_mono (Entails.refl _)
                (sepConj_mono_left h776_split))))))) ?_
  rw [hekp (s.sp + 664#64) (s.sp + 672#64) (s.sp + 680#64) (s.sp + 688#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      heks (s.sp + 696#64) (s.sp + 704#64) (s.sp + 712#64) (s.sp + 720#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hspk (s.sp + 728#64) (s.sp + 736#64) (s.sp + 744#64) (s.sp + 752#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hidk (x.bundleA + 120#64) (x.bundleA + 128#64) (x.bundleA + 136#64) (x.bundleA + 144#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 b0 b1 b2 b3 b4 b5 b6,
      mr_32_eq_words4 (s.sp + 1904#64),
      mr_32_eq_words4 (s.sp + 2336#64),
      mr_32_eq_words4 (s.sp + 2496#64),
      mr_split (s.sp + 4064#64) (s.sp + 4096#64) 32 32 64 rfl (by bv_omega),
      mr_32_eq_words4 (s.sp + 4064#64), mr_32_eq_words4 (s.sp + 4096#64),
      mr_split (s.sp + 5632#64) (s.sp + 5664#64) 32 32 64 rfl (by bv_omega),
      mr_32_eq_words4 (s.sp + 5632#64), mr_32_eq_words4 (s.sp + 5664#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 43 (apply SepWP.exists_left; intro _)
  simp only [sepConj_assoc]
  dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt, initPcExt] at hpc hk ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))) = prog
    reverting [Program.fetch, Program.externAt?]
  examples_hide_fetches
  wp_steps
  -- Restore `sp + 1880` to `sevenHi` for `LDUR W8, [X8, #3]`
  conv => arg 4; simp only [← sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 b0 b1 b2 b3 b4 b5 b6,
    sepConj_assoc]
  wp_steps
  -- Reassociate `sp + 776` from `sevenHi` to `sevenLo` for `STR W9, [SP, #776]`
  conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 776#64 777#64 778#64 779#64 780#64 781#64 782#64,
    sepConj_assoc]
  wp_steps
  have hkpLoWords : ∀ rest : SepProp,
      ((s.sp + 776#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        (((s.sp + 780#64) ↦₈ b4) ∗ (((s.sp + 781#64) ↦₈ b5) ∗ (((s.sp + 782#64) ↦₈ b6) ∗
          (((s.sp + 783#64) ↦₆₄ u1) ∗ (((s.sp + 791#64) ↦₆₄ u2) ∗
            (((s.sp + 799#64) ↦₆₄ u3) ∗ (((s.sp + 807#64) ↦₆₄ u4) ∗ rest))))))) =
      ((s.sp + 776#64) ↦₆₄ kpp0) ∗ (((s.sp + 784#64) ↦₆₄ kpp1) ∗
        (((s.sp + 792#64) ↦₆₄ kpp2) ∗ (((s.sp + 800#64) ↦₆₄ kpp3) ∗
          (((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList.take 7) ∗ rest)))) := fun rest => by
    have hL := hkpLo (s.sp + 776#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hL
    rw [hkpp (s.sp + 776#64) (s.sp + 784#64) (s.sp + 792#64) (s.sp + 800#64)
      (by bv_omega) (by bv_omega) (by bv_omega)] at hL
    simpa only [sepConj_assoc] using congrArg (· ∗ rest) hL
  have hkpHiWords : ∀ rest : SepProp,
      ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
        (((s.sp + 815#64) ↦₆₄ u5) ∗ (((s.sp + 823#64) ↦₆₄ u6) ∗
          (((s.sp + 831#64) ↦₆₄ u7) ∗ (((s.sp + 839#64) ↦₈ b63) ∗ rest)))) =
      ((s.sp + 808#64) ↦₆₄ kps0) ∗ (((s.sp + 816#64) ↦₆₄ kps1) ∗
        (((s.sp + 824#64) ↦₆₄ kps2) ∗ (((s.sp + 832#64) ↦₆₄ kps3) ∗ rest))) := fun rest => by
    have hH := hkpHi (s.sp + 808#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hH
    rw [hkps (s.sp + 808#64) (s.sp + 816#64) (s.sp + 824#64) (s.sp + 832#64)
      (by bv_omega) (by bv_omega) (by bv_omega)] at hH
    simpa only [sepConj_assoc] using congrArg (· ∗ rest) hH
  conv => arg 4; rw [hkpLoWords]
  wp_steps
  conv => arg 4; rw [hkpHiWords]
  wp_steps
  refine SepWP.weaken_pre (P' :=
      ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        memRegion (s.sp + 696#64) 72 ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
        ((s.sp + 5664#64) ↦ₛ ekASk) ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
        ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        F) (by
    try simp only [sepConj_assoc]
    rw [words4_to_slice_rest (hkpp (s.sp + 776#64) (s.sp + 784#64) (s.sp + 792#64) (s.sp + 800#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hkps (s.sp + 808#64) (s.sp + 816#64) (s.sp + 824#64) (s.sp + 832#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hekp (s.sp + 664#64) (s.sp + 672#64) (s.sp + 680#64) (s.sp + 688#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hspk (s.sp + 1904#64) (s.sp + 1912#64) (s.sp + 1920#64) (s.sp + 1928#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hidk (s.sp + 2336#64) (s.sp + 2344#64) (s.sp + 2352#64) (s.sp + 2360#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hspk (s.sp + 2496#64) (s.sp + 2504#64) (s.sp + 2512#64) (s.sp + 2520#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hkpp (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hkps (s.sp + 4096#64) (s.sp + 4104#64) (s.sp + 4112#64) (s.sp + 4120#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hekp (s.sp + 5632#64) (s.sp + 5640#64) (s.sp + 5648#64) (s.sp + 5656#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (heks (s.sp + 5664#64) (s.sp + 5672#64) (s.sp + 5680#64) (s.sp + 5688#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hidk (x.bundleA + 120#64) (x.bundleA + 128#64) (x.bundleA + 136#64) (x.bundleA + 144#64)
          (by bv_omega) (by bv_omega) (by bv_omega))]
    have hm696 :
        ((s.sp + 696#64) ↦₆₄ eks0) ∗ (((s.sp + 704#64) ↦₆₄ eks1) ∗
          (((s.sp + 712#64) ↦₆₄ eks2) ∗ (((s.sp + 720#64) ↦₆₄ eks3) ∗
            (((s.sp + 728#64) ↦₆₄ spk0) ∗ (((s.sp + 736#64) ↦₆₄ spk1) ∗
              (((s.sp + 744#64) ↦₆₄ spk2) ∗ (((s.sp + 752#64) ↦₆₄ spk3) ∗
                ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64))))))))) ⊢
        memRegion (s.sp + 696#64) 72 := by
      have h1 :
          (((s.sp + 696#64) ↦₆₄ eks0) ∗ ((s.sp + 704#64) ↦₆₄ eks1) ∗
            ((s.sp + 712#64) ↦₆₄ eks2) ∗ ((s.sp + 720#64) ↦₆₄ eks3)) ⊢
          memRegion (s.sp + 696#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
          words4_entails_mr32 (s.sp + 696#64) eks0 eks1 eks2 eks3
      have h2 :
          (((s.sp + 728#64) ↦₆₄ spk0) ∗ ((s.sp + 736#64) ↦₆₄ spk1) ∗
            ((s.sp + 744#64) ↦₆₄ spk2) ∗ ((s.sp + 752#64) ↦₆₄ spk3)) ⊢
          memRegion (s.sp + 728#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
          words4_entails_mr32 (s.sp + 728#64) spk0 spk1 spk2 spk3
      simpa only [sepConj_assoc] using
        mr_fold (s.sp + 696#64) (s.sp + 728#64) 32 40 72 h1
          (mr_fold (s.sp + 728#64) (s.sp + 760#64) 32 8 40 h2 (mr_of_u64 _ _) rfl (by bv_omega))
          rfl (by bv_omega)
    have hm1864 :
        ((s.sp + 1864#64) ↦₆₄ u7) ∗ (((s.sp + 1872#64) ↦₈ b63) ∗
          (memRegion (s.sp + 1873#64) 7 ∗
            (((s.sp + 1880#64) ↦₈ b0) ∗ (((s.sp + 1881#64) ↦₈ b1) ∗
              (((s.sp + 1882#64) ↦₈ b2) ∗
                (((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
                  memRegion (s.sp + 1887#64) 1)))))) ⊢
        memRegion (s.sp + 1864#64) 24 := by
      have h7 :
          (((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗
            ((s.sp + 1882#64) ↦₈ b2) ∗ ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) ⊢
          memRegion (s.sp + 1880#64) 7 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
          sevenHi_entails_mr7 (s.sp + 1880#64) b0 b1 b2 (b6 ++ b5 ++ b4 ++ b3)
      simpa only [sepConj_assoc] using
        mr_fold (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 (mr_of_u64 _ _)
          (mr_fold (s.sp + 1872#64) (s.sp + 1873#64) 1 15 16 (mr_of_u8 _ _)
            (mr_fold (s.sp + 1873#64) (s.sp + 1880#64) 7 8 15 (Entails.refl _)
              (mr_fold (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8 h7 (Entails.refl _) rfl (by bv_omega))
              rfl (by bv_omega))
            rfl (by bv_omega))
          rfl (by bv_omega)
    try simp only [sepConj_assoc]
    refine entails_by_focus (by sep_frame) hm696 ?_
    refine entails_by_focus (by sep_frame) hm1864 ?_
    sep_frame) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [calleeSavedVRegs, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

/-- Stage 2 Step C1 (`+1412 → +1616`, `initProg`). -/
theorem segC_step1_unpack {img : Obj.Image} {W : CliHooks}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8} {u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s 0x0584)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = u1)
    (hx27 : s.readReg64 (.gpr 27#5) = u2)
    (hx25 : s.readReg64 (.gpr 25#5) = u3)
    (hx28 : s.readReg64 (.gpr 28#5) = u4)
    (hx24 : s.readReg64 (.gpr 24#5) = u5)
    (hx21 : s.readReg64 (.gpr 21#5) = u6)
    (hkpLo : ∀ a : BitVec 64,
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
        ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
        (a ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((a + 32#64) ↦ₛ kp.privateKey.bytes.toList.take 7))
    (hkpHi : ∀ a : BitVec 64,
      (a ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
        ((a + 7#64) ↦₆₄ u5) ∗ ((a + 15#64) ↦₆₄ u6) ∗
        ((a + 23#64) ↦₆₄ u7) ∗ ((a + 31#64) ↦₈ b63) =
        (a ↦ₛ kp.privateKey.bytes.toList))
    (hekPkLen : ekAPk.length = 32)
    (hekSkLen : ekASk.length = 32)
    (hk : ∀ sm : State,
      sm.pc = initPc img W 0x0650 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.readReg64 .fp = s.readReg64 .fp →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.symtab = s.symtab →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 20#5) = x.kpkPtr →
      sm.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sm.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sm.readReg64 (.gpr 25#5) = 1568#64 →
      sm.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      post sm
        (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          memRegion (s.sp + 696#64) 72 ∗
          ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          memRegion (s.sp + 1864#64) 24 ∗
          ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
          ((s.sp + 5664#64) ↦ₛ ekASk) ∗
          ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
          ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          F)) :
    SepWP (initProg img W) (initPc img W 0x0650) s
      (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        ((s.sp + 696#64) ↦ₛ ekASk) ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        memRegion (s.sp + 776#64) 64 ∗
        ((s.sp + 1864#64) ↦₆₄ u7) ∗
        ((s.sp + 1872#64) ↦₈ b63) ∗
        memRegion (s.sp + 1873#64) 7 ∗
        ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
        ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
        memRegion (s.sp + 1887#64) 1 ∗
        memRegion (s.sp + 1904#64) 32 ∗
        memRegion (s.sp + 2336#64) 32 ∗
        memRegion (s.sp + 2496#64) 32 ∗
        memRegion (s.sp + 4064#64) 64 ∗
        memRegion (s.sp + 5632#64) 64 ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
        ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        F)
      post (initOom s0) :=
  segC_step1_unpack_ext (ext := cliHookExterns W)
    ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0,
      hctrl.inv, hctrl.vregs, hctrl.spAligned⟩
    hx22 hx26 hx27 hx25 hx28 hx24 hx21 hkpLo hkpHi hekPkLen hekSkLen hk

/-- `SepWPp` call combinator under `TraceFsSound` that also preserves `s.symtab`. -/
theorem sepWPp_call_cli {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog)
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ∗ F ⊢ oom sf)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      sf.symtab = s.symtab →
      (sf.trace = s.trace → sf.fs.files = s.fs.files) →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  intro R' hm hL
  have hpreR : s.mem ⊨ spec.pre x s ∗ (F ∗ R') := by
    rw [← sepConj_assoc]
    exact Arm64.Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpreR hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hf : sm.trace = s.trace → sm.fs.files = s.fs.files := fun htr =>
      hFs.files_eq hsteps (evs := []) (by simpa using htr) NoFsEv.nil
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hsteps.keepsFrozen hsteps.symtab_eq hf R' hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, hpan sm⟩)⟩
  · rw [hexit] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st,
      Arm64.Satisfies.mono (sepConj_mono_left (hoom sm)) hpost⟩)⟩

theorem inInitiateExt_of_call {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s sf : State} {k0 k1 : Nat}
    (hctrl : InInitiateExt img ext s0 s k0)
    (hpc : sf.pc = initPcExt img ext k1)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s.sp)
    (hcs : CalleeSavedPreserved s sf)
    (hkf : s.mem.KeepsFrozen sf.mem)
    (hsym : sf.symtab = s.symtab)
    (hfiles : sf.fs.files = s.fs.files) :
    InInitiateExt img ext s0 sf k1 := by
  rcases hcs with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  exact inInitiateExt_of_step hctrl hpc hrun hsp hfp hx19 hsym hvregs hkf hfiles

theorem inInitiate_of_call {img : Obj.Image} {W : CliHooks} {s0 s sf : State} {k0 k1 : Nat}
    (hctrl : InInitiate img W s0 s k0)
    (hpc : sf.pc = initPc img W k1)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s.sp)
    (hcs : CalleeSavedPreserved s sf)
    (hkf : s.mem.KeepsFrozen sf.mem)
    (hsym : sf.symtab = s.symtab)
    (hfiles : sf.fs.files = s.fs.files) :
    InInitiate img W s0 sf k1 := by
  rcases hcs with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  exact inInitiate_of_step hctrl hpc hrun hsp hfp hx19 hsym hvregs hkf hfiles

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

