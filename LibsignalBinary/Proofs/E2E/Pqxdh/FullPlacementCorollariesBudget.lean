/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedBBudget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalFullPlacement]` Corollaries for `Pqxdh::accept` and `initialize_bob_session`

Proves `VmPreserved`-strengthened `<PublicKey>::is_canonical` (Block `202`) under
`[LibsignalFullPlacement]` and instantiates `AcceptPlacedBBudget`, `AcceptErrOwnedPlacedBudget`,
`InitBobCutPlacedBudget`, and `InitBobErrOwnedPlacedBudget` with `PqxdhPlacedHookContracts` and
`vecAppendElements_fast_placed_ok_cl` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open SignalPqxdh (isCanonicalRef scalarIsInRange)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  blkPC_202 blkPl_202 blkPl_75 full_ls_subroutine_ok_of_plain libsignalSessionLib
  lsLogFilterAddr lsMemcpySym lsProg_75 lsProg_79 lsmpl lsρ ls_hook_ok_any
)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.Shared (
  CryptoUnaryGhost DalekMontToEdGhost
  bv_add_neg64 bv_sub_sub_lit
  dalekMontToEdOutAt dalekMontToEdOutAt_none dalekMontToEdOutAt_some dalekMontToEdStubSpecPlaced
  lsDalekMontToEdSym lsDalekTorsionFreeSym pqxdhHookStack
  readReg_setMem_setPC_pre readReg_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
  stackAt_ecPubKeyIsCanonical_call
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives StructuralPrims WellSizedAcceptKeysInput
  bytesToBv8 cryptoBoolRegStubSpec dalekMontToEdOutBv8 dalekMontToEdStubSpec pqxdhEntryStack
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  BobCutPost PrimitivesMatchCrypto
  bobFrameAtSpqr bobParamsFieldsAt bobSpqrCutCells initBobSavedRegs pqxdhAcceptOptFieldsAt
  toSignalPqxdhPrimitives
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget (
  vecAppendElements_fast_placed_ok_cl
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  ecPubKeyIsCanonicalCallSpec pqxdhAcceptOptFieldsFrozenPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedBBudget (
  pqxdhAccept_opt_fields_placed_ok_of_block
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget (
  pqxdhAcceptErrOwnedFrozenPlacedSpec pqxdhAccept_err_owned_placed_ok_of_block
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  PqxdhPlacedHookContracts cryptoBoolRegStubBudgetSpec dalekMontToEdStubBudgetSpec
  hookSat_framelessMemcpy_of_allocMemcpyVm
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (
  initBob_to_spqr_full_frozen_placed_of_accept
  initializeBobSessionErrFrozenPlacedSpec
  initializeBobSession_cut_frozen_placed_of_accept
  initializeBobSession_err_frozen_placed_ok_of_accept
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSessionErrOwnedFrozenPlacedSpec
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. `VmPreserved`-Strengthened Block `202` (`<PublicKey>::is_canonical`) -/

private abbrev SBytes := SignalPqxdh.Bytes
private abbrev sBytesToBv8 := CryptoVerification.E2E.Pqxdh.Shared.bytesToBv8

private def dalekMontToEdStubVmSpecPlaced (P : SignalPqxdh.Primitives) :
    Spec DalekMontToEdGhost where
  pre := (dalekMontToEdStubSpecPlaced P).pre
  post := fun g s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ sBytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes g.signBit ∗
      stackAt s0.sp pqxdhHookStack

private def cryptoBoolRegStubVmSpec (pred : SBytes → Bool) (inLen : Nat) :
    Spec CryptoUnaryGhost where
  pre := (CryptoVerification.E2E.Pqxdh.Shared.cryptoBoolRegStubSpec pred inLen).pre
  post := fun g s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 32 = (if pred g.inBytes then 1#32 else 0#32)⌝ ∗
      (g.inPtr ↦ₛ sBytesToBv8 g.inBytes) ∗
      stackAt s0.sp pqxdhHookStack

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

private theorem sepWP_vm_trans {prog : Program} {target : BitVec 64} {s0 s : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (h0 : VmPreserved s0 s)
    (h : SepWP prog target s Pre (fun sf P_f => VmPreserved s sf ∧ post sf P_f)) :
    SepWP prog target s Pre (fun sf P_f => VmPreserved s0 sf ∧ post sf P_f) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hp⟩ => ⟨h0.trans hvm, hp⟩

private theorem sepWP_cut_vm {P : Program} {b mid ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) ret sm Pm post oom))) :
    SepWP (P.rebase b Hk) ret s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps1, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (hcont hvm) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem memRegion168_of_cell_and_memRegion160 (a : BitVec 64) (v : BitVec 64)
    (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (a + 8#64) bs
  refine Entails.trans (sepConj_mono_left h1) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h2)) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion160_of_bytes160 (a : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦ₛ bs) ∗ R_tail ⊢ memRegion a 160 ∗ R_tail := by
  have h1 : (a ↦ₛ bs) ⊢ memRegion a 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion a bs
  exact sepConj_mono_left h1

private theorem exists_unpack64_of_length_160 {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a R_tail,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1 ∗ ((a + 16#64) ↦₆₄ w2 ∗ ((a + 24#64) ↦₆₄ w3 ∗
        ((a + 32#64) ↦₆₄ w4 ∗ ((a + 40#64) ↦₆₄ w5 ∗ ((a + 48#64) ↦₆₄ w6 ∗ ((a + 56#64) ↦₆₄ w7 ∗
        ((a + 64#64) ↦₆₄ w8 ∗ ((a + 72#64) ↦₆₄ w9 ∗ ((a + 80#64) ↦₆₄ w10 ∗ ((a + 88#64) ↦₆₄ w11 ∗
        ((a + 96#64) ↦₆₄ w12 ∗ ((a + 104#64) ↦₆₄ w13 ∗ ((a + 112#64) ↦₆₄ w14 ∗
        ((a + 120#64) ↦₆₄ w15 ∗ ((a + 128#64) ↦₆₄ w16 ∗ ((a + 136#64) ↦₆₄ w17 ∗
        ((a + 144#64) ↦₆₄ w18 ∗ ((a + 152#64) ↦₆₄ w19 ∗
         R_tail))))))))))))))))))) =
        (a ↦ₛ bs) ∗ R_tail := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, fun a R_tail => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++
      ((bs.drop 64).take 32 ++ ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3
    rw [s3] at s2
    rw [s2] at s1
    exact s1
  symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0,
    pointsToBytes_append, h1, hp1,
    pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sepWP_memRegion160_head {prog : Program} {ret : BitVec 64} {s : State}
    (a : BitVec 64) {P_pre F_rest : SepProp}
    (heq : P_pre = memRegion a 160 ∗ F_rest) {Q : State → SepProp → Prop}
    (h : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 : BitVec 64,
      SepWP prog ret s
        ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1 ∗ ((a + 16#64) ↦₆₄ u2 ∗ ((a + 24#64) ↦₆₄ u3 ∗
        ((a + 32#64) ↦₆₄ u4 ∗ ((a + 40#64) ↦₆₄ u5 ∗ ((a + 48#64) ↦₆₄ u6 ∗ ((a + 56#64) ↦₆₄ u7 ∗
        ((a + 64#64) ↦₆₄ u8 ∗ ((a + 72#64) ↦₆₄ u9 ∗ ((a + 80#64) ↦₆₄ u10 ∗
        ((a + 88#64) ↦₆₄ u11 ∗ ((a + 96#64) ↦₆₄ u12 ∗ ((a + 104#64) ↦₆₄ u13 ∗
        ((a + 112#64) ↦₆₄ u14 ∗ ((a + 120#64) ↦₆₄ u15 ∗ ((a + 128#64) ↦₆₄ u16 ∗
        ((a + 136#64) ↦₆₄ u17 ∗ ((a + 144#64) ↦₆₄ u18 ∗ ((a + 152#64) ↦₆₄ u19 ∗
         F_rest)))))))))))))))))))) Q) :
    SepWP prog ret s P_pre Q := by
  rw [heq, memRegion_eq_exists_bytes a 160 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen => ?_
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15,
    u16, u17, u18, u19, hbs⟩ :=
    exists_unpack64_of_length_160 hlen
  rw [← hbs a F_rest]
  exact h u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19

private theorem sBytesToBv8_getD (bs : SBytes) (i : Nat) :
    (sBytesToBv8 bs).getD i 0#8 = (bs.getD i 0).toBitVec := by
  induction bs generalizing i with
  | nil => simp [sBytesToBv8, CryptoVerification.E2E.Pqxdh.Shared.bytesToBv8]
  | cons b rest ih =>
    cases i with
    | zero =>
      rcases b with ⟨⟨val, isLt⟩⟩
      simp [sBytesToBv8, CryptoVerification.E2E.Pqxdh.Shared.bytesToBv8]
    | succ j => exact ih j

private theorem uint8_getLsbD7_eq_true_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = true ↔ ((b &&& 0x80) == 0) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_getLsbD7_eq_false_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = false ↔ ((b &&& 0x80) == 0) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_true_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = true ↔ decide (b ≥ 0xED) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_false_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = false ↔ decide (b ≥ 0xED) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_b31_7f_eq (b : UInt8) (h7 : ((b &&& 0x80) == 0) = true) :
    (BitVec.truncate 32 (BitVec.signExtend 64 b.toBitVec) == 127#32) = ((b &&& 0x7F) == 0x7F) := by
  rcases b with ⟨bv⟩
  revert bv h7; decide

private theorem uint8_toBitVec_eq_ff_iff (b : UInt8) :
    (b.toBitVec = 0xff#8) ↔ (b = 0xFF) := by
  rcases b with ⟨bv⟩
  constructor
  · intro h; subst h; rfl
  · intro h; exact congrArg UInt8.toBitVec h

private theorem bv64_add1_eq_zero_iff (x : BitVec 64) :
    (x + 1#64 == 0#64) = (x == 0xffffffffffffffff#64) := by
  bv_bits

private theorem bv64_allOnes_getElem (i : Nat) (hi : i < 64) :
    (0xffffffffffffffff#64 : BitVec 64)[i] = true := by
  revert i hi; decide

private theorem bv64_and_eq_allOnes_iff (a b : BitVec 64) :
    (a &&& b = 0xffffffffffffffff#64) ↔
      (a = 0xffffffffffffffff#64 ∧ b = 0xffffffffffffffff#64) := by
  constructor
  · intro h
    constructor
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.1
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.2
  · rintro ⟨rfl, rfl⟩; rfl

private theorem pack64_eq_allOnes_iff (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7 = 0xffffffffffffffff#64) ↔
      (b0 = 0xff#8 ∧ b1 = 0xff#8 ∧ b2 = 0xff#8 ∧ b3 = 0xff#8 ∧
       b4 = 0xff#8 ∧ b5 = 0xff#8 ∧ b6 = 0xff#8 ∧ b7 = 0xff#8) := by
  unfold pack64
  bv_bits

private theorem list_take_drop_succ (xs : List UInt8) (i n : Nat) (hi : i < xs.length) :
    (xs.drop i).take (n + 1) = xs.getD i 0 :: (xs.drop (i + 1)).take n := by
  have hget : xs.getD i 0 = xs[i] := by simp [List.getD, hi]
  rw [List.drop_eq_getElem_cons hi, ← hget]
  rfl

private theorem list32_drop1_take30_eq (xs : List UInt8) (h : xs.length = 32) :
    (xs.drop 1).take 30 =
      [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] := by
  repeat (rw [list_take_drop_succ _ _ _ (by omega)])
  rfl

private theorem list32_drop1_take30_eq_replicate_iff (xs : List UInt8) (h : xs.length = 32) :
    ((xs.drop 1).take 30 == List.replicate 30 0xFF) = true ↔
      (xs.getD 1 0 = 0xFF ∧ xs.getD 2 0 = 0xFF ∧ xs.getD 3 0 = 0xFF ∧ xs.getD 4 0 = 0xFF ∧
       xs.getD 5 0 = 0xFF ∧ xs.getD 6 0 = 0xFF ∧ xs.getD 7 0 = 0xFF ∧ xs.getD 8 0 = 0xFF ∧
       xs.getD 9 0 = 0xFF ∧ xs.getD 10 0 = 0xFF ∧ xs.getD 11 0 = 0xFF ∧ xs.getD 12 0 = 0xFF ∧
       xs.getD 13 0 = 0xFF ∧ xs.getD 14 0 = 0xFF ∧ xs.getD 15 0 = 0xFF ∧ xs.getD 16 0 = 0xFF ∧
       xs.getD 17 0 = 0xFF ∧ xs.getD 18 0 = 0xFF ∧ xs.getD 19 0 = 0xFF ∧ xs.getD 20 0 = 0xFF ∧
       xs.getD 21 0 = 0xFF ∧ xs.getD 22 0 = 0xFF ∧ xs.getD 23 0 = 0xFF ∧ xs.getD 24 0 = 0xFF ∧
       xs.getD 25 0 = 0xFF ∧ xs.getD 26 0 = 0xFF ∧ xs.getD 27 0 = 0xFF ∧ xs.getD 28 0 = 0xFF ∧
       xs.getD 29 0 = 0xFF ∧ xs.getD 30 0 = 0xFF) := by
  rw [beq_iff_eq, list32_drop1_take30_eq xs h]
  change [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] =
      [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ↔ _
  simp only [List.cons.injEq, and_true]

private theorem pack64_4_allOnes_eq_drop1_take30 (keyBytes : SBytes) (h : keyBytes.length = 32) :
    ((pack64 ((sBytesToBv8 keyBytes).getD 1 0#8) ((sBytesToBv8 keyBytes).getD 2 0#8)
              ((sBytesToBv8 keyBytes).getD 3 0#8) ((sBytesToBv8 keyBytes).getD 4 0#8)
              ((sBytesToBv8 keyBytes).getD 5 0#8) ((sBytesToBv8 keyBytes).getD 6 0#8)
              ((sBytesToBv8 keyBytes).getD 7 0#8) ((sBytesToBv8 keyBytes).getD 8 0#8) &&&
            pack64 ((sBytesToBv8 keyBytes).getD 9 0#8) ((sBytesToBv8 keyBytes).getD 10 0#8)
              ((sBytesToBv8 keyBytes).getD 11 0#8) ((sBytesToBv8 keyBytes).getD 12 0#8)
              ((sBytesToBv8 keyBytes).getD 13 0#8) ((sBytesToBv8 keyBytes).getD 14 0#8)
              ((sBytesToBv8 keyBytes).getD 15 0#8) ((sBytesToBv8 keyBytes).getD 16 0#8) &&&
          (pack64 ((sBytesToBv8 keyBytes).getD 17 0#8) ((sBytesToBv8 keyBytes).getD 18 0#8)
              ((sBytesToBv8 keyBytes).getD 19 0#8) ((sBytesToBv8 keyBytes).getD 20 0#8)
              ((sBytesToBv8 keyBytes).getD 21 0#8) ((sBytesToBv8 keyBytes).getD 22 0#8)
              ((sBytesToBv8 keyBytes).getD 23 0#8) ((sBytesToBv8 keyBytes).getD 24 0#8) &&&
            pack64 ((sBytesToBv8 keyBytes).getD 23 0#8) ((sBytesToBv8 keyBytes).getD 24 0#8)
              ((sBytesToBv8 keyBytes).getD 25 0#8) ((sBytesToBv8 keyBytes).getD 26 0#8)
              ((sBytesToBv8 keyBytes).getD 27 0#8) ((sBytesToBv8 keyBytes).getD 28 0#8)
              ((sBytesToBv8 keyBytes).getD 29 0#8) ((sBytesToBv8 keyBytes).getD 30 0#8))) +
        1#64 == 0#64) =
      ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) := by
  rw [bv64_add1_eq_zero_iff]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff,
    pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff,
    list32_drop1_take30_eq_replicate_iff keyBytes h]
  simp only [sBytesToBv8_getD, uint8_toBitVec_eq_ff_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
            ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨_, _, h25, h26, h27, h28, h29, h30⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
           h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
            h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
    exact ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
           ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨h23, h24, h25, h26, h27, h28, h29, h30⟩⟩

private theorem ecPubKeyIsCanonical_tail_eq (P : SignalPqxdh.Primitives) (keyBytes edPt : SBytes)
    (h : keyBytes.length = 32)
    (hmont : P.montToEd keyBytes 0 = some edPt)
    (htors : P.isTorsionFree edPt = true)
    (hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true) :
    (if isCanonicalRef P keyBytes = true then (1#8 : BitVec 8) else 0#8) =
      BitVec.setWidth 8
        (if
          (if (BitVec.truncate 32
              (BitVec.signExtend 64 ((sBytesToBv8 keyBytes).getD 31 0#8)) == 127#32) = true then
            (pack64 ((sBytesToBv8 keyBytes).getD 1 0#8) ((sBytesToBv8 keyBytes).getD 2 0#8)
                      ((sBytesToBv8 keyBytes).getD 3 0#8) ((sBytesToBv8 keyBytes).getD 4 0#8)
                      ((sBytesToBv8 keyBytes).getD 5 0#8) ((sBytesToBv8 keyBytes).getD 6 0#8)
                      ((sBytesToBv8 keyBytes).getD 7 0#8) ((sBytesToBv8 keyBytes).getD 8 0#8) &&&
                    pack64 ((sBytesToBv8 keyBytes).getD 9 0#8) ((sBytesToBv8 keyBytes).getD 10 0#8)
                      ((sBytesToBv8 keyBytes).getD 11 0#8) ((sBytesToBv8 keyBytes).getD 12 0#8)
                      ((sBytesToBv8 keyBytes).getD 13 0#8) ((sBytesToBv8 keyBytes).getD 14 0#8)
                      ((sBytesToBv8 keyBytes).getD 15 0#8) ((sBytesToBv8 keyBytes).getD 16 0#8) &&&
                  (pack64 ((sBytesToBv8 keyBytes).getD 17 0#8) ((sBytesToBv8 keyBytes).getD 18 0#8)
                      ((sBytesToBv8 keyBytes).getD 19 0#8) ((sBytesToBv8 keyBytes).getD 20 0#8)
                      ((sBytesToBv8 keyBytes).getD 21 0#8) ((sBytesToBv8 keyBytes).getD 22 0#8)
                      ((sBytesToBv8 keyBytes).getD 23 0#8) ((sBytesToBv8 keyBytes).getD 24 0#8) &&&
                    pack64 ((sBytesToBv8 keyBytes).getD 23 0#8) ((sBytesToBv8 keyBytes).getD 24 0#8)
                      ((sBytesToBv8 keyBytes).getD 25 0#8) ((sBytesToBv8 keyBytes).getD 26 0#8)
                      ((sBytesToBv8 keyBytes).getD 27 0#8) ((sBytesToBv8 keyBytes).getD 28 0#8)
                      ((sBytesToBv8 keyBytes).getD 29 0#8) ((sBytesToBv8 keyBytes).getD 30 0#8))) +
                1#64 ==
              0#64
          else false) =
            true then
          (0#64 : BitVec 64)
        else 1#64) := by
  have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
  rw [pack64_4_allOnes_eq_drop1_take30 keyBytes h, sBytesToBv8_getD keyBytes 31,
    uint8_b31_7f_eq (keyBytes.getD 31 0) hb31_u8]
  simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
  cases ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) <;>
    cases ((keyBytes.getD 31 0 &&& 0x7F) == 0x7F) <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem State_ite_setPState_setPC (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) :
    @ite State c inst ((s.setPState ps1).setPC pc) ((s.setPState ps2).setPC pc) =
      (s.setPState (@ite PState c inst ps1 ps2)).setPC pc := by
  by_cases hc : c <;> simp [hc]

@[local simp, local wp_norm, local arm64_norm]
private theorem State_ite_setPState_setPC_setMem (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) (m : Memory) :
    @ite State c inst (((s.setPState ps1).setPC pc).setMem m)
      (((s.setPState ps2).setPC pc).setMem m) =
      ((s.setPState (@ite PState c inst ps1 ps2)).setPC pc).setMem m := by
  by_cases hc : c <;> simp [hc]

@[local simp, local wp_norm, local arm64_norm]
private theorem ConditionHolds_ite (cond : CondCode) (c : Prop) [inst : Decidable c]
    (ps1 ps2 : PState) :
    ConditionHolds cond (@ite PState c inst ps1 ps2) =
      @ite Bool c inst (ConditionHolds cond ps1) (ConditionHolds cond ps2) := by
  by_cases hc : c <;> simp [hc]

set_option maxHeartbeats 1600000 in
private theorem isCanonical_placed_vm_ok'_placed [LibsignalFullPlacement]
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubVmSpecPlaced P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubVmSpec P.isTorsionFree 160)) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (blkPl_202).base
      (withVmPreserved (CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpec P)) := by
  apply subroutine_ok_withVmPreserved_intro
  have hmont_call : subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (lsρ lsDalekMontToEdSym) (dalekMontToEdStubVmSpecPlaced P) :=
    ls_hook_ok_any hmontHook
  have htors_call : subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (lsρ lsDalekTorsionFreeSym) (cryptoBoolRegStubVmSpec P.isTorsionFree 160) :=
    ls_hook_ok_any htorsHook
  clear hmontHook htorsHook
  dsimp only [dalekMontToEdStubVmSpecPlaced, dalekMontToEdStubSpecPlaced] at hmont_call
  dsimp only [cryptoBoolRegStubVmSpec,
    CryptoVerification.E2E.Pqxdh.Shared.cryptoBoolRegStubSpec] at htors_call
  intro ⟨keyPtr, keyBytes⟩ R s0 hpc hrun hpre hsp_align
  have hsp_al : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  dsimp only [CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpec] at *
  refine SepWP.pure_elim ?_
  rintro ⟨h_1, h⟩
  subst h_1
  simp only [stackAt_ecPubKeyIsCanonical_call]
  cells_unfold
  wp_pull_exists
  have hcanon_eq : P.isCanonicalEC keyBytes = isCanonicalRef P keyBytes :=
    hisCanon keyBytes
  rw [hcanon_eq]
  have hlen_bv : (sBytesToBv8 keyBytes).length = 32 := by
    simp [sBytesToBv8, CryptoVerification.E2E.Pqxdh.Shared.bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 hlen_bv
  have hpk_sp_tail (R_tail : SepProp) :
      (s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗
      ((s0.sp - 384#64) ↦₆₄ w2 ∗ ((s0.sp - 376#64) ↦₆₄ w3 ∗ R_tail))) =
      (s0.sp - 400#64) ↦ₛ sBytesToBv8 keyBytes ∗ R_tail := by
    have hpk_sp := hpk_cells (s0.sp - 400#64)
    have ha1 : s0.sp - 400#64 + 8#64 = s0.sp - 392#64 := by bv_arith
    have ha2 : s0.sp - 400#64 + 16#64 = s0.sp - 384#64 := by bv_arith
    have ha3 : s0.sp - 400#64 + 24#64 = s0.sp - 376#64 := by bv_arith
    rw [ha1, ha2, ha3] at hpk_sp
    rw [hpk_sp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  have hpk_reg0_tail (R_tail : SepProp) :
      s0.readReg64 (Reg.gpr 0#5) ↦₆₄ w0 ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3 ∗ R_tail))) =
      s0.readReg64 (Reg.gpr 0#5) ↦ₛ sBytesToBv8 keyBytes ∗ R_tail := by
    rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5)), sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply sepWP_cut_vm (mid := lsρ lsDalekMontToEdSym)
  by_vm_steps (
    wp_conv_pre => rw [← hpk_reg0_tail]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp_all)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    wp_conv_pre => rw [hpk_reg0_tail, hpk_sp_tail]
    wp_call hmont_call ⟨keyBytes, 0, s0.sp - 400#64, s0.sp - 360#64⟩
    wp_conv_pre => rw [← hpk_sp_tail]
    have hvm12 : VmPreserved s0 sf := hvm1.trans ‹VmPreserved _ sf›
    have htr1 : sf.trace = s0.trace := by simp_all
    cases hmont : P.montToEd keyBytes 0 with
    | none =>
      have hcanon_none : isCanonicalRef P keyBytes = false := by
        simp [isCanonicalRef, hmont]
      rw [hcanon_none]
      apply sepWP_vm_trans hvm12
      by_vm_steps (
        wp_conv_pre =>
          rw [dalekMontToEdOutAt_none P keyBytes 0 hmont (s0.sp - 360#64), sepConj_assoc]
        wp_steps
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (memRegion168_of_cell_and_memRegion160 (s0.sp - 360#64) 0#64 _))))) ?_
        wp_done)
    | some edPt =>
      have hed_len : edPt.length = 160 := hmontLen keyBytes 0 edPt hmont
      have hed_bv_len : (sBytesToBv8 edPt).length = 160 := by
        simp [sBytesToBv8, CryptoVerification.E2E.Pqxdh.Shared.bytesToBv8, hed_len]
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
        e16, e17, e18, e19, hed_cells⟩ :=
        exists_unpack64_of_length_160 hed_bv_len
      refine sepWP_memRegion160_head (s0.sp - 192#64)
        (F_rest := (s0.sp - 400#64) ↦₆₄ w0 ∗
          ((s0.sp - 392#64) ↦₆₄ w1 ∗
            ((s0.sp - 384#64) ↦₆₄ w2 ∗
              ((s0.sp - 376#64) ↦₆₄ w3 ∗
                (dalekMontToEdOutAt P (s0.sp - 360#64) keyBytes 0 ∗
                  (stackAt (s0.sp - 400#64) pqxdhHookStack ∗
                    (s0.readReg64 (Reg.gpr 0#5) ↦ₛ sBytesToBv8 keyBytes ∗
                      (memRegion (s0.sp - 368#64) 8 ∗
                          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                                (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))))))))))
        (by sep_ac_rfl)
        fun u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 => ?_
      apply sepWP_cut_vm (mid := lsρ lsDalekTorsionFreeSym)
      by_vm_steps (
        wp_conv_pre =>
          rw [dalekMontToEdOutAt_some P keyBytes edPt 0 hmont hed_len (s0.sp - 360#64),
            sepConj_assoc ((s0.sp - 360#64) ↦₆₄ 1#64),
            ← hed_cells (s0.sp - 360#64 + 8#64)]
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp_all)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
        wp_conv_pre =>
          rw [hed_cells (s0.sp - 192#64), hed_cells (s0.sp - 360#64 + 8#64)]
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (memRegion168_of_cell_and_bytes160
              (s0.sp - 360#64) 1#64 hed_bv_len _)))))) ?_
        wp_call htors_call ⟨s0.sp - 192#64, edPt⟩
        have hvm23 : VmPreserved s0 sf_1 := hvm12.trans (hvm2.trans ‹VmPreserved _ sf_1›)
        have htr2 : sf_1.trace = s0.trace := by simp_all
        have hx0_tors :
            BitVec.setWidth 32 (sf_1.readReg64 (Reg.gpr 0#5)) =
              (if P.isTorsionFree edPt then 1#32 else 0#32) := by assumption
        refine SepWP.weaken_pre (memRegion160_of_bytes160 (s0.sp - 192#64) hed_bv_len _) ?_
        apply sepWP_vm_trans hvm23
        by_vm_steps (
          cases htors : P.isTorsionFree edPt with
          | false =>
            have hcanon_false : isCanonicalRef P keyBytes = false := by
              simp [isCanonicalRef, hmont, htors]
            rw [hcanon_false]
            simp only [htors, Bool.false_eq_true, ite_false] at hx0_tors
            have hx0_8 : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#8 := by
              revert hx0_tors; bv_bits
            wp_steps
            wp_done
          | true =>
            simp only [htors, ite_true] at hx0_tors
            have hfocus8 (off : Nat) (hoff : off < 32) (R_tail : SepProp) :
                s0.readReg64 (Reg.gpr 0#5) ↦ₛ sBytesToBv8 keyBytes ∗ R_tail =
                  ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₈
                    (sBytesToBv8 keyBytes).getD off 0#8) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (sBytesToBv8 keyBytes).take off) ∗
                   ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 1)) ↦ₛ
                    (sBytesToBv8 keyBytes).drop (off + 1) ∗ R_tail)) := by
              rw [pointsToBytes_focus8 (s0.readReg64 (Reg.gpr 0#5)) (sBytesToBv8 keyBytes) off
                  (by rw [hlen_bv]; exact hoff),
                sepConj_assoc, sepConj_assoc]
            have hfocus64 (off : Nat) (hoff : off + 8 ≤ 32) (R_tail : SepProp) :
                s0.readReg64 (Reg.gpr 0#5) ↦ₛ sBytesToBv8 keyBytes ∗ R_tail =
                  ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₆₄
                    pack64 ((sBytesToBv8 keyBytes).getD off 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 1) 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 2) 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 3) 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 4) 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 5) 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 6) 0#8)
                      ((sBytesToBv8 keyBytes).getD (off + 7) 0#8)) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (sBytesToBv8 keyBytes).take off) ∗
                   ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 8)) ↦ₛ
                    (sBytesToBv8 keyBytes).drop (off + 8) ∗ R_tail)) := by
              rw [pointsToBytes_focus64 (s0.readReg64 (Reg.gpr 0#5)) (sBytesToBv8 keyBytes) off
                  (by rw [hlen_bv]; exact hoff),
                sepConj_assoc, sepConj_assoc]
            wp_conv_pre => rw [hfocus8 31 (by decide)]
            wp_steps
            wp_conv_pre => rw [← hfocus8 31 (by decide)]
            cases hb31 : ((sBytesToBv8 keyBytes).getD 31 0#8).getLsbD 7 with
            | true =>
              have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = false := by
                rw [sBytesToBv8_getD] at hb31
                exact (uint8_getLsbD7_eq_true_iff _).mp hb31
              have hcanon_b31 : isCanonicalRef P keyBytes = false := by
                unfold isCanonicalRef; rw [hb31_u8]; simp
              rw [hcanon_b31]
              simp only [beq_self_eq_true, ite_true]
              wp_steps
              wp_done
            | false =>
              have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true := by
                rw [sBytesToBv8_getD] at hb31
                exact (uint8_getLsbD7_eq_false_iff _).mp hb31
              simp only [beq_iff_eq, Bool.false_eq_true, ite_false]
              wp_conv_pre => rw [hfocus8 0 (by decide)]
              wp_steps
              wp_conv_pre => rw [← hfocus8 0 (by decide)]
              cases hb0 : (BitVec.zeroExtend 64 ((sBytesToBv8 keyBytes).getD 0 0#8)).ult 237#64 with
              | true =>
                have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = false := by
                  rw [sBytesToBv8_getD] at hb0
                  exact (uint8_ult237_eq_true_iff _).mp hb0
                have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
                have hcanon_b0 : isCanonicalRef P keyBytes = true := by
                  simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8,
                    hmont, htors]
                  rfl
                rw [hcanon_b0]
                simp only [ite_true]
                wp_steps
                wp_done
              | false =>
                have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true := by
                  rw [sBytesToBv8_getD] at hb0
                  exact (uint8_ult237_eq_false_iff _).mp hb0
                simp only [Bool.false_eq_true, ite_false]
                wp_conv_pre => rw [hfocus64 1 (by decide)]
                wp_step
                wp_conv_pre => rw [← hfocus64 1 (by decide), hfocus64 9 (by decide)]
                wp_steps
                wp_conv_pre => rw [← hfocus64 9 (by decide), hfocus64 17 (by decide)]
                wp_step
                wp_conv_pre => rw [← hfocus64 17 (by decide), hfocus64 23 (by decide)]
                wp_steps
                wp_conv_pre => rw [← hfocus64 23 (by decide)]
                rw [ecPubKeyIsCanonical_tail_eq P keyBytes edPt h hmont htors hb31_u8 hb0_u8]
                wp_done)))

private theorem isCanonical_placed_vm_ok'_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubVmSpecPlaced P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubVmSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl
        (withVmPreserved (CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpec P))) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_placed_vm_ok'_placed hisCanon hmontLen hmontHook htorsHook)

/-! ## 2. Closed `[LibsignalFullPlacement]` Budget Corollaries for `Accept` & `InitBob*` -/

private theorem dalekMontToEdOutBv8_entails_outAt (P : Primitives) (outPtr : BitVec 64)
    (inBytes : Bytes) (signBit : UInt8) :
    (outPtr ↦ₛ dalekMontToEdOutBv8 P inBytes signBit) ⊢
      dalekMontToEdOutAt (toSignalPqxdhPrimitives P) outPtr inBytes signBit := by
  unfold dalekMontToEdOutBv8 dalekMontToEdOutAt
  change (outPtr ↦ₛ match P.montToEd inBytes signBit with
    | some edPt => CryptoVerification.E2E.Pqxdh.Initiator.u64le 1#64 ++
        CryptoVerification.E2E.Pqxdh.Initiator.fitBv8 160 edPt
    | none => CryptoVerification.E2E.Pqxdh.Initiator.u64le 0#64 ++ List.replicate 160 0#8) ⊢
    match P.montToEd inBytes signBit with
    | some edPt => outPtr ↦ₛ (CryptoVerification.E2E.Pqxdh.Shared.u64le 1#64 ++
        CryptoVerification.E2E.Pqxdh.Shared.fitBv8 160 edPt)
    | none => (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160
  cases P.montToEd inBytes signBit with
  | some edPt =>
    dsimp only
    have hu1 : CryptoVerification.E2E.Pqxdh.Initiator.u64le 1#64 =
        CryptoVerification.E2E.Pqxdh.Shared.u64le 1#64 := by decide
    rw [hu1]
    exact Entails.refl _
  | none =>
    dsimp only
    have hu0 : CryptoVerification.E2E.Pqxdh.Initiator.u64le 0#64 = unpack64 0#64 := by decide
    rw [hu0, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
    have hlen160 : (List.replicate 160 (0#8 : BitVec 8)).length = 160 := by decide
    have hmem : ((outPtr + 8#64) ↦ₛ List.replicate 160 (0#8 : BitVec 8)) ⊢
        memRegion (outPtr + 8#64) 160 := by
      rw [← hlen160]
      exact pointsToBytes_entails_memRegion (outPtr + 8#64) _
    exact sepConj_mono_right hmem

/-- Adapts `isCanonical_placed_vm_ok'_cl` (`Block 202`) to `AcceptBudget.ecPubKeyIsCanonicalCallSpec P`
(`withVmPreserved (ResponderCore.ecPubKeyIsCanonicalCallSpec P)`) at `lsmpl.base 202` under
`[LibsignalFullPlacement]`. -/
theorem ecPubKeyIsCanonical_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubBudgetSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) := by
  have hmontVm :
      HookSat H lsDalekMontToEdSym (dalekMontToEdStubVmSpecPlaced (toSignalPqxdhPrimitives P)) := by
    obtain ⟨fnM, hfnM, hokM⟩ := hmontHook
    refine ⟨fnM, hfnM, fun gm Rm sm hrunm hprem hspm => ?_⟩
    rcases hokM ⟨gm.inBytes, gm.signBit, gm.inPtr, gm.outPtr⟩ Rm sm hrunm hprem hspm with
      ⟨hkf, hsym, ⟨hret, hcc, hq⟩ | hrest⟩
    · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      dsimp only [dalekMontToEdStubBudgetSpec, withVmPreserved,
        dalekMontToEdStubSpec, dalekMontToEdStubVmSpecPlaced,
        dalekMontToEdStubSpecPlaced] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨hvm, hq'⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq'
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hvm, hq'.1⟩, ?_⟩
      have hb_eq : bytesToBv8 gm.inBytes = sBytesToBv8 gm.inBytes := rfl
      rw [hb_eq] at hq'
      exact Satisfies.mono
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
          (dalekMontToEdOutBv8_entails_outAt P gm.outPtr gm.inBytes gm.signBit))))
        hq'.2
    · exact ⟨hkf, hsym, Or.inr hrest⟩
  have htorsVm :
      HookSat H lsDalekTorsionFreeSym
        (cryptoBoolRegStubVmSpec (toSignalPqxdhPrimitives P).isTorsionFree 160) := by
    obtain ⟨fnT, hfnT, hokT⟩ := htorsHook
    refine ⟨fnT, hfnT, fun gt Rt st hrunt hpret hspt => ?_⟩
    rcases hokT ⟨gt.inPtr, gt.inBytes⟩ Rt st hrunt hpret hspt with
      ⟨hkf, hsym, ⟨hret, hcc, hq⟩ | hrest⟩
    · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      dsimp only [cryptoBoolRegStubBudgetSpec, withVmPreserved,
        cryptoBoolRegStubSpec, cryptoBoolRegStubVmSpec,
        CryptoVerification.E2E.Pqxdh.Shared.cryptoBoolRegStubSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨hvm, hq'⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hvm, hq'.1⟩, hq'.2⟩
    · exact ⟨hkf, hsym, Or.inr hrest⟩
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  exact (isCanonical_placed_vm_ok'_cl (P := toSignalPqxdhPrimitives P)
    hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len hmontVm htorsVm).mono_outcome
    ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp fun _ hout => hout

/-- Closed `[LibsignalFullPlacement]` budget-threaded contract for `Pqxdh::accept` (Block `79`)
lifted to any `callerProg` (`[IsLsBlockProg callerProg i H]`) at `lsmpl.base 79` from
`PqxdhPlacedHookContracts` and `HookSat H lsMemcpySym framelessMemcpySpec`. -/
theorem pqxdhAccept_opt_fields_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_opt_fields_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (vecAppendElements_fast_placed_ok_cl h_memcpy)
    (hH.hkdfExtract_ok hP)
    (hH.hkdfExpandMultiInfo_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.kyberDecaps

theorem pqxdhAccept_opt_fields_full_placed_ok_of_block_std [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`Pqxdh::accept` (Block `79`) lifted to any `callerProg` at `lsmpl.base 79`. -/
theorem pqxdhAccept_err_owned_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy

theorem pqxdhAccept_err_owned_full_placed_ok_of_block_std [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_err_owned_full_placed_ok_of_block hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded rejecting run of `initialize_bob_session`
(Block `75`) on `lsProg_75 H`. -/
theorem initializeBobSession_err_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_frozen_placed_ok_of_accept
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)

theorem initializeBobSession_err_full_placed_ok_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_full_placed_ok hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting run of
`initialize_bob_session` (Block `75`) on `lsProg_75 H`. -/
theorem initializeBobSession_err_owned_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
    (pqxdhAccept_err_owned_full_placed_ok_of_block hWF hP hH h_memcpy)

theorem initializeBobSession_err_owned_full_placed_ok_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_owned_full_placed_ok hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded frame-retaining cut of
`initialize_bob_session` (Block `75`) from entry to `spqr::initial_state` (`lsmpl.base 327`) for
SPQR-V1 `BobTailV1`. -/
theorem initBob_to_spqr_full_placed [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptOptFieldsEnv P inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        LibsignalFrozen lsmpl sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_to_spqr_full_frozen_placed_of_accept hWF
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initBob_to_spqr_full_placed_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptOptFieldsEnv P inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        LibsignalFrozen lsmpl sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_to_spqr_full_placed hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Closed `[LibsignalFullPlacement]` budget-threaded `BobCutPost` cut of `initialize_bob_session`
(Block `75`) at `spqr::initial_state` (`lsmpl.base 327`). -/
theorem initializeBobSession_cut_full_placed [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp :=
  initializeBobSession_cut_frozen_placed_of_accept hWF
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)
    s0 st inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
    outPtr drKey Frame hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc
    hsame

theorem initializeBobSession_cut_full_placed_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp :=
  initializeBobSession_cut_full_placed hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)
    s0 st inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
    outPtr drKey Frame hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc
    hsame

end LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
