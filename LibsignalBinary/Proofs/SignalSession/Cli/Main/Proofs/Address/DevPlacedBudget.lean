/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.PrefixPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.DevPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# Budget-Threaded Relocatable Post-`ServiceId` Tag Check and Device Dispatch

`RustCliAllocBudget` proof of `step_dev_dispatch_placed` on Block `580` against
`CalleesBudget.addressSpec`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.DevPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (kindByte serviceIdParse uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (extHookStack parseSidResultAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_580 blkPl_580)
open CryptoVerification.SignalSession.Cli.MainHops (AddressCall addrParse rsplitDot)
open CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
  (AddrUpperSaved addrSavedRegs joinPlusOff noneExitOff parseSidResultAt_some_pack_tail
   parseSidRetOff scratch17_pack_byte scratch32_split_17 sepWPp_of_sepWP_lscro subStackSize)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget
  (AddrFrameCommon AddrGoalPost)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
  (AddrPanicFalse step_none_exit_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.PrefixPlacedBudget
  (step_join_plus_placed)

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?

private theorem zext32_8_43_false_d {b : BitVec 8} (hne : (b == 43#8) = false) :
    ((b.zeroExtend 32 == 43#32) = false) ∧
    ((b.zeroExtend 32 - 43#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-43#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 43#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem zext32_8_45_false_d {b : BitVec 8} (hne : (b == 45#8) = false) :
    ((b.zeroExtend 32 == 45#32) = false) ∧
    ((b.zeroExtend 32 - 45#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-45#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 45#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem kindByte_zext32_beq2_d (pni : Bool) :
    (((kindByte pni).zeroExtend 32 == 2#32) = false) ∧
    (((kindByte pni).zeroExtend 32 - 2#32 == 0#32) = false) ∧
    (((kindByte pni).zeroExtend 32 + (-2#32) == 0#32) = false) := by
  cases pni <;> decide

private theorem kindByte_zext32_bne2_d (pni : Bool) :
    (((kindByte pni).zeroExtend 32 != 2#32) = true) ∧
    (((kindByte pni).zeroExtend 32 - 2#32 != 0#32) = true) := by
  cases pni <;> decide

private theorem bv_ne_zero_and_ne_one_d {n : Nat} (h2 : 2 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false ∧
    (BitVec.ofNat 64 n == 1#64) = false ∧
    (BitVec.ofNat 64 n - 1#64 == 0#64) = false ∧
    (BitVec.ofNat 64 n + (-1#64) == 0#64) = false := by
  have h0 : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h; have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht; change n = 0 at ht; omega
  have h1 : BitVec.ofNat 64 n ≠ 1#64 := by
    intro h; have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht; change n = 1 at ht; omega
  have hsub1 : BitVec.ofNat 64 n - 1#64 ≠ 0#64 := by
    intro h; exact h1 (by clear * - h; bv_omega)
  have hadd1 : BitVec.ofNat 64 n + (-1#64) ≠ 0#64 := by
    intro h; exact h1 (by clear * - h; bv_omega)
  exact ⟨beq_eq_false_iff_ne.mpr h0, beq_eq_false_iff_ne.mpr h1,
    beq_eq_false_iff_ne.mpr hsub1, beq_eq_false_iff_ne.mpr hadd1⟩

private theorem with_vm_state {prog : Program} {ret : BitVec 64} {s s_cur : State}
    {Pre : SepProp} {post Qp : State → SepProp → Prop}
    (hvm : VmPreserved s s_cur)
    (h : VmPreserved s s_cur → SepWPp prog ret s_cur Pre post Qp) :
    SepWPp prog ret s_cur Pre post Qp :=
  h hvm

set_option maxHeartbeats 800000 in
theorem step_dev_dispatch_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hres : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (hfit : FitsEnv M lim st (AddressEnv uuidTryParse x))
    (name dev : List (BitVec 8))
    (hbs_eq : x.bs = name ++ (46#8 :: dev))
    (hbs_lt64 : x.bs.length < 2 ^ 64)
    (hrsplit : rsplitDot x.bs = some (name, dev))
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_580).base + parseSidRetOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = x.p)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.bs.length)
    (hcs : AddrUpperSaved s0 s) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s
      ((x.p ↦ₛ name) ∗
        parseSidResultAt ((s0.sp - 96#64) + 12#64) (serviceIdParse uuidTryParse name) ∗
        stackAt (s0.sp - 96#64) subStackSize ∗
        (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          memRegion (s0.sp - 96#64) 12 ∗
          memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
          addrSavedRegs s0.sp s0 ∗ A.pool lim st s))
      (AddrGoalPost A lim resStack x st s0)
      AddrPanicFalse := by
  try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22] at hx19 hx20 hx21 hx22
  have hbs_sep :
      (x.p ↦ₛ x.bs) =
        (x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) := by
    rw [hbs_eq, pointsToBytes_append, pointsToBytes_cons]
  have hexit := @step_none_exit_placed _ M A lim st H resStack hres hstkle x
  have hjoin := @step_join_plus_placed _ M A lim st H resStack hFs hres hstkle x hfit name
  try dsimp only [parseSidRetOff] at hpc ⊢
  cases hsid : serviceIdParse uuidTryParse name with
  | none =>
    dsimp only [parseSidResultAt]
    have hnone : addrParse uuidTryParse x.bs = none := by
      simp only [addrParse, hrsplit, hsid]
    apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
    wp_steps
    apply SepWP.done
      (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
    refine with_vm_state (s := s) (by simp only [arm64_norm]) fun hvm => ?_
    rw [← A.pool_of_vmPreserved hvm]
    have hpack_ps_none : ∀ {s_cur : State},
        ((x.p ↦ₛ name) ∗
          ((((s0.sp - 96#64) + 12#64) ↦₈ 2#8) ∗
            memRegion (((s0.sp - 96#64) + 12#64) + 1#64) 16) ∗
          stackAt (s0.sp - 96#64) subStackSize ∗
          (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
            memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            memRegion (s0.sp - 96#64) 12 ∗
            memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
            addrSavedRegs s0.sp s0 ∗ A.pool lim st s_cur)) ⊢
        ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      intro s_cur
      have h17 := scratch17_pack_byte ((s0.sp - 96#64) + 12#64) 2#8
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left h17)) ?_
      unfold AddrFrameCommon
      rw [hbs_sep, scratch32_split_17 (s0.sp - 96#64)]
      generalize subStackSize = ssz
      generalize addrSavedRegs s0.sp s0 = asr
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpack_ps_none ?_
    exact hexit hnone hal0
      (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19])
      (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
  | some sidRes =>
    rcases sidRes with ⟨pni, u⟩
    obtain ⟨htag_beq, htag_sub, htag_add⟩ := kindByte_zext32_beq2_d pni
    obtain ⟨htag_bne, htag_sub_bne⟩ := kindByte_zext32_bne2_d pni
    have hsome_pack :
        ((x.p ↦ₛ name) ∗
          parseSidResultAt ((s0.sp - 96#64) + 12#64) (some (pni, u)) ∗
          stackAt (s0.sp - 96#64) subStackSize ∗
          (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
            memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            memRegion (s0.sp - 96#64) 12 ∗
            memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
            addrSavedRegs s0.sp s0 ∗ A.pool lim st s)) ⊢
        ((((s0.sp - 96#64) + 12#64) ↦₈ kindByte pni) ∗
          memRegion (((s0.sp - 96#64) + 12#64) + 1#64) 16 ∗
          memRegion (s0.sp - 96#64) 12 ∗
          memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          stackAt (s0.sp - 96#64) subStackSize ∗
          addrSavedRegs s0.sp s0 ∗ A.pool lim st s) := by
      have hp := parseSidResultAt_some_pack_tail ((s0.sp - 96#64) + 12#64) pni u
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left hp)) ?_
      generalize subStackSize = ssz
      generalize addrSavedRegs s0.sp s0 = asr
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hsome_pack ?_
    have hpack_scratch :
        ∀ {s_cur : State} (R1 R2 R3 : SepProp),
          ((((s0.sp - 96#64) + 12#64) ↦₈ kindByte pni) ∗
            memRegion (((s0.sp - 96#64) + 12#64) + 1#64) 16 ∗
            memRegion (s0.sp - 96#64) 12 ∗
            memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
            R1 ∗ R2 ∗ R3 ∗
            memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            stackAt (s0.sp - 96#64) subStackSize ∗
            addrSavedRegs s0.sp s0 ∗ A.pool lim st s_cur) ⊢
          ((R1 ∗ R2 ∗ R3) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      intro s_cur R1 R2 R3
      have h17 := scratch17_pack_byte ((s0.sp - 96#64) + 12#64) (kindByte pni)
      rw [← sepConj_assoc]
      refine Entails.trans (sepConj_mono_left h17) ?_
      unfold AddrFrameCommon
      rw [scratch32_split_17 (s0.sp - 96#64)]
      generalize subStackSize = ssz
      generalize addrSavedRegs s0.sp s0 = asr
      exact Entails.of_eq (by sep_ac_rfl)
    have htot : x.bs.length = name.length + 1 + dev.length := by
      rw [hbs_eq, List.length_append, List.length_cons]; omega
    have hdev_lt64 : dev.length < 2 ^ 64 := by omega
    have hnp1_lt64 : name.length + 1 < 2 ^ 64 := by omega
    have htot_lt64 : name.length + 1 + dev.length < 2 ^ 64 := by omega
    have hx22_dev :
        s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (name.length + 1 + dev.length) := by
      rw [hx22, htot]
    have hdev_len_sub :
        BitVec.ofNat 64 (name.length + 1 + dev.length) - (BitVec.ofNat 64 name.length + 1#64) =
          BitVec.ofNat 64 dev.length := by
      have hp1 : BitVec.ofNat 64 name.length + 1#64 = BitVec.ofNat 64 (name.length + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hnp1_lt64, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hnp1_lt64)]
      rw [hp1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt htot_lt64, Nat.mod_eq_of_lt hnp1_lt64, Nat.mod_eq_of_lt hdev_lt64]
      omega
    have hdev_len_sub' :
        BitVec.ofNat 64 (name.length + 1 + dev.length) + -(BitVec.ofNat 64 name.length + 1#64) =
          BitVec.ofNat 64 dev.length := by
      rw [← BitVec.sub_eq_add_neg]; exact hdev_len_sub
    clear hx22 htot hnp1_lt64 htot_lt64
    have haddr10 :
        x.p + BitVec.ofNat 64 name.length + 1#64 =
          x.p + (BitVec.ofNat 64 name.length + 1#64) :=
      BitVec.add_assoc _ _ _
    rcases dev with _ | ⟨c0, _ | ⟨c1, tail⟩⟩
    · have hnone : addrParse uuidTryParse x.bs = none := by
        simp only [addrParse, hrsplit, hsid]; rfl
      apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
      wp_steps
      apply SepWP.done
        (by simp only [noneExitOff, List.length_nil, arm64_norm, hx20, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      refine with_vm_state (s := s) (by simp only [arm64_norm]) fun hvm => ?_
      rw [← A.pool_of_vmPreserved hvm]
      refine SepWPp.weaken_pre
        (Entails.trans (hpack_scratch _ _ _)
          (show _ ⊢ ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 _) by
            rw [hbs_sep]
            generalize AddrFrameCommon A lim resStack st s0 _ = afc
            exact Entails.of_eq (by sep_ac_rfl))) ?_
      exact hexit hnone hal0
        (by simp only [noneExitOff, List.length_nil, arm64_norm, hx20, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
    · have hlen1 : [c0].length = 1 := rfl
      have h1byte :
          ∀ (b : BitVec 8) (R : SepProp),
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ b) ∗ R =
              ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ [b]) ∗ R := by
        intro b R; rw [pointsToBytes_singleton]
      rw [pointsToBytes_singleton, haddr10]
      by_cases hc43 : c0 = 43#8
      · subst hc43
        have hnone : addrParse uuidTryParse x.bs = none := by
          simp only [addrParse, hrsplit, hsid]; rfl
        apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
        wp_steps
        apply SepWP.done
          (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
        refine with_vm_state (s := s) (by simp only [arm64_norm]) fun hvm => ?_
        rw [← A.pool_of_vmPreserved hvm]
        rw [← haddr10, h1byte]
        refine SepWPp.weaken_pre
          (Entails.trans (hpack_scratch _ _ _)
            (show _ ⊢ ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 _) by
              rw [hbs_sep]
              generalize AddrFrameCommon A lim resStack st s0 _ = afc
              exact Entails.of_eq (by sep_ac_rfl))) ?_
        exact hexit hnone hal0
          (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19])
          (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
      · have hne43 : (c0 == 43#8) = false := beq_eq_false_iff_ne.mpr hc43
        obtain ⟨hb43_1, hb43_2, hb43_3, hb43_4⟩ := zext32_8_43_false_d hne43
        by_cases hc45 : c0 = 45#8
        · subst hc45
          have hnone : addrParse uuidTryParse x.bs = none := by
            simp only [addrParse, hrsplit, hsid]; rfl
          apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
          wp_steps
          apply SepWP.done
            (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          refine with_vm_state (s := s) (by simp only [arm64_norm]) fun hvm => ?_
          rw [← A.pool_of_vmPreserved hvm]
          rw [← haddr10, h1byte]
          refine SepWPp.weaken_pre
            (Entails.trans (hpack_scratch _ _ _)
              (show _ ⊢ ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 _) by
                rw [hbs_sep]
                generalize AddrFrameCommon A lim resStack st s0 _ = afc
                exact Entails.of_eq (by sep_ac_rfl))) ?_
          exact hexit hnone hal0
            (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [arm64_norm, hx19])
            (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
        · have hne45 : (c0 == 45#8) = false := beq_eq_false_iff_ne.mpr hc45
          obtain ⟨hb45_1, hb45_2, hb45_3, hb45_4⟩ := zext32_8_45_false_d hne45
          apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + joinPlusOff) hcrl
          wp_steps
          apply SepWP.done
            (by simp only [joinPlusOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          intro hcrl5
          refine with_vm_state (s := s) (by simp only [arm64_norm]) fun hvm => ?_
          rw [← A.pool_of_vmPreserved hvm]
          rw [← haddr10] at hcrl5 ⊢
          rw [h1byte]
          refine SepWPp.weaken_pre
            (Entails.trans (hpack_scratch _ _ _)
              (by simp only [sepConj_assoc]; exact Entails.refl _)) ?_
          exact hjoin c0 [] (pni, u)
            hbs_eq hrsplit hsid (fun h => (hc43 h).elim) hdev_lt64 hal0 hcrl5
            (by simp only [joinPlusOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [List.length_singleton, arm64_norm, hx20, hx22_dev, hdev_len_sub, hdev_len_sub', *])
            (by simp only [arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *])
            (by simp only [arm64_norm, hx20, hx21])
            (by simp only [arm64_norm, hx19])
            (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx21])
            (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
    · have h2len : 2 ≤ (c0 :: c1 :: tail).length := by simp
      obtain ⟨hlen_ne0, hlen_ne1, hlen_sub1, hlen_add1⟩ := bv_ne_zero_and_ne_one_d h2len hdev_lt64
      have hcons_c0 :
          ∀ R : SepProp,
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ c0) ∗
              (((x.p + BitVec.ofNat 64 name.length + 1#64 + 1#64) ↦ₛ (c1 :: tail)) ∗ R) =
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ (c0 :: c1 :: tail)) ∗ R := by
        intro R; rw [← sepConj_assoc, ← pointsToBytes_cons]
      rw [pointsToBytes_cons, sepConj_assoc, haddr10]
      apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + joinPlusOff) hcrl
      wp_steps
      apply SepWP.done
        (by simp only [joinPlusOff, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      intro hcrl5
      refine with_vm_state (s := s) (by simp only [arm64_norm]) fun hvm => ?_
      rw [← A.pool_of_vmPreserved hvm]
      rw [← haddr10] at hcrl5 ⊢
      rw [hcons_c0]
      refine SepWPp.weaken_pre
        (Entails.trans (hpack_scratch _ _ _)
          (by simp only [sepConj_assoc]; exact Entails.refl _)) ?_
      exact hjoin c0 (c1 :: tail) (pni, u)
        hbs_eq hrsplit hsid (fun _ => List.cons_ne_nil _ _) hdev_lt64 hal0 hcrl5
        (by simp only [joinPlusOff, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx20, hx22_dev, hdev_len_sub, hdev_len_sub'])
        (by simp only [arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *])
        (by simp only [arm64_norm, hx20, hx21])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.DevPlacedBudget
