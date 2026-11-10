/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.LoopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.PrefixPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# Budget-Threaded Relocatable Post-Sign and Sign-Handling Blocks for `signal_session::address`

`RustCliAllocBudget` proofs of `step_post_sign_placed` and `step_join_plus_placed` on Block `580`
against `CalleesBudget.addressSpec`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.PrefixPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_580 blkPl_580)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddressCall addrParse isDigit parseUnsigned rsplitDot)
open CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
  (AddrUpperSaved digitSub32 digitSub32_toNat isDigit_iff_sub32_ule9 joinPlusOff loopHeadOff
   noneExitOff not_isDigit_iff_hi9 parseUnsigned_bad_digit parseUnsigned_some_of_all_digits
   postSignOff sepWPp_of_sepWP_lscro stripPlus sxtbCheckOff two_digits_madd zext64_ofNat32)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget
  (AddrFrameCommon AddrGoalPost)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
  (AddrPanicFalse sepWPp_transport_addrFrame step_none_exit_placed step_sxtb_and_alloc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.LoopPlacedBudget
  (step_digit_loop_placed)

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?

private theorem zext32_8_43_false_p {b : BitVec 8} (hne : (b == 43#8) = false) :
    ((b.zeroExtend 32 == 43#32) = false) ∧
    ((b.zeroExtend 32 - 43#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-43#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 43#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem bv_uge_3_of_ge3_p {n : Nat} (h3 : 3 ≤ n) (hn : n < 2 ^ 64) :
    (3#64).ule (BitVec.ofNat 64 n) = true ∧
      (BitVec.ofNat 64 n).ult 3#64 = false := by
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact ⟨decide_eq_true h3, decide_eq_false (by omega)⟩

private theorem parseUnsigned_some_of_all_digits_pre {dev ds : List (BitVec 8)}
    (hds : ds = stripPlus dev) (hne : ds ≠ [])
    (hdig : ∀ c ∈ ds, isDigit c = true)
    (hle : ds.foldl (fun a c => 10 * a + (c.toNat - 48)) 0 ≤ 255) :
    parseUnsigned 255 dev = some (ds.foldl (fun a c => 10 * a + (c.toNat - 48)) 0) :=
  parseUnsigned_some_of_all_digits hds hne hdig hle

/-! ### Post-sign device dispatch (`+196 .. +252` and `+288 -> +292`) -/

set_option maxHeartbeats 800000 in
theorem step_post_sign_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (hfit : FitsEnv M lim st (AddressEnv uuidTryParse x))
    (name dev ds : List (BitVec 8))
    (sidRes : Bool × List.Vector (BitVec 8) 16)
    (ptr0 : BitVec 64)
    (hbs_eq : x.bs = name ++ (46#8 :: dev))
    (hrsplit : rsplitDot x.bs = some (name, dev))
    (hsid : serviceIdParse uuidTryParse name = some sidRes)
    (hds : ds = stripPlus dev)
    (hds_ne : ds ≠ [])
    (hds_lt64 : ds.length < 2 ^ 64)
    (hdev_repack : ∀ P_ds : SepProp, (P_ds ⊢ (ptr0 ↦ₛ ds)) →
      P_ds ∗ (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
        else emp) ⊢ ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev))
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_580).base + postSignOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ptr0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ds.length)
    (hx19 : s.readReg64 .x19 = x.out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = x.p)
    (hcs : AddrUpperSaved s0 s) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s
      ((ptr0 ↦ₛ ds) ∗
        (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
         else emp) ∗
        ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
        (x.p ↦ₛ name) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s)
      (AddrGoalPost A lim resStack x st s0)
      AddrPanicFalse := by
  try dsimp only [Reg.x8, Reg.x9, Reg.x19, Reg.x20, Reg.x21] at hx8 hx9 hx19 hx20 hx21
  have hpack_none : ∀ {s_cur : State},
      ((ptr0 ↦ₛ ds) ∗
        (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
         else emp) ∗
        ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
        (x.p ↦ₛ name) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) ⊢
      ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
    intro s_cur
    have hd1 := hdev_repack (ptr0 ↦ₛ ds) (Entails.refl _)
    have hreord1 :
        ((ptr0 ↦ₛ ds) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) =
        (((ptr0 ↦ₛ ds) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp)) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      generalize AddrFrameCommon A lim resStack st s0 s_cur = afc
      sep_ac_rfl
    rw [hreord1]
    refine Entails.trans (sepConj_mono_left hd1) ?_
    have hbs_all :
        ((x.p ↦ₛ name) ∗ (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev))) = (x.p ↦ₛ x.bs) := by
      rw [← pointsToBytes_cons, ← pointsToBytes_append, ← hbs_eq]
    have hreord2 :
        (((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) =
        (((x.p ↦ₛ name) ∗ (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev))) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      generalize AddrFrameCommon A lim resStack st s0 s_cur = afc
      sep_ac_rfl
    rw [hreord2, hbs_all]
    exact Entails.refl _
  have hpack_some : ∀ {s_cur : State},
      ((ptr0 ↦ₛ ds) ∗
        (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
         else emp) ∗
        ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
        (x.p ↦ₛ name) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) ⊢
      ((x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
    intro s_cur
    have hd1 := hdev_repack (ptr0 ↦ₛ ds) (Entails.refl _)
    have hreord1 :
        ((ptr0 ↦ₛ ds) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) =
        (((ptr0 ↦ₛ ds) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp)) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      generalize AddrFrameCommon A lim resStack st s0 s_cur = afc
      sep_ac_rfl
    rw [hreord1]
    refine Entails.trans (sepConj_mono_left hd1) ?_
    have hdot :
        (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev)) =
          ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) :=
      (pointsToBytes_cons _ _ _).symm
    have hreord2 :
        (((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) =
        ((x.p ↦ₛ name) ∗ (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev)) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      generalize AddrFrameCommon A lim resStack st s0 s_cur = afc
      sep_ac_rfl
    rw [hreord2, hdot]
    exact Entails.refl _
  have hexit := @step_none_exit_placed _ M A lim st H resStack hstk hstkle x
  have halloc := @step_sxtb_and_alloc_placed _ M A lim st H resStack hFs hstk hstkle x hfit name dev sidRes
  have hloop := @step_digit_loop_placed _ M A lim st H resStack hFs hstk hstkle x hfit name dev ds sidRes ptr0
    hbs_eq hrsplit hsid hds hds_ne hds_lt64 hdev_repack
  try dsimp only [postSignOff] at hpc ⊢
  have hstrip_eq : stripPlus dev = ds := hds.symm
  clear hds
  rcases ds with _ | ⟨d0, _ | ⟨d1, rest'⟩⟩
  · exact (hds_ne rfl).elim
  · have hx9_1 : s.readReg64 (Reg.gpr 9#5) = 1#64 := hx9
    clear hx9
    rw [pointsToBytes_singleton]
    by_cases hd0 : isDigit d0 = true
    · have hhi_f : (9#32).ult (d0.zeroExtend 32 - 0x30#32) = false := by
        simpa only [digitSub32] using (not_isDigit_iff_hi9 d0).trans (by simp [hd0])
      have hule_t : (d0.zeroExtend 32 - 0x30#32).ule 9#32 = true := by
        simpa only [digitSub32] using (isDigit_iff_sub32_ule9 d0).trans hd0
      have hv0 : d0.toNat - 48 ≤ 9 := by clear * - hd0; revert d0 hd0; decide
      have hparse : parseUnsigned 255 dev = some (d0.toNat - 48) := by
        simpa [List.foldl] using parseUnsigned_some_of_all_digits_pre hstrip_eq.symm
          (List.cons_ne_nil _ _)
          (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; exact hd0)
          (by simp [List.foldl]; omega)
      apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + sxtbCheckOff) hcrl
      wp_steps
      apply SepWP.done
        (by simp only [sxtbCheckOff, arm64_norm, hx9_1, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      intro hcrl'
      transport_addr_frame
      have hw24 : (d0.zeroExtend 32 - 0x30#32).zeroExtend 64 = BitVec.ofNat 64 (d0.toNat - 48) := by
        rw [show d0.zeroExtend 32 - 0x30#32 = BitVec.ofNat 32 (d0.toNat - 48) from
          digitSub32_toNat d0 hd0]
        exact zext64_ofNat32 (d0.toNat - 48) (by omega)
      rw [← pointsToBytes_singleton]
      refine SepWPp.weaken_pre hpack_some ?_
      exact halloc (d0.toNat - 48)
        hbs_eq hrsplit hsid hparse (by omega) hal0 hcrl'
        (by simp only [sxtbCheckOff, arm64_norm, hx9_1, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hw24])
        (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
    · have hd0_f : isDigit d0 = false := Bool.eq_false_iff.mpr hd0
      have hhi_t : (9#32).ult (d0.zeroExtend 32 - 0x30#32) = true := by
        simpa only [digitSub32] using (not_isDigit_iff_hi9 d0).trans (by simp [hd0_f])
      have hule_f : (d0.zeroExtend 32 - 0x30#32).ule 9#32 = false := by
        simpa only [digitSub32] using (isDigit_iff_sub32_ule9 d0).trans hd0_f
      have hnone : addrParse uuidTryParse x.bs = none := by
        simp only [addrParse, hrsplit, hsid, parseUnsigned_bad_digit hstrip_eq.symm (by simp) hd0_f]
      apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
      wp_steps
      apply SepWP.done
        (by simp only [noneExitOff, arm64_norm, hx9_1, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      transport_addr_frame
      rw [← pointsToBytes_singleton]
      refine SepWPp.weaken_pre hpack_none ?_
      exact hexit hnone hal0
        (by simp only [noneExitOff, arm64_norm, hx9_1, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
  · rcases rest' with _ | ⟨d2, tail'⟩
    · have hx9_2 : s.readReg64 (Reg.gpr 9#5) = 2#64 := hx9
      clear hx9
      have h2bytes : (ptr0 ↦₈ d0) ∗ ((ptr0 + 1#64) ↦₈ d1) = (ptr0 ↦ₛ [d0, d1]) := by
        rw [pointsToBytes_cons, pointsToBytes_singleton]
      rw [pointsToBytes_cons, pointsToBytes_singleton, sepConj_assoc]
      by_cases hd0 : isDigit d0 = true
      · have hhi0_f : (9#32).ult (d0.zeroExtend 32 - 0x30#32) = false := by
          simpa only [digitSub32] using (not_isDigit_iff_hi9 d0).trans (by simp [hd0])
        have hule0_t : (d0.zeroExtend 32 - 0x30#32).ule 9#32 = true := by
          simpa only [digitSub32] using (isDigit_iff_sub32_ule9 d0).trans hd0
        by_cases hd1 : isDigit d1 = true
        · have hhi1_f : (9#32).ult (d1.zeroExtend 32 - 0x30#32) = false := by
            simpa only [digitSub32] using (not_isDigit_iff_hi9 d1).trans (by simp [hd1])
          have hule1_t : (d1.zeroExtend 32 - 0x30#32).ule 9#32 = true := by
            simpa only [digitSub32] using (isDigit_iff_sub32_ule9 d1).trans hd1
          have hv0 : d0.toNat - 48 ≤ 9 := by clear * - hd0; revert d0 hd0; decide
          have hv1 : d1.toNat - 48 ≤ 9 := by clear * - hd1; revert d1 hd1; decide
          set val2 := 10 * (d0.toNat - 48) + (d1.toNat - 48)
          have hparse : parseUnsigned 255 dev = some val2 := by
            simpa [List.foldl, val2] using parseUnsigned_some_of_all_digits_pre hstrip_eq.symm
              (List.cons_ne_nil _ _)
              (fun c hc => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                rcases hc with rfl | rfl <;> assumption)
              (by simp [List.foldl]; omega)
          apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + sxtbCheckOff) hcrl
          wp_steps
          apply SepWP.done
            (by simp only [sxtbCheckOff, arm64_norm, hx9_2, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          intro hcrl'
          transport_addr_frame
          have hmadd :
              ((d1.zeroExtend 32 - 0x30#32) +
                (d0.zeroExtend 32 - 0x30#32) * 10#32).zeroExtend 64 = BitVec.ofNat 64 val2 ∧
              ((d0.zeroExtend 32 - 0x30#32) * 10#32 +
                (d1.zeroExtend 32 - 0x30#32)).zeroExtend 64 = BitVec.ofNat 64 val2 := by
            have h32 : (d0.zeroExtend 32 - 0x30#32) * 10#32 + (d1.zeroExtend 32 - 0x30#32) =
                BitVec.ofNat 32 val2 := two_digits_madd d0 d1 hd0 hd1
            have hcomm : (d1.zeroExtend 32 - 0x30#32) + (d0.zeroExtend 32 - 0x30#32) * 10#32 =
                BitVec.ofNat 32 val2 := by rw [BitVec.add_comm]; exact h32
            have hz : (BitVec.ofNat 32 val2).zeroExtend 64 = BitVec.ofNat 64 val2 :=
              zext64_ofNat32 val2 (by omega)
            exact ⟨hcomm.symm ▸ hz, h32.symm ▸ hz⟩
          rcases hmadd with ⟨hmadd1, hmadd2⟩
          rw [← sepConj_assoc, h2bytes]
          refine SepWPp.weaken_pre hpack_some ?_
          exact halloc val2
            hbs_eq hrsplit hsid hparse (by omega) hal0 hcrl'
            (by simp only [sxtbCheckOff, arm64_norm, hx9_2, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [arm64_norm, hx19])
            (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx21])
            (by simp only [arm64_norm, hmadd1, hmadd2])
            (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
                simp only [AddrUpperSaved, arm64_norm, *])
        · have hd1_f : isDigit d1 = false := Bool.eq_false_iff.mpr hd1
          have hhi1_t : (9#32).ult (d1.zeroExtend 32 - 0x30#32) = true := by
            simpa only [digitSub32] using (not_isDigit_iff_hi9 d1).trans (by simp [hd1_f])
          have hule1_f : (d1.zeroExtend 32 - 0x30#32).ule 9#32 = false := by
            simpa only [digitSub32] using (isDigit_iff_sub32_ule9 d1).trans hd1_f
          have hnone : addrParse uuidTryParse x.bs = none := by
            simp only [addrParse, hrsplit, hsid,
              parseUnsigned_bad_digit hstrip_eq.symm (by simp) hd1_f]
          apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
          wp_steps
          apply SepWP.done
            (by simp only [noneExitOff, arm64_norm, hx9_2, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          transport_addr_frame
          rw [← sepConj_assoc, h2bytes]
          refine SepWPp.weaken_pre hpack_none ?_
          exact hexit hnone hal0
            (by simp only [noneExitOff, arm64_norm, hx9_2, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [arm64_norm, hx19])
            (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
                simp only [AddrUpperSaved, arm64_norm, *])
      · have hd0_f : isDigit d0 = false := Bool.eq_false_iff.mpr hd0
        have hhi0_t : (9#32).ult (d0.zeroExtend 32 - 0x30#32) = true := by
          simpa only [digitSub32] using (not_isDigit_iff_hi9 d0).trans (by simp [hd0_f])
        have hule0_f : (d0.zeroExtend 32 - 0x30#32).ule 9#32 = false := by
          simpa only [digitSub32] using (isDigit_iff_sub32_ule9 d0).trans hd0_f
        have hnone : addrParse uuidTryParse x.bs = none := by
          simp only [addrParse, hrsplit, hsid,
            parseUnsigned_bad_digit hstrip_eq.symm (by simp) hd0_f]
        apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
        wp_steps
        apply SepWP.done
          (by simp only [noneExitOff, arm64_norm, hx9_2, *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
        transport_addr_frame
        rw [← sepConj_assoc, h2bytes]
        refine SepWPp.weaken_pre hpack_none ?_
        exact hexit hnone hal0
          (by simp only [noneExitOff, arm64_norm, hx9_2, *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19])
          (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
              simp only [AddrUpperSaved, arm64_norm, *])
    · obtain ⟨h3_ule, h3_ult⟩ := bv_uge_3_of_ge3_p
        (n := (d0 :: d1 :: d2 :: tail').length) (by simp) hds_lt64
      apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + loopHeadOff) hcrl
      wp_steps
      apply SepWP.done
        (by simp only [loopHeadOff, arm64_norm, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      intro hcrl'
      transport_addr_frame
      have hpack_loop : ∀ {s_cur : State},
          ((ptr0 ↦ₛ (d0 :: d1 :: d2 :: tail')) ∗
            (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
             else emp) ∗
            ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
            (x.p ↦ₛ name) ∗
            memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) ⊢
          ((ptr0 ↦ₛ []) ∗ (ptr0 ↦ₛ (d0 :: d1 :: d2 :: tail')) ∗
            (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
             else emp) ∗
            ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
            (x.p ↦ₛ name) ∗
            memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
        intro s_cur
        rw [pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
      refine SepWPp.weaken_pre hpack_loop ?_
      exact hloop (d0 :: d1 :: d2 :: tail') [] ptr0
        rfl (Nat.zero_le _) (fun _ hc => nomatch hc) (by simp)
        hal0 hcrl'
        (by simp only [loopHeadOff, arm64_norm, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx8])
        (by simp only [arm64_norm, hx9])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [List.foldl, arm64_norm])
        (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
            simp only [AddrUpperSaved, arm64_norm, *])

/-! ### Sign-handling join point (`+180 .. +192`) -/

theorem step_join_plus_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (hfit : FitsEnv M lim st (AddressEnv uuidTryParse x))
    (name : List (BitVec 8))
    (c0 : BitVec 8) (rest_dev : List (BitVec 8))
    (sidRes : Bool × List.Vector (BitVec 8) 16)
    (hbs_eq : x.bs = name ++ (46#8 :: c0 :: rest_dev))
    (hrsplit : rsplitDot x.bs = some (name, c0 :: rest_dev))
    (hsid : serviceIdParse uuidTryParse name = some sidRes)
    (hplus_ne : c0 = 43#8 → rest_dev ≠ [])
    (hdev_lt64 : (c0 :: rest_dev).length < 2 ^ 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_580).base + joinPlusOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (c0 :: rest_dev).length)
    (hx9 : s.readReg64 .x9 = c0.zeroExtend 64)
    (hx10 : s.readReg64 .x10 = x.p + BitVec.ofNat 64 name.length + 1#64)
    (hx19 : s.readReg64 .x19 = x.out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = x.p)
    (hcs : AddrUpperSaved s0 s) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s
      (((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ (c0 :: rest_dev)) ∗
        ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
        (x.p ↦ₛ name) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s)
      (AddrGoalPost A lim resStack x st s0)
      AddrPanicFalse := by
  try dsimp only [Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21] at hx8 hx9 hx10 hx19 hx20 hx21
  have hpost := @step_post_sign_placed _ M A lim st H resStack hFs hstk hstkle x hfit name
  try dsimp only [joinPlusOff] at hpc ⊢
  by_cases hplus : c0 = 43#8
  · subst hplus
    rw [pointsToBytes_cons, sepConj_assoc]
    apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + postSignOff) hcrl
    wp_steps
    apply SepWP.done
      (by simp only [postSignOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
    intro hcrl'
    transport_addr_frame
    have hsub1 : BitVec.ofNat 64 (43#8 :: rest_dev).length - 1#64 =
        BitVec.ofNat 64 rest_dev.length := by
      have h1 : (43#8 :: rest_dev).length = rest_dev.length + 1 := rfl
      rw [h1] at hdev_lt64 ⊢
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hdev_lt64, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hdev_lt64)]
      omega
    have hpack_plus : ∀ {s_cur : State},
        (((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64 + 1#64) ↦ₛ rest_dev) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) ⊢
        (((x.p + BitVec.ofNat 64 name.length + 1#64 + 1#64) ↦ₛ rest_dev) ∗
          (if (43#8 :: rest_dev).head? = some 43#8 then
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8) else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      intro s_cur
      simp only [List.head?_cons, ↓reduceIte]
      generalize AddrFrameCommon A lim resStack st s0 s_cur = afc
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpack_plus ?_
    exact hpost (43#8 :: rest_dev) rest_dev sidRes
      (x.p + BitVec.ofNat 64 name.length + 1#64 + 1#64) hbs_eq hrsplit hsid
      (by simp [stripPlus]) (hplus_ne rfl) (by simp only [List.length_cons] at hdev_lt64; omega)
      (fun P_ds hP => by
        simp only [List.head?_cons, ↓reduceIte]
        rw [pointsToBytes_cons, sepConj_comm]
        exact sepConj_mono_right hP)
      hal0 hcrl'
      (by simp only [postSignOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx9, hx10]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, hx8, hx9, hsub1]; try (clear * - hsub1; bv_omega))
      (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21])
      (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
  · have hne43 : (c0 == 43#8) = false := beq_eq_false_iff_ne.mpr hplus
    obtain ⟨hbeq43_1, hbeq43_2, hbeq43_3, hbeq43_4⟩ := zext32_8_43_false_p hne43
    apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + postSignOff) hcrl
    wp_steps
    apply SepWP.done
      (by simp only [postSignOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
    intro hcrl'
    transport_addr_frame
    have hhead_ne : ((c0 :: rest_dev).head? = some 43#8) = False :=
      eq_false fun h => hplus (Option.some.inj h)
    have hpack_noplus : ∀ {s_cur : State},
        (((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ (c0 :: rest_dev)) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) ⊢
        (((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ (c0 :: rest_dev)) ∗
          (if (c0 :: rest_dev).head? = some 43#8 then
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8) else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_cur) := by
      intro s_cur
      simp only [hhead_ne, ↓reduceIte]
      generalize AddrFrameCommon A lim resStack st s0 s_cur = afc
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpack_noplus ?_
    exact hpost (c0 :: rest_dev) (c0 :: rest_dev) sidRes
      (x.p + BitVec.ofNat 64 name.length + 1#64) hbs_eq hrsplit hsid
      (by simp [stripPlus, hplus]) (List.cons_ne_nil _ _) hdev_lt64
      (fun P_ds hP => by simp only [hhead_ne, ↓reduceIte, sepConj_emp]; exact hP)
      hal0 hcrl'
      (by simp only [postSignOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx9, hx10, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, hx8, hx9, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21])
      (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.PrefixPlacedBudget
