/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Alloc
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Prefix
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Post-`ServiceId::parse_from_service_id_string` Tag Check & Device Dispatch (`+116 .. +176`)
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

private theorem zext32_8_43_false {b : BitVec 8} (hne : (b == 43#8) = false) :
    ((b.zeroExtend 32 == 43#32) = false) ∧
    ((b.zeroExtend 32 - 43#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-43#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 43#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem zext32_8_45_false {b : BitVec 8} (hne : (b == 45#8) = false) :
    ((b.zeroExtend 32 == 45#32) = false) ∧
    ((b.zeroExtend 32 - 45#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-45#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 45#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem kindByte_zext32_beq2 (pni : Bool) :
    (((kindByte pni).zeroExtend 32 == 2#32) = false) ∧
    (((kindByte pni).zeroExtend 32 - 2#32 == 0#32) = false) ∧
    (((kindByte pni).zeroExtend 32 + (-2#32) == 0#32) = false) := by
  cases pni <;> decide

private theorem kindByte_zext32_bne2 (pni : Bool) :
    (((kindByte pni).zeroExtend 32 != 2#32) = true) ∧
    (((kindByte pni).zeroExtend 32 - 2#32 != 0#32) = true) := by
  cases pni <;> decide

private theorem bv_ne_zero_and_ne_one {n : Nat} (h2 : 2 ≤ n) (hn : n < 2 ^ 64) :
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

set_option maxHeartbeats 800000 in
theorem step_dev_dispatch {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hFs : AllocContractsFs img A ext)
    (hres : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (name dev : List (BitVec 8))
    (hbs_eq : x.bs = name ++ (46#8 :: dev))
    (hbs_lt64 : x.bs.length < 2 ^ 64)
    (hrsplit : rsplitDot x.bs = some (name, dev))
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressName + parseSidRetOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = x.p)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.bs.length)
    (hcs : AddrUpperSaved s0 s) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      ((x.p ↦ₛ name) ∗
        parseSidResultAt ((s0.sp - 96#64) + 12#64) (serviceIdParse uuidTryParse name) ∗
        stackAt (s0.sp - 96#64) subStackSize ∗
        (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          memRegion (s0.sp - 96#64) 12 ∗
          memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
          addrSavedRegs s0.sp s0 ∗ A.pool))
      (AddrGoalPost A resStack x s0)
      (AddrPanicAllow s0) := by
  try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22] at hx19 hx20 hx21 hx22
  have hbs_sep :
      (x.p ↦ₛ x.bs) =
        (x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) := by
    rw [hbs_eq, pointsToBytes_append, pointsToBytes_cons]
  have hexit := @step_none_exit img A ext resStack hres hstkle x
  have hjoin := @step_join_plus img A ext resStack hFs hres hstkle x name
  have hfn : libsignalSessionCode.fnOff addressName = num% (ls_off% "libsignal_cli::address") :=
    addr_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode addrDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::address")) 116 64
  clear hfn
  try dsimp only [tripleRatchetProgAtExt, parseSidRetOff] at hexit hjoin hpc ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr addressName = fnBase
  examples_hide_fetches
  cases hsid : serviceIdParse uuidTryParse name with
  | none =>
    dsimp only [parseSidResultAt]
    have hnone : addrParse uuidTryParse x.bs = none := by
      simp only [addrParse, hrsplit, hsid]
    apply SepWPp.of_sepWP (mid := fnBase + noneExitOff)
    wp_steps
    apply SepWP.done
      (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
    have hpack_ps_none :
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
            addrSavedRegs s0.sp s0 ∗ A.pool)) ⊢
        ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
      have h17 := scratch17_pack_byte ((s0.sp - 96#64) + 12#64) 2#8
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left h17)) ?_
      unfold AddrFrameCommon
      rw [hbs_sep, scratch32_split_17 (s0.sp - 96#64)]
      generalize subStackSize = ssz
      exact Entails.of_eq (by ac_rfl)
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
    obtain ⟨htag_beq, htag_sub, htag_add⟩ := kindByte_zext32_beq2 pni
    obtain ⟨htag_bne, htag_sub_bne⟩ := kindByte_zext32_bne2 pni
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
            addrSavedRegs s0.sp s0 ∗ A.pool)) ⊢
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
          addrSavedRegs s0.sp s0 ∗ A.pool) := by
      have hp := parseSidResultAt_some_pack_tail ((s0.sp - 96#64) + 12#64) pni u
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left hp)) ?_
      generalize subStackSize = ssz
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hsome_pack ?_
    have hpack_scratch :
        ∀ R1 R2 R3 : SepProp,
          ((((s0.sp - 96#64) + 12#64) ↦₈ kindByte pni) ∗
            memRegion (((s0.sp - 96#64) + 12#64) + 1#64) 16 ∗
            memRegion (s0.sp - 96#64) 12 ∗
            memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
            R1 ∗ R2 ∗ R3 ∗
            memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            stackAt (s0.sp - 96#64) subStackSize ∗
            addrSavedRegs s0.sp s0 ∗ A.pool) ⊢
          ((R1 ∗ R2 ∗ R3) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
      intro R1 R2 R3
      have h17 := scratch17_pack_byte ((s0.sp - 96#64) + 12#64) (kindByte pni)
      rw [← sepConj_assoc]
      refine Entails.trans (sepConj_mono_left h17) ?_
      unfold AddrFrameCommon
      rw [scratch32_split_17 (s0.sp - 96#64)]
      generalize subStackSize = ssz
      exact Entails.of_eq (by ac_rfl)
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
      apply SepWPp.of_sepWP (mid := fnBase + noneExitOff)
      wp_steps
      apply SepWP.done
        (by simp only [noneExitOff, List.length_nil, arm64_norm, hx20, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      refine SepWPp.weaken_pre
        (Entails.trans (hpack_scratch _ _ _)
          (show _ ⊢ ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) by
            rw [hbs_sep]; exact Entails.of_eq (by ac_rfl))) ?_
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
        apply SepWPp.of_sepWP (mid := fnBase + noneExitOff)
        wp_steps
        apply SepWP.done
          (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
        rw [← haddr10, h1byte]
        refine SepWPp.weaken_pre
          (Entails.trans (hpack_scratch _ _ _)
            (show _ ⊢ ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) by
              rw [hbs_sep]; exact Entails.of_eq (by ac_rfl))) ?_
        exact hexit hnone hal0
          (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19])
          (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
      · have hne43 : (c0 == 43#8) = false := beq_eq_false_iff_ne.mpr hc43
        obtain ⟨hb43_1, hb43_2, hb43_3, hb43_4⟩ := zext32_8_43_false hne43
        by_cases hc45 : c0 = 45#8
        · subst hc45
          have hnone : addrParse uuidTryParse x.bs = none := by
            simp only [addrParse, hrsplit, hsid]; rfl
          apply SepWPp.of_sepWP (mid := fnBase + noneExitOff)
          wp_steps
          apply SepWP.done
            (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          rw [← haddr10, h1byte]
          refine SepWPp.weaken_pre
            (Entails.trans (hpack_scratch _ _ _)
              (show _ ⊢ ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) by
                rw [hbs_sep]; exact Entails.of_eq (by ac_rfl))) ?_
          exact hexit hnone hal0
            (by simp only [noneExitOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [arm64_norm, hx19])
            (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
        · have hne45 : (c0 == 45#8) = false := beq_eq_false_iff_ne.mpr hc45
          obtain ⟨hb45_1, hb45_2, hb45_3, hb45_4⟩ := zext32_8_45_false hne45
          apply SepWPp.of_sepWP_inImage (mid := fnBase + joinPlusOff) hinv
          wp_steps
          apply SepWP.done
            (by simp only [joinPlusOff, List.length_singleton, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          intro hinv5
          rw [← haddr10] at hinv5 ⊢
          rw [h1byte]
          refine SepWPp.weaken_pre
            (Entails.trans (hpack_scratch _ _ _)
              (by simp only [sepConj_assoc]; exact Entails.refl _)) ?_
          exact hjoin c0 [] (pni, u)
            hbs_eq hrsplit hsid (fun h => (hc43 h).elim) hdev_lt64 hal0 hinv5
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
      obtain ⟨hlen_ne0, hlen_ne1, hlen_sub1, hlen_add1⟩ := bv_ne_zero_and_ne_one h2len hdev_lt64
      have hcons_c0 :
          ∀ R : SepProp,
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ c0) ∗
              (((x.p + BitVec.ofNat 64 name.length + 1#64 + 1#64) ↦ₛ (c1 :: tail)) ∗ R) =
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ (c0 :: c1 :: tail)) ∗ R := by
        intro R; rw [← sepConj_assoc, ← pointsToBytes_cons]
      rw [pointsToBytes_cons, sepConj_assoc, haddr10]
      apply SepWPp.of_sepWP_inImage (mid := fnBase + joinPlusOff) hinv
      wp_steps
      apply SepWP.done
        (by simp only [joinPlusOff, arm64_norm, hx20, hx21, hx22_dev, hdev_len_sub, hdev_len_sub', *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      intro hinv5
      rw [← haddr10] at hinv5 ⊢
      rw [hcons_c0]
      refine SepWPp.weaken_pre
        (Entails.trans (hpack_scratch _ _ _)
          (by simp only [sepConj_assoc]; exact Entails.refl _)) ?_
      exact hjoin c0 (c1 :: tail) (pni, u)
        hbs_eq hrsplit hsid (fun _ => List.cons_ne_nil _ _) hdev_lt64 hal0 hinv5
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

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
