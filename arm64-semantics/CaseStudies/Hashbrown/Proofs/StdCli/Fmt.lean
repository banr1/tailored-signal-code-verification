/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.FormatBase

/-!
# Placement-Generic `<u64 as core::fmt::Display>::fmt` Proofs

Placement-generic symbolic execution and `subroutine_ok` contracts for `Formatter::pad_integral`
and `<u64 as core::fmt::Display>::fmt` parameterized by `HbCliLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

private theorem memRegion1_entails (p : BitVec 64) :
    memRegion p 1 ⊢ ∃∗ b : BitVec 8, p ↦₈ b := by
  have h := memRegion_succ_off p 0 0 (by decide)
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  rw [h0, memRegion_zero, sepConj_emp] at h
  exact Entails.of_eq h

private theorem pointsTo8_pair_eq_16 (p : BitVec 64) (b0 b1 : BitVec 8) :
    ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1)) = (p ↦₁₆ (b1 ++ b0)) := by
  have h := pointsToBytes_cons_off p 0 b0 [b1]
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have h1 : p + BitVec.ofNat 64 1 = p + 1#64 := rfl
  rw [h0, h1, pointsToBytes_singleton, pointsToBytes2_eq_pointsTo16] at h
  exact h.symm

private theorem memRegion2_entails (p : BitVec 64) :
    memRegion p 2 ⊢ ∃∗ w : BitVec 16, p ↦₁₆ w := by
  have h2 := memRegion_succ_off p 0 1 (by decide)
  have h1 := memRegion_succ_off p 1 0 (by decide)
  have hp0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have hp1 : p + BitVec.ofNat 64 1 = p + 1#64 := rfl
  rw [hp1, memRegion_zero, sepConj_emp] at h1
  rw [hp0, hp1, h1, show (1 + 1 : Nat) = 2 from rfl] at h2
  rw [h2, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b0 => ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b1 => ?_
  rw [pointsTo8_pair_eq_16]
  exact Entails.sepExists_intro (b1 ++ b0)

private theorem memRegion4_entails8 (p : BitVec 64) :
    memRegion p 4 ⊢
      (∃∗ b0 : BitVec 8, p ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (p + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (p + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (p + 3#64) ↦₈ b3) := by
  rw [memRegion_split_le p 2 4 (by decide) (by decide),
      memRegion_split_le p 1 2 (by decide) (by decide),
      memRegion_split_le (p + 2#64) 1 2 (by decide) (by decide),
      show p + 2#64 + 1#64 = p + 3#64 by simp [bv_lin_norm],
      sepConj_assoc]
  exact sepConj_mono (memRegion1_entails p)
    (sepConj_mono (memRegion1_entails (p + 1#64))
      (sepConj_mono (memRegion1_entails (p + 2#64)) (memRegion1_entails (p + 3#64))))

private theorem pointsTo16_pair_eq_fourDecDigits (p : BitVec 64) (r : Nat) :
    ((p ↦₁₆ pack16 (decDigitByte (r / 100 / 10)) (decDigitByte (r / 100 % 10))) ∗
     ((p + 2#64) ↦₁₆ pack16 (decDigitByte (r % 100 / 10)) (decDigitByte (r % 100 % 10)))) =
    (p ↦ₛ fourDecDigits r) := by
  unfold pack16 fourDecDigits
  rw [← pointsToBytes2_eq_pointsTo16, ← pointsToBytes2_eq_pointsTo16]
  have happ := pointsToBytes_append p
    [decDigitByte (r / 100 / 10), decDigitByte (r / 100 % 10)]
    [decDigitByte (r % 100 / 10), decDigitByte (r % 100 % 10)]
  simpa only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] using happ.symm

private theorem pointsTo8_quad_eq_fourDecDigits (p : BitVec 64) (r : Nat) :
    ((p ↦₈ decDigitByte (r / 100 / 10)) ∗
     ((p + 1#64) ↦₈ decDigitByte (r / 100 % 10)) ∗
     ((p + 2#64) ↦₈ decDigitByte (r % 100 / 10)) ∗
     ((p + 3#64) ↦₈ decDigitByte (r % 100 % 10))) =
    (p ↦ₛ fourDecDigits r) := by
  have h1 := pointsTo8_pair_eq_16 p (decDigitByte (r / 100 / 10)) (decDigitByte (r / 100 % 10))
  have h2 := pointsTo8_pair_eq_16 (p + 2#64) (decDigitByte (r % 100 / 10)) (decDigitByte (r % 100 % 10))
  rw [show p + 2#64 + 1#64 = p + 3#64 by simp [bv_lin_norm]] at h2
  rw [← sepConj_assoc, h1, h2]
  exact pointsTo16_pair_eq_fourDecDigits p r

private theorem bv_div_10000 {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (BitVec.ofNat 64 m) * 0x346dc5d63886594b#128) >>> 64) >>> 11 =
      BitVec.ofNat 64 (m / 10000) := by
  have hc128 : (0x346dc5d63886594b#128) = BitVec.zeroExtend 128 0x346dc5d63886594b#64 := rfl
  rw [hc128]
  change (((BitVec.ofNat 64 m).setWidth 128 * (0x346dc5d63886594b#64).setWidth 128) >>> 64).setWidth 64 >>> 11 =
    BitVec.ofNat 64 (m / 10000)
  rw [BitVec.setWidth_umulh]
  apply BitVec.eq_of_toNat_eq
  have hb : (0x346dc5d63886594b#64).toNat = 3777893186295716171 := rfl
  simp only [BitVec.toNat_ushiftRight, hb, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hm]
  have hhi : m * 3777893186295716171 / 18446744073709551616 < 2 ^ 64 := by omega
  have hq : m / 10000 < 2 ^ 64 := by omega
  have hpow64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hpow11 : (2 : Nat) ^ 11 = 2048 := by decide
  rw [hpow64, hpow11] at *
  rw [Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hq, Nat.div_div_eq_div_mul]
  have hmagic := magic_div_10000 hm
  omega

private theorem bv_msub32_rem (x c : Nat) (hc : 0 < c) (hr : x % c < 2 ^ 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 x) -
      BitVec.truncate 32 (BitVec.ofNat 64 (x / c)) * BitVec.ofNat 32 c) =
      BitVec.ofNat 64 (x % c) := by
  have hx : x = x % c + (x / c) * c := by have := Nat.div_add_mod' x c; omega
  have h32 : BitVec.truncate 32 (BitVec.ofNat 64 x) -
      BitVec.truncate 32 (BitVec.ofNat 64 (x / c)) * BitVec.ofNat 32 c = BitVec.ofNat 32 (x % c) := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    conv => lhs; arg 1; rw [hx]
    rw [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.add_sub_cancel]
  rw [h32]
  apply BitVec.eq_of_toNat_eq
  have _ := hc
  simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : x % c < 2 ^ 64)]

private theorem bv_lsr2_32 {r : Nat} (hr : r < 10000) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 r))) >>> 2 =
      BitVec.ofNat 64 (r / 4) ∧
    (BitVec.ofNat 64 (r / 4) &&& 16383#64) = BitVec.ofNat 64 (r / 4) := by
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : r < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : r < 2 ^ 32), Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 64)]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 64)]
    have hm14 : (16383#64).toNat = 2 ^ 14 - 1 := rfl
    rw [hm14, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 14)]

private theorem bv_magic_div100_step {r : Nat} (hr : r < 10000) :
    BitVec.truncate 32
      ((BitVec.zeroExtend 64 (0#32 + BitVec.truncate 32 (BitVec.ofNat 64 (r / 4)) * 5243#32)) >>> 17) =
      BitVec.ofNat 32 (r / 100) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 32 (r / 100)) = BitVec.ofNat 64 (r / 100) ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 r) -
      BitVec.ofNat 32 (r / 100) * 100#32) = BitVec.ofNat 64 (r % 100) := by
  have hm := magic_div_100 hr
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : r / 4 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (r / 4) * 5243 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (r / 4) * 5243 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : r / 100 < 2 ^ 32)]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : r / 100 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : r / 100 < 2 ^ 64)]
  · have hrem := bv_msub32_rem r 100 (by decide) (by omega)
    have hq32 : BitVec.truncate 32 (BitVec.ofNat 64 (r / 100)) = BitVec.ofNat 32 (r / 100) := by
      rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rwa [hq32] at hrem

private theorem bv_uxtw_lsl1 {d : Nat} (hd : d < 100) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 d))) <<< 1 = BitVec.ofNat 64 (2 * d) ∧
    (BitVec.zeroExtend 64 (BitVec.truncate 16 (BitVec.ofNat 64 d))) <<< 1 = BitVec.ofNat 64 (2 * d) ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 d)) = BitVec.ofNat 64 d ∧
    (BitVec.ofNat 64 d &&& 0xffff#64) = BitVec.ofNat 64 d ∧
    (BitVec.ofNat 64 d) <<< 1 = BitVec.ofNat 64 (2 * d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 2 * d < 2 ^ 64)]; omega
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 16), Nat.mod_eq_of_lt (by omega : 2 * d < 2 ^ 64)]; omega
  · simp [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : d < 2 ^ 32)]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
    have hmask : (0xffff#64).toNat = 2 ^ 16 - 1 := rfl
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : d < 2 ^ 16)]
  · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * d < 2 ^ 64)]; omega

private theorem bv_ult_9999999 {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.ult 9999999#64 (BitVec.ofNat 64 m) = decide (9999999 < m) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.ult, Nat.mod_eq_of_lt hm]

private theorem bv_inner_iter_k (bufBase : BitVec 64) {k' : Nat} (hk' : k' ≤ 4) :
    let x11 := -BitVec.ofNat 64 (16 - 4 * k')
    let x12 := bufBase - BitVec.ofNat 64 (18 - 4 * k')
    (20#64 + x11 - 4#64).ult 20#64 = true ∧
    (20#64 + x11 - 3#64).ult 20#64 = true ∧
    (20#64 + x11 - 2#64).ult 20#64 = true ∧
    (20#64 + x11 - 1#64).ult 20#64 = true ∧
    x12 + 20#64 + (-2#64) = bufBase + BitVec.ofNat 64 (4 * k') ∧
    x12 + 20#64 + (-1#64) = bufBase + BitVec.ofNat 64 (4 * k') + 1#64 ∧
    x12 + 20#64 = bufBase + BitVec.ofNat 64 (4 * k') + 2#64 ∧
    x12 + 20#64 + 1#64 = bufBase + BitVec.ofNat 64 (4 * k') + 3#64 ∧
    x11 - 4#64 = -BitVec.ofNat 64 (20 - 4 * k') ∧
    x12 - 4#64 = bufBase - BitVec.ofNat 64 (22 - 4 * k') ∧
    20#64 + (-BitVec.ofNat 64 (20 - 4 * k')) = BitVec.ofNat 64 (4 * k') := by
  rcases (by omega : k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 ∨ k' = 4) with rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := { decide := true }) [bv_lin_norm]

private theorem u64FmtInner_div10000_iter_wp {P : Program} {C : HbCliLayout}
    {target_pc bufBase : BitVec 64} {k' m : Nat} {suffix : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords (C.u64FmtInnerAddr + 0x14#64) u64FmtInnerDigitsWords)
    (hk' : k' ≤ 4) (hm_lo : 1000 ≤ m) (hm64 : m < 2 ^ 64)
    (hpc : s.pc = C.u64FmtInnerAddr + 0x48#64) (hrun : s.status = .Running)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = 20#64)
    (hx9  : s.readReg64 (.gpr 9#5) = C.decDigitsLutAddr)
    (hx11 : s.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (16 - 4 * k'))
    (hx12 : s.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (18 - 4 * k'))
    (hx13 : s.readReg64 (.gpr 13#5) = 0x346dc5d63886594b#64)
    (hx14 : s.readReg64 (.gpr 14#5) = 10000#64)
    (hx15 : s.readReg64 (.gpr 15#5) = 5243#64)
    (hx16 : s.readReg64 (.gpr 16#5) = 100#64)
    (hx17 : s.readReg64 (.gpr 17#5) = 9999999#64)
    (hx18 : s.readReg64 (.gpr 18#5) = BitVec.ofNat 64 m)
    (hnext : ∀ s' : State,
      s'.pc = (if 9999999 < m then C.u64FmtInnerAddr + 0x48#64 else C.u64FmtInnerAddr + 0xe0#64) →
      s'.status = .Running → s'.sp = s.sp →
      CpuAuxPreserved s s' → CalleeSavedPreserved s s' →
      s'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      s'.readReg64 (.gpr 1#5) = bufBase →
      s'.readReg64 (.gpr 2#5) = 20#64 →
      s'.readReg64 (.gpr 9#5) = C.decDigitsLutAddr →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (m / 10000) →
      s'.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (20 - 4 * k') →
      s'.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (22 - 4 * k') →
      s'.readReg64 (.gpr 13#5) = 0x346dc5d63886594b#64 →
      s'.readReg64 (.gpr 14#5) = 10000#64 →
      s'.readReg64 (.gpr 15#5) = 5243#64 →
      s'.readReg64 (.gpr 16#5) = 100#64 →
      s'.readReg64 (.gpr 17#5) = 9999999#64 →
      s'.readReg64 (.gpr 18#5) = BitVec.ofNat 64 (m / 10000) →
      SepWP (P.withSvc noSyscalls) target_pc s'
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (4 * k') ∗
          ((bufBase + BitVec.ofNat 64 (4 * k')) ↦ₛ (fourDecDigits (m % 10000) ++ suffix))) ∗ F)
        post oom) :
    SepWP (P.withSvc noSyscalls) target_pc s
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (4 * (k' + 1)) ∗
        ((bufBase + BitVec.ofNat 64 (4 * (k' + 1))) ↦ₛ suffix)) ∗ F)
      post oom := by
  have hcode : (P.withSvc noSyscalls).hasCode (C.u64FmtInnerAddr + 0x14#64)
      u64FmtInnerDigitsWords := hc
  have _ := hm_lo
  have hdiv := bv_div_10000 hm64
  have hrem := bv_msub32_rem m 10000 (by decide) (by omega)
  obtain ⟨hlsr2a, hlsr2b⟩ := bv_lsr2_32 (r := m % 10000) (by omega)
  obtain ⟨hdiv100a, humull, hdiv100b⟩ := bv_magic_div100_step (r := m % 10000) (by omega)
  have hrem100 := bv_msub32_rem (m % 10000) 100 (by decide) (by omega)
  obtain ⟨hd1_uxtw, _, _, _, _⟩ := bv_uxtw_lsl1 (d := (m % 10000) / 100) (by omega)
  obtain ⟨_, hd2_uxth, hd2_zext, hd2_and, hd2_lsl⟩ := bv_uxtw_lsl1 (d := (m % 10000) % 100) (by omega)
  obtain ⟨hcmp1, hcmp2, hcmp3, hcmp4, haddr0, haddr1, haddr2, haddr3, hx11_step, hx12_step, _⟩ :=
    bv_inner_iter_k bufBase hk'
  have hult9 := bv_ult_9999999 hm64
  have hpre_split : memRegion bufBase (4 * (k' + 1)) ⊢
      memRegion bufBase (4 * k') ∗
        ((∃∗ b0 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k')) ↦₈ b0) ∗
         (∃∗ b1 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k') + 1#64) ↦₈ b1) ∗
         (∃∗ b2 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k') + 2#64) ↦₈ b2) ∗
         (∃∗ b3 : BitVec 8, (bufBase + BitVec.ofNat 64 (4 * k') + 3#64) ↦₈ b3)) := by
    rw [memRegion_split_le bufBase (4 * k') (4 * (k' + 1)) (by omega) (by omega),
        show 4 * (k' + 1) - 4 * k' = 4 by omega]
    exact sepConj_mono_right (memRegion4_entails8 (bufBase + BitVec.ofNat 64 (4 * k')))
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre_split))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro b0
  apply SepWP.exists_elim; intro b1
  apply SepWP.exists_elim; intro b2
  apply SepWP.exists_elim; intro b3
  conv =>
    arg 4; arg 1; arg 1
    rw [decDigitsLut_focus8_pair C.decDigitsLutAddr (i := (m % 10000) / 100) (by omega)]
  iterate 23 wp_step
  conv =>
    arg 4; arg 1; arg 1
    rw [← decDigitsLut_focus8_pair C.decDigitsLutAddr (i := (m % 10000) / 100) (by omega),
        decDigitsLut_focus8_pair C.decDigitsLutAddr (i := (m % 10000) % 100) (by omega)]
  iterate 15 wp_step
  have hent_out :
      ((((C.decDigitsLutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100))) ↦₈ᵣ
            decDigitByte (m % 10000 % 100 / 10) ∗
          (C.decDigitsLutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100)) + 1#64) ↦₈ᵣ
            decDigitByte (m % 10000 % 100 % 10)) ∗
        (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes.take (2 * (m % 10000 % 100)) ∗
          (C.decDigitsLutAddr + BitVec.ofNat 64 (2 * (m % 10000 % 100) + 2)) ↦ᵣ
            decDigitsLutBytes.drop (2 * (m % 10000 % 100) + 2))) ∗
      (memRegion bufBase (4 * k') ∗
        ((bufBase + BitVec.ofNat 64 (4 * k')) ↦₈ decDigitByte (m % 10000 / 100 / 10) ∗
         (bufBase + BitVec.ofNat 64 (4 * k') + 1#64) ↦₈ decDigitByte (m % 10000 / 100 % 10) ∗
         (bufBase + BitVec.ofNat 64 (4 * k') + 2#64) ↦₈ decDigitByte (m % 10000 % 100 / 10) ∗
         (bufBase + BitVec.ofNat 64 (4 * k') + 3#64) ↦₈ decDigitByte (m % 10000 % 100 % 10))) ∗
      (bufBase + BitVec.ofNat 64 (4 * (k' + 1))) ↦ₛ suffix) ∗ F ⊢
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (4 * k') ∗
        ((bufBase + BitVec.ofNat 64 (4 * k')) ↦ₛ (fourDecDigits (m % 10000) ++ suffix))) ∗ F) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus8_pair C.decDigitsLutAddr (i := (m % 10000) % 100) (by omega)]
    refine sepConj_mono_right ?_
    rw [sepConj_assoc, pointsTo8_quad_eq_fourDecDigits,
        ← pointsToBytes_append_off bufBase (4 * k') (4 * (k' + 1)) _ _
          (by rw [fourDecDigits_length]; omega)]
    exact Entails.refl _
  exact SepWP.weaken_pre hent_out (hnext _
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp [CpuAuxPreserved.refl])
    (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx13])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx14])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx15])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx16])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx17])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm]))

private theorem u64FmtInner_div10000_loop_wp {P : Program} {C : HbCliLayout}
    {target_pc bufBase : BitVec 64} {k m : Nat} {suffix : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords (C.u64FmtInnerAddr + 0x14#64) u64FmtInnerDigitsWords)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ 5) (hm_lo : 1000 ≤ m) (hm_pow : m < 10000 ^ k) (hm64 : m < 2 ^ 64)
    (hpc : s.pc = C.u64FmtInnerAddr + 0x48#64) (hrun : s.status = .Running)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = 20#64)
    (hx9  : s.readReg64 (.gpr 9#5) = C.decDigitsLutAddr)
    (hx11 : s.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (20 - 4 * k))
    (hx12 : s.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (22 - 4 * k))
    (hx13 : s.readReg64 (.gpr 13#5) = 0x346dc5d63886594b#64)
    (hx14 : s.readReg64 (.gpr 14#5) = 10000#64)
    (hx15 : s.readReg64 (.gpr 15#5) = 5243#64)
    (hx16 : s.readReg64 (.gpr 16#5) = 100#64)
    (hx17 : s.readReg64 (.gpr 17#5) = 9999999#64)
    (hx18 : s.readReg64 (.gpr 18#5) = BitVec.ofNat 64 m)
    (hnext : ∀ (s' : State) (idx0 q : Nat) (outSuffix : List (BitVec 8)),
      s'.pc = C.u64FmtInnerAddr + 0xe0#64 →
      s'.status = .Running → s'.sp = s.sp →
      CpuAuxPreserved s s' → CalleeSavedPreserved s s' →
      s'.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5) →
      s'.readReg64 (.gpr 1#5) = bufBase →
      s'.readReg64 (.gpr 2#5) = 20#64 →
      s'.readReg64 (.gpr 9#5) = C.decDigitsLutAddr →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 q →
      20#64 + s'.readReg64 (.gpr 11#5) = BitVec.ofNat 64 idx0 →
      idx0 ≤ 4 * (k - 1) →
      idx0 + outSuffix.length = 4 * k + suffix.length →
      q < 1000 →
      ((q = 0 ∧ outSuffix = formatDecimalNat m ++ suffix) ∨
       (1 ≤ q ∧ 4 ≤ idx0 ∧ formatDecimalNat q ++ outSuffix = formatDecimalNat m ++ suffix)) →
      SepWP (P.withSvc noSyscalls) target_pc s'
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase idx0 ∗
          ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix)) ∗ F)
        post oom) :
    SepWP (P.withSvc noSyscalls) target_pc s
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (4 * k) ∗
        ((bufBase + BitVec.ofNat 64 (4 * k)) ↦ₛ suffix)) ∗ F)
      post oom := by
  induction k generalizing s m suffix with
  | zero => omega
  | succ k' ih =>
    have hx11' : s.readReg64 (.gpr 11#5) = -BitVec.ofNat 64 (16 - 4 * k') := by
      rw [hx11, show 20 - 4 * (k' + 1) = 16 - 4 * k' by omega]
    have hx12' : s.readReg64 (.gpr 12#5) = bufBase - BitVec.ofNat 64 (18 - 4 * k') := by
      rw [hx12, show 22 - 4 * (k' + 1) = 18 - 4 * k' by omega]
    refine u64FmtInner_div10000_iter_wp hc (by omega) hm_lo hm64 hpc hrun hx1 hx2 hx9 hx11' hx12'
      hx13 hx14 hx15 hx16 hx17 hx18 ?_
    intro s₁ hpc₁ hrun₁ hsp₁ haux₁ hcs₁ hx0₁ hx1₁ hx2₁ hx9₁ hx10₁ hx11₁ hx12₁ hx13₁ hx14₁ hx15₁ hx16₁ hx17₁ hx18₁
    by_cases hhi : 9999999 < m
    · simp only [hhi, ↓reduceIte] at hpc₁
      have hk1 : 1 ≤ k' := by cases k' with | zero => simp at hm_pow; omega | succ _ => omega
      have hm_pow' : m / 10000 < 10000 ^ k' := by
        rw [Nat.pow_succ'] at hm_pow; exact Nat.div_lt_of_lt_mul hm_pow
      refine ih hk1 (by omega) (by omega) hm_pow' (by omega) hpc₁ hrun₁ hx1₁ hx2₁ hx9₁ hx11₁ hx12₁
        hx13₁ hx14₁ hx15₁ hx16₁ hx17₁ hx18₁ ?_
      intro s' idx0 q outSuffix hpc' hrun' hsp' haux' hcs' hx0' hx1' hx2' hx9' hx10' hx11'' hidx hlen hq hdisj
      have hfmt : formatDecimalNat (m / 10000) ++ (fourDecDigits (m % 10000) ++ suffix) =
          formatDecimalNat m ++ suffix := by
        rw [← List.append_assoc, ← formatDecimal_div_10000 (by omega)]
      exact hnext s' idx0 q outSuffix hpc' hrun' (hsp'.trans hsp₁)
        ⟨haux'.1.trans haux₁.1, haux'.2.1.trans haux₁.2.1,
         haux'.2.2.1.trans haux₁.2.2.1, haux'.2.2.2.trans haux₁.2.2.2⟩
        (CalleeSavedPreserved.trans hcs₁ hcs') (hx0'.trans hx0₁) hx1' hx2' hx9'
        hx10' hx11'' (by omega)
        (by simp only [List.length_append, fourDecDigits_length] at hlen; omega) hq
        (hdisj.imp (fun ⟨hq0, ho⟩ => ⟨hq0, ho.trans hfmt⟩)
                   (fun ⟨hq1, hi4, ho⟩ => ⟨hq1, hi4, ho.trans hfmt⟩))
    · simp only [hhi, ↓reduceIte] at hpc₁
      have hx11_add : 20#64 + s₁.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (4 * k') := by
        rw [hx11₁]
        exact (bv_inner_iter_k bufBase (k' := k') (by omega)).2.2.2.2.2.2.2.2.2.2
      refine hnext s₁ (4 * k') (m / 10000) (fourDecDigits (m % 10000) ++ suffix)
        hpc₁ hrun₁ hsp₁ haux₁ hcs₁ hx0₁ hx1₁ hx2₁ hx9₁ hx10₁ hx11_add
        (by omega) (by simp [fourDecDigits_length]; omega) (by omega) ?_
      by_cases h10k : m < 10000
      · left; refine ⟨by omega, ?_⟩
        rw [Nat.mod_eq_of_lt h10k, ← formatDecimal_of_1000_lt_10000 hm_lo h10k]
      · right
        have hk1 : 1 ≤ k' := by cases k' with | zero => simp at hm_pow; omega | succ _ => omega
        refine ⟨by omega, by omega, ?_⟩
        rw [← List.append_assoc, ← formatDecimal_div_10000 (by omega)]

private theorem bv_ofNat_sub_small {n d : Nat} (hd : d ≤ n) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 d = BitVec.ofNat 64 (n - d) := by
  conv => lhs; arg 1; rw [show n = (n - d) + d by omega]
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem CpuAuxPreserved.trans {s0 s1 s2 : State}
    (h01 : CpuAuxPreserved s0 s1) (h12 : CpuAuxPreserved s1 s2) : CpuAuxPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.trans h01.2.2.2⟩

private theorem bv_ubfiz_q1 {q1 : Nat} (hq1 : q1 < 10) :
    evalBitfield .W64 .UBFM 0#64 (BitVec.ofNat 64 q1) 63 3 = BitVec.ofNat 64 (2 * q1) ∧
    ((BitVec.ofNat 64 q1 &&& 15#64) <<< 1) = BitVec.ofNat 64 (2 * q1) ∧
    (BitVec.ofNat 64 q1 <<< 1) &&& 30#64 = BitVec.ofNat 64 (2 * q1) := by
  rcases (by omega : q1 = 0 ∨ q1 = 1 ∨ q1 = 2 ∨ q1 = 3 ∨ q1 = 4 ∨
    q1 = 5 ∨ q1 = 6 ∨ q1 = 7 ∨ q1 = 8 ∨ q1 = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem calleeSavedPreserved_write_fp {s0 s1 s2 : State} {fp : BitVec 64}
    (h01 : CalleeSavedPreserved s0 (s1.writeReg64 (.gpr 29#5) fp))
    (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 (s2.writeReg64 (.gpr 29#5) fp) := by
  simp (config := { decide := true }) only [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm] at h01 h12 ⊢
  exact ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem u64FmtInner_last_digit_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp_frame savedFp bufBase v : BitVec 64} {idx1 q1 : Nat} {suf1 : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords (C.u64FmtInnerAddr + 0x14#64) u64FmtInnerDigitsWords)
    (hpc : s.pc = C.u64FmtInnerAddr + 0x128#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_frame) (hsp_align : s.spAligned = true)
    (hx0  : s.readReg64 (.gpr 0#5) = v)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 idx1)
    (hx9  : s.readReg64 (.gpr 9#5) = C.decDigitsLutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 q1)
    (hq1_lt : q1 < 10) (hlen : idx1 + suf1.length = 20)
    (hcases : (v = 0#64 ∧ q1 = 0 ∧ idx1 = 20 ∧ suf1 = []) ∨
              (v ≠ 0#64 ∧ q1 = 0 ∧ suf1 = formatDecimalNat v.toNat) ∨
              (v ≠ 0#64 ∧ 1 ≤ q1 ∧ 1 ≤ idx1 ∧ decDigitByte q1 :: suf1 = formatDecimalNat v.toNat))
    (hnext : ∀ s' : State,
      s'.pc = ret_pc →
      s'.status = .Running → s'.sp = sp_frame + 16#64 →
      CpuAuxPreserved s s' →
      CalleeSavedPreserved (s.writeReg64 (.gpr 29#5) savedFp) s' →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length) →
      SepWP (P.withSvc noSyscalls) target_pc s'
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
        post oom) :
    SepWP (P.withSvc noSyscalls) target_pc s
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase idx1 ∗
        ((bufBase + BitVec.ofNat 64 idx1) ↦ₛ suf1) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
      post oom := by
  subst hsp
  have hcode : (P.withSvc noSyscalls).hasCode (C.u64FmtInnerAddr + 0x14#64)
      u64FmtInnerDigitsWords := hc
  rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hv0, rfl, rfl⟩ | ⟨hv0, hq1_lo, hidx1_lo, hsuf⟩
  · have hpre : memRegion bufBase 20 ⊢
        memRegion bufBase 19 ∗ ∃∗ b0 : BitVec 8, (bufBase + 19#64) ↦₈ b0 := by
      rw [memRegion_split_le bufBase 19 20 (by decide) (by decide)]
      exact sepConj_mono_right (memRegion1_entails _)
    refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre))) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b0
    conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus8_odd C.decDigitsLutAddr (i := 0) (by decide)]
    iterate 9 wp_step
    have hent :
        (((C.decDigitsLutAddr + BitVec.ofNat 64 (2 * 0 + 1)) ↦₈ᵣ decDigitByte 0 ∗
          (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes.take (2 * 0 + 1) ∗
            (C.decDigitsLutAddr + BitVec.ofNat 64 (2 * 0 + 2)) ↦ᵣ
              decDigitsLutBytes.drop (2 * 0 + 2))) ∗
        (memRegion bufBase 19 ∗ (bufBase + 19#64) ↦₈ decDigitByte 0) ∗
        (bufBase + BitVec.ofNat 64 20) ↦ₛ [] ∗
        (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F ⊢
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat (0#64).toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat (0#64).toNat).length)) ↦ₛ
            formatDecimalNat (0#64).toNat) ∗
          (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
      apply sepConj_mono_left
      rw [← decDigitsLut_focus8_odd C.decDigitsLutAddr (i := 0) (by decide)]
      refine sepConj_mono_right ?_
      have hf0 : formatDecimalNat (0#64).toNat = [decDigitByte 0] := rfl
      rw [hf0, List.length_singleton, show 20 - 1 = 19 from rfl, sepConj_assoc,
          ← sepConj_assoc ((bufBase + 19#64) ↦₈ decDigitByte 0),
          ← pointsToBytes_cons_off bufBase 19 (decDigitByte 0) []]
      exact Entails.refl _
    exact SepWP.weaken_pre hent (hnext _ (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp [CpuAuxPreserved.refl])
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm]))
  · have hv_beq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hv0
    iterate 5 wp_step
    have hidx_eq : idx1 = 20 - (formatDecimalNat v.toNat).length := by omega
    subst hidx_eq
    exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp [CpuAuxPreserved.refl])
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
  · have hv_beq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hv0
    have hq1_ne : BitVec.ofNat 64 q1 ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt (by omega : q1 < 2 ^ 64)] at this; omega
    have hq1_beq : (BitVec.ofNat 64 q1 == 0#64) = false := beq_eq_false_iff_ne.mpr hq1_ne
    obtain ⟨hubfiz1, hubfiz2, hubfiz3⟩ := bv_ubfiz_q1 hq1_lt
    have hsub1 := bv_ofNat_sub_small hidx1_lo
    have hlut_off : (C.decDigitsLutAddr + BitVec.ofNat 64 (2 * q1)) + 1#64 =
        C.decDigitsLutAddr + BitVec.ofNat 64 (2 * q1 + 1) := by
      rw [BitVec.add_assoc, ← @BitVec.ofNat_add 64 (2 * q1) 1]
    have hpre : memRegion bufBase idx1 ⊢
        memRegion bufBase (idx1 - 1) ∗
          ∃∗ b0 : BitVec 8, (bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ b0 := by
      rw [memRegion_split_le bufBase (idx1 - 1) idx1 (by omega) (by omega),
          show idx1 - (idx1 - 1) = 1 by omega]
      exact sepConj_mono_right (memRegion1_entails _)
    refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre))) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b0
    conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus8_odd C.decDigitsLutAddr (i := q1) hq1_lt]
    iterate 10 wp_step
    have hidx_eq : idx1 - 1 = 20 - (formatDecimalNat v.toNat).length := by
      have := congrArg List.length hsuf; simp at this; omega
    have hent :
        (((C.decDigitsLutAddr + BitVec.ofNat 64 (2 * q1 + 1)) ↦₈ᵣ decDigitByte q1 ∗
          (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes.take (2 * q1 + 1) ∗
            (C.decDigitsLutAddr + BitVec.ofNat 64 (2 * q1 + 2)) ↦ᵣ
              decDigitsLutBytes.drop (2 * q1 + 2))) ∗
        (memRegion bufBase (idx1 - 1) ∗
          (bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ decDigitByte q1) ∗
        (bufBase + BitVec.ofNat 64 idx1) ↦ₛ suf1 ∗
        (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F ⊢
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          (s.sp ↦₆₄ savedFp) ∗ ((s.sp + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
      apply sepConj_mono_left
      rw [← decDigitsLut_focus8_odd C.decDigitsLutAddr (i := q1) hq1_lt]
      refine sepConj_mono_right ?_
      have hcons := pointsToBytes_cons_off bufBase (idx1 - 1) (decDigitByte q1) suf1
      rw [show (idx1 - 1) + 1 = idx1 by omega] at hcons
      rw [sepConj_assoc, ← sepConj_assoc ((bufBase + BitVec.ofNat 64 (idx1 - 1)) ↦₈ decDigitByte q1),
          ← hcons, hsuf, ← hidx_eq]
      exact Entails.refl _
    exact SepWP.weaken_pre hent (hnext _ (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp [CpuAuxPreserved.refl])
      (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hidx_eq]))

private theorem u64FmtInner_two_digits_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp_frame savedFp bufBase v : BitVec 64} {idx0 q : Nat} {outSuffix : List (BitVec 8)}
    {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords (C.u64FmtInnerAddr + 0x14#64) u64FmtInnerDigitsWords)
    (hpc : s.pc = C.u64FmtInnerAddr + 0xfc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_frame) (hsp_align : s.spAligned = true)
    (hx0  : s.readReg64 (.gpr 0#5) = v)
    (hx1  : s.readReg64 (.gpr 1#5) = bufBase)
    (hx2  : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 idx0)
    (hx9  : s.readReg64 (.gpr 9#5) = C.decDigitsLutAddr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 q)
    (hv0 : v ≠ 0#64) (hq_lo : 10 ≤ q) (hq_lt : q < 1000)
    (hidx_lo : 4 ≤ idx0) (hlen : idx0 + outSuffix.length = 20)
    (hfmt : formatDecimalNat q ++ outSuffix = formatDecimalNat v.toNat)
    (hnext : ∀ s' : State,
      s'.pc = ret_pc →
      s'.status = .Running → s'.sp = sp_frame + 16#64 →
      CpuAuxPreserved s s' →
      CalleeSavedPreserved (s.writeReg64 (.gpr 29#5) savedFp) s' →
      s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length) →
      SepWP (P.withSvc noSyscalls) target_pc s'
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
        post oom) :
    SepWP (P.withSvc noSyscalls) target_pc s
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase idx0 ∗
        ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F)
      post oom := by
  have hcode : (P.withSvc noSyscalls).hasCode (C.u64FmtInnerAddr + 0x14#64)
      u64FmtInnerDigitsWords := hc
  obtain ⟨hlsr2a, hlsr2b⟩ := bv_lsr2_32 (r := q) (by omega)
  obtain ⟨hdiv100a, humull, hdiv100b⟩ := bv_magic_div100_step (r := q) (by omega)
  have hrem100 := bv_msub32_rem q 100 (by decide) (by omega)
  obtain ⟨_, _, hd_zext, hd_and, hd_lsl⟩ := bv_uxtw_lsl1 (d := q % 100) (by omega)
  obtain ⟨_, _, hq100_zext, _, _⟩ := bv_uxtw_lsl1 (d := q / 100) (by omega)
  have hsub2 := bv_ofNat_sub_small (show 2 ≤ idx0 by omega)
  have hpre : memRegion bufBase idx0 ⊢
      memRegion bufBase (idx0 - 2) ∗
        ∃∗ w0 : BitVec 16, (bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦₁₆ w0 := by
    rw [memRegion_split_le bufBase (idx0 - 2) idx0 (by omega) (by omega),
        show idx0 - (idx0 - 2) = 2 by omega]
    exact sepConj_mono_right (memRegion2_entails _)
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hpre))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  conv => arg 4; arg 1; arg 1; rw [decDigitsLut_focus16 C.decDigitsLutAddr (i := q % 100) (by omega)]
  iterate 11 wp_step
  let suf1 := [decDigitByte (q % 100 / 10), decDigitByte (q % 100 % 10)] ++ outSuffix
  have hent :
      (((C.decDigitsLutAddr + BitVec.ofNat 64 (2 * (q % 100))) ↦₁₆ᵣ
          pack16 (decDigitByte (q % 100 / 10)) (decDigitByte (q % 100 % 10)) ∗
        (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes.take (2 * (q % 100)) ∗
          (C.decDigitsLutAddr + BitVec.ofNat 64 (2 * (q % 100) + 2)) ↦ᵣ
            decDigitsLutBytes.drop (2 * (q % 100) + 2))) ∗
      (memRegion bufBase (idx0 - 2) ∗
        (bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦₁₆
          pack16 (decDigitByte (q % 100 / 10)) (decDigitByte (q % 100 % 10))) ∗
      (bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix ∗
      (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F ⊢
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (idx0 - 2) ∗
        ((bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦ₛ suf1) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
    apply sepConj_mono_left
    rw [← decDigitsLut_focus16 C.decDigitsLutAddr (i := q % 100) (by omega)]
    refine sepConj_mono_right ?_
    unfold pack16 suf1
    rw [sepConj_assoc,
        ← sepConj_assoc ((bufBase + BitVec.ofNat 64 (idx0 - 2)) ↦₁₆ _),
        ← pointsToBytes2_eq_pointsTo16,
        ← pointsToBytes_append_off bufBase (idx0 - 2) idx0 _ _ (by simp; omega)]
    exact Entails.refl _
  refine SepWP.weaken_pre hent (u64FmtInner_last_digit_wp (v := v) (idx1 := idx0 - 2) (q1 := q / 100) hc
    (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp)
    (by unfold State.spAligned at *; simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp_align)
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by omega) (by simp [suf1]; omega) ?_ ?_)
  · by_cases h100 : q < 100
    · right; left; refine ⟨hv0, by omega, ?_⟩
      rw [← hfmt, formatDecimal_two_digits hq_lo h100]; simp [suf1, Nat.mod_eq_of_lt h100]
    · right; right; refine ⟨hv0, by omega, by omega, ?_⟩
      rw [← hfmt, formatDecimal_three_digits (by omega) hq_lt]
      simp only [suf1, List.cons_append, List.nil_append]
      rw [show q % 100 / 10 = q / 10 % 10 by omega, show q % 100 % 10 = q % 10 by omega]
  · intro s' hpc' hrun' hsp' haux' hcs' hx0'
    refine hnext s' hpc' hrun' hsp'
      (CpuAuxPreserved.trans (by simp [CpuAuxPreserved.refl]) haux')
      (CalleeSavedPreserved.trans
        (calleeSavedPreserved_write_fp (CalleeSavedPreserved.rfl _)
          (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]))
        hcs')
      hx0'

private theorem step_u64FmtInnerLut_adr {P : Program} {C : HbCliLayout} {target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlut : hasInstrs P (C.u64FmtInnerAddr + 0x10#64) (u64FmtInnerLutInstrs C))
    (hpc : s.pc = C.u64FmtInnerAddr + 0x10#64) (hrun : s.status = .Running)
    (hnext : SepWP P target_pc
      ((s.writeReg64 (.gpr 9#5) C.decDigitsLutAddr).setPC (C.u64FmtInnerAddr + 0x14#64))
      Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hf0 : P.fetch (C.u64FmtInnerAddr + 0x10#64) =
      some (.adr false .x9 (C.decDigitsLutAddr - (C.u64FmtInnerAddr + 0x10#64))) := by
    simpa [u64FmtInnerLutInstrs] using hlut 0 (by simp [u64FmtInnerLutInstrs])
  exact SepWP.step_pure hpc hrun hf0
    (by simp [wp_norm, arm64_norm, Reg.x9, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem u64FmtInner_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp1 bufBase v : BitVec 64} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : HbFmtCode P C)
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s0.pc = C.u64FmtInnerAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp1) (hsp_align : s0.spAligned = true)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = v)
    (hx1 : s0.readReg64 .x1 = bufBase)
    (hx2 : s0.readReg64 .x2 = 20#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp1 → CalleeSavedPreserved s0 sf →
      sf.readReg64 .x0 = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length) →
      FmtPureStatePreserved s0 sf →
      SepWP P target_pc sf
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
          ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
            formatDecimalNat v.toNat) ∗
          stackFrameAt sp1 0x10) ∗ F)
        post oom) :
    SepWP P target_pc s0
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase 20 ∗
        stackFrameAt sp1 0x10) ∗ F)
      post oom := by
  subst hsp
  refine SepWP.seq_noSyscalls (mid_pc := ret_pc)
    (Q := fun sm Pm =>
      (Pm ⊢ ((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
        ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
          formatDecimalNat v.toNat) ∗
        stackFrameAt s0.sp 0x10) ∗ F) ∧
      sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧
      sm.readReg64 .x0 = BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length))
    hext ?_ (fun sf Pf hpc_f hrun_f hpure ⟨hent, hsp_f, hcs_f, hx0_f⟩ =>
      SepWP.weaken_pre hent (hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hpure))
  have hc_pro : (P.withSvc noSyscalls).hasCode C.u64FmtInnerAddr u64FmtInnerPrologueWords :=
    hcode.u64InnerPrologue
  have hc_dig : (P.withSvc noSyscalls).hasCode (C.u64FmtInnerAddr + 0x14#64)
    u64FmtInnerDigitsWords := hcode.u64InnerDigits
  have hx0' : s0.readReg64 (.gpr 0#5) = v := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = bufBase := hx1
  have hx2' : s0.readReg64 (.gpr 2#5) = 20#64 := hx2
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  conv =>
    arg 4
    rw [← stackAt_eq_stackFrameAt s0.sp 16, stackAt_eq_cells s0.sp 2]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  iterate 2 (apply SepWP.exists_elim; intro _)
  iterate 4 wp_step
  refine step_u64FmtInnerLut_adr (hcode.withSvc noSyscalls).u64InnerLut
    (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  let sp_frame := s0.sp - 16#64
  let savedFp := s0.readReg64 (.gpr 29#5)
  have hpre_norm :
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase 20 ∗
        (((s0.sp - 16#64) ↦₆₄ savedFp) ∗ ((s0.sp - 8#64) ↦₆₄ ret_pc))) ∗ F) ⊢
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase 20 ∗
        ((bufBase + BitVec.ofNat 64 20) ↦ₛ []) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) := by
    rw [pointsToBytes_nil]
    apply sepConj_mono_left
    refine sepConj_mono_right (sepConj_mono_right ?_)
    dsimp only [sp_frame]
    rw [emp_sepConj, show s0.sp - 16#64 + 8#64 = s0.sp - 8#64 by simp [bv_lin_norm]]
    exact Entails.refl _
  refine SepWP.weaken_pre hpre_norm ?_
  have hrepack :
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
        ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
          formatDecimalNat v.toNat) ∗
        (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) ⊢
      (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        memRegion bufBase (20 - (formatDecimalNat v.toNat).length) ∗
        ((bufBase + BitVec.ofNat 64 (20 - (formatDecimalNat v.toNat).length)) ↦ₛ
          formatDecimalNat v.toNat) ∗
        stackFrameAt s0.sp 0x10) ∗ F) := by
    apply sepConj_mono_left
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    dsimp only [sp_frame]
    rw [show s0.sp - 16#64 + 8#64 = s0.sp - 8#64 by simp [bv_lin_norm],
        ← stackAt_eq_stackFrameAt s0.sp 16, stackAt_eq_cells s0.sp 2]
    simp only [Nat.reduceMul]
    refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub]
    exact cells_sub_one_entails 8
  by_cases hlt1000 : v.toNat < 1000
  · have hv_ult : v.ult 1000#64 = true := by simp [BitVec.ult, hlt1000]
    by_cases hlt10 : v.toNat < 10
    · have hv_ult10 : v.ult 10#64 = true := by simp [BitVec.ult, hlt10]
      iterate 4 wp_step
      refine u64FmtInner_last_digit_wp (v := v) (idx1 := 20) (q1 := v.toNat) (suf1 := [])
        hcode.u64InnerDigits
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, sp_frame])
        (by unfold State.spAligned at *; simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp_align)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, BitVec.ofNat_toNat])
        hlt10 rfl ?_ ?_
      · by_cases hv0 : v = 0#64
        · subst hv0; left; exact ⟨rfl, rfl, rfl, rfl⟩
        · right; right
          have hv_pos : 1 ≤ v.toNat := by
            cases h : v.toNat with
            | zero => exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv0
            | succ _ => omega
          exact ⟨hv0, hv_pos, by decide, (formatDecimal_of_lt_10 hlt10).symm⟩
      · intro s' hpc' hrun' hsp' haux' hcs' hx0'
        refine SepWP.done hpc' hrun' ⟨?_, hrepack, ?_, ?_, hx0'⟩
        · exact CpuAuxPreserved.trans (by simp [CpuAuxPreserved.refl]) haux'
        · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
        · exact CalleeSavedPreserved.trans
            (by dsimp only [savedFp]
                simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
            hcs'
    · have hv_ult10 : v.ult 10#64 = false := by
        apply Bool.eq_false_iff.mpr; simp [BitVec.ult]; omega
      have hv0 : v ≠ 0#64 := by rintro rfl; simp at hlt10
      iterate 4 wp_step
      refine u64FmtInner_two_digits_wp (v := v) (idx0 := 20) (q := v.toNat) (outSuffix := [])
        hcode.u64InnerDigits
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, sp_frame])
        (by unfold State.spAligned at *; simpa (config := { decide := true }) [wp_norm, arm64_norm] using hsp_align)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, BitVec.ofNat_toNat])
        hv0 (by omega) hlt1000 (by decide) rfl (List.append_nil _) ?_
      intro s' hpc' hrun' hsp' haux' hcs' hx0'
      refine SepWP.done hpc' hrun' ⟨?_, hrepack, ?_, ?_, hx0'⟩
      · exact CpuAuxPreserved.trans (by simp [CpuAuxPreserved.refl]) haux'
      · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
      · exact CalleeSavedPreserved.trans
          (by dsimp only [savedFp]
              simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
          hcs'
  · have hv_ult : v.ult 1000#64 = false := by
      apply Bool.eq_false_iff.mpr; simp [BitVec.ult]; omega
    have hv0 : v ≠ 0#64 := by rintro rfl; simp at hlt1000
    iterate 13 wp_step
    rw [show (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase 20 ∗ ((bufBase + BitVec.ofNat 64 20) ↦ₛ []) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) =
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase (4 * 5) ∗
          ((bufBase + BitVec.ofNat 64 (4 * 5)) ↦ₛ [])) ∗
         ((sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc) ∗ F)) by ac_rfl]
    refine u64FmtInner_div10000_loop_wp (k := 5) (m := v.toNat) (suffix := [])
      hcode.u64InnerDigits
      (by decide) (by decide) (by omega) (Nat.lt_trans v.isLt (by decide)) v.isLt
      (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1'])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx2'])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) [wp_norm, arm64_norm, BitVec.ofNat_toNat]) ?_
    intro s₁ idx0 q outSuffix hpc₁ hrun₁ hsp₁ haux₁ hcs₁ hx0₁ hx1₁ hx2₁ hx9₁ hx10₁ hx11_add _ hlen₁ hq_lt hdisj
    rw [show (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase idx0 ∗ ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix)) ∗
         ((sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc) ∗ F)) =
        (((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion bufBase idx0 ∗ ((bufBase + BitVec.ofNat 64 idx0) ↦ₛ outSuffix) ∗
          (sp_frame ↦₆₄ savedFp) ∗ ((sp_frame + 8#64) ↦₆₄ ret_pc)) ∗ F) by ac_rfl]
    have hsp₁' : s₁.sp = sp_frame :=
      hsp₁.trans (by simp (config := { decide := true }) [wp_norm, arm64_norm, sp_frame])
    have hsp_align₁ : s₁.spAligned = true := by
      unfold State.spAligned at *; rw [hsp₁']
      simpa (config := { decide := true }) [wp_norm, arm64_norm, sp_frame] using hsp_align
    have hx0₁' : s₁.readReg64 (.gpr 0#5) = v :=
      hx0₁.trans (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0'])
    have haux₁' : CpuAuxPreserved s0 s₁ :=
      CpuAuxPreserved.trans (by simp [CpuAuxPreserved.refl]) haux₁
    have hcs₁' : CalleeSavedPreserved s0 (s₁.writeReg64 (.gpr 29#5) savedFp) :=
      calleeSavedPreserved_write_fp
        (by dsimp only [savedFp]
            simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm])
        hcs₁
    by_cases hlt10 : q < 10
    · have hule10 : (10#64).ule (BitVec.ofNat 64 q) = false := by
        apply Bool.eq_false_iff.mpr; simp [BitVec.ule, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]; omega
      iterate 4 wp_step
      refine u64FmtInner_last_digit_wp (v := v) (idx1 := idx0) (q1 := q) (suf1 := outSuffix)
        hcode.u64InnerDigits
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun₁])
        (by simpa [wp_norm, arm64_norm] using hsp₁')
        (by unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align₁)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0₁'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10₁])
        hlt10 (by simpa using hlen₁) ?_ ?_
      · rcases hdisj with ⟨rfl, ho⟩ | ⟨hq1, hi4, ho⟩
        · right; left; rw [List.append_nil] at ho; exact ⟨hv0, rfl, ho⟩
        · right; right
          rw [formatDecimal_of_lt_10 hlt10, List.singleton_append, List.append_nil] at ho
          exact ⟨hv0, hq1, by omega, ho⟩
      · intro s' hpc' hrun' hsp' haux' hcs' hx0'
        refine SepWP.done hpc' hrun' ⟨?_, hrepack, ?_, ?_, hx0'⟩
        · exact haux₁'.trans (CpuAuxPreserved.trans (by simp [CpuAuxPreserved.refl]) haux')
        · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
        · exact CalleeSavedPreserved.trans
            (calleeSavedPreserved_write_fp hcs₁'
              (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]))
            hcs'
    · have hule10 : (10#64).ule (BitVec.ofNat 64 q) = true := by
        simp [BitVec.ule, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]; omega
      rcases hdisj with ⟨rfl, _⟩ | ⟨_, hi4, hfmt⟩
      · omega
      rw [List.append_nil] at hfmt
      iterate 3 wp_step
      refine u64FmtInner_two_digits_wp (v := v) (idx0 := idx0) (q := q) (outSuffix := outSuffix)
        hcode.u64InnerDigits
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun₁])
        (by simpa [wp_norm, arm64_norm] using hsp₁')
        (by unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align₁)
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx0₁'])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx1₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx9₁])
        (by simp (config := { decide := true }) [wp_norm, arm64_norm, hx10₁])
        hv0 (by omega) hq_lt hi4 (by simpa using hlen₁) hfmt ?_
      intro s' hpc' hrun' hsp' haux' hcs' hx0'
      refine SepWP.done hpc' hrun' ⟨?_, hrepack, ?_, ?_, hx0'⟩
      · exact haux₁'.trans (CpuAuxPreserved.trans (by simp [CpuAuxPreserved.refl]) haux')
      · rw [hsp']; dsimp only [sp_frame]; simp [bv_lin_norm]
      · exact CalleeSavedPreserved.trans
          (calleeSavedPreserved_write_fp hcs₁'
            (by simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]))
          hcs'

private theorem pointsTo64_fmtFlags_split (a : BitVec 64) :
    (a ↦₆₄ 0x60000020#64) =
      (a ↦₃₂ 0x60000020#32) ∗ ((a + 4#64) ↦₁₆ 0#16) ∗ ((a + 6#64) ↦₁₆ 0#16) := by
  rw [pointsTo64_split32', show (0x60000020#64).truncate 32 = 0x60000020#32 by decide,
      show (0x60000020#64).extractLsb' 32 32 = (0#8 ++ 0#8 ++ 0#8 ++ 0#8) by decide,
      ← pointsToBytes4_eq_pointsTo32,
      pointsToBytes_take_drop (a + 4#64) 2 [0#8, 0#8, 0#8, 0#8] (by decide)]
  simp only [List.take, List.drop, BitVec.add_assoc,
    show (4#64 : BitVec 64) + BitVec.ofNat 64 2 = 6#64 by decide,
    pointsToBytes2_eq_pointsTo16]
  rfl

private theorem pageLo12_trunc12_eq (target : BitVec 64) :
    (pageLo12 target).truncate 12 = target.truncate 12 := by
  unfold pageLo12; bv_bits

private theorem step_padIntegralCallPrefix_bl {P : Program} {C : HbCliLayout} {target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbl : hasInstrs P (C.padIntegralAddr + 0x88#64) (padIntegralCallPrefixInstrs C))
    (hpc : s.pc = C.padIntegralAddr + 0x88#64) (hrun : s.status = .Running)
    (hnext : SepWP P target_pc
      ((s.writeReg64 (.gpr 30#5) (C.padIntegralAddr + 0x8c#64)).setPC
        C.padIntegralWritePrefixAddr)
      Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hf0 : P.fetch (C.padIntegralAddr + 0x88#64) =
      some (.bl (C.padIntegralWritePrefixAddr - (C.padIntegralAddr + 0x88#64))) := by
    simpa [padIntegralCallPrefixInstrs] using hbl 0 (by simp [padIntegralCallPrefixInstrs])
  exact SepWP.step_pure hpc hrun hf0
    (by simp [wp_norm, arm64_norm, Reg.lr, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem step_u64CallInner_bl {P : Program} {C : HbCliLayout} {target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbl : hasInstrs P (C.u64DisplayFmtAddr + 0x2c#64) (u64DisplayCallInnerInstrs C))
    (hpc : s.pc = C.u64DisplayFmtAddr + 0x2c#64) (hrun : s.status = .Running)
    (hnext : SepWP P target_pc
      ((s.writeReg64 (.gpr 30#5) (C.u64DisplayFmtAddr + 0x30#64)).setPC
        C.u64FmtInnerAddr)
      Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hf0 : P.fetch (C.u64DisplayFmtAddr + 0x2c#64) =
      some (.bl (C.u64FmtInnerAddr - (C.u64DisplayFmtAddr + 0x2c#64))) := by
    simpa [u64DisplayCallInnerInstrs] using hbl 0 (by simp [u64DisplayCallInnerInstrs])
  exact SepWP.step_pure hpc hrun hf0
    (by simp [wp_norm, arm64_norm, Reg.lr, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem step_u64CallPad_bl {P : Program} {C : HbCliLayout} {target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbl : hasInstrs P (C.u64DisplayFmtAddr + 0x48#64) (u64DisplayCallPadInstrs C))
    (hpc : s.pc = C.u64DisplayFmtAddr + 0x48#64) (hrun : s.status = .Running)
    (hnext : SepWP P target_pc
      ((s.writeReg64 (.gpr 30#5) (C.u64DisplayFmtAddr + 0x4c#64)).setPC
        C.padIntegralAddr)
      Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hf0 : P.fetch (C.u64DisplayFmtAddr + 0x48#64) =
      some (.bl (C.padIntegralAddr - (C.u64DisplayFmtAddr + 0x48#64))) := by
    simpa [u64DisplayCallPadInstrs] using hbl 0 (by simp [u64DisplayCallPadInstrs])
  exact SepWP.step_pure hpc hrun hf0
    (by simp [wp_norm, arm64_norm, Reg.lr, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) hnext

private theorem u64Display_slice_bounds {sp0 : BitVec 64} {len : Nat}
    (hsp : 0x100 ≤ sp0.toNat) (hlo : 1 ≤ len) (hhi : len ≤ 20) :
    let slicePtr := (sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - len)
    slicePtr ≠ 0#64 ∧
    slicePtr.toNat + len + 8 ≤ 2 ^ 64 ∧
    20#64 - BitVec.ofNat 64 (20 - len) = BitVec.ofNat 64 len ∧
    (BitVec.ofNat 64 len).ult 0#64 = false := by
  have hlt := sp0.isLt
  have hsp1 : (sp0 - 0x50#64).toNat = sp0.toNat - 80 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 80 ≤ sp0.toNat; omega)]; rfl
  have hbuf : ((sp0 - 0x50#64) + 0x0c#64).toNat = sp0.toNat - 68 := by
    rw [BitVec.toNat_add, hsp1]
    change (sp0.toNat - 80 + 12) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hsl : ((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - len)).toNat =
      sp0.toNat - 68 + (20 - len) := by
    rw [BitVec.toNat_add, hbuf, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 20 - len < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : sp0.toNat - 68 + (20 - len) < 2 ^ 64)]
  refine ⟨?_, by omega, ?_, by simp [BitVec.ult]⟩
  · intro h0; have := congrArg BitVec.toNat h0; simp [hsl] at this; omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt (by omega : 20 - len < 2 ^ 64)])]
    simp [Nat.mod_eq_of_lt (by omega : 20 - len < 2 ^ 64), Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]
    omega

private theorem u64Display_stack_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 0x50 =
      stackFrameAt sp0 48 ∗ memRegion (sp0 - 0x50#64) 12 ∗
        memRegion ((sp0 - 0x50#64) + 0x0c#64) 20 := by
  rw [show (0x50 : Nat) = 48 + 32 from rfl, stackFrameAt_split sp0 48 32 (by decide),
      stackFrameAt_eq_memRegion (sp0 - BitVec.ofNat 64 48) 32 (by decide),
      show sp0 - BitVec.ofNat 64 48 - BitVec.ofNat 64 32 = sp0 - 0x50#64 by simp [bv_lin_norm],
      memRegion_split_le (sp0 - 0x50#64) 12 32 (by decide) (by decide)]

private theorem u64Display_buf_repack (sp0 : BitVec 64) (bs : List (BitVec 8))
    (hhi : bs.length ≤ 20) :
    memRegion (sp0 - 0x50#64) 12 ∗
      memRegion ((sp0 - 0x50#64) + 0x0c#64) (20 - bs.length) ∗
      (((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) ↦ₛ bs) ⊢
      stackFrameAt (sp0 - BitVec.ofNat 64 48) 32 := by
  have hbs : (((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) ↦ₛ bs) ⊢
      memRegion ((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) bs.length := by
    have h := pointsToBytes_memRegion_entails
      ((sp0 - 0x50#64) + 0x0c#64 + BitVec.ofNat 64 (20 - bs.length)) bs bs.length
      (Nat.le_refl _) (by omega)
    simpa [Nat.sub_self, memRegion_zero, sepConj_emp] using h
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hbs)) ?_
  have hm := memRegion_split_le ((sp0 - 0x50#64) + 0x0c#64) (20 - bs.length) 20 (by omega) (by decide)
  rw [show 20 - (20 - bs.length) = bs.length by omega] at hm
  rw [← hm, ← memRegion_split_le (sp0 - 0x50#64) 12 32 (by decide) (by decide),
      stackFrameAt_eq_memRegion (sp0 - BitVec.ofNat 64 48) 32 (by decide),
      show sp0 - BitVec.ofNat 64 48 - BitVec.ofNat 64 32 = sp0 - 0x50#64 by simp [bv_lin_norm]]
  exact Entails.refl _

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q := h ▸ Entails.refl P

/-- Spatial bundle of unchanged caller/rodata resources for `<u64 as Display>::fmt`. -/
def u64DisplayStaticRes (C : HbCliLayout) (writerPtr valPtr formatterPtr v : BitVec 64) : SepProp :=
  (valPtr ↦₆₄ v) ∗
  (formatterPtr ↦₆₄ writerPtr) ∗
  ((formatterPtr + 8#64) ↦₆₄ C.adapterWriteVtableAddr) ∗
  ((formatterPtr + 16#64) ↦₆₄ 0x60000020#64) ∗
  HbAdapterWriteVtableRo C ∗
  (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes)

/-- Specification for `<u64 as core::fmt::Display>::fmt` on a default-flags `Formatter`. -/
def u64DisplayFmtDefaultSpec (C : HbCliLayout) (writerPtr : BitVec 64)
    (writeStackBytes : Nat) (W : List (BitVec 8) → State → SepProp)
    (valPtr formatterPtr v : BitVec 64) (emitted : List (BitVec 8)) : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = valPtr ∧ s0.readReg64 .x1 = formatterPtr ∧ 0x100 ≤ s0.sp.toNat⌝ ∗
    u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
    W emitted s0 ∗
    stackFrameAt s0.sp (0x80 + max 0x30 writeStackBytes)
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s0 sf⌝ ∗
    u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
    W (emitted ++ formatDecimalNat v.toNat) sf ∗
    stackFrameAt s0.sp (0x80 + max 0x30 writeStackBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Continuation-passing `SepWP` theorem for `core::fmt::Formatter::pad_integral`
    (`C.padIntegralAddr`) on a default-flags `Formatter` with `is_nonnegative = true` (`w1 = 1`)
    and empty prefix (`x3 = 0`). -/
theorem padIntegral_default_wp {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    {target_pc ret_pc sp1 valPtr formatterPtr v slicePtr : BitVec 64}
    {emitted bs : List (BitVec 8)} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : HbFmtCode P C)
    (hw : HbFmtWriter P C writerPtr writeStackBytes W)
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s0.pc = C.padIntegralAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp1) (hsp_align : s0.spAligned = true)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = formatterPtr)
    (hx1 : s0.readReg64 .x1 = 1#64)
    (hx3 : s0.readReg64 .x3 = 0#64)
    (hx4 : s0.readReg64 .x4 = slicePtr)
    (hx5 : s0.readReg64 .x5 = BitVec.ofNat 64 bs.length)
    (hlo : 1 ≤ bs.length) (hhi : bs.length ≤ 20) (hno_nl : 0x0a#8 ∉ bs)
    (hsl_ne : slicePtr ≠ 0#64) (hsl_fit : slicePtr.toNat + bs.length + 8 ≤ 2 ^ 64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp1 → CalleeSavedPreserved s0 sf →
      sf.readReg64 .x0 = 0#64 → FmtIoStatePreserved s0 sf →
      SepWP P target_pc sf
        ((u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
          (slicePtr ↦ₛ bs) ∗
          W (emitted ++ bs) sf ∗
          stackFrameAt sp1 (0x30 + max 0x30 writeStackBytes)) ∗ F)
        post oom) :
    SepWP P target_pc s0
      ((u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
        (slicePtr ↦ₛ bs) ∗
        W emitted s0 ∗
        stackFrameAt sp1 (0x30 + max 0x30 writeStackBytes)) ∗ F)
      post oom := by
  subst hsp
  let ws := max 0x30 writeStackBytes
  have hws_lo : 0x70 ≤ ws := by have := hw.stack_lo; omega
  have hws_le : ws ≤ 2 ^ 32 := by have := hw.stack_le; omega
  let sp2 := s0.sp - 0x70#64
  have hlen_ult : (BitVec.ofNat 64 bs.length).ult 0#64 = false := by simp [BitVec.ult]
  have hx0' : s0.readReg64 (.gpr 0#5) = formatterPtr := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = 1#64 := hx1
  have hx3' : s0.readReg64 (.gpr 3#5) = 0#64 := hx3
  have hx4' : s0.readReg64 (.gpr 4#5) = slicePtr := hx4
  have hx5' : s0.readReg64 (.gpr 5#5) = BitVec.ofNat 64 bs.length := hx5
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  conv =>
    arg 4
    rw [show 0x30 + max 0x30 writeStackBytes = 0x70 + (ws - 0x40) by omega,
        stackFrameAt_split s0.sp 0x70 (ws - 0x40) (by omega),
        ← stackAt_eq_stackFrameAt s0.sp 112, stackAt_eq_cells s0.sp 14]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro v_pad0
  apply SepWP.exists_elim; intro v_pad1
  iterate 12 (apply SepWP.exists_elim; intro _)
  let SavedPad : SepProp :=
    ((s0.sp - 112#64) ↦₆₄ v_pad0) ∗
    ((s0.sp - 104#64) ↦₆₄ v_pad1) ∗
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
    ((s0.sp - 88#64) ↦₆₄ ret_pc) ∗
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
    ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))
  refine SepWP.seq_noSyscalls (mid_pc := C.padIntegralWritePrefixAddr)
    (Q := fun s1 P1 =>
      (P1 ⊢ stackFrameAt sp2 0x30 ∗
        (stackFrameAt (sp2 - 0x30#64) (ws - 0x70) ∗
         u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
         (slicePtr ↦ₛ bs) ∗ SavedPad ∗ W emitted s0 ∗ F)) ∧
      s1.sp = sp2 ∧ s1.spAligned = true ∧
      s1.readReg64 Reg.lr = C.padIntegralAddr + 0x8c#64 ∧
      s1.readReg32 .x2 = 0xffffffff#32 ∧ s1.readReg64 .x3 = 0#64 ∧
      s1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length ∧
      s1.readReg64 (.gpr 21#5) = C.adapterWriteVtableAddr ∧
      s1.readReg64 (.gpr 25#5) = writerPtr ∧
      s1.readReg64 (.gpr 28#5) = slicePtr ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0)
    hext ?_ ?_
  · have hc_pro : (P.withSvc noSyscalls).hasCode C.padIntegralAddr padIntegralPrologueWords :=
      hcode.padIntPrologue
    dsimp only [u64DisplayStaticRes]
    rw [pointsTo64_fmtFlags_split (formatterPtr + 16#64)]
    iterate 34 wp_step
    refine step_padIntegralCallPrefix_bl (hcode.withSvc noSyscalls).padIntCallPrefix
      (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine SepWP.done rfl (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hws_split : stackFrameAt (s0.sp - 112#64) (ws - 0x40) =
          stackFrameAt sp2 0x30 ∗ stackFrameAt (sp2 - 0x30#64) (ws - 0x70) := by
        dsimp only [sp2]
        conv => lhs; rw [show ws - 0x40 = 0x30 + (ws - 0x70) by omega]
        exact stackFrameAt_split (s0.sp - 112#64) 0x30 (ws - 0x70) (by omega)
      rw [hws_split, ← pointsTo64_fmtFlags_split (formatterPtr + 16#64)]
      apply entails_of_eq
      dsimp only [sp2, SavedPad]
      simp only [bv_lin_norm]; ac_rfl
    · simp [wp_norm, arm64_norm, sp2]
    · unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align
    · simp [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
  · intro s1 P1 hpc1 hrun1 hpure01 ⟨hent1, hsp1, hsp_align1, hlr1, hw2_1, hx3_1,
      hx19_1, hx21_1, hx25_1, hx28_1, hvregs1⟩
    refine SepWP.weaken_pre hent1 ?_
    refine padIntegralWritePrefix_none_wp hcode.padPrefix_words hext hpc1 hrun1 hsp1
      hsp_align1 hlr1 hw2_1 hx3_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcs12 hx0_2 hpure12
    have hpure02 := FmtPureStatePreserved.trans hpure01 hpure12
    have hsp_align2 : s2.spAligned = true := by unfold State.spAligned at *; rwa [hsp2, ← hsp1]
    have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
    have hx19_2 : s2.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length := hcs12.1.trans hx19_1
    have hx21_2 : s2.readReg64 (.gpr 21#5) = C.adapterWriteVtableAddr := hcs12.2.2.1.trans hx21_1
    have hx25_2 : s2.readReg64 (.gpr 25#5) = writerPtr := hcs12.2.2.2.2.2.2.1.trans hx25_1
    have hx28_2 : s2.readReg64 (.gpr 28#5) = slicePtr := hcs12.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 :=
      hcs12.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    let FrameCall : SepProp :=
      stackFrameAt (s0.sp - BitVec.ofNat 64 writeStackBytes) (0x30 + ws - writeStackBytes) ∗
      u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗ F
    refine SepWP.seq_noSyscalls (mid_pc := C.adapterWriteStrAddr)
      (Q := fun s3 P3 =>
        (P3 ⊢ (W emitted s0 ∗ (slicePtr ↦ₛ bs) ∗ stackFrameAt s0.sp writeStackBytes) ∗ FrameCall) ∧
        s3.sp = s0.sp ∧ s3.spAligned = true ∧
        s3.readReg64 Reg.lr = ret_pc ∧
        s3.readReg64 .x0 = writerPtr ∧ s3.readReg64 .x1 = slicePtr ∧
        s3.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
        CalleeSavedPreserved s0 s3)
      hext ?_ ?_
    · have hc_tail : (P.withSvc noSyscalls).hasCode (C.padIntegralAddr + 0x8c#64)
        padIntegralTailWords := hcode.padIntTail
      dsimp only [u64DisplayStaticRes, HbAdapterWriteVtableRo, SavedPad, sp2] at hsp2 ⊢
      iterate 13 wp_step
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2]) ?_
      refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hsaved_ent : SavedPad ⊢ stackFrameAt s0.sp 0x70 := by
          dsimp only [SavedPad]
          rw [← stackAt_eq_stackFrameAt s0.sp 112, stackAt_eq_cells s0.sp 14]
          simp only [Nat.reduceMul]
          iterate 13 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
          exact cells_sub_one_entails 8
        have hws_mrg : stackFrameAt sp2 0x30 ∗ stackFrameAt (sp2 - 0x30#64) (ws - 0x70) =
            stackFrameAt (s0.sp - BitVec.ofNat 64 0x70) (ws - 0x40) := by
          dsimp only [sp2]
          symm; conv => lhs; rw [show ws - 0x40 = 0x30 + (ws - 0x70) by omega]
          exact stackFrameAt_split (s0.sp - 0x70#64) 0x30 (ws - 0x70) (by omega)
        have hstack_ent : SavedPad ∗ (stackFrameAt sp2 0x30 ∗ stackFrameAt (sp2 - 0x30#64) (ws - 0x70)) ⊢
            stackFrameAt s0.sp writeStackBytes ∗
              stackFrameAt (s0.sp - BitVec.ofNat 64 writeStackBytes) (0x30 + ws - writeStackBytes) := by
          rw [hws_mrg]
          refine Entails.trans (sepConj_mono_left hsaved_ent) ?_
          rw [← stackFrameAt_split s0.sp 0x70 (ws - 0x40) (by omega),
              show 0x70 + (ws - 0x40) = writeStackBytes + (0x30 + ws - writeStackBytes) by omega,
              stackFrameAt_split s0.sp writeStackBytes (0x30 + ws - writeStackBytes) (by omega)]
          exact Entails.refl _
        refine Entails.trans (Q := (SavedPad ∗ (stackFrameAt sp2 0x30 ∗ stackFrameAt (sp2 - 0x30#64) (ws - 0x70))) ∗
            (W emitted s0 ∗ (slicePtr ↦ₛ bs) ∗ u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗ F))
          (by apply entails_of_eq; dsimp only [SavedPad, sp2, u64DisplayStaticRes, HbAdapterWriteVtableRo]; ac_rfl) ?_
        refine Entails.trans (sepConj_mono_left hstack_ent) ?_
        apply entails_of_eq; dsimp only [FrameCall]; ac_rfl
      · simp [wp_norm, arm64_norm, bv_lin_norm]
      · unfold State.spAligned at *; simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_align
      · simp [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, hvregs2]
    · intro s3 P3 hpc3 hrun3 hpure23 ⟨hent3, hsp3, hsp_align3, hlr3, hx0_3, hx1_3, hx2_3, hcs03⟩
      have hpure03 := FmtPureStatePreserved.trans hpure02 hpure23
      have hent3' : P3 ⊢ (W emitted s3 ∗ (slicePtr ↦ₛ bs) ∗ stackFrameAt s0.sp writeStackBytes) ∗ FrameCall :=
        Entails.trans hent3 (sepConj_mono_left (sepConj_mono_left (hw.pure_transport emitted hpure03)))
      refine SepWP.weaken_pre hent3' ?_
      refine SepWP.call_subroutine_frame
        (hw.write_str_owned emitted bs slicePtr hlo hhi hno_nl hsl_ne hsl_fit)
        (x := ()) (F := FrameCall) hpc3 hrun3 hsp_align3 hlr3 ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
      · intro R hm
        dsimp only; simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0_3, hx1_3, hx2_3⟩, by simpa [hsp3, sepConj_assoc] using hm⟩
      · intro sf hpcf hrunf hspf hcs3f
        apply SepWP.of_reaches_pc; intro R hm
        dsimp only at hm; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        obtain ⟨⟨hx0_f, hio3f⟩, hm⟩ := hm
        have hio0f := FmtIoStatePreserved.trans hpure03.toIo hio3f
        have hspf' : sf.sp = s0.sp := hspf.trans hsp3
        have hcs0f := CalleeSavedPreserved.trans hcs03 hcs3f
        apply SepWP.to_reaches_pc ?_
          (P := (W (emitted ++ bs) sf ∗ (slicePtr ↦ₛ bs) ∗ stackFrameAt s0.sp writeStackBytes) ∗ FrameCall)
          (by simpa [hsp3, sepConj_assoc] using hm)
        have hrepack : (W (emitted ++ bs) sf ∗ (slicePtr ↦ₛ bs) ∗ stackFrameAt s0.sp writeStackBytes) ∗ FrameCall ⊢
            (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
              (slicePtr ↦ₛ bs) ∗ W (emitted ++ bs) sf ∗
              stackFrameAt s0.sp (0x30 + max 0x30 writeStackBytes)) ∗ F := by
          have hws_mrg : stackFrameAt s0.sp writeStackBytes ∗
              stackFrameAt (s0.sp - BitVec.ofNat 64 writeStackBytes) (0x30 + ws - writeStackBytes) =
              stackFrameAt s0.sp (0x30 + max 0x30 writeStackBytes) := by
            symm; conv => lhs; rw [show 0x30 + max 0x30 writeStackBytes = writeStackBytes + (0x30 + ws - writeStackBytes) by omega]
            exact stackFrameAt_split s0.sp writeStackBytes (0x30 + ws - writeStackBytes) (by omega)
          dsimp only [FrameCall]
          apply entails_of_eq
          rw [← hws_mrg]; ac_rfl
        exact SepWP.weaken_pre hrepack (hnext sf hpcf hrunf hspf' hcs0f hx0_f hio0f)

private def CalleeSaved22_28 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem CalleeSaved22_28.trans_cs {s0 s1 s2 : State}
    (h01 : CalleeSaved22_28 s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSaved22_28 s0 s2 :=
  ⟨h12.2.2.2.1.trans h01.1,
   h12.2.2.2.2.1.trans h01.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.1,
   h12.2.2.2.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

/-- Continuation-passing `SepWP` theorem for `<u64 as core::fmt::Display>::fmt` on a default-flags
    `Formatter` (`[formatterPtr] = writerPtr`, `[formatterPtr + 8] = C.adapterWriteVtableAddr`,
    `[formatterPtr + 16] = 0x60000020#64`). -/
theorem u64DisplayFmt_default_wp {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    {target_pc ret_pc sp0 valPtr formatterPtr v : BitVec 64}
    {emitted : List (BitVec 8)} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : HbFmtCode P C)
    (hw : HbFmtWriter P C writerPtr writeStackBytes W)
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s0.pc = C.u64DisplayFmtAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true) (hsp_lo : 0x100 ≤ sp0.toNat)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = valPtr)
    (hx1 : s0.readReg64 .x1 = formatterPtr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.readReg64 .x0 = 0#64 → FmtIoStatePreserved s0 sf →
      SepWP P target_pc sf
        ((u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
          W (emitted ++ formatDecimalNat v.toNat) sf ∗
          stackFrameAt sp0 (0x80 + max 0x30 writeStackBytes)) ∗ F)
        post oom) :
    SepWP P target_pc s0
      ((u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
        W emitted s0 ∗
        stackFrameAt sp0 (0x80 + max 0x30 writeStackBytes)) ∗ F)
      post oom := by
  subst hsp
  let ws := max 0x30 writeStackBytes
  have hws_lo : 0x70 ≤ ws := by have := hw.stack_lo; omega
  have hws_le : ws ≤ 2 ^ 32 := by have := hw.stack_le; omega
  let sp1 := s0.sp - 0x50#64
  let bufBase := sp1 + 0x0c#64
  let bs := formatDecimalNat v.toNat
  let len := bs.length
  let slicePtr := bufBase + BitVec.ofNat 64 (20 - len)
  obtain ⟨hlo, hhi⟩ := formatDecimal_length_bounds v.isLt
  have hno_nl := formatDecimal_not_mem_nl v.toNat
  obtain ⟨hsl_ne, hsl_fit, hlen_sub, _⟩ := u64Display_slice_bounds hsp_lo hlo hhi
  have hx0' : s0.readReg64 (.gpr 0#5) = valPtr := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = formatterPtr := hx1
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  conv =>
    arg 4
    rw [show 0x80 + max 0x30 writeStackBytes = 0x50 + (0x30 + ws) by omega,
        stackFrameAt_split s0.sp 0x50 (0x30 + ws) (by omega),
        u64Display_stack_unpack s0.sp,
        ← stackAt_eq_stackFrameAt s0.sp 48, stackAt_eq_cells s0.sp 6]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro v_slot38
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  let SavedSlots : SepProp :=
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ ret_pc) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ v_slot38) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))
  refine SepWP.seq_noSyscalls (mid_pc := C.u64FmtInnerAddr)
    (Q := fun s1 P1 =>
      (P1 ⊢ ((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗ memRegion bufBase 20 ∗ stackFrameAt sp1 0x10) ∗
        (stackFrameAt (sp1 - 0x10#64) (0x20 + ws) ∗
         (valPtr ↦₆₄ v) ∗ (formatterPtr ↦₆₄ writerPtr) ∗
         ((formatterPtr + 8#64) ↦₆₄ C.adapterWriteVtableAddr) ∗
         ((formatterPtr + 16#64) ↦₆₄ 0x60000020#64) ∗
         HbAdapterWriteVtableRo C ∗
         memRegion sp1 12 ∗ SavedSlots ∗ W emitted s0 ∗ F)) ∧
      s1.sp = sp1 ∧ s1.spAligned = true ∧
      s1.readReg64 Reg.lr = C.u64DisplayFmtAddr + 0x30#64 ∧
      s1.readReg64 .x0 = v ∧ s1.readReg64 .x1 = bufBase ∧ s1.readReg64 .x2 = 20#64 ∧
      s1.readReg64 (.gpr 19#5) = formatterPtr ∧
      s1.readReg64 (.gpr 20#5) = 20#64 ∧
      s1.readReg64 (.gpr 21#5) = bufBase ∧
      CalleeSaved22_28 s0 s1)
    hext ?_ ?_
  · have hc_pro : (P.withSvc noSyscalls).hasCode C.u64DisplayFmtAddr u64DisplayPrologueWords :=
      hcode.u64Prologue
    dsimp only [u64DisplayStaticRes]
    iterate 11 wp_step
    refine step_u64CallInner_bl (hcode.withSvc noSyscalls).u64CallInner
      (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine SepWP.done rfl (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hws_split : stackFrameAt (s0.sp - 80#64) (0x30 + ws) =
          stackFrameAt sp1 0x10 ∗ stackFrameAt (sp1 - 0x10#64) (0x20 + ws) := by
        dsimp only [sp1]
        conv => lhs; rw [show 0x30 + ws = 0x10 + (0x20 + ws) by omega]
        exact stackFrameAt_split (s0.sp - 80#64) 0x10 (0x20 + ws) (by omega)
      rw [hws_split]
      apply entails_of_eq
      dsimp only [sp1, bufBase, SavedSlots]
      simp only [bv_lin_norm]; ac_rfl
    · simp [wp_norm, arm64_norm, sp1]
    · unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align
    · simp [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · dsimp only [sp1, bufBase]; simp (config := { decide := true }) [wp_norm, arm64_norm, bv_lin_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · dsimp only [sp1, bufBase]; simp (config := { decide := true }) [wp_norm, arm64_norm, bv_lin_norm]
    · simp (config := { decide := true }) [CalleeSaved22_28, wp_norm, arm64_norm]
  · intro s1 P1 hpc1 hrun1 hpure01 ⟨hent1, hsp1, hsp_align1, hlr1, hx0_1, hx1_1, hx2_1,
      hx19_1, hx20_1, hx21_1, hcs22_1⟩
    refine SepWP.weaken_pre hent1 ?_
    refine u64FmtInner_wp hcode hext hpc1 hrun1 hsp1 hsp_align1 hlr1 hx0_1 hx1_1 hx2_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcs12 hx0_2 hpure12
    have hpure02 := FmtPureStatePreserved.trans hpure01 hpure12
    have hsp_align2 : s2.spAligned = true := by unfold State.spAligned at *; rwa [hsp2, ← hsp1]
    have hx0_2' : s2.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (20 - len) := hx0_2
    have hx19_2 : s2.readReg64 (.gpr 19#5) = formatterPtr := hcs12.1.trans hx19_1
    have hx20_2 : s2.readReg64 (.gpr 20#5) = 20#64 := hcs12.2.1.trans hx20_1
    have hx21_2 : s2.readReg64 (.gpr 21#5) = bufBase := hcs12.2.2.1.trans hx21_1
    have hcs22_2 : CalleeSaved22_28 s0 s2 := hcs22_1.trans_cs hcs12
    refine SepWP.seq_noSyscalls (mid_pc := C.padIntegralAddr)
      (Q := fun s3 P3 =>
        (P3 ⊢ (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
          (slicePtr ↦ₛ bs) ∗ W emitted s0 ∗
          stackFrameAt sp1 (0x30 + max 0x30 writeStackBytes)) ∗
          (memRegion sp1 12 ∗ memRegion bufBase (20 - len) ∗ SavedSlots ∗ F)) ∧
        s3.sp = sp1 ∧ s3.spAligned = true ∧
        s3.readReg64 Reg.lr = C.u64DisplayFmtAddr + 0x4c#64 ∧
        s3.readReg64 .x0 = formatterPtr ∧ s3.readReg64 .x1 = 1#64 ∧
        s3.readReg64 .x3 = 0#64 ∧ s3.readReg64 .x4 = slicePtr ∧
        s3.readReg64 .x5 = BitVec.ofNat 64 len ∧
        CalleeSaved22_28 s0 s3)
      hext ?_ ?_
    · have hc_mid : (P.withSvc noSyscalls).hasCode (C.u64DisplayFmtAddr + 0x30#64)
        u64DisplayMidWords := hcode.u64Mid_words
      iterate 6 wp_step
      refine step_u64CallPad_bl (hcode.withSvc noSyscalls).u64CallPad
        (by simp [bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2]) ?_
      refine SepWP.done rfl (by simp [wp_norm, arm64_norm, hrun2]) ?_
      refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hws_mrg : stackFrameAt sp1 0x10 ∗ stackFrameAt (sp1 - 0x10#64) (0x20 + ws) =
            stackFrameAt sp1 (0x30 + max 0x30 writeStackBytes) := by
          symm; conv => lhs; rw [show 0x30 + max 0x30 writeStackBytes = 0x10 + (0x20 + ws) by omega]
          exact stackFrameAt_split sp1 0x10 (0x20 + ws) (by omega)
        refine Entails.trans (Q := ((C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
            memRegion bufBase (20 - len) ∗ (slicePtr ↦ₛ bs) ∗
            (stackFrameAt sp1 0x10 ∗ stackFrameAt (sp1 - 0x10#64) (0x20 + ws))) ∗
            ((valPtr ↦₆₄ v) ∗ (formatterPtr ↦₆₄ writerPtr) ∗
             ((formatterPtr + 8#64) ↦₆₄ C.adapterWriteVtableAddr) ∗
             ((formatterPtr + 16#64) ↦₆₄ 0x60000020#64) ∗
             HbAdapterWriteVtableRo C ∗
             memRegion sp1 12 ∗ SavedSlots ∗ W emitted s0 ∗ F))
          (by apply entails_of_eq; dsimp only [bs, len, slicePtr]; ac_rfl) ?_
        rw [hws_mrg]
        apply entails_of_eq; dsimp only [u64DisplayStaticRes]; ac_rfl
      · simp [wp_norm, arm64_norm, hsp2]
      · unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align2
      · simp [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · dsimp only [slicePtr, bufBase, sp1, len, bs]; simp (config := { decide := true }) [wp_norm, arm64_norm, bv_lin_norm]
      · dsimp only [len, bs]; simp (config := { decide := true }) [wp_norm, arm64_norm]
      · obtain ⟨h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs22_2
        simp (config := { decide := true }) [CalleeSaved22_28, wp_norm, arm64_norm,
          h22, h23, h24, h25, h26, h27, h28, hv]
    · intro s3 P3 hpc3 hrun3 hpure23 ⟨hent3, hsp3, hsp_align3, hlr3, hx0_3, hx1_3,
        hx3_3, hx4_3, hx5_3, hcs22_3⟩
      have hpure03 := FmtPureStatePreserved.trans hpure02 hpure23
      have hent3' : P3 ⊢ (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
          (slicePtr ↦ₛ bs) ∗ W emitted s3 ∗
          stackFrameAt sp1 (0x30 + max 0x30 writeStackBytes)) ∗
          (memRegion sp1 12 ∗ memRegion bufBase (20 - len) ∗ SavedSlots ∗ F) :=
        Entails.trans hent3
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (hw.pure_transport emitted hpure03)))))
      refine SepWP.weaken_pre hent3' ?_
      refine padIntegral_default_wp hcode hw hext hpc3 hrun3 hsp3 hsp_align3 hlr3
        hx0_3 hx1_3 hx3_3 hx4_3 hx5_3 hlo hhi hno_nl hsl_ne hsl_fit ?_
      intro s4 hpc4 hrun4 hsp4 hcs34 hx0_4 hio34
      have hio04 := FmtIoStatePreserved.trans hpure03.toIo hio34
      have hx0_4' : s4.readReg64 (.gpr 0#5) = 0#64 := hx0_4
      have hcs22_4 : CalleeSaved22_28 s0 s4 := hcs22_3.trans_cs hcs34
      refine SepWP.seq_noSyscalls (mid_pc := ret_pc)
        (Q := fun sf Pf =>
          (Pf ⊢ (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
            W (emitted ++ bs) s4 ∗ stackFrameAt s0.sp (0x80 + ws)) ∗ F) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = 0#64)
        hext ?_ ?_
      · have hc_epi : (P.withSvc noSyscalls).hasCode (C.u64DisplayFmtAddr + 0x4c#64)
          u64DisplayEpilogueWords := hcode.u64Epilogue
        dsimp only [SavedSlots, sp1] at hsp4 ⊢
        iterate 5 wp_step
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4]) ?_
        refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_⟩
        · have hsaved_ent : SavedSlots ⊢ stackFrameAt s0.sp 48 := by
            dsimp only [SavedSlots]
            rw [← stackAt_eq_stackFrameAt s0.sp 48, stackAt_eq_cells s0.sp 6]
            simp only [Nat.reduceMul]
            iterate 5 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
            exact cells_sub_one_entails 8
          have hbuf_ent : memRegion sp1 12 ∗ memRegion bufBase (20 - len) ∗ (slicePtr ↦ₛ bs) ⊢
              stackFrameAt (s0.sp - BitVec.ofNat 64 48) 32 :=
            u64Display_buf_repack s0.sp bs hhi
          refine Entails.trans (Q := (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
              W (emitted ++ bs) s4 ∗
              (SavedSlots ∗ (memRegion sp1 12 ∗ memRegion bufBase (20 - len) ∗ (slicePtr ↦ₛ bs)) ∗
               stackFrameAt sp1 (0x30 + ws))) ∗ F)
            (by apply entails_of_eq; dsimp only [SavedSlots, sp1, ws]; ac_rfl) ?_
          apply sepConj_mono_left
          refine sepConj_mono_right (sepConj_mono_right ?_)
          refine Entails.trans (sepConj_mono_left hsaved_ent) ?_
          refine Entails.trans (sepConj_mono_right (sepConj_mono_left hbuf_ent)) ?_
          rw [← sepConj_assoc, ← stackFrameAt_split s0.sp 48 32 (by decide),
              show (48 : Nat) + 32 = 0x50 from rfl,
              ← stackFrameAt_split s0.sp 0x50 (0x30 + ws) (by omega),
              show 0x50 + (0x30 + ws) = 0x80 + ws by omega]
          exact Entails.refl _
        · simp [wp_norm, arm64_norm, bv_lin_norm]
        · obtain ⟨h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs22_4
          simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm,
            h22, h23, h24, h25, h26, h27, h28, hv]
        · simp (config := { decide := true }) [wp_norm, arm64_norm, hx0_4']
      · intro sf Pf hpcf hrunf hpure4f ⟨hentf, hspf, hcs0f, hx0f⟩
        have hio0f := FmtIoStatePreserved.trans hio04 hpure4f.toIo
        have hentf' : Pf ⊢ (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
            W (emitted ++ formatDecimalNat v.toNat) sf ∗
            stackFrameAt s0.sp (0x80 + max 0x30 writeStackBytes)) ∗ F :=
          Entails.trans hentf
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (hw.pure_transport (emitted ++ formatDecimalNat v.toNat) hpure4f))))
        exact SepWP.weaken_pre hentf' (hnext sf hpcf hrunf hspf hcs0f hx0f hio0f)

/-- `subroutine_ok` wrapper for `<u64 as core::fmt::Display>::fmt` on a default-flags `Formatter`. -/
theorem u64DisplayFmt_default_ok {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    (hcode : HbFmtCode P C)
    (hw : HbFmtWriter P C writerPtr writeStackBytes W)
    (hext : ∀ pc, P.externAt? pc = none)
    (valPtr formatterPtr v : BitVec 64) (emitted : List (BitVec 8)) :
    subroutine_ok P C.u64DisplayFmtAddr
      (u64DisplayFmtDefaultSpec C writerPtr writeStackBytes W valPtr formatterPtr v emitted) := by
  refine subroutine_ok_of_sepWP_init fun _ R s0 hpc hrun hpre hsp => ?_
  dsimp only [u64DisplayFmtDefaultSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hsp_lo⟩, hmem⟩ := hpre
  refine ⟨(u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
      W emitted s0 ∗ stackFrameAt s0.sp (0x80 + max 0x30 writeStackBytes)) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine u64DisplayFmt_default_wp hcode hw hext hpc hrun rfl hsp hsp_lo rfl hx0 hx1
    fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hio_f => ?_
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [sepConj_emp] at hm
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, hio_f⟩, by simpa [sepConj_assoc] using hm⟩

end CaseStudies.Hashbrown.Proofs.StdCli
