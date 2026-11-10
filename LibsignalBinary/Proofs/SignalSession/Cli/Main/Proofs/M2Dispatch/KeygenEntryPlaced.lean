/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenMidPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Relocatable `keygen` Sign/Length Entry & Digits `1, 0` (`M+0x39c .. M+0x3ec`, Block `617`)

Verifies the sign/length entry check (`M+0x39c .. M+0x3b4`) and final two unrolled decimal digit
steps (`M+0x3b8 .. M+0x3ec`) of `keygen`'s `u32` count parser under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Digits `1, 0` (`M+0x3d0`, `M+0x3b8`) -/

set_option maxHeartbeats 400000 in
theorem step_unroll_3c8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 dsPtr : BitVec 64}
    {bs1 bs2 bs3 pref rest : List (BitVec 8)} {b : BitVec 8} {me : AddrV} {acc : Nat} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hne_ds : stripPlus bs3 ≠ []) (hs : InMainPlaced CodeOk s0 s 0x3d0)
    (kr : KeygenRegs s0 s buf vcap vptr) (hlen_le : rest.length ≤ 6)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap) (hx8 : s.readReg64 (.gpr 8#5) = dsPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (2 + rest.length))
    (hacc_lt : acc < 10) (hx9 : (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 acc)
    (hds : stripPlus bs3 = pref ++ (b :: rest)) (hpref_dig : ∀ x ∈ pref, isDigit x = true)
    (hpref_val : pref.foldl (fun a x => 10 * a + (x.toNat - 48)) 0 = acc)
    (hrest : ((dsPtr + 1#64) ↦ₛ (b :: rest)) ∗ RestP3 = cStrAt p3 bs3) :
    KeygenGoalPlaced K s w3 (((dsPtr + 1#64) ↦ₛ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  rw [ProofLib.pointsToBytes_cons, sepConj_assoc, sepConj_assoc]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  by_cases hdig : isDigit b = true
  · have hhi_f := digit_hi_false hdig
    have hv_lt : 10 * acc + (b.toNat - 48) < 100 := by
      simp only [isDigit, decide_eq_true_eq] at hdig; omega
    have hmadd := madd_digit_lo32 (acc := acc) hdig (by omega)
    rcases rest with _ | ⟨b2, tail2⟩
    · rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x52c#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_keygen_524_placed (w3 := w3) (v := 10 * acc + (b.toNat - 48)) K
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
          (by simp only [arm64_norm, hx1]) (by omega)
          (by kg_simp) hne_ds
          (by rw [hds]; exact append_dig hpref_dig hdig)
          (by rw [hds]; simp [List.foldl_append, hpref_val]))
      rw [← hrest, ProofLib.pointsToBytes_cons]; exact Entails.of_eq (by ac_rfl)
    · have hne2 : (BitVec.ofNat 64 (2 + (b2 :: tail2).length) == 2#64) = false := by
        apply beq_false_of_ne; intro h
        have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hlen_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x3f0#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hrest' : ((dsPtr + 2#64) ↦ₛ (b2 :: tail2)) ∗ (((dsPtr + 1#64) ↦₈ b) ∗ RestP3) =
          cStrAt p3 bs3 := by
        rw [← hrest]; (conv_rhs => rw [ProofLib.pointsToBytes_cons])
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre
        (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
        (step_unroll_3e8_placed (w3 := w3) (pref := pref ++ [b]) K hne_ds
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [List.length_cons] at hlen_le; omega)
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
          (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx8])
          (by simp only [arm64_norm, hx10]; congr 1; simp only [List.length_cons]; omega)
          (by simp only [arm64_norm]) hv_lt (by kg_simp)
          (by simp [hds]) (append_dig hpref_dig hdig) (by simp [List.foldl_append, hpref_val]) hrest')
  · have hdig_f : isDigit b = false := Bool.eq_false_iff.mpr hdig
    have hhi_t := digit_hi_true hdig
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x534#64) hinv
    wp_steps
    apply SepWP.done (by kg_simp) (by kg_simp)
    intro hinv1
    have hmem : b ∈ stripPlus bs3 := by rw [hds]; simp
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_keygen_52c_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp, hinv1,
         by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
        (K.parse_none (parseUnsigned_none_of_nonDigit hmem hdig_f)))
    rw [← hrest, ProofLib.pointsToBytes_cons]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem step_unroll_3b0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 dsPtr : BitVec 64}
    {bs1 bs2 bs3 rest : List (BitVec 8)} {b : BitVec 8} {me : AddrV} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x3b8) (kr : KeygenRegs s0 s buf vcap vptr)
    (hlen_le : rest.length ≤ 7)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap) (hx8 : s.readReg64 (.gpr 8#5) = dsPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (1 + rest.length))
    (hds : stripPlus bs3 = b :: rest)
    (hrest : (dsPtr ↦ₛ (b :: rest)) ∗ RestP3 = cStrAt p3 bs3) :
    KeygenGoalPlaced K s w3 ((dsPtr ↦ₛ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  have hne_ds : stripPlus bs3 ≠ [] := by rw [hds]; simp
  rw [ProofLib.pointsToBytes_cons, sepConj_assoc, sepConj_assoc]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  by_cases hdig : isDigit b = true
  · have hhi_f := digit_hi_false hdig
    have hv_lt : b.toNat - 48 < 10 := by
      simp only [isDigit, decide_eq_true_eq] at hdig; omega
    rcases rest with _ | ⟨b1, tail1⟩
    · rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x52c#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hw9 : (b.setWidth 32 - 48#32) = BitVec.ofNat 32 (b.toNat - 48) := by
        apply BitVec.eq_of_toNat_eq; simp only [isDigit, decide_eq_true_eq] at hdig
        have := b.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_keygen_524_placed (w3 := w3) (v := b.toNat - 48) K
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
          (by simp only [arm64_norm, hx1]) (by omega)
          (by rw [← hw9]; kg_simp) hne_ds
          (by rw [hds]; intro x hx; rw [List.mem_singleton.mp hx]; exact hdig)
          (by rw [hds]; simp))
      rw [← hrest, ProofLib.pointsToBytes_cons]; exact Entails.of_eq (by ac_rfl)
    · have hne1 : (BitVec.ofNat 64 (1 + (b1 :: tail1).length) == 1#64) = false := by
        apply beq_false_of_ne; intro h
        have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hlen_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x3d0#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hw9 : (b.setWidth 32 - 48#32) = BitVec.ofNat 32 (b.toNat - 48) := by
        apply BitVec.eq_of_toNat_eq; simp only [isDigit, decide_eq_true_eq] at hdig
        have := b.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      have hrest' : ((dsPtr + 1#64) ↦ₛ (b1 :: tail1)) ∗ ((dsPtr ↦₈ b) ∗ RestP3) = cStrAt p3 bs3 := by
        rw [← hrest]; (conv_rhs => rw [ProofLib.pointsToBytes_cons]); ac_rfl
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (step_unroll_3c8_placed (w3 := w3) (pref := [b]) K hne_ds
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [List.length_cons] at hlen_le; omega)
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
          (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx8])
          (by simp only [arm64_norm, hx10]; congr 1; simp only [List.length_cons]; omega)
          hv_lt (by rw [← hw9]; kg_simp) (by simp [hds])
          (fun x hx => by rw [List.mem_singleton.mp hx]; exact hdig) (by simp) hrest')
  · have hdig_f : isDigit b = false := Bool.eq_false_iff.mpr hdig
    have hhi_t := digit_hi_true hdig
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x534#64) hinv
    wp_steps
    apply SepWP.done (by kg_simp) (by kg_simp)
    intro hinv1
    have hmem : b ∈ stripPlus bs3 := by rw [hds]; simp
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_keygen_52c_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp, hinv1,
         by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
        (K.parse_none (parseUnsigned_none_of_nonDigit hmem hdig_f)))
    rw [← hrest, ProofLib.pointsToBytes_cons]; exact Entails.of_eq (by ac_rfl)

/-! ## 2. Sign/Length Entry (`M+0x39c`) -/

set_option maxHeartbeats 400000 in
theorem step_keygen_394_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 dsPtr : BitVec 64}
    {bs1 bs2 bs3 tail : List (BitVec 8)} {b0 d0 : BitVec 8} {me : AddrV} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A uuidParse i s0 ret stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x39c) (kr : KeygenRegs s0 s buf vcap vptr)
    (hbs3_le : bs3.length ≤ 16384)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx8 : s.readReg64 (.gpr 8#5) = b0.setWidth 64)
    (hx25 : s.readReg64 (.gpr 25#5) = p3)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length)
    (hplus_ptr : dsPtr = if b0 = 43#8 then p3 + 1#64 else p3)
    (hplus_len : (stripPlus bs3).length = bs3.length - (if b0 = 43#8 then 1 else 0))
    (hds : stripPlus bs3 = d0 :: tail)
    (hrest : (dsPtr ↦ₛ (d0 :: tail)) ∗ RestP3 = cStrAt p3 bs3) :
    KeygenGoalPlaced K s w3 ((dsPtr ↦ₛ (d0 :: tail)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  have hds_le : (stripPlus bs3).length ≤ 16384 := by omega
  have hds_pos : 1 ≤ (stripPlus bs3).length := by rw [hds]; simp
  have hbs3_lt : bs3.length < 2 ^ 64 := by omega
  have hds_lt : (stripPlus bs3).length < 2 ^ 64 := by omega
  have hsub_len :
      (BitVec.ofNat 64 bs3.length - if (b0.zeroExtend 32 != 43#32) = true then 0#64 else 1#64) =
        BitVec.ofNat 64 (stripPlus bs3).length := by
    by_cases hp : b0 = 43#8
    · subst hp
      have hne : ((43#8 : BitVec 8).zeroExtend 32 != 43#32) = false := by decide
      simp only [hplus_len, ↓reduceIte] at hds_pos hds_lt ⊢
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbs3_lt, Nat.mod_eq_of_lt hds_lt]
      omega
    · have hp32 : (b0.zeroExtend 32 != 43#32) = true := by
        simp only [bne]; rw [beq_false_of_ne]; rfl; bv_omega
      simp only [hp, ↓reduceIte, Nat.sub_zero] at hplus_len
      simp only [hp32, ↓reduceIte, BitVec.sub_zero, hplus_len]
  have hcinc_ptr :
      (if (b0.zeroExtend 32 != 43#32) = true then p3 else p3 + 1#64) = dsPtr := by
    by_cases hp : b0 = 43#8
    · subst hp; simp [hplus_ptr]
    · have hp32 : (b0.zeroExtend 32 != 43#32) = true := by
        simp only [bne]; rw [beq_false_of_ne]; rfl; bv_omega
      simp [hp, hp32, hplus_ptr]
  replace hplus_ptr := hplus_ptr.symm
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  have hdt_lt : (d0 :: tail).length < 2 ^ 64 := by rw [← hds]; exact hds_lt
  by_cases hge9 : 9 ≤ (d0 :: tail).length
  · have hhs : BitVec.ule 9#64 (BitVec.ofNat 64 (d0 :: tail).length) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdt_lt]
      exact decide_eq_true hge9
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x4e8#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    rw [← hds] at hinv1 ⊢
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre (by rw [hds]; exact Entails.refl _)
      (step_keygen_4e0_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv1,
         by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by rw [hds]; simp) hds_le
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
        (by simp only [arm64_norm, hx1])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, hds])
        (by rw [hds]; exact hrest))
  · have hlt9 : BitVec.ule 9#64 (BitVec.ofNat 64 (d0 :: tail).length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdt_lt]
      exact decide_eq_false hge9
    have hne0 : (BitVec.ofNat 64 (d0 :: tail).length == 0#64) = false := by
      apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdt_lt] at htn; simp at htn
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x3b8#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    rw [← mProgPlaced_eq]
    exact step_unroll_3b0_placed K
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv1,
       by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [List.length_cons] at hge9; omega)
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
      (by simp only [arm64_norm, hx1])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; congr 1; exact Nat.add_comm _ 1)
      hds hrest

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
