/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenMidPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenUnrollPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `keygen` Digits `3, 2` (`M+0x3f0 .. M+0x43c`)

Budget-threaded verification of unrolled decimal digit steps 3 and 2 of `keygen`'s `u32` count
parser on Block `617` with read-only `argv`, threading `A.pool` inside `KeygenGoalPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenMidPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV InMainPlaced LsCodeInv isDigit mPcPlaced_eq mProgPlaced mProgPlaced_eq parseArgs
   sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (KeygenRegs append_dig digit_hi_false digit_hi_true madd_digit_lo32
   parseUnsigned_none_of_nonDigit stripPlus)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlacedBudget
  (KeygenCtxPlaced KeygenGoalPlaced keygenBase_congr_vm step_keygen_524_placed
   step_keygen_52c_placed step_keygen_f04_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenUnrollPlacedBudget
  (step_unroll_438_placed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 400000 in
theorem step_unroll_404_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st : M.σ} {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 dsPtr : BitVec 64}
    {bs1 bs2 bs3 pref rest : List (BitVec 8)} {b : BitVec 8} {me : AddrV} {acc : Nat} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hne_ds : stripPlus bs3 ≠ []) (hs : InMainPlaced CodeOk s0 s 0x40c)
    (kr : KeygenRegs s0 s buf vcap vptr)
    (hlen_le : rest.length ≤ 4)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx8 : s.readReg64 (.gpr 8#5) = dsPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (4 + rest.length))
    (hx12 : (s.readReg64 (.gpr 12#5)).setWidth 32 = 10#32)
    (hacc_lt : acc < 10 ^ 3) (hx9 : (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 acc)
    (hds : stripPlus bs3 = pref ++ (b :: rest)) (hpref_dig : ∀ x ∈ pref, isDigit x = true)
    (hpref_val : pref.foldl (fun a x => 10 * a + (x.toNat - 48)) 0 = acc)
    (hrest : ((dsPtr + 3#64) ↦ᵣ (b :: rest)) ∗ RestP3 = cStrAtRO p3 bs3) :
    KeygenGoalPlaced K s w3 (((dsPtr + 3#64) ↦ᵣ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  rw [ProofLib.pointsToBytesRO_cons, sepConj_assoc, sepConj_assoc]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  by_cases hdig : isDigit b = true
  · have hhi_f := digit_hi_false hdig
    have hv_lt : 10 * acc + (b.toNat - 48) < 10 ^ 4 := by
      simp only [isDigit, decide_eq_true_eq] at hdig; omega
    have hmadd := madd_digit_lo32 (acc := acc) hdig (by omega)
    rcases rest with _ | ⟨b4, tail4⟩
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
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
        bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)
    · have hne4 : (BitVec.ofNat 64 (4 + (b4 :: tail4).length) == 4#64) = false := by
        apply beq_false_of_ne; intro h
        have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hlen_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x440#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hrest' : ((dsPtr + 4#64) ↦ᵣ (b4 :: tail4)) ∗ (((dsPtr + 3#64) ↦₈ᵣ b) ∗ RestP3) =
          cStrAtRO p3 bs3 := by
        rw [← hrest]; (conv_rhs => rw [ProofLib.pointsToBytesRO_cons])
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_unroll_438_placed (w3 := w3) (pref := pref ++ [b]) K hne_ds
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [List.length_cons] at hlen_le; omega)
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
          (by simp only [arm64_norm, hx15]) (by simp only [arm64_norm, hx8])
          (by simp only [arm64_norm, hx10]; congr 1; simp only [List.length_cons]; omega)
          (by simp only [arm64_norm, hx12]) hv_lt (by kg_simp)
          (by simp [hds]) (append_dig hpref_dig hdig) (by simp [List.foldl_append, hpref_val]) hrest')
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
        bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
  · have hdig_f : isDigit b = false := Bool.eq_false_iff.mpr hdig
    have hhi_t := digit_hi_true hdig
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xf40#64) hinv
    wp_steps
    apply SepWP.done (by kg_simp) (by kg_simp)
    intro hinv1
    have hmem : b ∈ stripPlus bs3 := by rw [hds]; simp
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_keygen_f04_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp, hinv1,
         by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
        (K.parse_none (parseUnsigned_none_of_nonDigit hmem hdig_f)))
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
      bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 400000 in
theorem step_unroll_3e8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st : M.σ} {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 dsPtr : BitVec 64}
    {bs1 bs2 bs3 pref rest : List (BitVec 8)} {b : BitVec 8} {me : AddrV} {acc : Nat} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hne_ds : stripPlus bs3 ≠ []) (hs : InMainPlaced CodeOk s0 s 0x3f0)
    (kr : KeygenRegs s0 s buf vcap vptr) (hlen_le : rest.length ≤ 5)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap) (hx8 : s.readReg64 (.gpr 8#5) = dsPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (3 + rest.length))
    (hx12 : (s.readReg64 (.gpr 12#5)).setWidth 32 = 10#32)
    (hacc_lt : acc < 100) (hx9 : (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 acc)
    (hds : stripPlus bs3 = pref ++ (b :: rest)) (hpref_dig : ∀ x ∈ pref, isDigit x = true)
    (hpref_val : pref.foldl (fun a x => 10 * a + (x.toNat - 48)) 0 = acc)
    (hrest : ((dsPtr + 2#64) ↦ᵣ (b :: rest)) ∗ RestP3 = cStrAtRO p3 bs3) :
    KeygenGoalPlaced K s w3 (((dsPtr + 2#64) ↦ᵣ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  rw [ProofLib.pointsToBytesRO_cons, sepConj_assoc, sepConj_assoc]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  by_cases hdig : isDigit b = true
  · have hhi_f := digit_hi_false hdig
    have hv_lt : 10 * acc + (b.toNat - 48) < 10 ^ 3 := by
      simp only [isDigit, decide_eq_true_eq] at hdig; omega
    have hmadd := madd_digit_lo32 (acc := acc) hdig (by omega)
    rcases rest with _ | ⟨b3, tail3⟩
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
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
        bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)
    · have hne3 : (BitVec.ofNat 64 (3 + (b3 :: tail3).length) == 3#64) = false := by
        apply beq_false_of_ne; intro h
        have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hlen_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x40c#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hrest' : ((dsPtr + 3#64) ↦ᵣ (b3 :: tail3)) ∗ (((dsPtr + 2#64) ↦₈ᵣ b) ∗ RestP3) =
          cStrAtRO p3 bs3 := by
        rw [← hrest]; (conv_rhs => rw [ProofLib.pointsToBytesRO_cons])
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_unroll_404_placed (w3 := w3) (pref := pref ++ [b]) K hne_ds
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
          (by simp only [arm64_norm, hx12]) hv_lt (by kg_simp)
          (by simp [hds]) (append_dig hpref_dig hdig) (by simp [List.foldl_append, hpref_val]) hrest')
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
        bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
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
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
      bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenMidPlacedBudget
