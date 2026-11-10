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
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenLoopPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `keygen` Multi-Digit Loop (`M+0x4e8 .. M+0x524`)

Budget-threaded verification of `keygen`'s `≥ 9`-digit overflow-checked decimal parsing loop on
Block `617` with read-only `argv`, threading `A.pool` inside `KeygenGoalPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenLoopPlacedBudget

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
  (KeygenRegs digit_hi_false digit_hi_true parseUnsigned_none_of_mul10_overflow
   parseUnsigned_none_of_nonDigit parseUnsigned_none_of_overflow shl32_bit0 stripPlus
   tst_hi32_shift tst_hi32_zero_of_setWidth32)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlacedBudget
  (KeygenCtxPlaced KeygenGoalPlaced keygenBase_congr_vm step_keygen_524_placed
   step_keygen_530_fail_placed step_keygen_f90_placed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem step_keygen_51c_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x524) (kr : KeygenRegs s0 s buf vcap vptr)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hw11 : (s.readReg64 (.gpr 11#5)).setWidth 32 = 0#32)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
  wp_steps
  apply SepWP.done (by kg_simp) (by kg_simp)
  intro hinv1
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_keygen_530_fail_placed (w3 := w3) K
      ⟨by rw [mPcPlaced_eq]; kg_simp,
       by kg_simp, by kg_simp, by kg_simp, hinv1,
       by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
      (by kg_simp) hparse)
  conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
    bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  exact Entails.refl _

set_option maxHeartbeats 400000 in
theorem step_keygen_loop_no_m10_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 remPtr : BitVec 64}
    {bs1 bs2 bs3 pref rest : List (BitVec 8)} {b : BitVec 8} {me : AddrV}
    {acc : Nat} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x4f0) (kr : KeygenRegs s0 s buf vcap vptr)
    (hlen_le : (b :: rest).length ≤ 16384)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx8 : s.readReg64 (.gpr 8#5) = remPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (b :: rest).length)
    (hx12 : s.readReg64 (.gpr 12#5) = 10#64)
    (hacc_lt : acc < 2 ^ 32) (hm10_lt : 10 * acc < 2 ^ 32)
    (hx9 : (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 acc)
    (hds : stripPlus bs3 = pref ++ (b :: rest))
    (hpref_dig : ∀ x ∈ pref, isDigit x = true)
    (hpref_val : pref.foldl (fun a x => 10 * a + (x.toNat - 48)) 0 = acc)
    (hrest : (remPtr ↦ᵣ (b :: rest)) ∗ RestP3 = cStrAtRO p3 bs3)
    (ih : ∀ (s1 : State),
      InMainPlaced CodeOk s0 s1 0x4f0 → KeygenRegs s0 s1 buf vcap vptr →
      rest.length ≤ 16384 →
      s1.readReg64 (.gpr 22#5) = ptr →
      s1.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length →
      s1.readReg64 (.gpr 1#5) = cap →
      s1.readReg64 (.gpr 8#5) = remPtr + 1#64 →
      s1.readReg64 (.gpr 10#5) = BitVec.ofNat 64 rest.length →
      s1.readReg64 (.gpr 12#5) = 10#64 →
      10 * acc + (b.toNat - 48) < 2 ^ 32 →
      (s1.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 (10 * acc + (b.toNat - 48)) →
      stripPlus bs3 = (pref ++ [b]) ++ rest →
      (∀ x ∈ pref ++ [b], isDigit x = true) →
      (pref ++ [b]).foldl (fun a x => 10 * a + (x.toNat - 48)) 0 = 10 * acc + (b.toNat - 48) →
      ((remPtr + 1#64) ↦ᵣ rest) ∗ ((remPtr ↦₈ᵣ b) ∗ RestP3) = cStrAtRO p3 bs3 →
      KeygenGoalPlaced K s1 w3 (((remPtr + 1#64) ↦ᵣ rest) ∗ ((remPtr ↦₈ᵣ b) ∗ RestP3))) :
    KeygenGoalPlaced K s w3 ((remPtr ↦ᵣ (b :: rest)) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  have hm10_64 : 10 * acc < 2 ^ 64 := by omega
  have hlt64 : acc < 2 ^ 64 := by omega
  have hlen_ne0 : (BitVec.ofNat 64 (b :: rest).length == 0#64) = false := by
    apply beq_false_of_ne; intro h
    have htn := congrArg BitVec.toNat h
    simp only [List.length_cons] at hlen_le
    simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
  have humull : (BitVec.ofNat 32 acc).setWidth 64 * 10#64 = BitVec.ofNat 64 (10 * acc) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hacc_lt, Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hm10_64,
      Nat.mod_eq_of_lt (Nat.mul_comm 10 acc ▸ hm10_64), Nat.mul_comm]
  have htst_z : (BitVec.ofNat 64 (10 * acc) &&& (-4294967296#64) == 0#64) = true := by
    apply beq_iff_eq.mpr
    have h1 : BitVec.ofNat 64 (10 * acc) = (BitVec.ofNat 32 (10 * acc)).setWidth 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hm10_lt, Nat.mod_eq_of_lt hm10_64]
    rw [h1]; exact tst_hi32_zero_of_setWidth32 _
  have hm10_w32 : (BitVec.ofNat 64 (10 * acc)).setWidth 32 = BitVec.ofNat 32 (10 * acc) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hm10_lt, Nat.mod_eq_of_lt hm10_64]
  rw [ProofLib.pointsToBytesRO_cons, sepConj_assoc, sepConj_assoc]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  by_cases hdig_b : isDigit b = true
  · have hhi_f := digit_hi_false hdig_b
    have hb_lt10 : b.toNat - 48 < 10 := by
      simp only [isDigit, decide_eq_true_eq] at hdig_b; omega
    have hb_sub : (b.setWidth 32 - 48#32).toNat = b.toNat - 48 := by
      simp only [isDigit, decide_eq_true_eq] at hdig_b
      have := b.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    by_cases hover : 2 ^ 32 ≤ 10 * acc + (b.toNat - 48)
    · have hule_f :
          (b.setWidth 32 - 48#32).ule (b.setWidth 32 - 48#32 + BitVec.ofNat 32 (10 * acc)) = false := by
        simp only [BitVec.ule, BitVec.toNat_add, BitVec.toNat_ofNat, hb_sub,
          Nat.mod_eq_of_lt hm10_lt]
        exact decide_eq_false (by omega)
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x524#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none :=
        K.parse_none (parseUnsigned_none_of_overflow (pref := pref ++ [b]) (rem := rest)
          (acc := 10 * acc + (b.toNat - 48))
          (by simp [hds]) (by simp [List.foldl_append, hpref_val]) hover)
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_keygen_51c_placed (w3 := w3) K
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
          (by kg_simp) hparse_none)
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw
        w1 bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)
    · have hover_lt : 10 * acc + (b.toNat - 48) < 2 ^ 32 := by omega
      have hsum32 : (b.setWidth 32 - 48#32) + BitVec.ofNat 32 (10 * acc) =
          BitVec.ofNat 32 (10 * acc + (b.toNat - 48)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hb_sub,
          Nat.mod_eq_of_lt hm10_lt, Nat.mod_eq_of_lt hover_lt]
        have : (b.toNat - 48 + 10 * acc) < 2 ^ 32 := by omega
        rw [Nat.mod_eq_of_lt this]; omega
      have hule_t : (b.setWidth 32 - 48#32).ule (BitVec.ofNat 32 (10 * acc + (b.toNat - 48))) = true := by
        simp only [BitVec.ule, BitVec.toNat_ofNat, hb_sub, Nat.mod_eq_of_lt hover_lt]
        exact decide_eq_true (by omega)
      have hlen_sub : BitVec.ofNat 64 (b :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
        simp only [List.length_cons] at hlen_le
        have hr1 : rest.length + 1 < 2 ^ 64 := by omega
        have hr0 : rest.length < 2 ^ 64 := by omega
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, List.length_cons,
          Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr0]
        omega
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x4f0#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      have hrest' : ((remPtr + 1#64) ↦ᵣ rest) ∗ ((remPtr ↦₈ᵣ b) ∗ RestP3) = cStrAtRO p3 bs3 := by
        rw [← hrest, ProofLib.pointsToBytesRO_cons]; sep_ac_rfl
      have hdig_pref' : ∀ x ∈ pref ++ [b], isDigit x = true := by
        intro x hx; rcases List.mem_append.mp hx with hp | hb
        · exact hpref_dig x hp
        · rw [List.mem_singleton.mp hb]; exact hdig_b
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (ih _
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [List.length_cons] at hlen_le; omega)
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
          (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx8])
          (by simp only [arm64_norm, hx10, hlen_sub])
          (by simp only [arm64_norm, hx12]) hover_lt
          (by kg_simp)
          (by simp [hds]) hdig_pref' (by simp [List.foldl_append, hpref_val]) hrest')
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw
        w1 bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      exact Entails.of_eq (by sep_ac_rfl)
  · have hdig_f : isDigit b = false := Bool.eq_false_iff.mpr hdig_b
    have hhi_t := digit_hi_true hdig_b
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
    wp_steps
    apply SepWP.done (by kg_simp) (by kg_simp)
    intro hinv1
    have hmem_b : b ∈ stripPlus bs3 := by rw [hds]; simp
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_keygen_530_fail_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp, hinv1,
         by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
        (by kg_simp) (K.parse_none (parseUnsigned_none_of_nonDigit hmem_b hdig_f)))
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
      bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    rw [← hrest, ProofLib.pointsToBytesRO_cons]; exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 400000 in
theorem step_keygen_loop_4e8_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hne_ds : stripPlus bs3 ≠ []) :
    ∀ (rem : List (BitVec 8)) (s : State) (remPtr : BitVec 64) (pref : List (BitVec 8))
      (acc : Nat) (RestP3 : SepProp),
      InMainPlaced CodeOk s0 s 0x4f0 → KeygenRegs s0 s buf vcap vptr →
      rem.length ≤ 16384 →
      s.readReg64 (.gpr 22#5) = ptr →
      s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length →
      s.readReg64 (.gpr 1#5) = cap →
      s.readReg64 (.gpr 8#5) = remPtr →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 rem.length →
      s.readReg64 (.gpr 12#5) = 10#64 →
      acc < 2 ^ 32 →
      (s.readReg64 (.gpr 9#5)).setWidth 32 = BitVec.ofNat 32 acc →
      stripPlus bs3 = pref ++ rem →
      (∀ b ∈ pref, isDigit b = true) →
      pref.foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = acc →
      (remPtr ↦ᵣ rem) ∗ RestP3 = cStrAtRO p3 bs3 →
      KeygenGoalPlaced K s w3 ((remPtr ↦ᵣ rem) ∗ RestP3)
  | [], s, remPtr, pref, acc, RestP3, hs, kr, _, hx22, hx15, hx1, _, hx10, _, hacc_lt, hx9,
      hds, hpref_dig, hpref_val, hrest => by
    dsimp only [KeygenGoalPlaced]
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x52c#64) hinv
    wp_steps
    apply SepWP.done (by kg_simp) (by kg_simp)
    intro hinv1
    have hval' : (stripPlus bs3).foldl (fun a b => 10 * a + (b.toNat - 48)) 0 = acc := by
      rw [hds, List.append_nil]; exact hpref_val
    have hdig' : ∀ b ∈ stripPlus bs3, isDigit b = true := by
      rw [hds, List.append_nil]; exact hpref_dig
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_keygen_524_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp, hinv1,
         by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
        (by simp only [arm64_norm, hx1]) hacc_lt (by simp only [arm64_norm, hx9])
        hne_ds hdig' hval')
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
      bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    rw [← hrest]; exact Entails.of_eq (by sep_ac_rfl)
  | b :: rest, s, remPtr, pref, acc, RestP3, hs, kr, hlen_le, hx22, hx15, hx1, hx8, hx10, hx12,
      hacc_lt, hx9, hds, hpref_dig, hpref_val, hrest => by
    by_cases hm10 : 2 ^ 32 ≤ 10 * acc
    · dsimp only [KeygenGoalPlaced]
      have hlt64 : acc < 2 ^ 64 := by omega
      have h10_64 : 10 * acc < 2 ^ 64 := by omega
      have hlen_ne0 : (BitVec.ofNat 64 (b :: rest).length == 0#64) = false := by
        apply beq_false_of_ne; intro h
        have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hlen_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      have humull : (BitVec.ofNat 32 acc).setWidth 64 * 10#64 = BitVec.ofNat 64 (10 * acc) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hacc_lt, Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt h10_64,
          Nat.mod_eq_of_lt (Nat.mul_comm 10 acc ▸ h10_64), Nat.mul_comm]
      have htst_nz : (BitVec.ofNat 64 (10 * acc) &&& (-4294967296#64) == 0#64) = false := by
        apply beq_false_of_ne; intro h
        have hdiv_pos : 0 < (10 * acc) / 2 ^ 32 := Nat.div_pos hm10 (by decide)
        have hsh := congrArg (fun x : BitVec 64 => (x >>> 32).toNat) h
        rw [tst_hi32_shift] at hsh
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
          Nat.mod_eq_of_lt h10_64] at hsh
        omega
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
      rw [mPcPlaced_eq] at hpc
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xfc4#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_keygen_f90_placed (w3 := w3) K
          ⟨by rw [mPcPlaced_eq]; kg_simp,
           by kg_simp, by kg_simp, by kg_simp, hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
           by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
           by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
          (by simp only [arm64_norm, hx8]) hrest
          (K.parse_none (parseUnsigned_none_of_mul10_overflow hds hpref_val.symm hm10)))
      conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw
        w1 bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
      exact Entails.refl _
    · exact step_keygen_loop_no_m10_placed K hs kr hlen_le hx22 hx15 hx1 hx8 hx10 hx12
        hacc_lt (by omega) hx9 hds hpref_dig hpref_val hrest
        (fun s1 => step_keygen_loop_4e8_placed K hne_ds rest s1 (remPtr + 1#64)
          (pref ++ [b]) (10 * acc + (b.toNat - 48)) ((remPtr ↦₈ᵣ b) ∗ RestP3))

theorem step_keygen_4e0_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 dsPtr : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV} {RestP3 : SepProp}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x4e8) (kr : KeygenRegs s0 s buf vcap vptr)
    (hne_ds : stripPlus bs3 ≠ []) (hlen_le : (stripPlus bs3).length ≤ 16384)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx8 : s.readReg64 (.gpr 8#5) = dsPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (stripPlus bs3).length)
    (hrest : (dsPtr ↦ᵣ stripPlus bs3) ∗ RestP3 = cStrAtRO p3 bs3) :
    KeygenGoalPlaced K s w3 ((dsPtr ↦ᵣ stripPlus bs3) ∗ RestP3) := by
  dsimp only [KeygenGoalPlaced]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x4f0#64) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_keygen_loop_4e8_placed (w3 := w3) K hne_ds (stripPlus bs3) _ dsPtr [] 0 RestP3
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
       by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
       by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
      hlen_le
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
      (by simp only [arm64_norm, hx1]) (by simp only [arm64_norm, hx8])
      (by simp only [arm64_norm, hx10]) (by simp only [arm64_norm]) (by decide)
      (by simp only [arm64_norm]) rfl (fun _ h => nomatch h) rfl hrest)
  conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw w1
    bs1 bs2 bs3 me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
  exact Entails.refl _

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenLoopPlacedBudget
