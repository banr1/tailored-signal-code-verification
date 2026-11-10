/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `keygen` Dispatch Arm (`M+0x1cc .. M+0x23c`, Block `617`)

Verifies `main`'s 3-argument `"keygen"` match, `signal_session::address` call, and `M+0x218` entry
into the `u32` decimal parser with read-only `argvAtROP` and `RustCliAllocBudget M` under
`KeygenBranchEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced CallV CallW InMainPlaced LsCodeInv addrParse argsBuf
   callCellsPlaced callHeap locals mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainSaved
   parseArgs sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (KeygenRegs argsBufTail argsBuf_three_cons argsBuf_three_eq
   cells4_to_memRegion_32 cliInputsOk_elem cmn1_false fsp_align_of_spAligned
   le48_keygen_iff locals_merge_memRegion m2LocalsRest main_call_keepsFs_placed
   parseArgs_three_bad_cmd parseUnsigned_nil parseUnsigned_singleton_minus
   parseUnsigned_singleton_plus perm_parseFail_pre protocolAddressAt_to_words pure_intro_entails
   stackAt_split_ge stripPlus utf8_init_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (MainCalleesROBlk617 addressSpecRO address_ro_keepsFs_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (ExitKPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
  (bytes6_eq_pointsTo32_16RO cStrAtRO_split)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenConvPlacedBudget
  (KeygenCtxPlaced KeygenGoalPlaced keygenBase keygenBase_congr_vm step_keygen_52c_placed
   step_keygen_530_fail_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenEntryPlacedBudget
  (step_keygen_394_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
  (step_parseFail_af8_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim st s' = A.pool lim st s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

/-- Exact deterministic `AllocEvent` list emitted on the `M+0x1cc` `"keygen"` dispatch arm prior to
the tail `vptr` deallocation (`addressEvents uuidParse bs2` when `bs1 = utf8 "keygen"`, else `[]`). -/
def keygenBranchEvents (uuidParse : UuidParser) (bs1 bs2 : List (BitVec 8)) :
    List AllocEvent :=
  if bs1 = utf8 "keygen" then addressEvents uuidParse bs2 else []

/-- Exact deterministic `AllocEvent` envelope for the `M+0x1cc` `"keygen"` dispatch arm prior to
the tail `vptr` deallocation. -/
def KeygenBranchEnv (uuidParse : UuidParser) (bs1 bs2 : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  evs = keygenBranchEvents uuidParse bs1 bs2

/-! ## 1. `M+0x218` Entry Into `u32` Parser -/

set_option maxHeartbeats 400000 in
theorem step_keygen_218_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 w3 : BitVec 64}
    {bs1 bs2 bs3 : List (BitVec 8)} {me : AddrV}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (K : KeygenCtxPlaced CodeOk H A lim st uuidParse i s0 stk hookStack resStack
      buf vcap vptr p0 p1 p2 p3 cap ptr devw w1 bs1 bs2 bs3 me Statics Q Qp oom)
    (hs : InMainPlaced CodeOk s0 s 0x218) (kr : KeygenRegs s0 s buf vcap vptr)
    (hbs3_le : bs3.length ≤ 16384)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr)
    (hx15 : s.readReg64 (.gpr 15#5) = BitVec.ofNat 64 me.name.length)
    (hx1 : s.readReg64 (.gpr 1#5) = cap)
    (hx25 : s.readReg64 (.gpr 25#5) = p3)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length) :
    KeygenGoalPlaced K s w3 (cStrAtRO p3 bs3) := by
  dsimp only [KeygenGoalPlaced]
  rcases bs3 with _ | ⟨b0, tail0⟩
  · obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x534#64) hinv
    wp_steps
    apply SepWP.done (by kg_simp) (by kg_simp)
    intro hinv1
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_keygen_52c_placed (w3 := w3) K
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp,
         hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
        ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
         by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
         by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
        (K.parse_none (parseUnsigned_nil _)))
    conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr devw
      w1 bs1 bs2 _ me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])]
    exact Entails.refl _
  · rcases tail0 with _ | ⟨b1, tail1⟩
    · simp only [List.length_singleton] at hx26
      rw [cStrAtRO_split p3 [b0], ProofLib.pointsToBytesRO_cons, sepConj_assoc, sepConj_assoc]
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
      rw [mPcPlaced_eq] at hpc
      rw [mProgPlaced_eq]
      by_cases hp : b0 = 43#8
      · subst hp
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
        wp_steps
        apply SepWP.done (by kg_simp) (by kg_simp)
        intro hinv1
        rw [← mProgPlaced_eq]
        refine SepWPp.weaken_pre ?_
          (step_keygen_530_fail_placed (w3 := w3) K
            ⟨by rw [mPcPlaced_eq]; kg_simp,
             by kg_simp, by kg_simp, by kg_simp,
             hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
            ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
             by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
             by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
            (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
            (by kg_simp) (K.parse_none (parseUnsigned_singleton_plus _)))
        conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr
          devw w1 bs1 bs2 _ me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
        rw [cStrAtRO_split p3 [43#8], ProofLib.pointsToBytesRO_cons]
        exact Entails.of_eq (by sep_ac_rfl)
      · have hp32 : (b0.setWidth 32 == 43#32) = false := by apply beq_false_of_ne; bv_omega
        have hp32_ne : (b0.zeroExtend 32 != 43#32) = true := by simp only [bne, hp32]; rfl
        by_cases hm : b0 = 45#8
        · subst hm
          apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x538#64) hinv
          wp_steps
          apply SepWP.done (by kg_simp) (by kg_simp)
          intro hinv1
          rw [← mProgPlaced_eq]
          refine SepWPp.weaken_pre ?_
            (step_keygen_530_fail_placed (w3 := w3) K
              ⟨by rw [mPcPlaced_eq]; kg_simp,
               by kg_simp, by kg_simp, by kg_simp,
               hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
              ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
               by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
               by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
              (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx1])
              (by kg_simp) (K.parse_none (parseUnsigned_singleton_minus _)))
          conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr
            devw w1 bs1 bs2 _ me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (fun _ => by simp only [arm64_norm])]
          rw [cStrAtRO_split p3 [45#8], ProofLib.pointsToBytesRO_cons]
          exact Entails.of_eq (by sep_ac_rfl)
        · have hm32 : (b0.setWidth 32 == 45#32) = false := by apply beq_false_of_ne; bv_omega
          have hm32_ne : (b0.zeroExtend 32 != 45#32) = true := by simp only [bne, hm32]; rfl
          apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x39c#64) hinv
          wp_steps
          apply SepWP.done (by kg_simp) (by kg_simp)
          intro hinv1
          rw [← mProgPlaced_eq]
          have hds1 : stripPlus [b0] = [b0] := by simp [stripPlus, hp]
          refine SepWPp.weaken_pre ?_
            (step_keygen_394_placed (w3 := w3) (dsPtr := p3) (b0 := b0) (d0 := b0) (tail := [])
              (RestP3 := (p3 + BitVec.ofNat 64 ([b0] : List (BitVec 8)).length) ↦₈ᵣ 0#8) K
              ⟨by rw [mPcPlaced_eq]; kg_simp,
               by kg_simp, by kg_simp, by kg_simp, hinv1,
               by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
              ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
               by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
               by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
              hbs3_le (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
              (by simp only [arm64_norm, hx1]) (by kg_simp)
              (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]; rfl)
              (by simp [hp]) (by simp [hds1, hp]) hds1 (cStrAtRO_split p3 [b0]).symm)
          conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr
            devw w1 bs1 bs2 _ me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (fun _ => by simp only [arm64_norm])]
          rw [ProofLib.pointsToBytesRO_cons]
          exact Entails.of_eq (by sep_ac_rfl)
    · have hne0 : (BitVec.ofNat 64 (b0 :: b1 :: tail1).length == 0#64) = false := by
        apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hbs3_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      have hne0' : (BitVec.ofNat 64 (b0 :: b1 :: tail1).length != 0#64) = true := by
        simp only [bne, hne0]; rfl
      have hne1 : (BitVec.ofNat 64 (b0 :: b1 :: tail1).length == 1#64) = false := by
        apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
        simp only [List.length_cons] at hbs3_le
        simp only [BitVec.toNat_ofNat, List.length_cons] at htn; omega
      have hne1' : (BitVec.ofNat 64 (b0 :: b1 :: tail1).length != 1#64) = true := by
        simp only [bne, hne1]; rfl
      rw [cStrAtRO_split p3 (b0 :: b1 :: tail1), ProofLib.pointsToBytesRO_cons, sepConj_assoc,
        sepConj_assoc]
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
      rw [mPcPlaced_eq] at hpc
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x39c#64) hinv
      wp_steps
      apply SepWP.done (by kg_simp) (by kg_simp)
      intro hinv1
      rw [← mProgPlaced_eq]
      have hin1 : InMainPlaced CodeOk s0 _ 0x39c :=
        ⟨by rw [mPcPlaced_eq]; kg_simp,
         by kg_simp, by kg_simp, by kg_simp,
         hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
      by_cases hp : b0 = 43#8
      · subst hp
        have hrest_plus : ((p3 + 1#64) ↦ᵣ (b1 :: tail1)) ∗
            ((p3 ↦₈ᵣ 43#8) ∗ ((p3 + BitVec.ofNat 64 (43#8 :: b1 :: tail1).length) ↦₈ᵣ 0#8)) =
            cStrAtRO p3 (43#8 :: b1 :: tail1) := by
          rw [cStrAtRO_split p3 (43#8 :: b1 :: tail1)]
          (conv_rhs => rw [ProofLib.pointsToBytesRO_cons]); sep_ac_rfl
        refine SepWPp.weaken_pre ?_
          (step_keygen_394_placed (w3 := w3) (dsPtr := p3 + 1#64) (b0 := 43#8) (d0 := b1)
            (tail := tail1)
            (RestP3 := (p3 ↦₈ᵣ 43#8) ∗
              ((p3 + BitVec.ofNat 64 (43#8 :: b1 :: tail1).length) ↦₈ᵣ 0#8))
            K hin1
            ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
             by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
             by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
            hbs3_le
            (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
            (by simp only [arm64_norm, hx1]) (by kg_simp)
            (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
            rfl (by simp [stripPlus]) rfl hrest_plus)
        conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr
          devw w1 bs1 bs2 _ me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
        exact Entails.of_eq (by sep_ac_rfl)
      · refine SepWPp.weaken_pre ?_
          (step_keygen_394_placed (w3 := w3) (dsPtr := p3) (b0 := b0) (d0 := b0)
            (tail := b1 :: tail1)
            (RestP3 := (p3 + BitVec.ofNat 64 (b0 :: b1 :: tail1).length) ↦₈ᵣ 0#8)
            K hin1
            ⟨by simp only [arm64_norm, kr.x19], by simp only [arm64_norm, kr.x20],
             by simp only [arm64_norm, kr.x23], by simp only [arm64_norm, kr.x24],
             by simp only [arm64_norm, kr.trace], by simp only [arm64_norm, kr.fs]⟩
            hbs3_le
            (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx15])
            (by simp only [arm64_norm, hx1]) (by kg_simp)
            (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
            (by simp [hp]) (by simp [stripPlus, hp]) (by simp [stripPlus, hp])
            (cStrAtRO_split p3 (b0 :: b1 :: tail1)).symm)
        conv => rhs; rw [keygenBase_congr_vm A lim st s0 s stk buf vcap vptr p0 p1 p2 p3 cap ptr
          devw w1 bs1 bs2 _ me Statics (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm])]
        (conv_rhs => rw [ProofLib.pointsToBytesRO_cons])
        exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. `"keygen"` Command Match & `address` Call (`M+0x1cc .. M+0x214`) -/

set_option maxHeartbeats 800000 in
theorem step_keygen_cmd_1cc_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 : BitVec 8} {bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hlen : i.argv.length = 3)
    (hps : ([(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] :
      List (BitVec 64 × List (BitVec 8))).map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2))
    (hs : InMainPlaced CodeOk s0 s 0x1cc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") ::
              [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2) st)) s' ∗
          Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") ::
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        (((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
          memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom := by
  dsimp only
  have ⟨_, hbs3_le, _⟩ :=
    cliInputsOk_elem hok hps
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  dsimp only at hbs3_le
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  let wlo : BitVec 32 := b3 ++ (b2 ++ (b1 ++ b0))
  let whi : BitVec 16 := b5 ++ b4
  have hwlo : (b3 ++ b2 ++ b1 ++ b0 : BitVec 32) = wlo := by dsimp only [wlo]; bv_bits
  have hwhi : (b5 ++ b4 : BitVec 16) = whi := rfl
  rw [argsBuf_three_eq A.repAlloc (p1, [b0, b1, b2, b3, b4, b5]) (p2, bs2) (p3, bs3) hvcap]
  by_cases hkey : wlo = 0x6779656b#32 ∧ whi = 0x6e65#16
  · have haddr := address_ro_keepsFs_placed_ok hc
    have hcmd : [b0, b1, b2, b3, b4, b5] = utf8 "keygen" :=
      (le48_keygen_iff b0 b1 b2 b3 b4 b5).mp hkey
    have hfit_addr_ev : FitsEvents M lim st (addressEvents uuidParse bs2) := by
      simpa only [keygenBranchEvents, hcmd, ↓reduceIte] using hfit
    dsimp only [argvAtROP]
    rw [cStrAtRO_split p1 [b0, b1, b2, b3, b4, b5], bytes6_eq_pointsTo32_16RO p1 b0 b1 b2 b3 b4 b5,
      hwlo, hwhi, hkey.1, hkey.2, cStrAtRO_split p2 bs2,
      stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hres_le hsub64]
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    have hfsp_align0 := fsp_align_of_spAligned hsp0
    generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
    have hfit_addr : FitsEnv M lim st (AddressEnv uuidParse ⟨fsp + 0x1b8#64, p2, bs2⟩) :=
      fun _ hevs => hevs ▸ hfit_addr_ev
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 580) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (⟨fsp + 0x1b8#64, p2, bs2⟩, st))
      (k_ret := 0x200)
      (F := ((vptr ↦₆₄ p1) ∗
          ((vptr + 8#64) ↦₆₄
            BitVec.ofNat 64 ([b0, b1, b2, b3, b4, b5] : List (BitVec 8)).length) ∗
          ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
          ((vptr + 32#64) ↦₆₄ p3) ∗ ((vptr + 40#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
          argsBufTail A.repAlloc vcap vptr
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
        ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗
        ((p1 ↦₃₂ᵣ 0x6779656b#32) ∗ ((p1 + 4#64) ↦₁₆ᵣ 0x6e65#16) ∗
          ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3, b4, b5] : List (BitVec 8)).length) ↦₈ᵣ 0#8)) ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗
        ((p2 + BitVec.ofNat 64 bs2.length) ↦₈ᵣ 0#8) ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        m2LocalsRest fsp ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - resStack) ∗ Statics)
      haddr hinv1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
      (by simp only [arm64_norm, *])
      (hP := ?_)
      (hnext := ?_)
    · dsimp only [addressSpecRO]
      conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm])]
      refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp]; sep_ac_rfl))
        (sepConj_mono_left (pure_intro_entails
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], hfit_addr⟩ (Entails.refl _)))
    intro sm hin hcs hfs_m
    dsimp only [addressSpecRO]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr_m, _, hevs⟩ => ?_
    dsimp only [AddressEnv] at hevs
    subst hevs
    let st1 := M.stepEvents (addressEvents uuidParse bs2) st
    have hx19_m : sm.readReg64 (.gpr 19#5) = buf := hcs.1.trans (by simp only [arm64_norm, *])
    have hx20_m : sm.readReg64 (.gpr 20#5) = vptr := hcs.2.1.trans (by simp only [arm64_norm, *])
    have hx23_m : sm.readReg64 (.gpr 23#5) = vcap :=
      hcs.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx24_m : sm.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
      hcs.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx25_m : sm.readReg64 (.gpr 25#5) = p3 :=
      hcs.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx26_m : sm.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length :=
      hcs.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have htr_m' : sm.trace = s0.trace :=
      htr_m.trans ((by simp only [arm64_norm, *] : _ = s.trace).trans htr)
    have hfs_m' : sm.fs = s0.fs :=
      hfs_m.trans ((by simp only [arm64_norm, *] : _ = s.fs).trans hfs)
    obtain ⟨hpc_m, hrun_m, hsp_m, hfp_m, hinv_m, hvregs_m, _⟩ := hin
    rw [hfsp] at hsp_m
    rw [mPcPlaced_eq] at hpc_m
    simp only [arm64_norm, hsp]
    cases hparse2 : addrParse uuidParse bs2 with
    | none =>
      dsimp only
      have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
        rw [← hps]; simp only [List.map_cons, List.map_nil, parseArgs, hcmd, ↓reduceIte, hparse2]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv_m
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      have hin2 : InMainPlaced CodeOk s0 _ 0xb54 := {
        pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
        run := by simp only [arm64_norm, *]
        sp := by simp only [arm64_norm, *]
        fp := by simp only [arm64_norm, *]
        inv := hinv2
        vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
        spAligned := hsp0 }
      have h32 : ((fsp + 440#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (fsp + 448#64) 24 ⊢ memRegion (fsp + 0x1b8#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          (Entails.trans
            (sepConj_mono_left
              (pointsTo64_entails_memRegion (fsp + 0x1b8#64) 0xffffffffffffffff#64))
            (Entails.of_eq (ProofLib.memRegion_split (fsp + 0x1b8#64) 8 24 (by decide)).symm))
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_parseFail_af8_pool_placed (hookStack := hookStack) (resStack := resStack)
          (st := st1) (buf := buf) (vcap := vcap) (vptr := vptr)
          (ps := [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)])
          (Rest := (p2 ↦ᵣ bs2) ∗
            ((s0.readReg64 (.gpr 1#5)) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
            ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ᵣ p1) ∗
            ((p1 ↦₃₂ᵣ 0x6779656b#32) ∗ ((p1 + 4#64) ↦₁₆ᵣ 0x6e65#16) ∗
              ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3, b4, b5] : List (BitVec 8)).length) ↦₈ᵣ 0#8)) ∗
            ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ᵣ p2) ∗
            ((p2 + BitVec.ofNat 64 bs2.length) ↦₈ᵣ 0#8) ∗
            ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
            ((s0.readReg64 (.gpr 1#5) + 32#64) ↦₆₄ᵣ 0#64) ∗ Statics)
          hc.allocFs hstk hstk64 hok hne hparse_none hin2
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
          hvcap (by simp only [arm64_norm, htr_m']) (by simp only [arm64_norm, hfs_m']) hexit)
      conv => arg 2; rw [pool_congr_vm A lim st1 sm (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm])]
      rw [hfsp, stackAt_split_ge fsp hres_le hsub64]
      have hloc := Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h32))))
        (locals_merge_memRegion fsp w3 w4 w1)
      rw [argsBuf_three_cons A.repAlloc (p1, [b0, b1, b2, b3, b4, b5]) (p2, bs2) (p3, bs3) hvcap]
      let LOC_n : SepProp :=
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
          (((fsp + 440#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 448#64) 24) ∗
          m2LocalsRest fsp
      let REST_n : SepProp :=
        (p2 ↦ᵣ bs2) ∗
          ((s0.readReg64 (.gpr 1#5)) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
          ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ᵣ p1) ∗
          ((p1 ↦₃₂ᵣ 0x6779656b#32) ∗ ((p1 + 4#64) ↦₁₆ᵣ 0x6e65#16) ∗
            ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3, b4, b5] : List (BitVec 8)).length) ↦₈ᵣ 0#8)) ∗
          ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ᵣ p2) ∗
          ((p2 + BitVec.ofNat 64 bs2.length) ↦₈ᵣ 0#8) ∗
          ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
          ((s0.readReg64 (.gpr 1#5) + 32#64) ↦₆₄ᵣ 0#64) ∗ Statics
      refine Entails.trans
        (Q := LOC_n ∗ (argsBuf A.repAlloc vcap vptr
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
            stackAt fsp resStack) ∗
          A.pool lim st1 sm ∗ REST_n))
        (Entails.of_eq (by dsimp only [LOC_n, REST_n, st1]; sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hloc) (perm_parseFail_pre _ _ _ _ _ _ _))
    | some me =>
      dsimp only
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
        sepExists_sepConj_right]
      refine SepWPp.exists_elim fun g => ?_
      have hpure_g : ∀ (A0 B0 C0 P0 R1 R2 : SepProp),
          A0 ∗ B0 ∗ C0 ∗ (P0 ∗ R1) ∗ R2 = P0 ∗ (R1 ∗ A0 ∗ B0 ∗ C0 ∗ R2) :=
        fun _ _ _ _ _ _ => by sep_ac_rfl
      rw [hpure_g]
      refine SepWPp.pure_elim fun ⟨hgname, _, hgdev⟩ => ?_
      refine SepWPp.weaken_pre
        (sepConj_mono_left (protocolAddressAt_to_words A.repAlloc (fsp + 0x1b8#64) hgname hgdev))
        ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun devw => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hcap_ne => ?_
      have hcmn : (g.name.cap + 1#64 == 0#64) = false := cmn1_false hcap_ne
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x218#64) hinv_m
      wp_steps_sync_pool ((blkPl_617).base + 0x218#64)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      rw [← mProgPlaced_eq]
      have hst1_eq : st1 =
          M.stepEvents (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2) st := by
        simp only [st1, keygenBranchEvents, hcmd, ↓reduceIte]
      let K : KeygenCtxPlaced CodeOk H A lim st1 uuidParse i s0 stk hookStack resStack
          buf vcap vptr p0 p1 p2 p3 g.name.cap g.name.ptr devw w1
          [b0, b1, b2, b3, b4, b5] bs2 bs3 me Statics Q Qp oom :=
        ⟨hc, hstk, hstk64, hok, hne, hlen, hps, hcmd, hparse2, hvcap, hexit,
         fun s' w c hp ha => by rw [hst1_eq]; exact hnext s' w c hp ha⟩
      refine SepWPp.weaken_pre ?_
        (step_keygen_218_placed (w3 := w3) K
          ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], hinv2,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
           by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m, hlen],
           by simp only [arm64_norm, htr_m'], by simp only [arm64_norm, hfs_m']⟩
          hbs3_le (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hx25_m])
          (by simp only [arm64_norm, hx26_m]))
      dsimp only [KeygenGoalPlaced, keygenBase, argvAtROP]
      rw [hfsp, stackAt_split_ge fsp hres_le hsub64, hlen,
        argsBuf_three_eq A.repAlloc (p1, [b0, b1, b2, b3, b4, b5]) (p2, bs2) (p3, bs3) hvcap,
        cStrAtRO_split p1 [b0, b1, b2, b3, b4, b5],
        bytes6_eq_pointsTo32_16RO p1 b0 b1 b2 b3 b4 b5,
        hwlo, hwhi, hkey.1, hkey.2, cStrAtRO_split p2 bs2]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hc4 : ((fsp + 0x1b8#64) ↦₆₄ g.name.cap) ∗ ((fsp + 0x1c0#64) ↦₆₄ g.name.ptr) ∗
          ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 me.name.length) ∗
          ((fsp + 0x1d0#64) ↦₆₄ devw) ⊢
          memRegion (fsp + 0x1b8#64) 32 :=
        by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          cells4_to_memRegion_32 (fsp + 0x1b8#64) g.name.cap g.name.ptr
            (BitVec.ofNat 64 me.name.length) devw
      have hp_s : ∀ (PL C0 C1 C2 C3 R0 : SepProp),
          PL ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ R0 ⊢ (C0 ∗ C1 ∗ C2 ∗ C3) ∗ (PL ∗ R0) :=
        fun _ _ _ _ _ _ => Entails.of_eq (by sep_ac_rfl)
      dsimp only [st1]
      exact Entails.trans (hp_s _ _ _ _ _ _)
        (Entails.trans (sepConj_mono_left hc4) (Entails.of_eq (by sep_ac_rfl)))
  · have hnkey : [b0, b1, b2, b3, b4, b5] ≠ utf8 "keygen" :=
      fun hc6 => hkey ((le48_keygen_iff b0 b1 b2 b3 b4 b5).mpr hc6)
    have hninit : [b0, b1, b2, b3, b4, b5] ≠ utf8 "init" := fun hc4 => by
      have hl := congrArg List.length hc4; rw [utf8_init_eq] at hl; simp at hl
    have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
      rw [← hps]; exact parseArgs_three_bad_cmd uuidParse _ bs2 bs3 hnkey hninit
    have hkey_cases : wlo ≠ 0x6779656b#32 ∨ whi ≠ 0x6e65#16 :=
      Decidable.not_and_iff_or_not.mp hkey
    dsimp only [argvAtROP]
    rw [cStrAtRO_split p1 [b0, b1, b2, b3, b4, b5], bytes6_eq_pointsTo32_16RO p1 b0 b1 b2 b3 b4 b5,
      hwlo, hwhi]
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
    wp_steps
    wp_step
    wp_steps
    apply SepWP.done
      (by rcases hkey_cases with hw1 | hw2 <;>
            simp only [arm64_norm, PState.ofBits4, ConditionHolds, *] <;>
            split_ifs at * <;> simp_all <;> bv_omega)
      (by simp only [arm64_norm, *])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xb54 := {
      pc := by
        rw [mPcPlaced_eq]
        rcases hkey_cases with hw1 | hw2 <;>
          simp only [arm64_norm, PState.ofBits4, ConditionHolds, *] <;>
          split_ifs at * <;> simp_all <;> bv_omega
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv1
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_parseFail_af8_pool_placed (hookStack := hookStack) (resStack := resStack)
        (st := st) (buf := buf) (vcap := vcap) (vptr := vptr)
        (ps := [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)])
        (Rest := ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
          ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ (p1 ↦₃₂ᵣ wlo) ∗ ((p1 + 4#64) ↦₁₆ᵣ whi) ∗
          ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3, b4, b5] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
          ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
          ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
          ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics)
        hc.allocFs hstk hstk64 hok hne hparse_none hin1
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs]) hexit)
    conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    rw [hfsp]
    let LOC : SepProp :=
      ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp
    let REST_b : SepProp :=
      ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
      ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ (p1 ↦₃₂ᵣ wlo) ∗ ((p1 + 4#64) ↦₁₆ᵣ whi) ∗
      ((p1 + BitVec.ofNat 64 ([b0, b1, b2, b3, b4, b5] : List (BitVec 8)).length) ↦₈ᵣ 0#8) ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗ cStrAtRO p3 bs3 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗ Statics
    refine Entails.trans
      (Q := LOC ∗ (argsBuf A.repAlloc vcap vptr
          [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ REST_b))
      (Entails.of_eq (by
        dsimp only [LOC, REST_b]
        rw [argsBuf_three_eq A.repAlloc (p1, [b0, b1, b2, b3, b4, b5]) (p2, bs2) (p3, bs3) hvcap]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
        (perm_parseFail_pre _ _ _ _ _ _ _))

theorem step_keygen_cmd_1cc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 : BitVec 8} {bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hlen : i.argv.length = 3)
    (hps : ([(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] :
      List (BitVec 64 × List (BitVec 8))).map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2))
    (hs : InMainPlaced CodeOk s0 s 0x1cc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") ::
              [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2) st)) s' ∗
          Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") ::
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        (((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
          memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_keygen_cmd_1cc_pool_placed hc hstk hstk64 hok hne hlen hps hfit hs hx19 hx20 hx23 hx24
    hvcap htr hfs (exitKPoolPlaced_of_exitKPlaced hexit) hnext

theorem step_keygen_cmd_1cc_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 : BitVec 8} {bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hlen : i.argv.length = 3)
    (hps : ([(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] :
      List (BitVec 64 × List (BitVec 8))).map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEvents M lim st (keygenBranchEvents uuidParse [b0, b1, b2, b3, b4, b5] bs2))
    (hs : InMainPlaced CodeOk s0 s 0x1cc)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") ::
              [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc vcap vptr [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf
          [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") ::
            [(p1, [b0, b1, b2, b3, b4, b5]), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        (((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
          memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_keygen_cmd_1cc_placed hc hstk hstk64 hok hne hlen hps hfit hs hx19 hx20 hx23 hx24 hvcap
    htr hfs hexit fun s' w c hp ha => hnext s' _ w c hp ha

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlacedBudget
