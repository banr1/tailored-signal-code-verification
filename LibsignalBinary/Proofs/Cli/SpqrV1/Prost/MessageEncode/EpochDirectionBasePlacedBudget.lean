/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Basic-Block Step Lemmas for `encode<EpochDirection> [local#3]` (Block `457`)

Defines budget-threaded placed contract propositions (`EncodeEpochDirection1*PlacedOk*`) and proves
`VmPreserved`-threaded basic-block step lemmas on CLI Block `457` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (encodeEpochDirectionPinnedExactVmSpecOf encodeEpochDirectionPinnedSpec
   encodeEpochDirectionPinnedSpecX encodeEpochDirectionSpec encodeEpochDirectionSpecX)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType)
open CryptoVerification.LibsignalTripleRatchet.Prost (StepInv StepInvPlaced)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf sp_sub_64_aligned stackAt_authEncode vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.ProtoRepr
  (bytesFieldEncodedLen epochDirectionPBEncodedLen u32VarintFieldEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq bv_add_ofNat_comm bv_bytesField_nonempty bv_u32VarintField_nonzero
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (AuthEncodeCalleeSavedPlaced epochDirectionElemsAt epochDirectionSavedFrame)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_457 lsProg_457)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem zext64_trunc32_orr_1 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 1#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_trunc32_orr_100000001 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 0x100000001#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] private theorem zext64_orr_1_32 (w : BitVec 32) :
    BitVec.zeroExtend 64 (w ||| 1#32) = BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

private theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hpost⟩

private theorem sepWP_done_vm_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hvm : VmPreserved s0 s)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => VmPreserved s0 sm ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨hvm, hpost⟩

/-! ## 1. Budget-Threaded Placed Contract Propositions (Block `457`) -/

def EncodeEpochDirection1PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_457 H) (blkPl_457).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpec A lim))

def EncodeEpochDirection1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_457 H) (blkPl_457).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionSpec A lim))

def EncodeEpochDirection1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_457 H) (blkPl_457).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecX A lim))

def EncodeEpochDirection1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_457 H) (blkPl_457).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecX A lim))

def EncodeEpochDirection1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection1PinnedPlacedOk A lim (Rust.withPanics ext)

def EncodeEpochDirection1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection1PlacedOk A lim (Rust.withPanics ext)

def EncodeEpochDirection1PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection1PinnedPlacedOkX A lim (Rust.withPanics ext)

def EncodeEpochDirection1PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeEpochDirection1PlacedOkX A lim (Rust.withPanics ext)

def EncodeEpochDirection1PinnedExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_457 H) (blkPl_457).base
    (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedExactVmSpecOf resStack A))

/-! ## 2. Relocatable `VmPreserved`-Threaded Step Lemmas (Block `457`) -/

/-- Shared prologue (`+0..+40`) on Block `457`: saves the 64-byte frame, prepares
`x0 = (tag << 3) | 2`, `x1 = v`, `x19 = v`, `x21 = dirA`, and threads `VmPreserved s sm`. -/
theorem step_epochDir_prologue_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (H : String → Option (State → State))
    (tag : BitVec 32) (dirA v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_457).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = stackAt sp (authEncodeStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_457).base + 40#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64) →
      sm.readReg64 .x1 = v → sm.readReg64 .x19 = v → sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_457 H) ret sm
        ((stackAt (sp - 64#64) (0x30 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hx0_eq :
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (2#64 ||| BitVec.zeroExtend 64 (BitVec.truncate 32 (s.readReg64 (Reg.gpr 0#5)) <<< 3))) =
      (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64) := by
    change BitVec.zeroExtend 64 (BitVec.truncate 32
      (2#64 ||| BitVec.zeroExtend 64 (s.readReg32 .x0 <<< 3))) = _
    rw [hw0]; dsimp only [WireType.toU32]; bv_bits
  rw [stackAt_authEncode hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  dsimp only [lsProg_457]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 40#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionSavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Inline `EpochDirection::encoded_len` computation (`+44..+168` and `+452..+484`) on Block `457`,
threading `VmPreserved s sm`. -/
theorem step_epochDir_len_placed [LibsignalPlacement] (H : String → Option (State → State))
    (v dirA nextPtr prevPtr sp : BitVec 64) (d : EpochDirectionPB)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63)
    (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = dirA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_457).base + 168#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (epochDirectionPBEncodedLen d) → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_457 H) ret sm (epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F) Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  subst hP
  dsimp only [epochDirectionElemsAt]
  obtain ⟨hnext_beq, hnext_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  obtain ⟨hprev_beq, hprev_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hctr : (d.ctr == 0#32) <;> cases hn : d.next.isEmpty <;> cases hp : d.prev.isEmpty
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have hadd12 := bv_add_ofNat_comm (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next)
        (c := epochDirectionPBEncodedLen d) rfl hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hadd12 := bv_add_ofNat_comm (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    have htot_eq : epochDirectionPBEncodedLen d =
        u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr) (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have htot_eq : epochDirectionPBEncodedLen d = u32VarintFieldEncodedLen d.ctr := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : bytesFieldEncodedLen d.next + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := bytesFieldEncodedLen d.next) (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hn_val := bv_bytesField_nonempty hn
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have hp_val := bv_bytesField_nonempty hp
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.prev := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hn]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp
  · have htot_eq : epochDirectionPBEncodedLen d = 0 := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hn, hp]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 168#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) hvmp

/-- Shared `ctr` tag push (`+192..+220`) on Block `457`, threading `VmPreserved s sm`. -/
theorem step_epochDir_push_ctr_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr dirA sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 192#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_457).base + 220#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = d.ctr.zeroExtend 64 → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_457 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F) Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_457]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 220#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Shared `next` tag push (`+248..+276`) on Block `457`, threading `VmPreserved s sm`. -/
theorem step_epochDir_push_next_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr dirA nextPtr sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 248#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = nextPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_457).base + 276#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.next.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = nextPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_457 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F) Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_457]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 276#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Shared `prev` tag push (`+352..+380`) on Block `457`, threading `VmPreserved s sm`. -/
theorem step_epochDir_push_prev_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr prevPtr sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 352#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = prevPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_457).base + 380#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = prevPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_457 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x1a#8]) ∗ F) Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_457]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 380#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x1a#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Shared epilogue (`+432..+452`) on Block `457`, threading `VmPreserved s sf`. -/
theorem step_epochDir_epilogue_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (H : String → Option (State → State))
    (sp : BitVec 64) {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 432#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
        (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInv s0 sf → VmPreserved s sf →
      Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp (lsProg_457 H) (s0.readReg64 .lr) s P Q Qp oom := by
  subst hP
  dsimp only [epochDirectionSavedFrame]
  have hsp_aligned := sp_sub_64_aligned halign
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hinv0⟩
  apply sepWPp_of_sepWP_cs_placed_vm (mid := s0.readReg64 .lr)
  wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hvmp hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1).1 hvmp))
  rw [stackAt_authEncode hres sp]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp)
    (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x24)
        (Entails.sepExists_right (s0.readReg64 .x23)
          (Entails.sepExists_right (s0.readReg64 .x22)
            (Entails.sepExists_right (s0.readReg64 .x21)
              (Entails.sepExists_right (s0.readReg64 .x20)
                (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
