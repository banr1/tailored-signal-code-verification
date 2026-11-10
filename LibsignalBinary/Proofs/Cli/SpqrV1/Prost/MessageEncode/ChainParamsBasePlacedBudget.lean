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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `encode<ChainParams> [local#3]` Step Lemmas (Block `453`)

Defines budget-threaded placed contract propositions (`EncodeChainParams1PlacedOk*`,
`EncodeChainParams1ExactPlacedOk`) and proves `VmPreserved`-threaded basic-block step lemmas on CLI
Block `453` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (encodeChainParamsExactVmSpecOf encodeChainParamsSpec encodeChainParamsSpecX)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB)
open CryptoVerification.LibsignalTripleRatchet.Prost (StepInv StepInvPlaced sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Auth (vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.ProtoRepr (u32VarintFieldEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (bv_add_ofNat_comm bv_u32VarintField_nonzero
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced chainParams_encodeRaw_length msgEnc48SavedFrame
   msgEnc48VarintStackOf stackAt_msgEnc48_varint stackAt_msgEnc48_varint_recombine
   u32VarintFieldEncodedLen_of_beq_true)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPC_453 blkPl_453 lsProg_453)

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

/-! ## 1. Budget-Threaded Placed Contract Propositions (Block `453`) -/

def EncodeChainParams1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_453 H) (blkPl_453).base
    (withLsCodeLoaded lsmpl (encodeChainParamsSpec A lim))

def EncodeChainParams1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_453 H) (blkPl_453).base
    (withLsCodeLoaded lsmpl (encodeChainParamsSpecX A lim))

def EncodeChainParams1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeChainParams1PlacedOk A lim (Rust.withPanics ext)

def EncodeChainParams1PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeChainParams1PlacedOkX A lim (Rust.withPanics ext)

def EncodeChainParams1ExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_453 H) (blkPl_453).base
    (withLsCodeLoaded lsmpl (encodeChainParamsExactVmSpecOf resStack A))

/-! ## 2. Relocatable `VmPreserved`-Threaded Step Lemmas (Block `453`) -/

theorem step_chainParams_prologue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (H : String → Option (State → State))
    (v sp : BitVec 64) (tag : BitVec 32) (p : ChainParamsPB)
    {s0 s : State}
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hhs0 : s = s0)
    (hP : P = stackAt sp (msgEnc48VarintStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = (blkPl_453).base + 40#64 →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = (2#32 ||| (tag <<< 3)).zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_453 H) ret sm
        ((stackAt (sp - 48#64) (0x30 + resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_453 H) ret s P Q Qp oom := by
  subst hP hhs0
  dsimp only [State.readReg32, Reg.x0, Reg.x1, Reg.x2] at hw0 hw1 hw2
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_varint hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  dsimp only [lsProg_453]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 40#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ sv3
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; congr 1; bv_bits)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp))

theorem step_chainParams_len_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State}
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base + 44#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + (if p.maxOooKeys == 0#32 then 204#64 else 116#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_453 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_453 H) ret s P Q Qp oom := by
  have hraw := chainParams_encodeRaw_length p
  cases hmj : (p.maxJump == 0#32) <;> cases hmo : (p.maxOooKeys == 0#32)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmo]
    have hmj_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmj)
    have hmo_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmo)
    have hadd := bv_add_ofNat_comm (u32VarintFieldEncodedLen p.maxJump) (u32VarintFieldEncodedLen p.maxOooKeys)
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 116#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmo]
    have hmj_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmj)
    have hmo_z := u32VarintFieldEncodedLen_of_beq_true hmo
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 204#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmo_z, Nat.add_zero]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmo]
    have hmj_z := u32VarintFieldEncodedLen_of_beq_true hmj
    have hmo_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hmo)
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 116#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmj_z, Nat.zero_add]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmj]
    have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmo]
    have hmj_z := u32VarintFieldEncodedLen_of_beq_true hmj
    have hmo_z := u32VarintFieldEncodedLen_of_beq_true hmo
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 204#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [hraw, hmj_z, hmo_z]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp

theorem step_chainParams_push_maxJump_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State}
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + 256#64 →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = p.maxJump.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_453 H) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_453 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_453]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 256#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp))

theorem step_chainParams_push_maxOooKeys_epilogue_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State}
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + 184#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr →
      sm.readReg64 .x0 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x1 = v →
      CalleeSavedPreserved s0 sm →
      MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_453 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_453 H) ret s P Q Qp oom := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [msgEnc48SavedFrame]
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_453]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 184#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv1
    refine SepWPp.weaken_pre
      (by
        dsimp only [msgEnc48SavedFrame]
        rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close)
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩
        hvmp))

theorem step_chainParams_epilogue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (H : String → Option (State → State))
    (sp sv3 : BitVec 64)
    {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base + 264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      VmPreserved s sf →
      Q sf (stackAt sp (msgEnc48VarintStackOf resStack) ∗ F)) :
    SepWPp (lsProg_453 H) (s0.readReg64 .lr) s P Q Qp oom := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [msgEnc48SavedFrame]
  dsimp only [lsProg_453]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := s0.readReg64 .lr)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv1
    refine SepWPp.weaken_pre
      (sepConj_mono_left
        (stackAt_msgEnc48_varint_recombine hres sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)))
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by epochEncLen_cc_close) (hinv0.trans hinv1).1 hvmp)))

theorem step_chainParams_after_hdr_branch_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base + (if p.maxOooKeys == 0#32 then 208#64 else 120#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + (if p.maxJump == 0#32 then 124#64 else 212#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = p.maxJump.zeroExtend 64 → MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_453 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_453 H) ret s P Q Qp oom := by
  cases hmo : (p.maxOooKeys == 0#32) <;> cases hmj : (p.maxJump == 0#32)
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmj]
    simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 212#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmj]
    simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 124#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmj]
    simp only [hmo, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 212#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmj64 : (BitVec.zeroExtend 64 p.maxJump == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmj]
    simp only [hmo, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 124#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp

theorem step_chainParams_after_maxJump_branch_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (p : ChainParamsPB) (v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_453).base + (if p.maxJump == 0#32 then 124#64 else 260#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_453).base + (if p.maxOooKeys == 0#32 then 264#64 else 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_453 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_453 H) ret s P Q Qp oom := by
  cases hmj : (p.maxJump == 0#32) <;> cases hmo : (p.maxOooKeys == 0#32)
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmo]
    simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 128#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmo]
    simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 264#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hmo]
    simp only [hmj, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 128#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmo64 : (BitVec.zeroExtend 64 p.maxOooKeys == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hmo]
    simp only [hmj, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_453).base + 264#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    exact hnext _ (by simp only [↓reduceIte, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv)
      hvmp

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget
