/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.ReprPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1 -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Shared Step Lemmas for `Authenticator::encode [local#3]` (Block `454`)

Defines budget-threaded `AuthEncode1*PlacedOk*` and exact-capacity contract propositions and proves
`VmPreserved`-threaded basic-block steppers on Block `454` (`lsProg_454 H`) under
`RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Auth.EncodeBasePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (authEncodeExactSpecOf authEncodeExactUnpinnedSpecOf authEncodePinnedSpec authEncodePinnedSpecX
   authEncodeSpec authEncodeSpecX)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB)
open CryptoVerification.LibsignalTripleRatchet.Prost (StepInvPlaced)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf authPBElemsAt sp_sub_64_aligned stackAt_authEncode vecU8At_close_one
   vecU8At_open_one)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBEncodedLen bytesFieldEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq bv_bytesField_nonempty
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64 zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Prost.MessageEncode (AuthEncodeCalleeSavedPlaced)
open CryptoVerification.Cli.SpqrV1.Auth.Placed (blkPl_454 lsProg_454)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
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

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_target_norm (base off target : BitVec 64) :
    (base + off) + (target - base - off) = target := by bv_omega

@[local arm64_norm] private theorem bv_bl_entry_norm (base target : BitVec 64) :
    base + (target - base - 0#64) = target := by bv_omega

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

/-! ## 1. Budget-Threaded Placed Contract Propositions (Block `454`) -/

/-- `encode<Authenticator> [local#3]` (Block `454`) meets `authEncodePinnedSpec A lim` under `[LibsignalPlacement]`. -/
def AuthEncode1PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_454 H) (blkPl_454).base
    (withLsCodeLoaded lsmpl (authEncodePinnedSpec A lim))

/-- `encode<Authenticator> [local#3]` (Block `454`) meets `authEncodeSpec A lim` under `[LibsignalPlacement]`. -/
def AuthEncode1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_454 H) (blkPl_454).base
    (withLsCodeLoaded lsmpl (authEncodeSpec A lim))

/-- `encode<Authenticator> [local#3]` (Block `454`) meets `authEncodePinnedSpecX A lim` under `[LibsignalPlacement]`. -/
def AuthEncode1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_454 H) (blkPl_454).base
    (withLsCodeLoaded lsmpl (authEncodePinnedSpecX A lim))

/-- `encode<Authenticator> [local#3]` (Block `454`) meets `authEncodeSpecX A lim` under `[LibsignalPlacement]`. -/
def AuthEncode1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_454 H) (blkPl_454).base
    (withLsCodeLoaded lsmpl (authEncodeSpecX A lim))

abbrev AuthEncode1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  AuthEncode1PinnedPlacedOk A lim H

abbrev AuthEncode1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  AuthEncode1PlacedOk A lim H

/-- Exact-capacity 0-allocation (`VmPreserved`) pinned contract on Block `454`. -/
def AuthEncode1ExactPlacedOk [LibsignalPlacement] (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_454 H) (blkPl_454).base
    (withLsCodeLoaded lsmpl (authEncodeExactSpecOf resStack A lim))

/-- Exact-capacity 0-allocation (`VmPreserved`) unpinned contract on Block `454`. -/
def AuthEncode1ExactUnpinnedPlacedOk [LibsignalPlacement] (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_454 H) (blkPl_454).base
    (withLsCodeLoaded lsmpl (authEncodeExactUnpinnedSpecOf resStack A lim))

/-! ## 2. Relocatable `VmPreserved`-Threaded Step Lemmas (Block `454`) -/

/-- Header-tag push (`+44..+72`) on Block `454`, threading `VmPreserved s sm`. -/
theorem step_auth_push_hdr_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_454).base + 44#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = authA)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_454).base + 72#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_454 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_454 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt, authPBElemsAt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_454]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 72#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by
        rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt, authPBElemsAt]
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Length-computation step (`+72..+144` and `+380..+396`) on Block `454`, threading `VmPreserved s sm`. -/
theorem step_auth_len_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (v authA sp : BitVec 64) (auth : AuthenticatorPB)
    (hrk_lt : auth.rootKey.length < 2 ^ 63) (hmk_lt : auth.macKey.length < 2 ^ 63)
    (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_454).base + 72#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_454).base + 144#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (authenticatorPBEncodedLen auth) → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length → sm.readReg64 .x21 = authA →
      sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_454 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_454 H) ret s P Q Qp oom := by
  obtain ⟨hrk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.rootKey) (by omega)
  obtain ⟨hmk_beq, hmk_bne⟩ := ofNat_length_beq_zero_of_lt (bs := auth.macKey) (by omega)
  cases hrk : auth.rootKey.isEmpty <;> cases hmk : auth.macKey.isEmpty
  · have hrk_val := bv_bytesField_nonempty hrk
    have hmk_val := bv_bytesField_nonempty hmk
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen auth.macKey)
        (b := bytesFieldEncodedLen auth.rootKey) (c := authenticatorPBEncodedLen auth) rfl hlen_fit
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 144#64)
    wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
      hvmp
  · have hrk_val := bv_bytesField_nonempty hrk
    have htot_eq : authenticatorPBEncodedLen auth = bytesFieldEncodedLen auth.rootKey := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hmk]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 144#64)
    wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
      hvmp
  · have hmk_val := bv_bytesField_nonempty hmk
    have htot_eq : authenticatorPBEncodedLen auth = bytesFieldEncodedLen auth.macKey := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hrk]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 144#64)
    wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
      hvmp
  · have htot_eq : authenticatorPBEncodedLen auth = 0 := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hrk, hmk]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 144#64)
    wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
      hvmp

/-- `root_key` tag push (`+176..+204`) on Block `454`, threading `VmPreserved s sm`. -/
theorem step_auth_push_rk_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr authA rkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_454).base + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = rkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_454).base + 204#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 auth.rootKey.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      sm.readReg64 .x23 = rkPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_454 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x0a#8]) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_454 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_454]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 204#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by
        rw [← vecU8At_close_one A v curCap curPtr curBs 0x0a#8 hlt]
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- `mac_key` tag push (`+280..+308`) on Block `454`, threading `VmPreserved s sm`. -/
theorem step_auth_push_mk_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (v curCap curPtr mkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_454).base + 280#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = mkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_454).base + 308#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 auth.macKey.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = mkPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_454 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_454 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  dsimp only [lsProg_454]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_454).base + 308#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by
        rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]
        exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Epilogue (`+360..+380`) on Block `454`, threading `VmPreserved s sf`. -/
theorem step_auth_epilogue_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64)
    (H : String → Option (State → State)) (sp : BitVec 64)
    {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_454).base + 360#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInvPlaced s0 sf → VmPreserved s sf →
      Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp (lsProg_454 H) (s0.readReg64 .lr) s P Q Qp oom := by
  subst hP
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
        (by epochEncLen_cc_close) (hinv0.trans hinv1) hvmp))
  rw [stackAt_authEncode hres sp]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp) (Entails.sepExists_right (s0.readReg64 .lr)
    (Entails.sepExists_right (s0.readReg64 .x24) (Entails.sepExists_right (s0.readReg64 .x23)
      (Entails.sepExists_right (s0.readReg64 .x22) (Entails.sepExists_right (s0.readReg64 .x21)
        (Entails.sepExists_right (s0.readReg64 .x20)
          (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

end LibsignalBinary.Proofs.Cli.SpqrV1.Auth.EncodeBasePlacedBudget
