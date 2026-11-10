/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<spqr::authenticator::Authenticator>::mac_hdr` (Block 342)

Proves `RustCliAllocBudget M` `[LibsignalPlacement]` contracts for block 342
against `authMacHdrPinnedSpec` and `authMacHdrSpec` with deterministic allocation
envelope `AuthMacHdrEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoVerification (LibsignalPlacement blkPC_342 blkPl_342 lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSpqrV1 (Authenticator Bytes Epoch LibcruxHmacCall)
open CryptoVerification.SpqrV1.Alloc (SliceConcat3Ghost)
open CryptoVerification.SpqrV1.Auth (
  AuthMacHdrGhost AuthMacHdrPinnedGhost AuthenticatorGhost
  authMacHdrStackX authenticatorAt authenticatorAt_eq_exists_pinned
  authenticatorPinAt authenticatorPinAt_entails_authenticatorAt
  pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length
  rodata_hdrLabel_placed vecU8At_expose_entails vecU8At_unexpose_entails
)
open CryptoVerification.SpqrV1.Auth.MacHdrFacts (
  hdrLabel_length macHdrUnchecked_eq_hmacWith rejoin_stack_authMacHdrX
  stackAt_authMacHdrX_split
)
open CryptoVerification.SpqrV1.ChainProofs (
  bytesAt bytesAt_false bytesAt_true
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv
  SepWPp.call_allowPanic_lsCallInv_mid
  SepWPp.call_allowPanic_lsCallInv_ret
  subroutine_ok_withLsCallInv_rodata1_keep
  withLsCallInv
)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget fitsEvents_append rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (
  LibcruxHmacEnv libcruxHmacBudgetSpec libcruxHmacSha256Events
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  SliceConcat3Env sliceConcat3Events sliceConcat3Spec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  subroutine_ok_post_entails
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocSpecWithStack
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false hdrLabel_length toBEBytes_8_length List.length_append
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

/-! ## Deterministic Allocation Envelope -/

/-- Deterministic `AllocEvent` list of `Authenticator::mac_hdr`: allocates `ct_mac_data`
(`41 + hdr.length` B), and when `macKey` and `ct_mac_data` fit in `u32`, runs
`libcrux_hmac::hmac` and deallocates `ct_mac_data`. -/
def authMacHdrEvents (auth : Authenticator) (hdr : Bytes) : List AllocEvent :=
  if auth.macKey.length < 2 ^ 32 ∧ 41 + hdr.length < 2 ^ 32 then
    sliceConcat3Events (41 + hdr.length) ++ libcruxHmacSha256Events ++
      rustDeallocEvents (41 + hdr.length) 1
  else
    sliceConcat3Events (41 + hdr.length)

def AuthMacHdrEnv (auth : Authenticator) (hdr : Bytes) (evs : List AllocEvent) : Prop :=
  evs = authMacHdrEvents auth hdr

theorem fitsEnv_authMacHdr_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {auth : Authenticator} {hdr : Bytes} :
    FitsEnv M lim st (AuthMacHdrEnv auth hdr) ↔
      FitsEvents M lim st (authMacHdrEvents auth hdr) :=
  FitsEnv.eq_iff

/-! ## Budget-Threaded Specifications -/

/-- Budget-threaded pinned specification of `Authenticator::mac_hdr` (retaining only the `u32` HMAC length-overflow panic). -/
def authMacHdrPinnedSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthMacHdrPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outVec ∧ s.readReg64 .x0 = x.selfA ∧
      s.readReg64 .x1 = x.ep ∧ s.readReg64 .x2 = x.hdrA ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.hdr.length ∧
      41 + x.hdr.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthMacHdrEnv x.auth x.hdr)⌝ ∗
      memRegion x.outVec 24 ∗
      authenticatorPinAt A.repAlloc x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool lim st s ∗ stackAt s.sp authMacHdrStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
        sf.trace = s0.trace ∧ AuthMacHdrEnv x.auth x.hdr evs⌝ ∗
      vecU8 A.repAlloc x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorPinAt A.repAlloc x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authMacHdrStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(2 ^ 32 ≤ x.auth.macKey.length ∨
      2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Budget-threaded unpinned specification of `Authenticator::mac_hdr`. -/
def authMacHdrSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthMacHdrGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outVec ∧ s.readReg64 .x0 = x.selfA ∧
      s.readReg64 .x1 = x.ep ∧ s.readReg64 .x2 = x.hdrA ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.hdr.length ∧
      41 + x.hdr.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthMacHdrEnv x.auth x.hdr)⌝ ∗
      memRegion x.outVec 24 ∗
      authenticatorAt A.repAlloc x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool lim st s ∗ stackAt s.sp authMacHdrStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
        sf.trace = s0.trace ∧ AuthMacHdrEnv x.auth x.hdr evs⌝ ∗
      vecU8 A.repAlloc x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorAt A.repAlloc x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authMacHdrStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(2 ^ 32 ≤ x.auth.macKey.length ∨
      2 ^ 32 ≤ (Authenticator.hdrLabel ++ toBEBytes 8 x.ep ++ x.hdr).length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

def AuthMacHdrPlacedOk [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_342).rebase (blkPl_342).base H) (blkPl_342).base
    (withLsCallInv lsmpl (authMacHdrSpec F M A lim))

/-! ## Helper Lemmas -/

private theorem onPanic_hmacBudget_entails_macHdr {s0 s sf : State} {P1 P2 : Prop} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜(P1 ∨ P2) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P1 ∨ P2) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

private theorem expose_concat3_vecU8At {A : RustAlloc} (sp : BitVec 64) (ptr : BitVec 64)
    (ep : Epoch) (hdr : Bytes) (hlen : 41 + hdr.length < 2 ^ 63) :
    vecU8At A (sp - 112#64)
      (BitVec.ofNat 64 (Authenticator.hdrLabel.length + (toBEBytes 8 ep).length + hdr.length))
      ptr (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr) ⊢
      ⌜ptr ≠ 0⌝ ∗
        ((sp - 112#64) ↦₆₄ BitVec.ofNat 64 (41 + hdr.length)) ∗
        ((sp - 104#64) ↦₆₄ ptr) ∗
        ((sp - 96#64) ↦₆₄ BitVec.ofNat 64 (41 + hdr.length)) ∗
        (ptr ↦ₛ (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr)) ∗
        A.live ptr (41 + hdr.length) 1 := by
  have h33 : Authenticator.hdrLabel.length = 33 := hdrLabel_length
  have h8 : (toBEBytes 8 ep).length = 8 := toBEBytes_8_length ep
  have hsum1 : Authenticator.hdrLabel.length + (toBEBytes 8 ep).length + hdr.length = 41 + hdr.length := by
    omega
  have hsum2 : (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr).length = 41 + hdr.length := by
    simp only [List.length_append, h33, h8]
  have hcap_toNat : (BitVec.ofNat 64 (41 + hdr.length)).toNat = 41 + hdr.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 (41 + hdr.length) ≠ 0 := by
    intro h0
    have h0' := congrArg BitVec.toNat h0
    rw [hcap_toNat] at h0'
    change 41 + hdr.length = 0 at h0'
    omega
  have ha8 : (sp - 112#64) + 8#64 = sp - 104#64 := by bv_omega
  have ha16 : (sp - 112#64) + 16#64 = sp - 96#64 := by bv_omega
  rw [hsum1]
  refine Entails.trans (vecU8At_expose_entails A (sp - 112#64)
    (BitVec.ofNat 64 (41 + hdr.length)) ptr (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr)) ?_
  simp only [hsum2, hcap_ne, ↓reduceIte, hcap_toNat, Nat.sub_self, memRegion_zero,
    sepConj_emp, ha8, ha16]
  rw [show (((sp - 112#64) ↦₆₄ BitVec.ofNat 64 (41 + hdr.length)) ∗
      ((sp - 104#64) ↦₆₄ ptr) ∗
      ((sp - 96#64) ↦₆₄ BitVec.ofNat 64 (41 + hdr.length)) ∗
      ⌜41 + hdr.length ≤ 41 + hdr.length ∧ 41 + hdr.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (ptr ↦ₛ (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr)) ∗
      A.live ptr (41 + hdr.length) 1) =
    (⌜41 + hdr.length ≤ 41 + hdr.length ∧ 41 + hdr.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((sp - 112#64) ↦₆₄ BitVec.ofNat 64 (41 + hdr.length)) ∗
      ((sp - 104#64) ↦₆₄ ptr) ∗
      ((sp - 96#64) ↦₆₄ BitVec.ofNat 64 (41 + hdr.length)) ∗
      (ptr ↦ₛ (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr)) ∗
      A.live ptr (41 + hdr.length) 1) by sep_ac_rfl]
  refine Entails.pure_left fun ⟨_, _, hptr_ne⟩ => ?_
  exact Entails.pure_right hptr_ne (Entails.of_eq rfl)

private def authMacHdrPinnedPostConcrete [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    (AuthMacHdrPinnedGhost × M.σ) → State → State → SepProp :=
  fun (x, st) s0 sf =>
    ⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
      sf.trace = s0.trace⌝ ∗
      (lsρ "spqr:.rodata..Lanon.140" ↦ᵣ Authenticator.hdrLabel) ∗
      vecU8 A.repAlloc x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
      authenticatorPinAt A.repAlloc x.g x.selfA x.auth ∗
      bytesAt x.hdrRO x.hdrA x.hdr ∗
      A.pool lim (M.stepEvents (authMacHdrEvents x.auth x.hdr) st) sf ∗
      stackAt s0.sp authMacHdrStackX

/-! ## Relocatable Contracts (Block 342) -/

set_option maxHeartbeats 1600000 in
/-- Block 342 (`Authenticator::mac_hdr`) meets `withLsCallInv lsmpl (authMacHdrPinnedSpec F M A lim)`. -/
theorem authMacHdrPinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat3Spec M A lim)))
    (h_hmac : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacBudgetSpec F M A lim)))
    (h_dealloc : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    subroutine_ok ((blkPC_342).rebase (blkPl_342).base H) (blkPl_342).base
      (withLsCallInv lsmpl (authMacHdrPinnedSpec F M A lim)) := by
  refine subroutine_ok_withLsCallInv_rodata1_keep rodata_hdrLabel_placed ?_
  refine subroutine_ok_post_entails
    (authMacHdrPinnedPostConcrete F M A lim)
    (fun (x, st) s0 sf => by
      dsimp only [authMacHdrPinnedPostConcrete, authMacHdrPinnedSpec]
      refine Entails.pure_left fun ⟨hmh, htr⟩ => ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_right (authMacHdrEvents x.auth x.hdr) ?_
      exact Entails.pure_right ⟨hmh, htr, rfl⟩ (Entails.refl _))
    ?_
  wpp_init x_st s0
  rcases x_st with ⟨⟨outVec, selfA, g, auth, ep, hdrRO, hdrA, hdr⟩, st⟩
  dsimp only [authMacHdrPinnedSpec] at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹_›, ‹_›⟩
  have hlen63 : 41 + hdr.length < 2 ^ 63 := ‹_›
  have hfits_env : FitsEnv M lim st (AuthMacHdrEnv auth hdr) := ‹_›
  have hfits_all : FitsEvents M lim st (authMacHdrEvents auth hdr) := hfits_env _ rfl
  have hfits_concat_ev : FitsEvents M lim st (sliceConcat3Events (41 + hdr.length)) := by
    dsimp only [authMacHdrEvents] at hfits_all
    split_ifs at hfits_all with hlt
    · rw [List.append_assoc, fitsEvents_append] at hfits_all
      exact hfits_all.1
    · exact hfits_all
  have hx8 : s0.readReg64 (.gpr 8#5) = outVec := ‹_›
  have hx0 : s0.readReg64 (.gpr 0#5) = selfA := ‹_›
  have hx1 : s0.readReg64 (.gpr 1#5) = ep := ‹_›
  have hx2 : s0.readReg64 (.gpr 2#5) = hdrA := ‹_›
  subst hx8 hx0 hx1 hx2
  have hadd24_8 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 8#64 = s0.readReg64 (.gpr 0#5) + 32#64 := by bv_omega
  have hadd24_16 : (s0.readReg64 (.gpr 0#5) + 0x18#64) + 16#64 = s0.readReg64 (.gpr 0#5) + 40#64 := by bv_omega
  dsimp only [authenticatorPinAt]
  refine SepWPp.rw_pre (by rw [stackAt_authMacHdrX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.fold
    (vecU8At_expose_entails A.repAlloc (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey)
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by rw [hadd24_8, hadd24_16]) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmac_le, hmac_lt63, hmac_ptr_ne⟩
  have hmac_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWPp.of_sepWP_lsCallInv
    (mid := lsmpl.base 386) hinv0 ?_
  wp_steps_sync_pool (lsmpl.base 386)
  refine SepWP.fold (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 40#64) (s0.readReg64 (.gpr 1#5))))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  let x_concat : SliceConcat3Ghost :=
    ⟨s0.sp - 112#64, s0.sp - 88#64,
      true, lsρ "spqr:.rodata..Lanon.140", Authenticator.hdrLabel,
      false, s0.sp - 40#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
      hdrRO, s0.readReg64 (.gpr 2#5), hdr⟩
  have hsum_concat :
      x_concat.bs0.length + x_concat.bs1.length + x_concat.bs2.length = 41 + hdr.length := by
    dsimp only [x_concat]
    rw [hdrLabel_length, toBEBytes_8_length]
  have hfits_concat : FitsEnv M lim st (SliceConcat3Env x_concat) := by
    intro evs hevs
    rw [hevs, hsum_concat]
    exact hfits_concat_ev
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat3Spec M A lim)) at h_concat
  apply (SepWPp.call_allowPanic_lsCallInv_mid h_concat (x := (x_concat, st)) hinv1)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_goal
  · wp_norm_lhs
  · intro R' hmR'
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left ?_) hmR'
    dsimp only [sliceConcat3Spec, x_concat]
    simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false, hdrLabel_length, toBEBytes_8_length,
      sepConj_assoc, wp_norm, arm64_norm]
    refine Entails.pure_right ⟨by omega, hfits_concat⟩ ?_
    sep_frame
  · intro _
    dsimp only [sliceConcat3Spec]
    exact Entails.pure_left fun h => False.elim h
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF_sf
  dsimp only [sliceConcat3Spec, x_concat]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun evs_concat => ?_
  refine SepWPp.exists_elim fun ptr => ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htrace_sf, hacp_sf, hevs_concat⟩
  have hevs_concat_eq : evs_concat = sliceConcat3Events (41 + hdr.length) := by
    dsimp only [SliceConcat3Env, x_concat] at hevs_concat
    rw [hdrLabel_length, toBEBytes_8_length] at hevs_concat
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hevs_concat
  subst hevs_concat_eq
  refine SepWPp.fold (expose_concat3_vecU8At s0.sp ptr (s0.readReg64 (.gpr 1#5)) hdr hlen63)
    (by sep_focus) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  intro hptr_ne
  have hcap_toNat : (BitVec.ofNat 64 (41 + hdr.length)).toNat = 41 + hdr.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 (41 + hdr.length) ≠ 0#64 := by
    intro h0
    have h0' := congrArg BitVec.toNat h0
    rw [hcap_toNat, BitVec.toNat_ofNat] at h0'
    omega
  have hcap_beq : (BitVec.ofNat 64 (41 + hdr.length) == 0#64) = false := beq_false_of_ne hcap_ne
  have hsp_sf' : sf.sp = s0.sp - 112#64 := by simpa [wp_norm, arm64_norm] using hsp_sf
  have hcs_sf_norm := hcs_sf
  unfold CalleeSavedPreserved at hcs_sf_norm
  simp only [wp_norm, arm64_norm] at hcs_sf_norm
  rcases hcs_sf_norm with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf,
    hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩
  wp_norm_hyp hpc_sf; wp_norm_hyp hsp_sf'; wp_norm_hyp hx19_sf; wp_norm_hyp hx20_sf
  wp_norm_hyp hx21_sf; wp_norm_hyp hx22_sf; wp_norm_hyp hx23_sf; wp_norm_hyp hx24_sf
  wp_norm_hyp hx25_sf; wp_norm_hyp hx26_sf; wp_norm_hyp hx27_sf; wp_norm_hyp hx28_sf
  wp_norm_hyp hx29_sf; wp_norm_hyp hvregs_sf; wp_norm_hyp htrace_sf
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac") hF_sf ?_
  wp_steps_sync_pool (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
  have hstack_sf : stackAt (s0.sp - 112#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [hsp_sf']
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  let st1 := M.stepEvents (sliceConcat3Events (41 + hdr.length)) st
  let x_hmac : LibcruxHmacCall :=
    ⟨s0.readReg64 (.gpr 8#5), g.macKey.ptr, auth.macKey,
      ptr, Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr⟩
  have hdata_len :
      (Authenticator.hdrLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr).length =
        41 + hdr.length := by
    simp only [List.length_append, hdrLabel_length, toBEBytes_8_length]
  have hfits_hmac : FitsEnv M lim st1 (LibcruxHmacEnv x_hmac) := by
    intro evs hevs
    dsimp only [LibcruxHmacEnv, x_hmac] at hevs
    rw [hdata_len] at hevs
    dsimp only [authMacHdrEvents] at hfits_all
    split_ifs at hevs with hlt
    · subst hevs
      simp only [hlt.1, hlt.2, and_self, ↓reduceIte] at hfits_all
      rw [List.append_assoc, fitsEvents_append] at hfits_all
      rw [fitsEvents_append] at hfits_all
      exact hfits_all.2.1
    · subst hevs
      simp
  change subroutine_ok _ _ (withLsCallInv lsmpl (libcruxHmacBudgetSpec F M A lim)) at h_hmac
  apply (SepWPp.call_allowPanic_lsCallInv_ret h_hmac (x := (x_hmac, st1)) hinv2)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_goal
  · wp_norm_lhs
  · intro R' hmR'
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left ?_) hmR'
    dsimp only [libcruxHmacBudgetSpec, x_hmac]
    simp (config := { decide := true }) only [
      hmac_toNat, hcap_toNat, sepConj_assoc, wp_norm, arm64_norm]
    refine Entails.pure_right hfits_hmac ?_
    sep_frame
  · intro _
    dsimp only [libcruxHmacBudgetSpec, x_hmac]
    exact onPanic_hmacBudget_entails_macHdr (by wp_norm_lhs)
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf_1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1 hF_sf1
  dsimp only [libcruxHmacBudgetSpec, x_hmac]
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro evs_hmac
  refine CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hk_lt32, hd_lt32, htrace_sf1, hevs_hmac⟩
  have hd_lt32' : 41 + hdr.length < 2 ^ 32 := by rwa [← hdata_len]
  have hevs_hmac_eq : evs_hmac = libcruxHmacSha256Events := by
    dsimp only [LibcruxHmacEnv] at hevs_hmac
    simpa only [hk_lt32, hd_lt32, and_self, ↓reduceIte] using hevs_hmac
  subst hevs_hmac_eq
  have hsp_sf1' : sf_1.sp = sf.sp := by simpa [wp_norm, arm64_norm] using hsp_sf1
  have hcs_sf1_norm := hcs_sf1
  unfold CalleeSavedPreserved at hcs_sf1_norm
  simp only [wp_norm, arm64_norm] at hcs_sf1_norm
  rcases hcs_sf1_norm with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  wp_norm_hyp hpc_sf1; wp_norm_hyp hsp_sf1'; wp_norm_hyp hx19_1; wp_norm_hyp hx20_1
  wp_norm_hyp hx21_1; wp_norm_hyp hx22_1; wp_norm_hyp hx23_1; wp_norm_hyp hx24_1
  wp_norm_hyp hx25_1; wp_norm_hyp hx26_1; wp_norm_hyp hx27_1; wp_norm_hyp hx28_1
  wp_norm_hyp hx29_1; wp_norm_hyp hvregs_1; wp_norm_hyp htrace_sf1
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  have hmr_data :
      (ptr ↦ₛ (Authenticator.hdrLabel ++ (toBEBytes 8 (s0.readReg64 (.gpr 1#5)) ++ hdr))) ⊢
        memRegion ptr (41 + hdr.length) := by
    rw [← List.append_assoc Authenticator.hdrLabel, ← hdata_len]
    exact pointsToBytes_entails_memRegion ptr _
  refine SepWP.fold hmr_data (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [hsp_sf1']
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  wp_call h_dealloc (ptr, 41 + hdr.length, 1, _)
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  have hstack_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 112#64) extHookStack := by
    rw [← hstack_sf1, ← hstack_sf]
  refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
  refine SepWP.fold (rejoin_stack_authMacHdrX s0.sp _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _) (by sep_focus) ?_
  have hmac_rejoin :
      ((s0.readReg64 (.gpr 0#5) + 0x18#64) ↦₆₄ g.macKey.cap) ∗
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
        ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        (if g.macKey.cap = 0 then emp
         else A.repAlloc.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ⊢
        vecU8At A.repAlloc (s0.readReg64 (.gpr 0#5) + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey := by
    rw [← hadd24_8, ← hadd24_16]
    exact vecU8At_unexpose_entails A.repAlloc (s0.readReg64 (.gpr 0#5) + 0x18#64)
      g.macKey.cap g.macKey.ptr auth.macKey hmac_le hmac_lt63 hmac_ptr_ne
  refine SepWP.fold hmac_rejoin (by sep_focus) ?_
  have hmacHdr_ok :
      auth.macHdr F (s0.readReg64 (.gpr 1#5)) hdr =
        .ok (auth.macHdrUnchecked F (s0.readReg64 (.gpr 1#5)) hdr) :=
    Authenticator.macHdr_of_lt F auth (s0.readReg64 (.gpr 1#5)) hdr hk_lt32 hd_lt32
  have htr_final : sf_2.trace = s0.trace := by
    have hacp_2 : AllocCallPreserved sf_1 sf_2 := ‹AllocCallPreserved _ sf_2›
    have htr2 : sf_2.trace = sf_1.trace := hacp_2.2.1
    wp_norm_hyp htr2
    exact htr2.trans (htrace_sf1.trans htrace_sf)
  wp_norm_hyp htr_final
  have hpool_eq :
      M.stepEvents (rustDeallocEvents (41 + hdr.length) 1)
        (M.stepEvents libcruxHmacSha256Events st1) =
        M.stepEvents (authMacHdrEvents auth hdr) st := by
    dsimp only [st1, authMacHdrEvents]
    simp only [hk_lt32, hd_lt32', and_self, ↓reduceIte,
      LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  rw [hpool_eq, ← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith F auth (s0.readReg64 (.gpr 1#5)) hdr]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨?_, by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal⟩
  intro hmR
  dsimp only [authMacHdrPinnedPostConcrete, authenticatorPinAt]
  refine Satisfies.mono (sepConj_mono_left ?_) hmR
  refine Entails.pure_right ⟨hmacHdr_ok, by wp_norm_goal⟩ ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Block 342 (`Authenticator::mac_hdr`) meets `withLsCallInv lsmpl (authMacHdrSpec F M A lim)`. -/
theorem authMacHdr_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat3Spec M A lim)))
    (h_hmac : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacBudgetSpec F M A lim)))
    (h_dealloc : subroutine_ok ((blkPC_342).rebase (blkPl_342).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    AuthMacHdrPlacedOk F M A lim H := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpin := authMacHdrPinned_placed_ok h_concat h_hmac h_dealloc
  simp only [authMacHdrSpec, withLsCallInv, authenticatorAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCallInv lsmpl (authMacHdrPinnedSpec F M A lim)).pre
        (⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩, st) s0 ∗ R := by
    simpa only [authMacHdrPinnedSpec, withLsCallInv] using hpre
  refine hpin.mono_outcome (⟨x.outVec, x.selfA, g, x.auth, x.ep, x.hdrRO, x.hdrA, x.hdr⟩, st)
    R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [authMacHdrPinnedSpec, authMacHdrSpec, withLsCallInv,
      sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    have hent :
        (⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
            sf.trace = s0.trace ∧ AuthMacHdrEnv x.auth x.hdr evs⌝ ∗
          vecU8 A.repAlloc x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
          authenticatorPinAt A.repAlloc g x.selfA x.auth ∗
          bytesAt x.hdrRO x.hdrA x.hdr ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authMacHdrStackX) ∗ R ⊢
        (⌜x.auth.macHdr F x.ep x.hdr = .ok (x.auth.macHdrUnchecked F x.ep x.hdr) ∧
            sf.trace = s0.trace ∧ AuthMacHdrEnv x.auth x.hdr evs⌝ ∗
          vecU8 A.repAlloc x.outVec (x.auth.macHdrUnchecked F x.ep x.hdr) ∗
          authenticatorAt A.repAlloc x.selfA x.auth ∗
          bytesAt x.hdrRO x.hdrA x.hdr ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authMacHdrStackX) ∗ R := by
      apply sepConj_mono_left
      exact sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (authenticatorPinAt_entails_authenticatorAt A.repAlloc g x.selfA x.auth)))
    exact Satisfies.mono hent hpost
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr hex)

end LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget
