/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueClones
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeySignalMessage::new` Input Clones and Key Serialization

Relocatable `[LibsignalPlacement]` stepping lemmas for `+0x000..+0x1ac` of `PreKeySignalMessage::new`
(block `41`) under `RustCliAllocBudget M`, tracking exact clone and serialization allocation events.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueClonesBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (IdentityKey SignalMessage macLength)
open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCl
   blkPl_205 lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym ls_hook_ok_of_mem lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (optKyberAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (preKeyMsgSavedRegs preKeyMsgSubStack optKyberCopyBuf)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
  (optKyberRestAt optKyberRestAt_some_eq optKyberAt_some_eq' optKyberCopyBuf_some_eq'
   pull_pure_second kyberIdOf getLsbD_63_ofNat_lt
   entails_of_sep_focus satisfies_of_sep_focus
   signalMessageRestBodyAt signalMessageAt_expose_ser
   stackAt_preKeyMsgSubStack_to_allocHook stackAt_preKeyMsgSubStack_to_publicKeySerialize)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
   AllocCallPreserved VmPreserved FitsEvents fitsEvents_append rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec
   publicKeySerializeEvents publicKeySerializeSpec fitsEnv_publicKeySerialize_iff
   subroutine_ok_noAllocShim_of_sessionShimBudget
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
  (preKeyMsg_shim_placed_ok preKeyMsg_alloc_placed_ok preKeyMsg_memcpy_placed_ok
   preKeyMsg_publicKeySerialize_placed_ok preKeyMsg_publicKeySerialize_placed_ok_noAllocShim)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks
   vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC vmPreserved_setPState
   vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
   vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
   vmPreserved_applyWriteback vmPreserved_setStatus vmPreserved_appendTrace
   vmPreserved_setFs vmPreserved_stepExclLoop tpidrEl0_applyWriteback)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem sp_sub_96_add_96 (a : BitVec 64) : a - 96#64 + 96#64 = a := by bv_lin

@[local simp, local arm64_norm]
private theorem noneCap_eq : noneCap = 0xffffffffffffffff#64 := rfl

private theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl h

/-! ## Prologue Clone Event Lists -/

def kyberCloneEvs (kp : Option KyberPayload) : List AllocEvent :=
  match kp with
  | none => []
  | some k => if k.ciphertext = [] then [] else rustAllocEvents k.ciphertext.length 1

def pkSerialize2Evs : List AllocEvent :=
  publicKeySerializeEvents ++ publicKeySerializeEvents

def msgCloneEvs (msg : SignalMessage) : List AllocEvent :=
  rustAllocEvents msg.serialized.length 1

/-! ## Frame Setup and Argument Spills (`+0x000..+0x04c`) -/

theorem preKeyMsg_entry_to_04c_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    (x : PreKeyMsgNewCall) (sp0 w304 w288 w280 : BitVec 64) (w292 : BitVec 32) (s0 : State)
    (hpc : s0.pc = (blkPl_41).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = x.regId)
    (hx2 : (s0.readReg64 .x2).setWidth 32 = if x.preKeyId.isSome then 1#32 else 0#32)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = x.spk)
    (hx5 : s0.readReg64 .x5 = x.kyA) (hx6 : s0.readReg64 .x6 = x.bkA)
    (hx7 : s0.readReg64 .x7 = x.ikA) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (lsProg_41 H) ((blkPl_41).base + 76#64) s0
      ((sp0 ↦₆₄ x.msgA) ∗ (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       ((sp0 - 304#64) ↦₆₄ w304) ∗ ((sp0 - 292#64) ↦₃₂ w292) ∗
       ((sp0 - 288#64) ↦₆₄ w288) ∗ ((sp0 - 280#64) ↦₆₄ w280) ∗ cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (s1.sp = sp0 - 368#64 ∧ s1.spAligned = true ∧ s1.readReg64 .x6 = x.bkA ∧
         s1.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64) ∧
         s1.readReg64 .x21 = x.spk.zeroExtend 64 ∧ s1.readReg64 .x22 = x.ikA ∧
         s1.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         s1.readReg64 .x25 = ((s0.readReg64 .x3).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x26 = ((s0.readReg64 .x0).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧ s1.trace = s0.trace ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        (P1 ⊢ (sp0 ↦₆₄ x.msgA) ∗ (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          preKeyMsgSavedRegs sp0 s0)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp] using hsp_align
  subst hsp
  simp only [arm64_norm] at hx1 hx2 hx4 hx5 hx6 hx7 hx8
  unfold preKeyMsgSavedRegs; cells_unfold
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · rw [← hx1, ← hx4]; simp only [State.spAligned, wp_norm, arm64_norm, *]
    · simp only [arm64_norm]; exact entails_of_sep_focus (by sep_focus)

/-! ## Optional Kyber Ciphertext Clone (`+0x04c..+0x0e0`) -/

theorem preKeyMsg_kyber_clone_wpp_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_shim : subroutine_ok (lsProg_41 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (h_alloc : subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false))
    (h_memcpy : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32)
    (st : M.σ) (s : State)
    (hky_max : ∀ k, x.kp = some k → k.ciphertext.length + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim st (kyberCloneEvs x.kp))
    (hpc : s.pc = (blkPl_41).base + 76#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 224#64) s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       optKyberRestAt A.repAlloc x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 =
           (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
          ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗ optKyberAt A.repAlloc x.kyA x.kyPtr x.kp ∗
          ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 312#64) ↦₆₄ w312') ∗ ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ optKyberCopyBuf A.repAlloc kyberCopyPtr x.kp ∗
          A.pool lim (M.stepEvents (kyberCloneEvs x.kp) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29
  cases hkp : x.kp with
  | none =>
    simp only [hkp, kyberCloneEvs, AllocCostModel.stepEvents_nil,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, kyberIdOf] at hx20 ⊢
    wp_steps_sync_pool ((blkPl_41).base + 224#64)
    refine SepWPp.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · refine Entails.sepExists_right w320
        (Entails.sepExists_right w312 (Entails.pure_right (fun h => by cases h) ?_))
      simp only [optKyberAt, optKyberRestAt, optKyberCopyBuf]
      exact entails_of_sep_focus (by sep_focus)
  | some k =>
    simp only [hkp, Option.isSome_some, ↓reduceIte, kyberIdOf,
      optKyberRestAt_some_eq, sepConj_assoc] at hx20 ⊢
    rw [pull_pure_second]; refine SepWPp.pure_elim fun ⟨hky_ne, hct_lt⟩ => ?_
    simp only [← sepConj_assoc]
    have hky_beq : (x.kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hky_ne
    have hct_msb : (BitVec.ofNat 64 k.ciphertext.length).getLsbD 63 = false :=
      getLsbD_63_ofNat_lt hct_lt
    have hct_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hct0 : BitVec.ofNat 64 k.ciphertext.length = 0#64
    · have hct_nil : k.ciphertext = [] := by
        have ht := congrArg BitVec.toNat hct0
        rw [hct_toNat, BitVec.toNat_zero] at ht
        exact List.eq_nil_of_length_eq_zero ht
      simp only [kyberCloneEvs, hct_nil, ↓reduceIte, AllocCostModel.stepEvents_nil]
      wp_steps_sync_pool ((blkPl_41).base + 224#64)
      refine SepWPp.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · simp only [State.spAligned, List.length_nil, wp_norm, arm64_norm, *]
      · refine Entails.sepExists_right 1#64 (Entails.sepExists_right w312 ?_)
        have h1_ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
        simp only [sepConj_assoc]; refine Entails.pure_right (fun _ => h1_ne) ?_
        rw [optKyberAt_some_eq' A.repAlloc x.kyA x.kyPtr k hky_ne hct_lt,
            optKyberCopyBuf_some_eq' A.repAlloc 1#64 k h1_ne hct_lt]
        simp only [hct_nil, List.length_nil, ↓reduceIte, arm64_norm]
        exact entails_of_sep_focus (by sep_focus)
    · have hct_beq : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hct0
      have hct_pos : 0 < k.ciphertext.length := by
        by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
      have hct_ne_nil : k.ciphertext ≠ [] := List.ne_nil_of_length_pos hct_pos
      have hfits_ev : FitsEvents M lim st (rustAllocEvents k.ciphertext.length 1) := by
        simpa only [kyberCloneEvs, hkp, hct_ne_nil, ↓reduceIte] using hfits
      have hlay : RustLayoutOk k.ciphertext.length 1 :=
        ⟨⟨hct_pos, ⟨0, rfl⟩, hky_max k hkp⟩, by decide⟩
      simp only [kyberCloneEvs, hct_ne_nil, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
      refine SepWPp.call_wpp (x := ()) (F := (x.kyA ↦₆₄ x.kyPtr) ∗
          ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          (A.live x.kyPtr k.ciphertext.length 1 ∗ (x.kyPtr ↦ₛ k.ciphertext)) ∗
          ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (x.kyA + 0x14#64) 4 ∗
          ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 296#64) ↦₃₂ w296) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          A.pool lim st _ ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
        h_shim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
        (by simp only [arm64_norm]; rfl)
        (fun R' hm => by
          simp only [noAllocShimBudgetSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
          exact satisfies_of_sep_focus hm (by sep_focus))
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
      intro sf1 hpc1 hrun1 hsp1
        ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1
      simp only [wp_norm, arm64_norm, *] at h26_1 h27_1 h28_1 hfp_1 hvregs_1
      simp only [noAllocShimBudgetSpec]
      refine SepWPp.pure_elim fun ⟨htr1, hvm1⟩ => ?_
      simp only [wp_norm, arm64_norm] at htr1
      refine SepWPp.transport_budgetPool hvm1 (hnext := ?_)
      wp_steps_sync_pool (lsρ lsRustAllocSym)
      refine SepWPp.call_wpp (x := (k.ciphertext.length, 1, st))
        (F := (x.kyA ↦₆₄ x.kyPtr) ∗
          ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          (A.live x.kyPtr k.ciphertext.length 1 ∗ (x.kyPtr ↦ₛ k.ciphertext)) ∗
          ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (x.kyA + 0x14#64) 4 ∗
          ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 296#64) ↦₃₂ w296) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
        h_alloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
        (by simp only [arm64_norm]; rfl)
        (fun R' hm => by
          rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)] at hm
          dsimp only [rustCliAllocNoOomSpec]
          simp only [sepConj_assoc]
          rw [satisfies_pure_sepConj]
          refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
            by simp only [BitVec.toNat_ofNat, wp_norm, arm64_norm, *], hlay, hfits_ev,
            by simp (config := { decide := true }) only [wp_norm, arm64_norm, *]⟩, ?_⟩
          simp only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
          exact satisfies_of_sep_focus hm (by sep_focus))
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
      intro sf2 hpc2 hrun2 hsp2
        ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2
      simp only [wp_norm, arm64_norm, *] at h26_2 h27_2 h28_2 hfp_2 hvregs_2
      simp only [rustCliAllocNoOomSpec, AllocCallPreserved, Bool.false_eq_true, ↓reduceIte,
        sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨⟨_, _, htr2, _⟩, hoom, _⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [wp_norm, arm64_norm] at htr2 hoom hoom_beq
      wp_steps_sync_pool (lsρ lsMemcpySym)
      refine SepWPp.call_wpp (x := ⟨sf2.readReg64 .x0, x.kyPtr, k.ciphertext⟩)
        (F := (x.kyA ↦₆₄ x.kyPtr) ∗
          ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          A.live x.kyPtr k.ciphertext.length 1 ∗
          ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (x.kyA + 0x14#64) 4 ∗
          ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗ ((sp0 - 320#64) ↦₆₄ sf2.readReg64 .x0) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 296#64) ↦₃₂ w296) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ A.live (sf2.readReg64 .x0) k.ciphertext.length 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents k.ciphertext.length 1) st) _ ∗
          stackAt sf2.sp allocHookStack ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
        h_memcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by simp only [arm64_norm]; rfl)
        (fun R' hm => by
          simp only [framelessMemcpyBudgetSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
          exact satisfies_of_sep_focus hm (by sep_focus))
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
      intro sf3 hpc3 hrun3 hsp3
        ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3, hvregs_3⟩
      simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3
      simp only [wp_norm, arm64_norm, *] at h26_3 h27_3 h28_3 hfp_3 hvregs_3
      simp only [framelessMemcpyBudgetSpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr3, hvm3⟩ => ?_
      simp only [wp_norm, arm64_norm] at htr3
      refine SepWPp.transport_budgetPool hvm3 (hnext := ?_)
      wp_steps_sync_pool ((blkPl_41).base + 224#64)
      refine SepWPp.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · simp only [State.spAligned, wp_norm, arm64_norm, *]
      · refine Entails.sepExists_right (sf2.readReg64 .x0)
          (Entails.sepExists_right x.bkA (Entails.pure_right (fun _ => hoom) ?_))
        rw [optKyberAt_some_eq' A.repAlloc x.kyA x.kyPtr k hky_ne hct_lt,
            optKyberCopyBuf_some_eq' A.repAlloc (sf2.readReg64 .x0) k hoom hct_lt,
            stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)]
        simp only [hct_ne_nil, ↓reduceIte, RustCliAllocBudget.repAlloc_live, hsp2, arm64_norm]
        exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_kyber_clone_wpp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32)
    (st : M.σ) (s : State)
    (hky_max : ∀ k, x.kp = some k → k.ciphertext.length + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim st (kyberCloneEvs x.kp))
    (hpc : s.pc = (blkPl_41).base + 76#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 224#64) s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       optKyberRestAt A.repAlloc x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 =
           (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
          ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗ optKyberAt A.repAlloc x.kyA x.kyPtr x.kp ∗
          ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 312#64) ↦₆₄ w312') ∗ ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ optKyberCopyBuf A.repAlloc kyberCopyPtr x.kp ∗
          A.pool lim (M.stepEvents (kyberCloneEvs x.kp) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_kyber_clone_wpp_placed_of_ok
    (subroutine_ok_noAllocShim_of_sessionShimBudget (preKeyMsg_shim_placed_ok hshim))
    (preKeyMsg_alloc_placed_ok halloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x sp0 w320 w312 w324 w296 ver32 pkId32 st s hky_max hfits
    hpc hrun hsp hsp_align hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29

theorem preKeyMsg_kyber_clone_wpp_placed_noAllocShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32)
    (st : M.σ) (s : State)
    (hky_max : ∀ k, x.kp = some k → k.ciphertext.length + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim st (kyberCloneEvs x.kp))
    (hpc : s.pc = (blkPl_41).base + 76#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 224#64) s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       optKyberRestAt A.repAlloc x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 =
           (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
          ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗ optKyberAt A.repAlloc x.kyA x.kyPtr x.kp ∗
          ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 312#64) ↦₆₄ w312') ∗ ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ optKyberCopyBuf A.repAlloc kyberCopyPtr x.kp ∗
          A.pool lim (M.stepEvents (kyberCloneEvs x.kp) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_kyber_clone_wpp_placed_of_ok
    (ls_hook_ok_of_mem hshim)
    (preKeyMsg_alloc_placed_ok halloc)
    (ls_hook_ok_of_mem hmemcpy)
    x sp0 w320 w312 w324 w296 ver32 pkId32 st s hky_max hfits
    hpc hrun hsp hsp_align hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29

/-! ## `PublicKey::serialize` Calls (`+0x0e0..+0x0fc`) -/

theorem preKeyMsg_pk_serialize_wpp_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hpk : subroutine_ok (lsProg_41 H) (blkPl_205).base
      (withLsCl lsmpl (publicKeySerializeSpec M A lim)))
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32)
    (st : M.σ) (s : State)
    (hfits : FitsEvents M lim st pkSerialize2Evs)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 252#64) s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x20 = x.bkA ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x28) x.baseKey.serialize ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool lim (M.stepEvents pkSerialize2Evs st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) := by
  have ⟨hfit1, hfit2⟩ :=
    (fitsEvents_append M lim publicKeySerializeEvents publicKeySerializeEvents st).mp hfits
  have hfitEnv1 := fitsEnv_publicKeySerialize_iff.mpr hfit1
  have hfitEnv2 := fitsEnv_publicKeySerialize_iff.mpr hfit2
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_205).base)
  wp_steps_sync_pool ((blkPl_205).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  refine SepWPp.call_wpp (x := (⟨x.bkA, x.baseKey⟩, st))
    (F := (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗ memRegion (sp0 - 368#64 - 7824#64) 3696)
    hpk (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl] at hm; exact not_satisfies_false_sepConj hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp0 - 368#64)] at hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    dsimp only [publicKeySerializeSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm, *], hfitEnv1⟩, ?_⟩
    simp only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1
    ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1
  simp only [wp_norm, arm64_norm, *] at h26_1 h27_1 h28_1 hfp_1 hvregs_1
  dsimp only [withLsCl]
  simp only [publicKeySerializeSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf,
    sepConj_assoc]
  refine SepWPp.pure_elim fun hcl1 => ?_
  refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx1_1 htr1
  apply SepWPp.of_sepWP_lscl hcl1 (mid := (blkPl_205).base)
  wp_steps_sync_pool ((blkPl_205).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl1' => ?_
  refine SepWPp.call_wpp
    (x := (⟨x.ikA, x.ik.publicKey⟩, M.stepEvents publicKeySerializeEvents st))
    (F := (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
      boxU8Buf A.repAlloc (sf1.readReg64 .x0) x.baseKey.serialize ∗
      memRegion (sp0 - 368#64 - 7824#64) 3696)
    hpk (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl] at hm; exact not_satisfies_false_sepConj hm) ?_
  · intro R' hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1', ?_⟩
    dsimp only [publicKeySerializeSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm, *], hfitEnv2⟩, ?_⟩
    simp only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2
    ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2
  simp only [wp_norm, arm64_norm, *] at h26_2 h27_2 h28_2 hfp_2 hvregs_2
  dsimp only [withLsCl]
  simp only [publicKeySerializeSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf,
    sepConj_assoc]
  refine SepWPp.pure_elim fun _hcl2 => ?_
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
  apply SepWPp.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [State.spAligned, wp_norm, arm64_norm, *], ?_⟩
  have hstep2 :
      M.stepEvents publicKeySerializeEvents (M.stepEvents publicKeySerializeEvents st) =
        M.stepEvents pkSerialize2Evs st := by
    simp only [pkSerialize2Evs, M.stepEvents_append]
  rw [hstep2, stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp0 - 368#64)]
  simp only [IdentityKey.serialize, CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStack,
    wp_norm, hsp1, h28_2, arm64_norm]
  exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_pk_serialize_wpp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32)
    (st : M.σ) (s : State)
    (hfits : FitsEvents M lim st pkSerialize2Evs)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 252#64) s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x20 = x.bkA ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x28) x.baseKey.serialize ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool lim (M.stepEvents pkSerialize2Evs st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_pk_serialize_wpp_placed_of_ok
    (preKeyMsg_publicKeySerialize_placed_ok hshim halloc)
    x sp0 kyberCap ver32 pkId32 st s hfits hcl hpc hrun hsp hsp_align
    hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29

theorem preKeyMsg_pk_serialize_wpp_placed_noAllocShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32)
    (st : M.σ) (s : State)
    (hfits : FitsEvents M lim st pkSerialize2Evs)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 252#64) s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x20 = x.bkA ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x28) x.baseKey.serialize ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool lim (M.stepEvents pkSerialize2Evs st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_pk_serialize_wpp_placed_of_ok
    (preKeyMsg_publicKeySerialize_placed_ok_noAllocShim hshim halloc)
    x sp0 kyberCap ver32 pkId32 st s hfits hcl hpc hrun hsp hsp_align
    hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29

/-! ## `SignalMessage.serialized` Clone (`+0x0fc..+0x1ac`) -/

theorem preKeyMsg_msg_clone_wpp_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_shim : subroutine_ok (lsProg_41 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (h_alloc : subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false))
    (h_memcpy : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32) (st : M.σ) (s : State)
    (hfits : FitsEvents M lim st (msgCloneEvs x.msg))
    (hpc : s.pc = (blkPl_41).base + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 428#64) s
      (signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₃₂ w328) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧ sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s ∧ 9 ≤ x.msg.serialized.length ∧
         x.msg.serialized.length < 2 ^ 40 ∧ sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x26) x.msg.serialized ∗
          A.pool lim (M.stepEvents (msgCloneEvs x.msg) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29
  conv => arg 4; rw [signalMessageAt_expose_ser A.repAlloc x.msgG x.msgA x.msg]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt63⟩ => SepWPp.pure_elim fun hser_wf => ?_
  simp only [← sepConj_assoc]
  have hser9 : 9 ≤ x.msg.serialized.length := by
    have := hser_wf.1; change 8 + 1 ≤ x.msg.serialized.length at this; omega
  have hser_lt40 : x.msg.serialized.length < 2 ^ 40 := hser_wf.2.1
  have hser_pos : 0 < x.msg.serialized.length := by omega
  have hser_ne_nil : x.msg.serialized ≠ [] := List.ne_nil_of_length_pos hser_pos
  have hser_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser0 : BitVec.ofNat 64 x.msg.serialized.length ≠ 0#64 := by
    intro h; have ht := congrArg BitVec.toNat h; rw [hser_toNat, BitVec.toNat_zero] at ht; omega
  have hser_beq : (BitVec.ofNat 64 x.msg.serialized.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hser0
  have hser_msb : (BitVec.ofNat 64 x.msg.serialized.length).getLsbD 63 = false :=
    getLsbD_63_ofNat_lt hser_lt63
  have hlay : RustLayoutOk x.msg.serialized.length 1 :=
    ⟨⟨hser_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  simp only [msgCloneEvs, hser_ne_nil, ↓reduceIte, RustCliAllocBudget.repAlloc_live] at hfits ⊢
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  refine SepWPp.call_wpp (x := ()) (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
      ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
      (A.live x.msgG.serPtr x.msg.serialized.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized)) ∗
      signalMessageRestBodyAt A.repAlloc x.msgG x.msgA x.msg ∗
      ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
      ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
      ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
      A.pool lim st _ ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
    h_shim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      simp only [noAllocShimBudgetSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
  intro sf1 hpc1 hrun1 hsp1
    ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1
  simp only [wp_norm, arm64_norm, *] at h26_1 h27_1 h28_1 hfp_1 hvregs_1
  simp only [noAllocShimBudgetSpec]
  refine SepWPp.pure_elim fun ⟨htr1, hvm1⟩ => ?_
  simp only [wp_norm, arm64_norm] at htr1
  refine SepWPp.transport_budgetPool hvm1 (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  refine SepWPp.call_wpp (x := (x.msg.serialized.length, 1, st))
    (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
      ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
      (A.live x.msgG.serPtr x.msg.serialized.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized)) ∗
      signalMessageRestBodyAt A.repAlloc x.msgG x.msgA x.msg ∗
      ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
      ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
      ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
      memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_alloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)] at hm
      dsimp only [rustCliAllocNoOomSpec]
      simp only [sepConj_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [BitVec.toNat_ofNat, wp_norm, arm64_norm, *], hlay, hfits,
        by simp (config := { decide := true }) only [wp_norm, arm64_norm, *]⟩, ?_⟩
      simp only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
  intro sf2 hpc2 hrun2 hsp2
    ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2
  simp only [wp_norm, arm64_norm, *] at h26_2 h27_2 h28_2 hfp_2 hvregs_2
  simp only [rustCliAllocNoOomSpec, AllocCallPreserved, Bool.false_eq_true, ↓reduceIte,
    sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨⟨_, _, htr2, _⟩, hoom, _⟩ => ?_
  have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  simp only [wp_norm, arm64_norm] at htr2 hoom hoom_beq
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWPp.call_wpp (x := ⟨sf2.readReg64 .x0, x.msgG.serPtr, x.msg.serialized⟩)
    (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
      ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
      A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
      signalMessageRestBodyAt A.repAlloc x.msgG x.msgA x.msg ∗
      ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
      ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
      ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
      A.live (sf2.readReg64 .x0) x.msg.serialized.length 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents x.msg.serialized.length 1) st) _ ∗
      stackAt sf2.sp allocHookStack ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_memcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      simp only [framelessMemcpyBudgetSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
  intro sf3 hpc3 hrun3 hsp3
    ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3, hvregs_3⟩
  simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3
  simp only [wp_norm, arm64_norm, *] at h26_3 h27_3 h28_3 hfp_3 hvregs_3
  simp only [framelessMemcpyBudgetSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, htr3, hvm3⟩ => ?_
  simp only [wp_norm, arm64_norm] at htr3
  refine SepWPp.transport_budgetPool hvm3 (hnext := ?_)
  wp_steps_sync_pool ((blkPl_41).base + 428#64)
  refine SepWPp.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · simp only [State.spAligned, wp_norm, arm64_norm, *]; exact ⟨hser_lt40, hoom⟩
  · rw [signalMessageAt_expose_ser A.repAlloc x.msgG x.msgA x.msg,
        stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)]
    have hp_msg1 : (x.msgG.serPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63) = True :=
      eq_true ⟨hser_ne, hser_lt63⟩
    have hp_msg2 : (macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.serialized.length < 2 ^ 40 ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)) = True := eq_true hser_wf
    rw [hp_msg1, hp_msg2, pure_true, emp_sepConj, emp_sepConj]
    simp only [wp_norm, arm64_norm, hsp2, hser_ne_nil, ↓reduceIte,
      RustCliAllocBudget.repAlloc_live]
    unfold boxU8Buf
    have hp_copy : (sf2.readReg64 (Reg.gpr 0#5) ≠ 0#64 ∧
        x.msg.serialized.length < 2 ^ 63) = True :=
      eq_true ⟨hoom, hser_lt63⟩
    rw [hp_copy, pure_true, emp_sepConj]
    simp only [hser_ne_nil, ↓reduceIte, RustCliAllocBudget.repAlloc_live, arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_msg_clone_wpp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32) (st : M.σ) (s : State)
    (hfits : FitsEvents M lim st (msgCloneEvs x.msg))
    (hpc : s.pc = (blkPl_41).base + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 428#64) s
      (signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₃₂ w328) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧ sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s ∧ 9 ≤ x.msg.serialized.length ∧
         x.msg.serialized.length < 2 ^ 40 ∧ sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x26) x.msg.serialized ∗
          A.pool lim (M.stepEvents (msgCloneEvs x.msg) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_msg_clone_wpp_placed_of_ok
    (subroutine_ok_noAllocShim_of_sessionShimBudget (preKeyMsg_shim_placed_ok hshim))
    (preKeyMsg_alloc_placed_ok halloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 w332 w328 ver32 pkId32 st s hfits
    hpc hrun hsp hsp_align hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29

theorem preKeyMsg_msg_clone_wpp_placed_noAllocShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32) (st : M.σ) (s : State)
    (hfits : FitsEvents M lim st (msgCloneEvs x.msg))
    (hpc : s.pc = (blkPl_41).base + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 428#64) s
      (signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₃₂ w328) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧ sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s ∧ 9 ≤ x.msg.serialized.length ∧
         x.msg.serialized.length < 2 ^ 40 ∧ sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x26) x.msg.serialized ∗
          A.pool lim (M.stepEvents (msgCloneEvs x.msg) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_msg_clone_wpp_placed_of_ok
    (ls_hook_ok_of_mem hshim)
    (preKeyMsg_alloc_placed_ok halloc)
    (ls_hook_ok_of_mem hmemcpy)
    x sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 w332 w328 ver32 pkId32 st s hfits
    hpc hrun hsp hsp_align hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueClonesBudget
