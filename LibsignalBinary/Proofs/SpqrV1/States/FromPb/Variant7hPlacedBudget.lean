/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7hPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part H

Lifts the `<PolyEncoder>::from_pb = Ok(enc)` stack move (`+3720 -> +7260 -> +7348`),
`s.receivingEk = none` cleanup (`+7348 -> +10556 -> +4632`), and `<PolyDecoder>::from_pb` setup,
call, and error cleanup (`+7348 -> +7400 -> +7404 -> +11096 -> +4632`) to `VmPreserved` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7hPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (PolyEncoder PolynomialError ProtoPolynomialDecoder spqrAuthApi)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   optProtoPolyDecoder_none_entails_memRegion_40 unchunkedCt1SentAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt protoPolynomialDecoderAt resultPolyDecoderFromPbAt resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v7_1400_realign_final_rest v7_1888_32_368_entails_memRegion_400
   v7_1888_tag_392_to_memRegion_400 v7_1896_realign_final_rest v7_896_spill_entails_memRegion_56
   v7_ct1SentAt_eq_unchunkedCt1SentAt v7_ct1SentAt_pack v7_ct1SentHeap
   v7_ct1SentHeap_entails_dealloc v7_ct1SentOtherCells v7_ct1SentWordsAt
   v7_ct1SentWordsAt_1264_eq_spill_other v7_ct1SentWordsAt_entails_128 v7_fsp_1264_add_137
   v7_fsp_1264_add_137_sext v7_fsp_1392_add_32 v7_fsp_1400_triple_rest v7_fsp_1401_add_8
   v7_fsp_1409_realign_rest v7_fsp_1896_triple_rest v7_fsp_1897_add_8 v7_fsp_1905_realign_rest
   v7_fsp_896_add_8 v7_fsp_904_realign_rest v7_fsp_904_realign_w24_rest
   v7_fsp_904_unrealign_w24_rest v7_memRegion_1392_400_split_32_368
   v7_memRegion_896_56_split_24_32 v7_optProtoPolyDecoderTail v7_polyEncoderAt_relocate_1888_to_1392
   v7_polyEncoderTag v7_polyEncoderTag_bne_two v7_polyEncoderTag_sub_two_beq_zero
   v7_resultPolyDecoder_err_entails_tag_392 v7_resultPolyEncoder_ok_eq
   v7_stackAt_encoderFromPbStack_eq_allocHook v7_x20_add_105 v7_x20_add_105_sext v7_x23_add_63
   v7_x23_add_63_sext v7_x25_add_32 v7_zext32_setWidth8 v7_zext64_32_setWidth32
   v7_zext64_32_setWidth8 v7_zext64_setWidth32_setWidth8 v7_zext64_setWidth8)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved allocMemcpyVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
  (sessionMemcpyVmAcpSpec subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (align_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget.toPlacedBudget seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget (v7_cleanup_11096_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlacedBudget
  (v7_cleanup_10556_placed v7_ct1SentSpillCells)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

attribute [local simp, local arm64_norm, local wp_norm]
  v7_polyEncoderTag_sub_two_beq_zero
  v7_x20_add_105_sext
  v7_x20_add_105
  v7_fsp_1897_add_8
  v7_x25_add_32
  v7_fsp_896_add_8
  v7_x23_add_63_sext
  v7_x23_add_63
  v7_fsp_1392_add_32
  v7_fsp_1264_add_137_sext
  v7_fsp_1264_add_137
  v7_fsp_1401_add_8
  v7_zext32_setWidth8
  v7_polyEncoderTag_bne_two
  v7_zext64_32_setWidth8
  v7_zext64_32_setWidth32
  v7_zext64_setWidth8
  v7_zext64_setWidth32_setWidth8

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

@[simp] private theorem stripS_pstate (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).pstate = s.pstate := rfl

private theorem vmPreserved_trans_congr {s₁ s₂ s₂' s₃ : State}
    (h12 : VmPreserved s₁ s₂) (h23 : VmPreserved s₂' s₃)
    (hbs : s₂'.brkStart = s₂.brkStart := by first | rfl | simp only [wp_norm, arm64_norm])
    (hbrk : s₂'.brk = s₂.brk := by first | rfl | simp only [wp_norm, arm64_norm])
    (htp : s₂'.tpidrEl0 = s₂.tpidrEl0 := by first | rfl | simp only [wp_norm, arm64_norm])
    (hphys : s₂'.physMemAvail = s₂.physMemAvail := by first | rfl | simp only [wp_norm, arm64_norm])
    (hperm : ∀ a, s₂'.mem.perm a = s₂.mem.perm a := by
      intro _; first | rfl | simp only [wp_norm, arm64_norm])
    (hfds : LibsignalBinary.Heap.FdsHiFrame s₂ s₂' := by
      intro _ _ _; first | rfl | simp only [wp_norm, arm64_norm]) :
    VmPreserved s₁ s₃ :=
  h12.trans (VmPreserved.trans ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, hfds⟩ h23)

private theorem with_vm_from {prog : Program} {target : BitVec 64} {s₀ s₁ s₁' s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h01 : VmPreserved s₀ s₁) (h12 : VmPreserved s₁' s)
    (hk : VmPreserved s₀ s → SepWP prog target s P post)
    (hbs : s₁'.brkStart = s₁.brkStart := by first | rfl | simp only [wp_norm, arm64_norm])
    (hbrk : s₁'.brk = s₁.brk := by first | rfl | simp only [wp_norm, arm64_norm])
    (htp : s₁'.tpidrEl0 = s₁.tpidrEl0 := by first | rfl | simp only [wp_norm, arm64_norm])
    (hphys : s₁'.physMemAvail = s₁.physMemAvail := by first | rfl | simp only [wp_norm, arm64_norm])
    (hperm : ∀ a, s₁'.mem.perm a = s₁.mem.perm a := by
      intro _; first | rfl | simp only [wp_norm, arm64_norm])
    (hfds : LibsignalBinary.Heap.FdsHiFrame s₁ s₁' := by
      intro _ _ _; first | rfl | simp only [wp_norm, arm64_norm]) :
    SepWP prog target s P post :=
  hk (vmPreserved_trans_congr h01 h12 hbs hbrk htp hphys hperm hfds)

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s₀ s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (hvm : VmPreserved s₀ s)
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => (Pm ⊢ P) ∧ sm = s ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ VmPreserved s₀ sm ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hp, hsm, hq⟩ => ⟨Entails.trans hp hent, hsm ▸ hvm, hq⟩

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. `<PolyEncoder>::from_pb = Ok(enc)` Move (`+3720 -> +7260 -> +7348`) -/

set_option maxHeartbeats 1200000 in
/-- `VmPreserved`-strengthened placed step `+3720 -> +7260 -> +7348` in Block `333` under
`allocMemcpyVmSpec`: when `<PolyEncoder>::from_pb` returns `.ok enc` at `fsp + 1888`, moves
`polyEncoderAt` from `fsp + 1888..2288` to `fsp + 1392..1792`, stores `p1` to `[sp, #0xc8]`
(`fsp + 200`) and `v7_polyEncoderTag enc` to `[sp, #0x10]` (`fsp + 16`), and sets `pstate`
according to `cmn x22, #0x1` (`addsPState64 cap_dec 1#64`) with `VmPreserved s1 sm`. -/
theorem v7_enc_ok_move_3720_to_7348_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hmemcpy_ok :
      subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7348#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.ok enc) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 896#64) 56 ∗
        ((fsp + 16#64) ↦₆₄ slot16_old) ∗
        ((fsp + 200#64) ↦₆₄ slot200_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          polyEncoderAt A (fsp + 1392#64) enc ∗
          memRegion (fsp + 896#64) 56 ∗
          ((fsp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hmemcpy :
      subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpyVmAcpSpec allocHookStack) :=
    subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm allocHookStack hmemcpy_ok
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, allocHookStack, stackAt] at hmemcpy
  wp_conv_pre =>
    rw [v7_resultPolyEncoder_ok_eq, v7_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v7_polyEncoderAt_relocate_1888_to_1392 A s1.sp enc)
      (sepConj_mono (v7_memRegion_1392_400_split_32_368 s1.sp)
        (sepConj_mono_left (v7_memRegion_896_56_split_24_32 s1.sp))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro e24
  apply ProofLib.SepWP.exists_left; intro e16
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e0
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro tail368
  apply ProofLib.SepWP.exists_left; intro P_heap
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜(((s1.sp + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      ((s1.sp + 1400#64) ↦₆₄ w8) ∗
      ((s1.sp + 1408#64) ↦₆₄ w16) ∗
      ((s1.sp + 1416#64) ↦₆₄ w24) ∗
      ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗ P_heap ⊢
        polyEncoderAt A (s1.sp + 1392#64) enc)⌝ ∗
    (memRegion (s1.sp - 4096#64) 4096 ∗
     memRegion (s1.sp - 5152#64) 1056 ∗
     (((s1.sp + 1888#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      ((s1.sp + 1896#64) ↦₆₄ w8) ∗
      ((s1.sp + 1904#64) ↦₆₄ w16) ∗
      ((s1.sp + 1912#64) ↦₆₄ w24) ∗
      ((s1.sp + 1920#64) ↦ₛ tail368.val) ∗
      P_heap) ∗
     (((s1.sp + 1392#64) ↦₆₄ e0) ∗
      ((s1.sp + 1400#64) ↦₆₄ e8) ∗
      ((s1.sp + 1408#64) ↦₆₄ e16) ∗
      ((s1.sp + 1416#64) ↦₆₄ e24) ∗
      memRegion (s1.sp + 1424#64) 368) ∗
     (((s1.sp + 896#64) ↦₆₄ d0) ∗
      ((s1.sp + 904#64) ↦₆₄ d8) ∗
      ((s1.sp + 912#64) ↦₆₄ d16) ∗
      memRegion (s1.sp + 920#64) 32) ∗
     ((s1.sp + 16#64) ↦₆₄ slot16_old) ∗
     ((s1.sp + 200#64) ↦₆₄ slot200_old) ∗
     Frame) by sep_ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hreloc
  change s1.pc = (blkPl_333).base + 3720#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7348#64) s1 _ _
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_333 blk333_noSvc0 (mid := lsρ "memcpy")
  intro m_strip
  wp_simp_pre [v7_fsp_1896_triple_rest, sepConj_assoc]
  wp_steps
  wp_simp_pre only [v7_fsp_1905_realign_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [v7_fsp_904_realign_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 : VmPreserved s1 _ :=
    hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  have hlen368 : (368 : Nat) = tail368.val.length := tail368.property.symm
  wp_simp_pre [hlen368, sepConj_assoc]
  wp_call hmemcpy (s1.sp + 1424#64, s1.sp + 1920#64, tail368.val)
  clear hlen368
  refine with_vm_from hvm1 (by assumption) fun hvm2 => ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_333 blk333_noSvc0 (mid := (blkPl_333).base + 7348#64)
  intro m_strip2
  wp_simp_pre only [v7_fsp_904_unrealign_w24_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v7_fsp_904_realign_w24_rest, sepConj_assoc]
  wp_step
  wp_simp_pre [v7_fsp_1400_triple_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step
  wp_simp_pre only [v7_fsp_1409_realign_rest, sepConj_assoc]
  wp_step
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real2 hnsp2 => ?_
  have hvm3 : VmPreserved _ _ :=
    hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm3 ⊢
  have hvm_all : VmPreserved s1 _ := vmPreserved_trans_congr hvm2 hvm3
  wp_simp_pre only
    [v7_fsp_904_unrealign_w24_rest, v7_1896_realign_final_rest, v7_1400_realign_final_rest,
     sepConj_assoc]
  refine align_pre_vm hvm_all ?_ ?_
  · have h1888_400 :=
      v7_1888_32_368_entails_memRegion_400 s1.sp (v7_polyEncoderTag enc) w8 w16 w24 tail368
    have h896_56 := v7_896_spill_entails_memRegion_56 s1.sp
      (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24)) (w24 >>> 8)
      ((d16 >>> 56).setWidth 8)
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s1.sp - 4096#64) 4096 ∗ memRegion (s1.sp - 5152#64) 1056) ∗
      (((s1.sp + 1888#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       ((s1.sp + 1896#64) ↦₆₄ w8) ∗ ((s1.sp + 1904#64) ↦₆₄ w16) ∗
       ((s1.sp + 1912#64) ↦₆₄ w24) ∗ ((s1.sp + 1920#64) ↦ₛ tail368.val)) ∗
      (((s1.sp + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       ((s1.sp + 1400#64) ↦₆₄ w8) ∗ ((s1.sp + 1408#64) ↦₆₄ w16) ∗
       ((s1.sp + 1416#64) ↦₆₄ w24) ∗ ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗ P_heap) ∗
      (((s1.sp + 896#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
       ((s1.sp + 904#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
       (((s1.sp + 912#64) ↦ₛ loBytes7 (w24 >>> 8)) ∗
        ((s1.sp + 919#64) ↦₈ (d16 >>> 56).setWidth 8)) ∗
       memRegion (s1.sp + 920#64) 32) ∗
      ((s1.sp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      ((s1.sp + 200#64) ↦₆₄ p1) ∗
      Frame by sep_ac_rfl)) ?_
    rw [← v7_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
    exact sepConj_mono (Entails.refl _) (sepConj_mono h1888_400
      (sepConj_mono hreloc (sepConj_mono h896_56 (Entails.refl _))))
  · wp_done

theorem v7_enc_ok_move_3720_to_7348_placed_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7348#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.ok enc) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 896#64) 56 ∗
        ((fsp + 16#64) ↦₆₄ slot16_old) ∗
        ((fsp + 200#64) ↦₆₄ slot200_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
          memRegion (fsp + 896#64) 56 ∗
          ((fsp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_enc_ok_move_3720_to_7348_placed hA.memcpy_ok s0 s1 fsp out pbA cap_dec c2 l1 p1 x21_val
    slot16_old slot200_old enc Frame hfsp_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

theorem v7_enc_ok_move_3720_to_7348_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7348#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.ok enc) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 896#64) 56 ∗
        ((fsp + 16#64) ↦₆₄ slot16_old) ∗
        ((fsp + 200#64) ↦₆₄ slot200_old) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
          memRegion (fsp + 896#64) 56 ∗
          ((fsp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_enc_ok_move_3720_to_7348_placed (A := A.repAlloc) hA.memcpy_ok
    s0 s1 fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old enc
    (Frame ∗ A.pool lim st s1)
    hfsp_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

theorem v7_enc_ok_move_3720_to_7348_of_budgetHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7348#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.ok enc) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 896#64) 56 ∗
        ((fsp + 16#64) ↦₆₄ slot16_old) ∗
        ((fsp + 200#64) ↦₆₄ slot200_old) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
          memRegion (fsp + 896#64) 56 ∗
          ((fsp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_enc_ok_move_3720_to_7348_placed_budget A lim st hA.toPlacedBudget
    s0 s1 fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old enc Frame
    hfsp_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

/-! ## 2. `s.receivingEk = none` Cleanup (`+7348 -> +10556 -> +4632`) -/

/-- Budget-threaded placed cleanup when `s.receivingEk = none` (`cap_dec = noneCap`,
`s1.pstate = addsPState64 noneCap 1#64`): steps `+7348 -> +10556`, drops `enc` at
`fsp + 1392..1792`, deallocates all 5 vectors of `uc` via `v7_cleanup_10556_placed`, and
reaches `+4632` under `FreeOnlyEvs`. -/
theorem v7_enc_ok_none_dec_7348_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((pbA + 184#64) ↦₆₄ noneCap) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) noneCap none) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hm_dec :
      ((pbA + 184#64) ↦₆₄ noneCap) ∗
      v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) noneCap none ⊢
      memRegion (pbA + 184#64) 40 := by
    unfold v7_optProtoPolyDecoderTail
    exact optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono
        (v7_ct1SentHeap_entails_dealloc A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5)
        (sepConj_mono_left hm_dec))))))) ?_
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 10556#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
      (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
       vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
       vecCapPtrDealloc A.repAlloc c5 p5) ∗
      memRegion (pbA + 184#64) 40 ∗
      A.pool lim st sm ∗
      Frame)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 7348#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10556#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 10556#64)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx24_2, htr2⟩
    rw [v7_ct1SentWordsAt_1264_eq_spill_other]
    have h10556 := v7_cleanup_10556_placed hA s0 s2 out c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 enc st
      (v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ∗
       memRegion (pbA + 184#64) 40 ∗ Frame)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx24_2 htr2
    refine SepWP.weaken_pre ?_ (SepWP.mono h10556 ?_)
    · exact Entails.of_eq (by sep_ac_rfl)
    · intro s3 P3 _ _ ⟨evs, hevs, hP3, hq⟩
      refine ⟨evs, hevs, Entails.trans hP3 ?_, hq⟩
      have h1264 :
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ⊢
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 := by
        rw [← v7_ct1SentWordsAt_1264_eq_spill_other]
        exact v7_ct1SentWordsAt_entails_128 ((s0.sp - 2400#64) + 1264#64)
          c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
      refine Entails.trans (Entails.of_eq (show _ =
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         memRegion (pbA + 184#64) 40 ∗
         A.pool lim (M.stepEvents evs st) s3 ∗
         Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h1264) (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. `<PolyDecoder>::from_pb` Copy (`+7348 -> +7400`) and Call (`+7400 -> lsmpl.base 376`) -/

/-- `VmPreserved`-strengthened placed copy of `ProtoPolynomialDecoder` (`40`B) from `pbA + 184`
to `fsp + 1848` (`sp + 0x738`) and setup of `x0 = fsp + 1888`, `x1 = fsp + 1848`,
`x22 = fsp + 1888` across `+7348 -> +7400` in Block `333`. -/
theorem v7_copy_dec_7348_to_7400_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 x21_val x23_val : BitVec 64)
    (decPb : ProtoPolynomialDecoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_dec : cap_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hpstate1 : s1.pstate = addsPState64 cap_dec 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7400#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some decPb) ∗
        memRegion (fsp + 1848#64) 40 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (pbA + 184#64) 40 ∗
          protoPolynomialDecoderAt A (fsp + 1848#64) decPb ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_copy_dec_7348_to_7400_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA cap_dec c2 l1 x21_val x23_val decPb Frame hfsp_align hcap_dec
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx23_1) (by simpa using hx24_1) (by simpa using hx26_1)
      (by simpa using hx27_1) (by simpa using hpstate1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx24_m, by simpa using hx26_m,
       by simpa using hx27_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_copy_dec_7348_to_7400_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 x21_val x23_val : BitVec 64)
    (decPb : ProtoPolynomialDecoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_dec : cap_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hpstate1 : s1.pstate = addsPState64 cap_dec 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7400#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (some decPb) ∗
        memRegion (fsp + 1848#64) 40 ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (pbA + 184#64) 40 ∗
          protoPolynomialDecoderAt A.repAlloc (fsp + 1848#64) decPb ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_copy_dec_7348_to_7400_placed (A := A.repAlloc) (ext := ext)
    s0 s1 fsp out pbA cap_dec c2 l1 x21_val x23_val decPb (Frame ∗ A.pool lim st s1)
    hfsp_align hcap_dec hpc1 hrun1 hsp1
    hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hpstate1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

alias v7_copy_dec_7352_to_7400_placed := v7_copy_dec_7348_to_7400_placed
alias v7_copy_dec_7352_to_7400_placed_budget := v7_copy_dec_7348_to_7400_placed_budget

/-- `VmPreserved`-strengthened placed `bl` instruction at `+7400` in Block `333` jumping to
`<PolyDecoder>::from_pb` entry (`lsmpl.base 376`). -/
theorem v7_bl_decoder_7400_to_35448_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA c2 l1 x21_val x23_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 7400#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1848#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 7404#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_bl_decoder_7400_to_35448_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA c2 l1 x21_val x23_val P
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx0_1) (by simpa using hx1_1) (by simpa using hx19_1)
      (by simpa using hx21_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx24_1) (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx24_m, by simpa using hx26_m,
       by simpa using hx27_m, by simpa using hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_bl_decoder_7400_to_35448_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA c2 l1 x21_val x23_val : BitVec 64)
    (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 7400#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1848#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1 (Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 7404#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_bl_decoder_7400_to_35448_placed (ext := ext)
    s0 s1 fsp out pbA c2 l1 x21_val x23_val (Rest ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 4. `<PolyDecoder>::from_pb = Err` Cleanup (`+7404 -> +11096 -> +4632`) -/

/-- Budget-threaded placed cleanup when `<PolyDecoder>::from_pb` returns `.error err` at
`fsp + 1888`: steps `+7404 -> +11096`, drops `enc` (`fsp + 1392..1792`) and `uc`
(`fsp + 1264..1392`) via `v7_cleanup_11096_placed`, and reaches `+4632` under `FreeOnlyEvs`. -/
theorem v7_dec_err_7404_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hpack_uc :
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
      unchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc := by
    rw [← v7_ct1SentAt_eq_unchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc]
    exact v7_ct1SentAt_pack A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
    (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
     v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
     A.pool lim st s1 ∗ Frame) by sep_ac_rfl))
    (sepConj_mono (v7_resultPolyDecoder_err_entails_tag_392 A.repAlloc (s0.sp - 2400#64) err)
      (sepConj_mono_left hpack_uc))) ?_
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 11096#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
      unchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc ∗
      A.pool lim st sm ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 7404#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 11096#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 11096#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      have hm400 := v7_1888_tag_392_to_memRegion_400 (s0.sp - 2400#64) 18446744073709551615#64
      refine Entails.trans (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 18446744073709551615#64) ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
         unchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc ∗
         A.pool lim st _ ∗
         Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm400) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    refine SepWP.mono
      (v7_cleanup_11096_placed hA s0 s2 out enc uc st
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Frame)
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2) ?_
    intro s3 P3 _ _ ⟨evs, hevs, hP3, hq⟩
    exact ⟨evs, hevs, Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl)), hq⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7hPlacedBudget
