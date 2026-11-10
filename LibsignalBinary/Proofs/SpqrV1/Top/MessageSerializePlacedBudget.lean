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
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen -- shake: keep
meta import ProofLib.SepLogic.WP.Apply -- shake: keep
meta import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Budget-Threaded Relocatable Verification of `<Message>::serialize`

Proves the allocation-budget `MessageSerializePlacedOkX` contract for
`<spqr::v1::chunked::states::Message>::serialize` (Block `352`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_320 blkPl_320
   extract_withLsCodeLoaded libsignalSessionLib lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (MAX_VARINT_BYTES_LEN Message MessagePayload MessageType PolyApi
   encodeVarintLoop encode_chunk encode_varint)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkIndexOff)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack reserveCap sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost SepWPp.call_cs_placed SepWPp.of_sepWP_cs_placed StepInvPlaced
   bv_len_add_one vecU8Buf vecU8Buf_eq_open_one vecU8Buf_snoc_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (false_eq_true')
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (len_beq_cap_false sp_sub_80_aligned spqrEncodeVarintStackX)
open CryptoVerification.SpqrV1.Top.Placed
  (blkLib_eq_352 blkPC_326 blkPl_326 blkPC_352 blkPl_352)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost MsgSerializeCalleeSavedPlaced
   encodeVarintLoop_length_le encode_varint_length_le
   extractLsb_hi_append64 extractLsb_lo_append64 list_eq_unpack64_4_of_len32
   memRegion_40_split_1_39 messageAt messagePayloadAt messageSerializeStackX
   pointsToBytes_unpack64_4_eq rem40_ult_31_of_gt rem40_ult_31_of_le
   stackAt_messageSerialize_eq stackAt_spqrEncodeVarint_to_allocHook
   stackAt_spqrEncodeVarint_to_doReserve subroutine_ok_withStepInvPlaced_of_block
   vecU8At_eq_header_buf vecU8At_init_40_one vecU8At_sp72_eq
   vecU8Buf_append_32_eq vecU8Buf_eq_open_32 withStepInvPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
   rustCliReallocBudgetSpec rustReallocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStack subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (doReserveSpec do_reserve_7_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
  (memRegion_24 session2ShimSpecWithStack session2ShimWithStack_of_noAllocShim)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
  (SpqrEncodeVarintEnv spqrEncodeVarintEvents_of_spare spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget
  (SpqrEncodeVarintPlacedOkExt SpqrEncodeVarintPlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (MessageSerializeEnv fitsEnv_messageSerialize_iff messageSerializeEnv_events
   messageSerializeEvents messageSerializeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  false_eq_true' extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. Re-Exports & Relocatable Target Predicate -/

export LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (messageSerializeEvents MessageSerializeEnv messageSerializeEnv_events
   fitsEnv_messageSerialize_iff messageSerializeSpecX)

/-- `<spqr::v1::chunked::states::Message>::serialize` (Block `352`) meets `withLsCodeLoaded
    lsmpl (messageSerializeSpecX P_api A lim)` on `libsignalSessionLib.blockProgram lsmpl 352
    (Rust.withPanics ext)`. -/
def MessageSerializePlacedOkX [LibsignalPlacement] (P_api : PolyApi) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 352 (Rust.withPanics ext))
    (lsmpl.base 352)
    (withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A lim))

private theorem fitsEvents_alloc40_of_messageSerialize {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {P_api : PolyApi} {x : MessageSerializeGhost P_api}
    (h : FitsEvents M lim st (messageSerializeEvents P_api x)) :
    FitsEvents M lim st (rustAllocEvents 40 1) := by
  unfold messageSerializeEvents at h
  cases hpay : x.msg.payload <;> simp only [hpay] at h
  · exact h
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · exact h
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1

private theorem shim_placed_ok [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec) :
    subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      (session2ShimSpecWithStack allocHookStack) :=
  session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim)

private theorem alloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
  subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem halloc))

private theorem doReserveEvents_40_32 (v ptr : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length ≤ 32) :
    doReserveEvents (DoReserveCall.mk v 40#64 ptr curBs 32) = rustReallocEvents 40 80 1 := by
  have hres :
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap
        (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap reserveCap
    change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hne : (40#64 : BitVec 64) ≠ 0#64 := by decide
  unfold doReserveEvents
  simp only [hne, ↓reduceIte, hres]; rfl

/-! ## 2. Placed Callee Call Helpers (`spqr::encode_varint` & `do_reserve_and_handle [local#7]`) -/

/-- Execute a `bl spqr::encode_varint` (`lsmpl.base 326`) call inside `<Message>::serialize`
    (Block `352`) when `cap = 40#64` and `curBs.length + 10 ≤ 40`, preserving `cap = 40#64`,
    `ptr`, and budget state `st`. -/
theorem step_call_spqrEncodeVarint_40_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State}
    (henc : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 326) (withStepInvPlaced s0 (spqrEncodeVarintSpecX A lim)))
    (val v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (st : M.σ)
    (hlen : curBs.length + 10 ≤ 40)
    {x : MessageSerializeGhost P_api} {st0 : M.σ} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 326)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v 40#64 ptr curBs ∗ A.pool lim st s ∗
      stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) sm
        ((vecU8At A.repAlloc v 40#64 ptr (encode_varint val curBs) ∗
          A.pool lim st sm ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  have hloop_le :
      curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤
        (40#64 : BitVec 64).toNat := by
    have h1 := encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN val
    have hm : MAX_VARINT_BYTES_LEN = 10 := rfl
    change curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤ 40; omega
  have hevs_nil := spqrEncodeVarintEvents_of_spare
    (x := EncodeVarintGhost.mk val v 40#64 ptr curBs) hloop_le
  have hfits_enc : FitsEnv M lim st
      (SpqrEncodeVarintEnv (EncodeVarintGhost.mk val v 40#64 ptr curBs)) := by
    intro evs hevs
    dsimp only [SpqrEncodeVarintEnv] at hevs
    rw [hevs, hevs_nil]
    trivial
  refine SepWPp.call_cs_placed (x := (EncodeVarintGhost.mk val v 40#64 ptr curBs, st)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withStepInvPlaced, spqrEncodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs.2.2.2.2.2.2.2, ⟨hx0, hx1, Or.inl hlen, hfits_enc⟩,
      by convert hm using 1; sep_ac_rfl⟩
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ hm
    dsimp only [withStepInvPlaced, spqrEncodeVarintSpecX] at hm
    rw [sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInvPlaced, spqrEncodeVarintSpecX, hsp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun htrm =>
      SepWPp.pure_elim fun hcap_prop => ?_
    obtain ⟨hcap_eq, hptr_eq⟩ := hcap_prop.2 hloop_le
    rw [hcap_eq, hptr_eq]
    refine SepWPp.weaken_pre (P' := ⌜evs = []⌝ ∗
        ((vecU8At A.repAlloc v 40#64 ptr (encode_varint val curBs) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F))
      (Entails.of_eq (by
        simp only [SpqrEncodeVarintEnv, hevs_nil]
        sep_ac_rfl))
      (SepWPp.pure_elim fun hevs_eq => ?_)
    subst hevs_eq
    simpa only [AllocCostModel.stepEvents_nil] using
      hnext sm hpcm hrunm hspm (htrm.trans htr)
        hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
        (hcs.trans (MsgSerializeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))

/-- Execute `bl do_reserve_and_handle [local#7]` (`lsmpl.base 320`) inside
    `<Message>::serialize` (Block `352`) when `cap = 40#64`, `curBs.length ≤ 32`, and
    `additional = 32`, growing capacity to `80#64`. -/
theorem step_call_doReserve7_40_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hres7 : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 320) (withStepInvPlaced s0 (doReserveSpec M A lim)))
    (v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (st1 : M.σ)
    (hlen : curBs.length ≤ 32)
    (hfits_res : FitsEvents M lim st1 (rustReallocEvents 40 80 1))
    {x : MessageSerializeGhost P_api} {st0 : M.σ} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 320)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 32#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v 40#64 ptr curBs ∗ A.pool lim st1 s ∗
      stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ (sm : State) (ptr' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) sm
        ((vecU8At A.repAlloc v 80#64 ptr' curBs ∗
          A.pool lim (M.stepEvents (rustReallocEvents 40 80 1) st1) sm ∗
          stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  have hres_eq : reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold reserveCap; change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hres_eq' :
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap
        (40#64 : BitVec 64).toNat curBs.length 32 = 80 := hres_eq
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  have hevs_eq := doReserveEvents_40_32 v ptr curBs hlen
  have hfits_env : FitsEnv M lim st1 (DoReserveEnv (DoReserveCall.mk v 40#64 ptr curBs 32)) := by
    rw [fitsEnv_doReserve_iff, hevs_eq]; exact hfits_res
  refine SepWPp.call_cs_placed (x := (DoReserveCall.mk v 40#64 ptr curBs 32, st1))
    (F := memRegion (sp - 80#64 - 16464#64) 12256 ∗ F)
    hres7 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)] at hm
    simp only [withStepInvPlaced, doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs.2.2.2.2.2.2.2, ⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, by rw [hres_eq']; decide, hfits_env⟩,
      by convert hm using 1; sep_ac_rfl⟩
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ hm
    dsimp only [withStepInvPlaced, doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack] at hm
    rw [sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInvPlaced, doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      hsp, hres_eq, hevs_eq, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm ptr' hpcm hrunm hspm (htrm.trans htr)
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
      (hcs.trans (MsgSerializeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Epilogue & Chunk Step Lemmas -/

private def poolPostAt (P_api : PolyApi) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : MessageSerializeGhost P_api)
    (st0 : M.σ) (sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜MessageSerializeEnv P_api x evs⌝ ∗
    A.pool lim (M.stepEvents evs st0) sf

/-- Shared return tail (`+0x168..+0x188`, `360..392`). -/
theorem step_msgSerialize_ret_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ) (evsDone : List AllocEvent)
    (capFinal ptrFinal v80 v56 r0 r1 r2 : BitVec 64) (bsFinal : List (BitVec 8))
    (hser : bsFinal = x.msg.serialize x.index)
    (hevs : MessageSerializeEnv P_api x evsDone)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 bsFinal.length) (hx19 : s.readReg64 .x19 = x.ret)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (((s0.sp - 72#64) ↦₆₄ capFinal) ∗ ((s0.sp - 64#64) ↦₆₄ ptrFinal) ∗
       ((s0.sp - 56#64) ↦₆₄ v56) ∗ vecU8Buf A.repAlloc capFinal ptrFinal bsFinal ∗
       messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents evsDone st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  subst hP
  rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs, _⟩
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
  intro hm_f
  have hvec_pack :
      (x.ret ↦₆₄ capFinal) ∗ ((x.ret + 8#64) ↦₆₄ ptrFinal) ∗
      ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (x.msg.serialize x.index).length) ∗
      vecU8Buf A.repAlloc capFinal ptrFinal bsFinal =
      vecU8At A.repAlloc x.ret capFinal ptrFinal (x.msg.serialize x.index) := by
    rw [← hser, vecU8At_eq_header_buf]
  show _ ⊨ (⌜_ = s0.trace⌝ ∗ messageAt P_api x.msgA x.msg ∗
      vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
      poolPostAt P_api A lim x st0 _ ∗
      stackAt s0.sp messageSerializeStackX) ∗ R
  simp only [vecU8, stackAt_messageSerialize_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v80, capFinal, ptrFinal, v56,
    s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x22, s0.readReg64 .x21,
    s0.readReg64 .x20, s0.readReg64 .x19, capFinal, ptrFinal, by simp only [arm64_norm, *], ?_⟩
  rw [← hvec_pack]; unfold poolPostAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc]
  refine ⟨evsDone, ?_⟩
  rw [eq_true hevs, pure_true_sepConj]
  convert hm_f using 1; sep_ac_rfl

/-- Non-chunk epilogue (`+0x15c..+0x188`, `348..392`). -/
theorem step_msgSerialize_epilogue_no_chunk_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ)
    (ptr v80 r0 r1 r2 : BitVec 64) (bs2 : List (BitVec 8)) (tag : BitVec 8)
    (hlt40 : bs2.length < (40#64 : BitVec 64).toNat)
    (hser : bs2 ++ [tag] = x.msg.serialize x.index)
    (hevs : MessageSerializeEnv P_api x (rustAllocEvents 40 1))
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length)
    (hx22 : (s.readReg64 .x22).setWidth 8 = tag) (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
       messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents (rustAllocEvents 40 1) st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  subst hP
  have hlen1 := bv_len_add_one bs2 tag
  rw [vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs2,
    vecU8Buf_eq_open_one A.repAlloc 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 360#64)
  wp_steps_sync_pool ((blkPl_352).base + 360#64)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact step_msgSerialize_ret_placed A lim ext x st0 (rustAllocEvents 40 1)
    40#64 ptr v80 (BitVec.ofNat 64 bs2.length) r0 r1 r2
    (bs2 ++ [tag]) hser hevs
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step⟩)
    (by rw [← vecU8Buf_snoc_eq A.repAlloc 40#64 ptr bs2 tag hlt40]; sep_ac_rfl)

/-- Chunk 32-byte copy and epilogue (`+0x13c..+0x158` + `+0x168..+0x188`, `316..344` +
    `360..392`). -/
theorem step_msgSerialize_copy_and_epilogue_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ) (evsDone : List AllocEvent)
    (c : P_api.Chunk) (capFinal ptrFinal v80 r0 r1 r2 : BitVec 64)
    (bs4 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hle32 : bs4.length + 32 ≤ capFinal.toNat)
    (hser : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index)
    (hevs : MessageSerializeEnv P_api x evsDone)
    (hmsg_eq :
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (vecU8At A.repAlloc (s0.sp - 72#64) capFinal ptrFinal bs4 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents evsDone st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  subst hP
  have hdata_len : (P_api.chunkData c).toList.length = 32 := (P_api.chunkData c).property
  obtain ⟨w0, w1, w2, w3, hw⟩ := list_eq_unpack64_4_of_len32 (P_api.chunkData c).toList hdata_len
  have hchunk_unfold :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦₆₄ w0) ∗
        ((x.msgA + 0x12#64) ↦₆₄ w1) ∗
        ((x.msgA + 0x1a#64) ↦₆₄ w2) ∗
        ((x.msgA + 0x22#64) ↦₆₄ w3) ∗
        ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; dsimp only
    rw [hw, pointsToBytes_unpack64_4_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  have hlen32_bv :
      BitVec.ofNat 64 bs4.length + 32#64 =
        BitVec.ofNat 64 (bs4 ++ (P_api.chunkData c).toList).length := by
    simp only [List.length_append, hdata_len, BitVec.ofNat_add]
  rw [hchunk_unfold, vecU8At_sp72_eq A.repAlloc s0.sp capFinal ptrFinal bs4,
    vecU8Buf_eq_open_32 A.repAlloc capFinal ptrFinal bs4 hle32]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 360#64)
  wp_steps_sync_pool ((blkPl_352).base + 360#64)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact step_msgSerialize_ret_placed A lim ext x st0 evsDone capFinal ptrFinal v80
    (BitVec.ofNat 64 bs4.length) r0 r1 r2
    (bs4 ++ (P_api.chunkData c).toList) hser hevs
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step⟩)
    (by rw [← vecU8Buf_append_32_eq A.repAlloc capFinal ptrFinal bs4 (P_api.chunkData c).toList
          w0 w1 w2 w3 hle32 hw hdata_len, ← hmsg_eq, hchunk_unfold]; sep_ac_rfl)

/-- Full chunk branch (`+0x10c..+0x188` & `+0x190..+0x1ac`, `268..392` & `400..428`). -/
theorem step_msgSerialize_chunk_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hres7 : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 320) (withStepInvPlaced s0 (doReserveSpec M A lim)))
    (henc : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 326) (withStepInvPlaced s0 (spqrEncodeVarintSpecX A lim)))
    (x : MessageSerializeGhost P_api) (st0 : M.σ)
    (hfits_all : FitsEvents M lim st0 (messageSerializeEvents P_api x))
    (c : P_api.Chunk) (ptr v80 r0 r1 r2 : BitVec 64)
    (bs2 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hlen21 : bs2.length ≤ 21)
    (hser : encode_chunk c (bs2 ++ [tag]) = x.msg.serialize x.index)
    (hevs_chunk : messageSerializeEvents P_api x =
      (let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
       if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
       else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1))
    (hmsg_eq :
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length) (hx22 : (s.readReg64 .x22).setWidth 8 = tag)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents (rustAllocEvents 40 1) st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  subst hP
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by change bs2.length < 40; omega
  have hlen1 := bv_len_add_one bs2 tag
  have hchunk_idx :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦ₛ (P_api.chunkData c).toList) ∗
        ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hchunk_idx, vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs2,
    vecU8Buf_eq_open_one A.repAlloc 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 326)
  wp_steps_sync_pool (lsmpl.base 326)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step1
  have hvec_bs3 := (vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr (bs2 ++ [tag])).symm
  refine step_call_spqrEncodeVarint_40_placed (P_api := P_api) (x := x) (st0 := st0) (R := R)
    A lim ext henc ((P_api.chunkIndex c).zeroExtend 64) (s0.sp - 72#64) ptr s0.sp ((blkPl_352).base + 296#64)
    (bs2 ++ [tag]) (M.stepEvents (rustAllocEvents 40 1) st0)
    (by simp only [List.length_append, List.length_singleton]; omega)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step1⟩)
    (by rw [hchunk_idx, ← hvec_bs3, ← vecU8Buf_snoc_eq A.repAlloc 40#64 ptr bs2 tag hlt40]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx19m hx20m _ _ _ hcsm
  have hx19m' : sm.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
  have hx20m' : sm.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
  let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
  have hbs4_len : bs4.length ≤ 32 := by
    have := encode_varint_length_le ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
    simp only [List.length_append, List.length_singleton] at this; dsimp only [bs4]; omega
  have hser4 : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index := hser
  change SepWPp _ _ sm ((vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs4 ∗ _) ∗ _) _ _
  rw [vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs4]
  by_cases hle32 : bs4.length + 32 ≤ 40
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_le hle32
    have hevs_le : MessageSerializeEnv P_api x (rustAllocEvents 40 1) := by
      unfold MessageSerializeEnv
      rw [hevs_chunk]; dsimp only [bs4] at hle32; simp only [hle32, ↓reduceIte]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 316#64)
    wp_steps_sync_pool ((blkPl_352).base + 316#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    exact step_msgSerialize_copy_and_epilogue_placed A lim ext x st0 (rustAllocEvents 40 1)
      c 40#64 ptr v80 r0 r1 r2 bs4 tag msgTail hle32 hser4 hevs_le hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_gt hle32 (by dsimp only [bs4] at hbs4_len ⊢; omega)
    have hevs_gt_eq : messageSerializeEvents P_api x =
        rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      rw [hevs_chunk]; dsimp only [bs4] at hle32; simp only [hle32, ↓reduceIte]
    have hevs_gt : MessageSerializeEnv P_api x
        (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1) :=
      hevs_gt_eq.symm
    have hfits_realloc :
        FitsEvents M lim (M.stepEvents (rustAllocEvents 40 1) st0) (rustReallocEvents 40 80 1) := by
      rw [hevs_gt_eq] at hfits_all
      exact ((fitsEvents_append M lim _ _ st0).mp hfits_all).2
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 320)
    wp_steps_sync_pool (lsmpl.base 320)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    refine step_call_doReserve7_40_placed (P_api := P_api) (x := x) (st0 := st0) (R := R)
      A lim ext hres7 (s0.sp - 72#64) ptr s0.sp ((blkPl_352).base + 420#64) bs4
      (M.stepEvents (rustAllocEvents 40 1) st0) hbs4_len hfits_realloc
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl) ?_
    intro sm2 ptr' hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
    have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
    have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
    rw [vecU8At_sp72_eq A.repAlloc s0.sp 80#64 ptr' bs4, ← M.stepEvents_append]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 316#64)
    wp_steps_sync_pool ((blkPl_352).base + 316#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step3
    have hle80 : bs4.length + 32 ≤ (80#64 : BitVec 64).toNat := by
      change bs4.length + 32 ≤ 80; dsimp only [bs4] at hbs4_len ⊢; omega
    exact step_msgSerialize_copy_and_epilogue_placed A lim ext x st0
      (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1)
      c 80#64 ptr' v80 r0 r1 r2 bs4 tag msgTail hle80 hser4 hevs_gt hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step3⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)

/-! ## 4. Entry Block & Relocatable Top-Level Theorems -/

/-- Entry block (`+0x000..+0x060`, `0..96`): saves callee-saved registers, allocates 40-byte
    buffer via `__rust_alloc(40, 1)` under `FitsEvents M lim st0 (rustAllocEvents 40 1)`, writes
    `[1#8]`, and executes the first two `spqr::encode_varint` calls (`x.msg.epoch` and
    `x.index.zeroExtend 64`), arriving at `(blkPl_352).base + 96#64`. -/
theorem step_msgSerialize_entry_placed [LibsignalPlacement] {P_api : PolyApi}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    {s0 : State}
    (henc : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 326) (withStepInvPlaced s0 (spqrEncodeVarintSpecX A lim)))
    (x : MessageSerializeGhost P_api) (st0 : M.σ)
    (hfits40 : FitsEvents M lim st0 (rustAllocEvents 40 1))
    (v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2 : BitVec 64)
    {R P : SepProp} {Q : State → SepProp → Prop}
    (hpc0 : s0.pc = (blkPl_352).base)
    (hrun0 : s0.status = .Running) (halign : s0.sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.msgA) (hx1 : (s0.readReg64 .x1).setWidth 32 = x.index)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hP : P =
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool lim st0 s0 ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
      ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8))
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      let bs1 := encode_varint x.msg.epoch [1#8]
      let bs2 := encode_varint (x.index.zeroExtend 64) bs1
      sm.pc = (blkPl_352).base + 96#64 →
      sm.status = .Running → sm.sp = s0.sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.msgA →
      MsgSerializeCalleeSavedPlaced s0 sm → bs2.length ≤ 21 →
      SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) sm
        (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
         (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
         (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
         A.pool lim (M.stepEvents (rustAllocEvents 40 1) st0) sm ∗
         stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hshim_stk := shim_placed_ok hshim
  have halloc_stk := alloc_placed_ok halloc
  subst hP
  rw [stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64)]
  have hsp0 : s0.spAligned = true := by simp only [State.spAligned, beq_iff_eq]; exact halign
  have hpos40 : 0 < 40 := by decide
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbound40 : 40 + 1 ≤ 2 ^ 63 := by decide
  have hal31 : 1 ≤ 2 ^ 31 := by decide
  have hlay40 : RustLayoutOk 40 1 := ⟨⟨hpos40, hpow1, hbound40⟩, hal31⟩
  rcases hfits40 with ⟨⟨hmax40, henf, hram, hva⟩, _⟩
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 52#64)
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim_stk ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc_stk
  wp_call halloc_stk (40, 1, st0)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_step0
  have hoom : sf_1.readReg64 .x0 ≠ 0#64 := by assumption
  have hoom_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  rw [memRegion_40_split_1_39 (sf_1.readReg64 .x0)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 326)
  wp_steps_sync_pool (lsmpl.base 326)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step1
  have hsp_sf : sf.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  refine step_call_spqrEncodeVarint_40_placed (P_api := P_api) (x := x) (st0 := st0) (R := R)
    A lim ext henc x.msg.epoch (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp ((blkPl_352).base + 84#64)
    [1#8] (M.stepEvents (rustAllocEvents 40 1) st0) (by decide)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv_step0.trans hinv_step1⟩ <;>
      simp only [wp_norm, arm64_norm, *])
    (by
      have hinit := vecU8At_init_40_one A.repAlloc (s0.sp - 72#64) (sf_1.readReg64 .x0) hoom
      simp only [arm64_norm] at hinit
      have hlive_eq : A.live (sf_1.readReg64 .x0) 40 1 = A.repAlloc.live (sf_1.readReg64 .x0) 40 1 := rfl
      rw [hsp_sf, hlive_eq, ← hinit, stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64),
        show s0.sp - 80#64 - 16464#64 = s0.sp - 16544#64 by bv_omega]
      simp only [arm64_norm]
      sep_ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19m1 hx20m1 hx21m1 _ _ hcsm1
  have hx19m1' : sm1.readReg64 .x19 = x.ret := by simp only [wp_norm, arm64_norm, *]
  have hx20m1' : sm1.readReg64 .x20 = x.msgA := by simp only [wp_norm, arm64_norm, *]
  have hx21m1' : (sm1.readReg64 .x21).setWidth 32 = x.index := by
    rw [hx21m1]; simp only [wp_norm, arm64_norm, *]
  let bs1 := encode_varint x.msg.epoch [1#8]
  have hbs1_len : bs1.length ≤ 11 := by
    have := encode_varint_length_le x.msg.epoch [1#8]; simp only [List.length_singleton] at this; omega
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 326)
  wp_steps_sync_pool (lsmpl.base 326)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step2
  refine step_call_spqrEncodeVarint_40_placed (P_api := P_api) (x := x) (st0 := st0) (R := R)
    A lim ext henc (x.index.zeroExtend 64) (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp ((blkPl_352).base + 96#64)
    bs1 (M.stepEvents (rustAllocEvents 40 1) st0) (by omega)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcsm1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
    (by sep_ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
  have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
  have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
  have hbs2_len :
      (encode_varint (x.index.zeroExtend 64) bs1).length ≤ 21 := by
    have := encode_varint_length_le (x.index.zeroExtend 64) bs1; omega
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sm2 (sf_1.readReg64 .x0) hpcm2 hrunm2 hspm2 htrm2 hx19m2' hx20m2' hcsm2 hbs2_len)

private theorem messageSerialize_placed_ok_blk_core [LibsignalPlacement] (P_api : PolyApi)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hres7 : subroutine_ok ((blkPC_320).rebase (blkPl_320).base (Rust.withPanics ext))
      (blkPl_320).base (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (henc_blk : subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
      (blkPl_326).base (withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A lim))) :
    subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (blkPl_352).base
      (withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A lim)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre hsp0
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hres7_s0 := subroutine_ok_withStepInvPlaced_of_block
    (callerProg := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) hcl0 hres7
  have henc_s0 := subroutine_ok_withStepInvPlaced_of_block
    (callerProg := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) hcl0 henc_blk
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp0
  simp only [messageSerializeSpecX, messageAt, memRegion_24, stackAt_messageSerialize_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, r2, r1, r0,
    ⟨hx0, hx1, hx8, hfits_env⟩, hpre⟩
  have hfits_all : FitsEvents M lim st0 (messageSerializeEvents P_api x) :=
    (fitsEnv_messageSerialize_iff P_api x).mp hfits_env
  have hfits40 : FitsEvents M lim st0 (rustAllocEvents 40 1) :=
    fitsEvents_alloc40_of_messageSerialize hfits_all
  refine ⟨(x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool lim st0 s0 ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗ ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8),
    R, by convert hpre using 1; sep_ac_rfl,
    step_msgSerialize_entry_placed A lim ext h_panic hshim halloc henc_s0 x st0 hfits40
      v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2
      hpc0 hrun0 halign hx0 hx1 hx8 rfl ?_⟩
  intro sm ptr bs1 bs2 hpcm hrunm hspm htrm hx19m hx20m hcsm hbs2_len
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by
    change bs2.length < 40; dsimp only [bs2, bs1] at hbs2_len ⊢; omega
  have hbeq := len_beq_cap_false hlt40
  change SepWPp _ _ sm
    (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
     (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗ _) _ _
  rw [vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs2]
  cases hpay : x.msg.payload with
  | none =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 348#64)
    wp_steps_sync_pool ((blkPl_352).base + 348#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : bs2 ++ [0#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_eq : MessageSerializeEnv P_api x (rustAllocEvents 40 1) := by
      unfold MessageSerializeEnv messageSerializeEvents; simp only [hpay]
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 0#8) ∗ memRegion (x.msgA + 0x09#64) 39 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk_placed A lim ext x st0 ptr v80 r0 r1 r2 bs2 0#8
      hlt40 hser hevs_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq, ← hmsg_eq]; sep_ac_rfl)
  | ct1Ack b_ack =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 348#64)
    wp_steps_sync_pool ((blkPl_352).base + 348#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : bs2 ++ [4#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_eq : MessageSerializeEnv P_api x (rustAllocEvents 40 1) := by
      unfold MessageSerializeEnv messageSerializeEvents; simp only [hpay]
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 4#8) ∗
        ((x.msgA + 0x09#64) ↦₈ (if b_ack then 1#8 else 0#8)) ∗ memRegion (x.msgA + 0x0a#64) 38 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk_placed A lim ext x st0 ptr v80 r0 r1 r2 bs2 4#8
      hlt40 hser hevs_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq, ← hmsg_eq]; sep_ac_rfl)
  | hdr c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64)
    wp_steps_sync_pool ((blkPl_352).base + 268#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [1#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [1#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 1#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A lim ext hres7_s0 henc_s0 x st0 hfits_all c ptr v80 r0 r1 r2 bs2 1#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ek c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64)
    wp_steps_sync_pool ((blkPl_352).base + 268#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [2#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [2#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 2#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A lim ext hres7_s0 henc_s0 x st0 hfits_all c ptr v80 r0 r1 r2 bs2 2#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ekCt1Ack c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64)
    wp_steps_sync_pool ((blkPl_352).base + 268#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [3#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [3#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 3#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A lim ext hres7_s0 henc_s0 x st0 hfits_all c ptr v80 r0 r1 r2 bs2 3#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ct1 c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64)
    wp_steps_sync_pool ((blkPl_352).base + 268#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [5#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [5#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 5#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A lim ext hres7_s0 henc_s0 x st0 hfits_all c ptr v80 r0 r1 r2 bs2 5#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ct2 c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64)
    wp_steps_sync_pool ((blkPl_352).base + 268#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [6#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [6#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 6#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A lim ext hres7_s0 henc_s0 x st0 hfits_all c ptr v80 r0 r1 r2 bs2 6#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], hinv_step⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)

/-- `<spqr::v1::chunked::states::Message>::serialize` (Block `352`, 110 insns) meets
    `withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A lim)` on `(blkPC_352).rebase
    (blkPl_352).base (Rust.withPanics ext)`. -/
theorem messageSerialize_placed_ok_blk_x [LibsignalPlacement] (P_api : PolyApi)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hres7 : subroutine_ok ((blkPC_320).rebase (blkPl_320).base (Rust.withPanics ext))
      (blkPl_320).base (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (henc : SpqrEncodeVarintPlacedOkExt A lim ext) :
    subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (blkPl_352).base
      (withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A lim)) :=
  messageSerialize_placed_ok_blk_core P_api A lim ext h_panic hshim halloc hres7
    henc

/-- Relocatable `<Message>::serialize` (Block `352`) correctness theorem on `blockProgram lsmpl
    352`. -/
theorem messageSerialize_placed_ok_x [LibsignalPlacement] (P_api : PolyApi)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hres7 : subroutine_ok ((blkPC_320).rebase (blkPl_320).base (Rust.withPanics ext))
      (blkPl_320).base (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (henc : SpqrEncodeVarintPlacedOkExt A lim ext) :
    MessageSerializePlacedOkX P_api A lim ext := by
  unfold MessageSerializePlacedOkX
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))]
  exact messageSerialize_placed_ok_blk_x P_api A lim ext h_panic hshim halloc hres7 henc

/-- Convenience wrapper discharging `hres7` directly from `HookSat` contracts via
    `DoReserveBudget.do_reserve_7_placed_ok`. -/
theorem messageSerialize_placed_ok_blk_of_hooks [LibsignalPlacement] (P_api : PolyApi)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (henc : SpqrEncodeVarintPlacedOkExt A lim ext) :
    subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (blkPl_352).base
      (withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A lim)) :=
  messageSerialize_placed_ok_blk_x P_api A lim ext h_panic hshim halloc
    (do_reserve_7_placed_ok h_panic hshim halloc hrealloc) henc

/-- Convenience wrapper on `blockProgram lsmpl 352` discharging `hres7` directly from `HookSat`
    contracts AND accepting `SpqrEncodeVarintPlacedOkX A lim ext`. -/
theorem messageSerialize_placed_ok_of_hooks [LibsignalPlacement] (P_api : PolyApi)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (henc : SpqrEncodeVarintPlacedOkX A lim ext) :
    MessageSerializePlacedOkX P_api A lim ext := by
  unfold MessageSerializePlacedOkX
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))]
  have henc_blk : subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
      (blkPl_326).base (withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A lim)) := by
    unfold SpqrEncodeVarintPlacedOkX at henc
    rwa [← IsLsBlockProg.eq_blockProgram
      (prog := (blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))] at henc
  exact messageSerialize_placed_ok_blk_core P_api A lim ext h_panic hshim halloc
    (do_reserve_7_placed_ok h_panic hshim halloc hrealloc) henc_blk

end LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
