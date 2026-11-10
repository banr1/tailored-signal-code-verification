/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Phase 3 Segments 1–5 (`+0x3dc .. +0x5ac`)

Phase 3 allocator event lists and `FitsEvents` splitting lemmas, state-indexed no-panic sequencing
helpers, and relocatable `[LibsignalPlacement]` budget-threaded segment proofs for `compute_mac`
and MAC append, `ciphertext` and `pq_ratchet` cloning, `addresses` boxing, and 120-byte `sret` stores.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks LibsignalCodeLoaded withLsCodeLoaded lsmpl lsρ
   lsRustAllocSym lsRustNoAllocShimSym lsMemcpySym)
open CryptoVerification.RustHeap
  (allocHookStack vecU8At)
open CryptoVerification.LibsignalProtoCodec (encode)
open CryptoGames.HMAC (keyToBytes32)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SignalMessageGhost UuidParser noneCap okTagVec signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_63 blkPl_63 SignalMessageNewGhost TraceVRegsEq
   add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap add_one_eq_zero_iff_noneCap
   addresses_length append64_extract_hi append64_extract_lo
   boxU8Buf bv_add_8_sub_self computeMacStack computeMacStackX
   encode_protoMsg_length_bounds framelessMemcpySpec mac_ls_externAt?_of_mem
   memRegion_16_eq_cells2 memRegion_sret_120
   model_serialized_eq model_serialized_length model_serialized_ne_nil noAllocShimSpec
   optAddrBoxBuf optSerializeAddressesAt serPrefix6_length
   signalMessageNew_computeMac_length signalMessageNew_of_sepWP_placed
   signalMessageNew_optSerializeAddressesAt_none_eq
   signalMessageNew_optSerializeAddressesAt_some_eq
   sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
   sret_cells_entails_signalMessageAt three_words_entails_cells3
   totCap_eq_serLen_add_8 vecU8At_eq_of_pos zeroExtend32_truncate8_eq)
open CryptoVerification.LibsignalTripleRatchet.NewMacAndBoxesCallees
  (entails_of_sep_focus pull_pure_mid9 satisfies_of_sep_focus)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStack rustCliAllocNoOomSpecWithStack
   subroutine_ok_allocNoOom_externWithStack_of_hookSat)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (ComputeMacEnv computeMacEvents computeMacSpec computeMacSpecWithStack computeMacSpecX
   fitsEnv_computeMac_iff)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (call_noPanic_placed newPostPrologueEvents)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_memcpy_placed_ok new_shim_placed_ok noAllocShimBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap
  bv_add_8_sub_self append64_extract_lo append64_extract_hi zeroExtend32_truncate8_eq

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_neg_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if ¬(v == 0#64) = true then b else a) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_not_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if (!(v == 0#64)) = true then b else a) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_pos_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if (v == 0#64) = true then a else b) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_neg_eq_max64_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if ¬v = 0xFFFFFFFFFFFFFFFF#64 then b else a) = (if v = noneCap then a else b) := by
  by_cases h : v = 0xFFFFFFFFFFFFFFFF#64 <;> simp [h, noneCap]

private theorem bind_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : let sc := s; SepWPp prog ret sc P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  h

private theorem call_noPanic_extern {α : Type} {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
        intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpost).elim
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact (hoom sm (F ∗ R) hoom_s hpost).elim

/-! ## Phase 3 event lists and `FitsEvents` splitting lemmas -/

/-- Events of Phase 3 Segment 2 (`ciphertext.into_boxed_slice()` clone) in `<SignalMessage>::new`. -/
def newCtCloneEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1

/-- Events of Phase 3 Segment 3 (`pq_ratchet` clone) in `<SignalMessage>::new`. -/
def newPqCloneEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1

/-- Events of Phase 3 Segment 6a (deallocating temporary `rkPtr` and `ctCopyPtr`). -/
def newDeallocRkAndCtEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  rustDeallocEvents 33 1 ++
    (if x.ciphertext.isEmpty then [] else rustDeallocEvents x.ciphertext.length 1)

/-- Events of Phase 3 Segment 6b (deallocating temporary `pqCopyPtr`). -/
def newDeallocPqEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  if x.pqRatchet.isEmpty then [] else rustDeallocEvents x.pqRatchet.length 1

/-- Total allocator event sequence of Phase 3 (`+0x3dc..ret`) in `<SignalMessage>::new`. -/
def newPhase3Events (x : SignalMessageNewGhost) : List AllocEvent :=
  computeMacEvents ++
    newCtCloneEvents x ++
    newPqCloneEvents x ++
    newDeallocRkAndCtEvents x ++
    newDeallocPqEvents x

theorem newPostPrologueEvents_eq_serAlloc_append_phase3 (parse : UuidParser)
    (x : SignalMessageNewGhost) :
    newPostPrologueEvents parse x =
      rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1 ++ newPhase3Events x := by
  simp only [newPostPrologueEvents, newPhase3Events, newCtCloneEvents, newPqCloneEvents,
    newDeallocRkAndCtEvents, newDeallocPqEvents, List.append_assoc]

theorem fitsEvents_segments_of_phase3 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : SignalMessageNewGhost}
    (h : FitsEvents M lim st (newPhase3Events x)) :
    let st1 := M.stepEvents computeMacEvents st
    let st2 := M.stepEvents (newCtCloneEvents x) st1
    let st3 := M.stepEvents (newPqCloneEvents x) st2
    let st6 := M.stepEvents (newDeallocRkAndCtEvents x) st3
    FitsEvents M lim st computeMacEvents ∧
      FitsEvents M lim st1 (newCtCloneEvents x) ∧
      FitsEvents M lim st2 (newPqCloneEvents x) ∧
      M.stepEvents (newDeallocPqEvents x) st6 = M.stepEvents (newPhase3Events x) st := by
  dsimp only [newPhase3Events] at h ⊢
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, hrest1⟩ := (fitsEvents_append M lim _ _ st).mp h
  obtain ⟨h2, hrest2⟩ := (fitsEvents_append M lim _ _ _).mp hrest1
  obtain ⟨h3, _hrest3⟩ := (fitsEvents_append M lim _ _ _).mp hrest2
  refine ⟨h1, h2, h3, ?_⟩
  simp only [← M.stepEvents_append, List.append_assoc]

/-! ## State-indexed `[LibsignalPlacement]` sequencing helpers -/

/-- State-indexed counterpart of `signalMessageNew_seq_noPanic_placed` allowing `P2` to depend on
the intermediate machine state `sm`. -/
theorem signalMessageNew_seq_noPanic_placed' [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hcl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hfoom).elim

/-- Sequence a state-indexed `SepWP` segment into an arbitrary `SepWPp` continuation while
preserving `LibsignalCodeLoaded`. -/
theorem signalMessageNew_seq_wp_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  signalMessageNew_seq_noPanic_placed' hcl (SepWPp.of_sepWP_ret h1) hfocus h2

/-! ## `compute_mac` and 8-byte MAC append (`+0x3dc → +0x440`) -/

theorem new_compute_mac_and_append_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecWithStack M A lim C.F cmStack)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st computeMacEvents)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1088#64)
      s
      (((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          cells (sp0 - 176#64) 3 ∗
          memRegion (sp0 - 152#64) 16 ∗
          boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized ∗
          A.pool lim (M.stepEvents computeMacEvents st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have hfit_env : FitsEnv M lim st ComputeMacEnv := fitsEnv_computeMac_iff.mpr hfit
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29
  have hser6_bounds :
      36 ≤ (x.serPrefix6 uuidTryParse).length ∧ (x.serPrefix6 uuidTryParse).length < 2 ^ 35 := by
    have ⟨_, _⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
    have := serPrefix6_length x
    omega
  have htotCap_toNat :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat =
        (x.serPrefix6 uuidTryParse).length + 8 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser6_toNat :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length).toNat =
        (x.serPrefix6 uuidTryParse).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrem8 :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat -
        (x.serPrefix6 uuidTryParse).length = 8 := by omega
  have h176_8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := by bv_lin
  have h176_16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := by bv_lin
  rw [totCap_eq_serLen_add_8 x,
    vecU8At_eq_of_pos A.repAlloc (sp0 - 176#64)
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
      serPtr (x.serPrefix6 uuidTryParse) (by omega),
    hrem8, memRegion_eight (serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length),
    h176_8, h176_16]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun wmac_dst => ?_
  rw [pull_pure_mid9]
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hserPtr_ne⟩ => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 60) hcl
  wp_steps_sync_pool (lsmpl.base 60)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl0
  refine call_noPanic_placed
    (x := (⟨sp0 - 152#64, x.senderIkA, x.senderIk, x.receiverIkA, x.receiverIk,
      x.macKeyA, x.macKey, serPtr, x.serPrefix6 uuidTryParse⟩, st))
    (F := ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 176#64) ↦₆₄ (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ∗
          (A.repAlloc).live serPtr
            (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ wmac_dst))
    hcl0 hMac (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    simp only [computeMacSpecWithStack, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine ⟨by omega, ?_⟩
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [computeMacSpecWithStack, okTagVec, bv_sub_add_lit sp0 152 8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  obtain ⟨macW, hmacW⟩ := exists_unpack64_of_length_8
    (signalMessageNew_computeMac_length C.F x.senderIk x.receiverIk x.macKey
      (x.serPrefix6 uuidTryParse))
  rw [hmacW, ← pointsTo64_eq_pointsToBytes (sp0 - 144#64) macW]
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_63).base + 1088#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [model_serialized_length, totCap_eq_serLen_add_8 x]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · simp only [hsp, arm64_norm]
    have hbox :
        A.live serPtr
            (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr ↦ₛ x.serPrefix6 uuidTryParse) ∗
           ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ macW)) ⊢
        boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized := by
      change (A.repAlloc).live serPtr
          (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
        ((serPtr ↦ₛ x.serPrefix6 uuidTryParse) ∗
         ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ macW)) ⊢ _
      rw [htotCap_toNat, pointsTo64_eq_pointsToBytes, ← hmacW, ← pointsToBytes_append,
        ← model_serialized_eq]
      have hlen_ser := model_serialized_length C.F x
      have hser6_len := serPrefix6_length x
      have hne_nil := model_serialized_ne_nil C.F x
      unfold boxU8Buf
      simp only [hne_nil, ↓reduceIte, hser6_len, hlen_ser]
      refine Entails.pure_right ⟨hserPtr_ne, by omega⟩ (Entails.refl _)
    have hcells3 :=
      three_words_entails_cells3 (sp0 - 176#64)
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
        serPtr
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    rw [h176_8, h176_16] at hcells3
    have hmem16 :
        ((sp0 - 152#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((sp0 - 144#64) ↦₆₄ macW) ⊢
        memRegion (sp0 - 152#64) 16 := by
      rw [memRegion_16_eq_cells2 (sp0 - 152#64), bv_sub_add_lit sp0 152 8]
      exact sepConj_mono (Entails.sepExists_intro 0xFFFFFFFFFFFFFFFE#64)
        (Entails.sepExists_intro macW)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hcells3 (sepConj_mono hmem16 (sepConj_mono_left hbox)))))))))
    exact entails_of_sep_focus (by sep_focus)

theorem new_compute_mac_and_append_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec M A lim C.F)))
    (x : SignalMessageNewGhost) (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st computeMacEvents)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1088#64)
      s
      (((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          cells (sp0 - 176#64) 3 ∗
          memRegion (sp0 - 152#64) 16 ∗
          boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized ∗
          A.pool lim (M.stepEvents computeMacEvents st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_compute_mac_and_append_wpp_placed_at hMac x sp0 serPtr addrCap hct_bound hpq_bound hfit s
    hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29

theorem new_compute_mac_and_append_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecX M A lim C.F)))
    (x : SignalMessageNewGhost) (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st computeMacEvents)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1088#64)
      s
      (((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          cells (sp0 - 176#64) 3 ∗
          memRegion (sp0 - 152#64) 16 ∗
          boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized ∗
          A.pool lim (M.stepEvents computeMacEvents st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_compute_mac_and_append_wpp_placed_at hMac x sp0 serPtr addrCap hct_bound hpq_bound hfit s
    hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29

/-! ## `ciphertext` clone (`+0x440 → +0x46c / +0x55c`) -/

theorem new_ct_clone_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hfit : FitsEvents M lim st (newCtCloneEvents x))
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1088#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64)
      s
      (((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x25) x.ciphertext ∗
          A.pool lim (M.stepEvents (newCtCloneEvents x) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx21 hx22 hx24 hx26 hx27 hx28 hx29
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · have hct_nil : x.ciphertext = [] := by
      have h := congrArg BitVec.toNat hct0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hevs_eq : newCtCloneEvents x = [] := by simp [newCtCloneEvents, hct_nil]
    rw [hevs_eq]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64)
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;> simp [hpq, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      simp only [hct_nil, ↓reduceIte, sepConj_emp, List.length_nil, M.stepEvents_nil, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := by
      by_contra hlt; simp [Nat.le_zero.mp (Nat.not_lt.mp hlt)] at hct0
    have hct_ne_nil : x.ciphertext ≠ [] := by
      intro h; simp [h] at hct_pos
    have hct_nonempty : x.ciphertext.isEmpty = false := List.isEmpty_eq_false_iff.mpr hct_ne_nil
    have hevs_eq : newCtCloneEvents x = rustAllocEvents x.ciphertext.length 1 := by
      simp [newCtCloneEvents, hct_nonempty]
    rw [hevs_eq] at hfit ⊢
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_msb : (BitVec.ofNat 64 x.ciphertext.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hct_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hct_beq : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hct0
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := subroutine_ok_allocNoOom_externWithStack_of_hookSat h_alloc
      (mac_ls_externAt?_of_mem (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)) hle hbnd
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_shim
    refine call_noPanic_extern (x := ())
      (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
            A.pool lim st s_shim ∗ stackAt (sp0 - 416#64) cmStack)
      hshim (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [s_shim, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_shim]
      simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    dsimp only [s_shim] at hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm1 => SepWPp.pure_elim fun htr1 => ?_
    dsimp only [s_shim] at hvm1 htr1 ⊢
    rw [← A.pool_transport lim st _ sf1 hvm1]
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine call_noPanic_extern (x := (x.ciphertext.length, 1, st))
      (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗ (x.ciphertextA ↦ₛ x.ciphertext))
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsum : x.ciphertext.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : RustLayoutOk x.ciphertext.length 1 :=
        ⟨⟨hct_pos, hpow1, hsum⟩, by decide⟩
      dsimp only [rustCliAllocNoOomExternSpecWithStack,
        _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
        rustCliAllocNoOomSpecWithStack]
      simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    dsimp only [rustCliAllocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr2, hoom, _halign_ptr⟩ => ?_
    have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
    let st' := M.stepEvents (rustAllocEvents x.ciphertext.length 1) st
    apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_mc
    refine call_noPanic_extern (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
      (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
            A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
            A.pool lim st' s_mc ∗ stackAt sf2.sp cmStack)
      hmemcpy (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
      (by simp only [s_mc, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_mc]
      simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf3 hpc3 hrun3 hsp3 hcs3
    dsimp only [s_mc] at hsp3 hcs3
    rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm3 => SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
    dsimp only [s_mc] at hvm3 htr3 ⊢
    rw [← A.pool_transport lim st' _ sf3 hvm3]
    simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64)
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;> simp [hpq, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [s_mc, wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      have h25_eq : sf3.readReg64 (Reg.gpr 25#5) = sf2.readReg64 (Reg.gpr 0#5) := by
        simp only [wp_norm, arm64_norm, *]
      simp only [hct_ne_nil, ↓reduceIte, h25_eq, hsp2, A.repAlloc_live_norm, st', wp_norm, arm64_norm]
      refine Entails.pure_right ⟨hoom, by omega⟩ ?_
      exact entails_of_sep_focus (by sep_focus)

theorem new_ct_clone_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hfit : FitsEvents M lim st (newCtCloneEvents x))
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1088#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64)
      s
      (((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x25) x.ciphertext ∗
          A.pool lim (M.stepEvents (newCtCloneEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_ct_clone_wpp_placed_at (by decide) (by decide) h_shim h_alloc h_mc x sp0 serPtr serLen
    addrCap hct_bound hfit s hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx26 hx27 hx28 hx29

theorem new_ct_clone_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hfit : FitsEvents M lim st (newCtCloneEvents x))
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1088#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64)
      s
      (((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x25) x.ciphertext ∗
          A.pool lim (M.stepEvents (newCtCloneEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_ct_clone_wpp_placed_at (by decide) (by decide) h_shim h_alloc h_mc x sp0 serPtr serLen
    addrCap hct_bound hfit s hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx26 hx27 hx28 hx29

/-! ## `pq_ratchet` clone (`+0x46c / +0x55c → +0x498 / +0x568`) -/

theorem new_pq_clone_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPqCloneEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool lim (M.stepEvents (newPqCloneEvents x) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  by_cases hpq0 : BitVec.ofNat 64 x.pqRatchet.length = 0#64
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_nil : x.pqRatchet = [] := by
      have h := congrArg BitVec.toNat hpq0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hevs_eq : newPqCloneEvents x = [] := by simp [newPqCloneEvents, hpq_nil]
    rw [hevs_eq]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64)
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases had : addrCap = 0xFFFFFFFFFFFFFFFF#64 <;> simp [had, noneCap, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      simp only [hpq_nil, ↓reduceIte, sepConj_emp, List.length_nil, M.stepEvents_nil, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_pos : 0 < x.pqRatchet.length := by
      by_contra hlt; simp [Nat.le_zero.mp (Nat.not_lt.mp hlt)] at hpq0
    have hpq_ne_nil : x.pqRatchet ≠ [] := by
      intro h; simp [h] at hpq_pos
    have hpq_nonempty : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr hpq_ne_nil
    have hevs_eq : newPqCloneEvents x = rustAllocEvents x.pqRatchet.length 1 := by
      simp [newPqCloneEvents, hpq_nonempty]
    rw [hevs_eq] at hfit ⊢
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpq_msb : (BitVec.ofNat 64 x.pqRatchet.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hpq_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := subroutine_ok_allocNoOom_externWithStack_of_hookSat h_alloc
      (mac_ls_externAt?_of_mem (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)) hle hbnd
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_shim
    refine call_noPanic_extern (x := ())
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
            A.pool lim st s_shim ∗ stackAt (sp0 - 416#64) cmStack)
      hshim (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [s_shim, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_shim]
      simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    dsimp only [s_shim] at hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm1 => SepWPp.pure_elim fun htr1 => ?_
    dsimp only [s_shim] at hvm1 htr1 ⊢
    rw [← A.pool_transport lim st _ sf1 hvm1]
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine call_noPanic_extern (x := (x.pqRatchet.length, 1, st))
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet))
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsum : x.pqRatchet.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : RustLayoutOk x.pqRatchet.length 1 :=
        ⟨⟨hpq_pos, hpow1, hsum⟩, by decide⟩
      dsimp only [rustCliAllocNoOomExternSpecWithStack,
        _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
        rustCliAllocNoOomSpecWithStack]
      simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    dsimp only [rustCliAllocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr2, hoom, _halign_ptr⟩ => ?_
    have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
    let st' := M.stepEvents (rustAllocEvents x.pqRatchet.length 1) st
    apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_mc
    refine call_noPanic_extern (x := ⟨sf2.readReg64 .x0, x.pqRatchetA, x.pqRatchet⟩)
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
            A.live (sf2.readReg64 .x0) x.pqRatchet.length 1 ∗
            A.pool lim st' s_mc ∗ stackAt sf2.sp cmStack)
      hmemcpy (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
      (by simp only [s_mc, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_mc]
      simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf3 hpc3 hrun3 hsp3 hcs3
    dsimp only [s_mc] at hsp3 hcs3
    rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm3 => SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
    dsimp only [s_mc] at hvm3 htr3 ⊢
    rw [← A.pool_transport lim st' _ sf3 hvm3]
    simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64)
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases had : addrCap = 0xFFFFFFFFFFFFFFFF#64 <;> simp [had, noneCap, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [s_mc, wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      have h23_eq : sf3.readReg64 (Reg.gpr 23#5) = sf2.readReg64 (Reg.gpr 0#5) := by
        simp only [wp_norm, arm64_norm, *]
      simp only [hpq_ne_nil, ↓reduceIte, h23_eq, hsp2, A.repAlloc_live_norm, st', wp_norm, arm64_norm]
      refine Entails.pure_right ⟨hoom, by omega⟩ ?_
      exact entails_of_sep_focus (by sep_focus)

theorem new_pq_clone_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPqCloneEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool lim (M.stepEvents (newPqCloneEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_pq_clone_wpp_placed_at (by decide) (by decide) h_shim h_alloc h_mc x sp0 serPtr serLen
    ctBoxPtr addrCap hpq_bound hfit s hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx25 hx26 hx27
    hx28 hx29

theorem new_pq_clone_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPqCloneEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool lim (M.stepEvents (newPqCloneEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_pq_clone_wpp_placed_at (by decide) (by decide) h_shim h_alloc h_mc x sp0 serPtr serLen
    ctBoxPtr addrCap hpq_bound hfit s hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx25 hx26 hx27
    hx28 hx29

/-! ## `addresses` inlined `into_boxed_slice` (`+0x498 / +0x568 → +0x578`) -/

theorem new_addr_into_boxed_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (x : SignalMessageNewGhost)
    (sp0 serPtr serLen ctBoxPtr pqBoxPtr addrCap : BitVec 64)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc =
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1400#64)
      s
      (optSerializeAddressesAt A.repAlloc (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       A.pool lim st s)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = pqBoxPtr ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          cells (sp0 - 216#64) 3 ∗
          optAddrBoxBuf A.repAlloc (sm.readReg64 .x0) (sm.readReg64 .x20)
            (x.addresses uuidTryParse) ∗
          A.pool lim st sm)) := by
  have h216_8 : sp0 - 216#64 + 8#64 = sp0 - 208#64 := by bv_lin
  have h216_16 : sp0 - 216#64 + 16#64 = sp0 - 200#64 := by bv_lin
  cases had : x.addresses uuidTryParse with
  | none =>
    simp only [had, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at haddrCap
    subst haddrCap
    simp only [↓reduceIte] at hpc
    rw [signalMessageNew_optSerializeAddressesAt_none_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => ?_
    wp_steps_sync_pool ((blkPl_63).base + 1400#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [optAddrBoxBuf, sepConj_emp, arm64_norm]
      have hc3 := three_words_entails_cells3 (sp0 - 216#64) noneCap w1 w0
      rw [h216_8, h216_16] at hc3
      refine Entails.trans ?_ (sepConj_mono_left hc3)
      exact entails_of_sep_focus (by sep_focus)
  | some ad =>
    have had_len := addresses_length had
    simp only [had, Option.isSome_some, ↓reduceIte] at haddrCap
    subst haddrCap
    have h36_ne : (36#64 = noneCap) = False := by decide
    simp only [h36_ne, ↓reduceIte] at hpc
    rw [signalMessageNew_optSerializeAddressesAt_some_eq A.repAlloc (sp0 - 216#64) had_len]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWP.exists_elim fun addrPtr => ?_
    rw [h216_8, h216_16]
    wp_steps_sync_pool ((blkPl_63).base + 1400#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [optAddrBoxBuf, had_len, arm64_norm]
      have hc3 := three_words_entails_cells3 (sp0 - 216#64) 36#64 addrPtr 36#64
      rw [h216_8, h216_16] at hc3
      refine Entails.trans ?_ (sepConj_mono_left hc3)
      exact entails_of_sep_focus (by sep_focus)

/-! ## 120-byte `sret` stores (`+0x578 → +0x5ac`) -/

theorem new_sret_stores_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (x : SignalMessageNewGhost)
    (sp0 serPtr ctBoxPtr pqBoxPtr addrBoxPtr addrBoxLen : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1400#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = addrBoxPtr)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = addrBoxLen)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1452#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       boxU8Buf A.repAlloc pqBoxPtr x.pqRatchet ∗
       boxU8Buf A.repAlloc ctBoxPtr x.ciphertext ∗
       boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized ∗
       optAddrBoxBuf A.repAlloc addrBoxPtr addrBoxLen (x.addresses uuidTryParse) ∗
       memRegion x.ret 120 ∗
       A.pool lim st s)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret
            (x.model C.F uuidTryParse)) ∗
          A.pool lim st sm)) := by
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_eq⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.senderRatchetKey.bytes)
  rw [hrk_eq x.senderRatchetKeyA, memRegion_sret_120 x.ret]
  simp only [cells, sepConj_emp, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  wp_steps_sync_pool ((blkPl_63).base + 1452#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simpa [State.spAligned, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · have hsret :=
      sret_cells_entails_signalMessageAt C.F A.repAlloc x serPtr ctBoxPtr pqBoxPtr
        addrBoxPtr addrBoxLen rk0 rk1 rk2 rk3 hrk_eq hct_bound hpq_bound
    simp only [← sepExists_sepConj_right]
    simp only [← sepExists_sepConj_left]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hsret)))))))))
    exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudgetAux
