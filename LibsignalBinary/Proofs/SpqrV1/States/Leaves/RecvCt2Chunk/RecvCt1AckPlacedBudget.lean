/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1Ack
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<EkReceivedCt1Sampled>::recv_ct1_ack` (Budget-Threaded, Block `343`)

Relocatable `[LibsignalPlacement]` budget-threaded contracts for `<EkReceivedCt1Sampled>::recv_ct1_ack`
on `lsProg_343 (Rust.withPanics ext)` (`53` instructions), including framed two-envelope
`send_ct2_encoder` call helpers and `EkReceivedCt1SampledRecvCt1AckPlacedOkX{,OfPrePostEnv,OfEnv}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_343 blkPl_343 extract_withLsCodeLoaded lsProg_343
   ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (Bytes MlKem PolyEncoder spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt2SampledAt chunkedCt2SampledSize chunkedEkReceivedCt1SampledAt
   chunkedEkReceivedCt1SampledSize chunked_400_join polyEncoderAt_entails_tag_vecs_tail
   unchunkedCt2SentAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt)
open CryptoVerification.SpqrV1.States.Leaves
  (EkReceivedCt1SampledRecvCt1AckGhost RecvCt1AckSaved SendCt2EncoderGhost authWordsList bv_sub_sub
   cells_1_unfold cells_7_unfold cells_8_unfold ct2SentWordsList of_sepWP_lscl recv_ct1_ack_ok_elim
   sendCt2EncoderStack sepWP_seq_lscl slice_and_tail_entails_vecCapPtrDealloc
   stackAt_176_from_dropPoly16 stackAt_176_split stackAt_176_to_allocHook stackAt_176_to_dropPoly16
   stackAt_176_to_sendCt2Encoder subroutine_ok_withLsCodeLoaded_of_left uc_56_and_headers_recompose
   unchunkedCt1SentEkReceivedAt_400_eq unchunkedCt2SentAt_extract vecU8_entails_slice_and_tail
   wordsAt wordsAt_7)
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget SeqEnv fitsEvents_append rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec drop_glue_poly16_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (EkReceivedCt1SampledRecvCt1AckEnv EkReceivedCt1SampledRecvCt1AckPlacedOkX
   EkReceivedCt1SampledRecvCt1AckPlacedOkXOfEnv EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv
   EkReceivedCt1SampledRecvCt1AckPostEnv EkReceivedCt1SampledRecvCt1AckPreEnv
   SendCt2EncoderBytesPostEnv SendCt2EncoderBytesPreEnv SendCt2EncoderPostEnv SendCt2EncoderPreEnv
   ekReceivedCt1SampledRecvCt1AckEnv_nonempty ekReceivedCt1SampledRecvCt1AckPlacedSpec
   ekReceivedCt1SampledRecvCt1AckPlacedSpecOfEnv
   ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv ekReceivedCt1SampledRecvCt1AckPreEnv_nonempty
   sendCt2EncoderSpec sendCt2EncoderSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget (call_dropGluePoly16_cl)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
  (call_sendCt2_cl_tight sepWPp_call_frozen_noPanic sepWPp_exists_left)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
  (EkReceivedCt1SampledRecvCt1AckPreEnv EkReceivedCt1SampledRecvCt1AckPostEnv
   EkReceivedCt1SampledRecvCt1AckEnv ekReceivedCt1SampledRecvCt1AckPreEnv_nonempty
   ekReceivedCt1SampledRecvCt1AckEnv_nonempty
   ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv
   ekReceivedCt1SampledRecvCt1AckPlacedSpecOfEnv
   ekReceivedCt1SampledRecvCt1AckPlacedSpec
   EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv
   EkReceivedCt1SampledRecvCt1AckPlacedOkXOfEnv
   EkReceivedCt1SampledRecvCt1AckPlacedOkX)

/-! ## 1. Two-Envelope `send_ct2_encoder` Call Helpers & Private Dealloc Combinators -/

/-- Two-envelope (`PreEnv` / `PostEnv`) framed relocatable call rule for
    `withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv)` (Block `382`). -/
theorem call_sendCt2Encoder_cl_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hevs⟩ => ?_
    have hassoc :
        (polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A.repAlloc outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs hcl_sf

theorem call_sendCt2Encoder_cl_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (SendCt2EncoderPreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SendCt2EncoderPostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2Encoder_cl_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b
    hct2_ptr hmac_ptr henc hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext
    hlr_ls

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem sepWP_choose_evs {α : Type} {prog : Program} {tgt : BitVec 64}
    {s : State} {P R : SepProp} {F : State → α → SepProp} {Extra : State → Prop} (w : α)
    (h : SepWP prog tgt s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ F sf w)) ∧ Extra sf)) :
    SepWP prog tgt s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ∃∗ x, F sf x)) ∧ Extra sf) :=
  SepWP.mono h fun sf _ _ _ ⟨hm, hex⟩ =>
    ⟨fun hPR => by rw [satisfies_sepExists]; exact ⟨w, hm hPR⟩, hex⟩

private theorem seqEnv_assoc_freeOnly {E1 E2 : List AllocEvent → Prop}
    {evs1 evs2 evs3 evs4 evs5 : List AllocEvent}
    (h1 : E1 evs1) (h2 : SeqEnv E2 FreeOnlyEvs evs2)
    (h3 : FreeOnlyEvs evs3) (h4 : FreeOnlyEvs evs4) (h5 : FreeOnlyEvs evs5) :
    SeqEnv (SeqEnv E1 E2) FreeOnlyEvs (evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5) := by
  rcases h2 with h2p | ⟨e2a, e2f, rfl, h2p, h2f⟩
  · have hpre : SeqEnv E1 E2 (evs1 ++ evs2) := SeqEnv.append h1 h2p
    have hfree : FreeOnlyEvs (evs3 ++ evs4 ++ evs5) := (h3.append h4).append h5
    simpa only [List.append_assoc] using SeqEnv.append hpre hfree
  · have hpre : SeqEnv E1 E2 (evs1 ++ e2a) := SeqEnv.append h1 h2p
    have hfree : FreeOnlyEvs (e2f ++ evs3 ++ evs4 ++ evs5) := ((h2f.append h3).append h4).append h5
    simpa only [List.append_assoc] using SeqEnv.append hpre hfree

/-! ## 2. Budget-Threaded Relocatable `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded relocatable `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`, `53` insns)
    with an explicit `withLsCodeLoaded` hypothesis for `drop_glue::<[Poly; 16]>` (Block `265`). -/
theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (hdrop : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX M A lim F K ext := by
  unfold EkReceivedCt1SampledRecvCt1AckPlacedOkX
    EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv
  apply subroutine_ok_withLsCodeLoaded_of_left
  have hdealloc_raw : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  simp only [ekReceivedCt1SampledRecvCt1AckPlacedSpec,
    ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv, lsProg_343,
    chunkedCt2SampledSize, chunkedEkReceivedCt1SampledSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hsend henc hdrop ⊢
  wpp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, st, outSt⟩, st_b⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA› ‹s0.readReg64 (Reg.gpr 1#5) = stA›
  obtain ⟨ct2, mac, hsc_ok, henc_ok⟩ := recv_ct1_ack_ok_elim (by assumption)
  have hfit_seq : FitsEnv M lim st_b
      (SeqEnv
        (UnchunkedSendCt2Env ⟨0#64, 0#64, st.uc, outSt.uc, ct2, mac⟩)
        (SendCt2EncoderBytesPreEnv ct2.length mac.length)) := by
    have hfit0 : FitsEnv M lim st_b
        (EkReceivedCt1SampledRecvCt1AckPreEnv K
          ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5), st, outSt⟩) := by
      assumption
    intro evs hevs
    apply hfit0 evs
    unfold EkReceivedCt1SampledRecvCt1AckPreEnv
    dsimp only
    rw [hsc_ok]
    exact hevs
  have hfit_send : FitsEnv M lim st_b
      (UnchunkedSendCt2PreEnv
        ⟨s0.sp - 168#64, s0.readReg64 (Reg.gpr 1#5) + 400#64, st.uc, outSt.uc, ct2, mac⟩) := by
    intro evs hevs
    have hevs0 : UnchunkedSendCt2PreEnv ⟨0#64, 0#64, st.uc, outSt.uc, ct2, mac⟩ evs := hevs
    exact hfit_seq evs (Or.inl (UnchunkedSendCt2PostEnv.of_pre hevs0))
  have hfsp_align : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 176#64 (by assumption) (by decide)
  apply of_sepWP_lscl hcl0 (mid := lsmpl.base 347)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 0#5)) (n := 400) (k := 56)
        (b' := s0.readReg64 (Reg.gpr 0#5) + 400#64) rfl rfl (by decide),
        stackAt_176_split s0.sp]
    unfold chunkedEkReceivedCt1SampledAt
    rw [unchunkedCt1SentEkReceivedAt_400_eq A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 176#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [arm64_norm]
  wp_steps_sync_pool (lsmpl.base 347)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq (unchunkedCt1SentEkReceivedAt_400_eq A.repAlloc
    (s0.readReg64 (Reg.gpr 1#5)) st.uc).symm) (by sep_focus) ?_
  refine call_sendCt2_cl_tight hsend
    (s0.sp - 168#64) (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc outSt.uc ct2 mac st_b
    hsc_ok hfit_send
    (ret_pc := (blkPl_343).base + 60#64) (next_pc := lsmpl.base 382) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 evs1 hpc1 hrun1 hsp1 hcs1 htr1 hevs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have h56_eq : (s0.sp - 168#64) + 56#64 = s0.sp - 112#64 := by bv_omega
  have h80_eq : (s0.sp - 168#64) + 80#64 = s0.sp - 88#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (stackAt_176_to_sendCt2Encoder s0.sp) (by sep_focus) ?_
  refine SepWP.fold (unchunkedCt2SentAt_extract A.repAlloc (s0.sp - 168#64) outSt.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s0.sp - 112#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s0.sp - 88#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  refine SepWP.fold (cells_7_unfold (s0.readReg64 (Reg.gpr 0#5) + 400#64)) (by sep_focus) ?_
  wp_pull_exists
  have hsp_uc_words :
      wordsAt (s0.sp - 168#64) (ct2SentWordsList g_uc outSt.uc.epoch) =
      (((s0.sp - 168#64) ↦₆₄ g_uc.v1.w0) ∗ ((s0.sp - 160#64) ↦₆₄ g_uc.v1.w1) ∗
       ((s0.sp - 152#64) ↦₆₄ g_uc.v1.w2) ∗ ((s0.sp - 144#64) ↦₆₄ g_uc.v2.w0) ∗
       ((s0.sp - 136#64) ↦₆₄ g_uc.v2.w1) ∗ ((s0.sp - 128#64) ↦₆₄ g_uc.v2.w2) ∗
       ((s0.sp - 120#64) ↦₆₄ outSt.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  have hout_uc_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ct2SentWordsList g_uc outSt.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g_uc.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g_uc.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g_uc.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g_uc.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g_uc.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g_uc.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ outSt.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_conv_pre => rw [hsp_uc_words]; simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_steps_sync_pool (lsmpl.base 382)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq hsp_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_56_and_headers_recompose
    (s0.readReg64 (Reg.gpr 0#5)) s0.sp outSt.uc g_uc _ _ _ _ _ _ _) (by sep_focus) ?_
  have hfit_enc : FitsEnv M lim (M.stepEvents evs1 st_b)
      (SendCt2EncoderPreEnv
        ⟨s0.readReg64 (Reg.gpr 0#5), ct2Ptr, ct2, macPtr, mac, outSt.sending_ct2⟩) := by
    intro e2 he2
    have hevs1_0 : UnchunkedSendCt2Env ⟨0#64, 0#64, st.uc, outSt.uc, ct2, mac⟩ evs1 := hevs1
    have he2_0 : SendCt2EncoderBytesPreEnv ct2.length mac.length e2 := he2
    exact ((fitsEvents_append M lim evs1 e2 st_b).mp (hfit_seq (evs1 ++ e2) (SeqEnv.append hevs1_0 he2_0))).2
  refine call_sendCt2Encoder_cl_tight henc
    (s0.readReg64 (Reg.gpr 0#5)) ct2Ptr macPtr ct2 mac outSt.sending_ct2
    (M.stepEvents evs1 st_b) hct2_ne hmac_ne henc_ok hfit_enc
    (ret_pc := (blkPl_343).base + 116#64) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1]) (by simp only [Reg.x0, arm64_norm, hx22_1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm]) (by sep_focus)
    (fun sf2 evs2 hpc2 hrun2 hsp2 hcs2 htr2 hevs2 hcl2 => ?_)
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 265)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx22_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_176_to_allocHook s0.sp) (by sep_focus) ?_
  have hout_join :
      polyEncoderAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) outSt.sending_ct2 ∗
        unchunkedCt2SentAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 400#64) outSt.uc ⊢
      chunkedCt2SampledAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) outSt := Entails.refl _
  refine SepWP.fold hout_join (by sep_focus) ?_
  refine seq_clean_evs (mid := (blkPl_343).base + 136#64)
    (P_evs := fun evs3 sm => (chunkedCt2SampledAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
      polyEncoderAt A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
      memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
      vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗
      unchunkedSendCt2PlacedRoAt ∗
      memRegion (s0.sp - 17632#64) 13360 ∗ memRegion (s0.sp - 176#64) 112 ∗
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
      A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st_b))) sm ∗
      stackAt (s0.sp - 176#64) allocHookStack)
    (Q := fun sm => RecvCt1AckSaved s0 sm (s0.sp - 176#64) (s0.readReg64 (Reg.gpr 1#5)) ct2Cap ct2Ptr)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hmac : (macCap == 0#64) = true <;>
      simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st
        (by dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19];
            simp only [arm64_norm]; sep_ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp2, htr2, hvregs_2]⟩
    · apply sepWP_evs_dealloc macCap.toNat 1
      wp_steps; wp_apply
      refine align_pre_st
        (by rw [hsp2]; dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19];
            sep_ac_rfl) ?_
      wp_done
  · intro evs3 s3 hevs3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3⟩
    refine seq_clean_evs (mid := (blkPl_343).base + 156#64)
      (P_evs := fun evs4 sm => (chunkedCt2SampledAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
        polyEncoderAt A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
        unchunkedSendCt2PlacedRoAt ∗
        memRegion (s0.sp - 17632#64) 13360 ∗ memRegion (s0.sp - 176#64) 112 ∗
        (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
        A.pool lim (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st_b)))) sm ∗
        stackAt (s0.sp - 176#64) allocHookStack)
      (Q := fun sm => RecvCt1AckSaved s0 sm (s0.sp - 176#64) (s0.readReg64 (Reg.gpr 1#5)) ct2Cap ct2Ptr)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hct2 : (ct2Cap == 0#64) = true <;>
        simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine align_pre_st (by simp only [arm64_norm]; try sep_ac_rfl) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3]⟩
      · apply sepWP_evs_dealloc ct2Cap.toNat 1
        wp_steps; wp_apply
        refine align_pre_st (by rw [hsp3]; sep_ac_rfl) ?_
        wp_done
    · intro evs4 s4 hevs4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp4, htr4, hvregs_4⟩
      refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A.repAlloc
        (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1) (by sep_focus) ?_
      wp_pull_exists; rename_i tag vecs
      wp_focus_pure; intro hvecs_len
      wp_steps_sync_pool (lsmpl.base 265)
      simp only [State.setMem_setMem]
      refine SepWP.fold (stackAt_176_to_dropPoly16 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine call_dropGluePoly16_cl hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs
        (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st_b))))
        (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
        (by simp only [arm64_norm])
        (by simpa only [arm64_norm] using hrun4)
        (by simp only [State.sp, arm64_norm, hsp4])
        (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
        (by simp only [Reg.lr, arm64_norm])
        (by simp only [arm64_norm, htr4])
        (by simp only [Reg.x0, arm64_norm, hx19_4])
        hvecs_len
        (by sep_focus)
        (fun sf evs5 hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf _hacp_sf hevs5 => ?_)
      have hstep_tot :
          M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st_b)))) =
            M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5) st_b := by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      rw [hstep_tot]
      refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 128 528 rfl (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_176_from_dropPoly16 s0.sp) (by sep_focus) ?_
      have hevs_tot : EkReceivedCt1SampledRecvCt1AckPostEnv K
          ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5), st, outSt⟩
          (evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5) := by
        unfold EkReceivedCt1SampledRecvCt1AckPostEnv EkReceivedCt1SampledRecvCt1AckPreEnv
        dsimp only
        rw [hsc_ok]
        have hevs1_0 : UnchunkedSendCt2Env ⟨0#64, 0#64, st.uc, outSt.uc, ct2, mac⟩ evs1 := hevs1
        have hevs2_0 : SendCt2EncoderBytesPostEnv ct2.length mac.length evs2 := hevs2
        exact seqEnv_assoc_freeOnly hevs1_0 hevs2_0 hevs3 hevs4 hevs5
      simp only [List.append_assoc] at hevs_tot
      refine sepWP_choose_evs (evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5) ?_
      wp_done

/-- Budget-threaded relocatable `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`, `53` insns)
    discharging `drop_glue::<[Poly; 16]>` (Block `265`) directly from `hdealloc`. -/
theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX M A lim F K ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop hdealloc hsend henc
    (ls_subroutine_ok_of_block (i := 343) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {PreEnv PostEnv : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop}
    (hpre_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPreEnv K x evs → PreEnv x evs)
    (hpost_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPostEnv K x evs → PostEnv x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (hdrop : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv M A lim F K PreEnv PostEnv ext := by
  have hok := ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop (F := F) (K := K)
    hdealloc hsend henc hdrop
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
    dsimp only [ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv] at hpre
    dsimp only [withLsCodeLoaded, ekReceivedCt1SampledRecvCt1AckPlacedSpec,
      ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨h0, h1, h2, hok_st, hfit, hlr⟩, hmem⟩
    exact ⟨⟨h0, h1, h2, hok_st, FitsEnv.mono (hpre_sub x) hfit, hlr⟩, hmem⟩
  · dsimp only [withLsCodeLoaded, ekReceivedCt1SampledRecvCt1AckPlacedSpec,
      ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hpost_sub x evs hq.1.2⟩, hq.2⟩

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {PreEnv PostEnv : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop}
    (hpre_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPreEnv K x evs → PreEnv x evs)
    (hpost_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPostEnv K x evs → PostEnv x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv M A lim F K PreEnv PostEnv ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop_ofPrePostEnv
    hpre_sub hpost_sub hdealloc hsend henc
    (ls_subroutine_ok_of_block (i := 343) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    {Env : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop}
    (hpost_sub : ∀ x evs, EkReceivedCt1SampledRecvCt1AckPostEnv K x evs → Env x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkXOfEnv M A lim F K Env ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_ofPrePostEnv
    (fun x evs h => hpost_sub x evs (Or.inl h)) hpost_sub hdealloc hsend henc

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1AckPlacedBudget
