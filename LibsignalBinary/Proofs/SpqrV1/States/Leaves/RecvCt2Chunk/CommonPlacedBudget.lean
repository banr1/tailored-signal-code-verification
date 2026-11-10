/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Shared Relocatable `RustCliAllocBudget` Call Helpers for `recv_ct1_ack` and `recv_ct2_chunk`

Non-panicking `SepWPp` / `SepWP` call combinators preserving frozen-memory invariants, together with
framed relocatable `RustCliAllocBudget M` call rules for `<unchunked::Ct1SentEkReceived>::send_ct2`
(Block `347`), `send_ct2_encoder` (Block `382`), `<PolyDecoder as Decoder>::add_chunk` (Block `419`),
and `drop_glue::<[Poly; 16]>` (Block `265`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap
  (vecU8)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk GF16 Mac MlKem NUM_POLYS PolyDecoder PolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyArrayBytes polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted addChunkStack addChunkTotal)
open CryptoVerification.SpqrV1.Drop
  (dropGluePoly16Stack unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt vecGF16ListOf)
open CryptoVerification.SpqrV1.Unchunked
  (unchunkedSendCt2PlacedRoAt)
open CryptoVerification.SpqrV1.States.Leaves
  (SendCt2EncoderGhost UnchunkedSendCt2Ghost sendCt2EncoderStack unchunkedSendCt2Stack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
  (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkEnv addChunkSpec)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget
  (SendCt2EncoderEnv sendCt2EncoderSpec sendCt2EncoderSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv)

/-! ## 1. Re-Exports of Pure/Spatial Helpers & `DefsPlacedBudget` Bridges -/

export CryptoVerification.SpqrV1.States.Leaves
  (recv_ct1_ack_ok_elim vecU8Tail vecU8_entails_slice_and_tail
   slice_and_tail_entails_vecCapPtrDealloc emptyPolyDecoder)

export CryptoVerification.SpqrV1.States.Leaves
  (expectDecoderNew_160 expectDecoderNew_960
   ct1_received_recv_ct2_chunk_ok_elim emptyPolyDecoder_strictSorted
   three_words_entails_sortedSetPtOf_empty)

export CryptoVerification.SpqrV1.States.Leaves
  (wordsAt_empty_slot_cons byte_1_unfold emptyPolyDecoder_recompose
   wordsAt_8 cells_8_unfold)

export CryptoVerification.SpqrV1.States.Leaves
  (sepWPp_call_frozen)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (sepWP_seq_lscl of_sepWP_lscl of_sepWP_lscro
   call_memcpy_relocate_vm call_memcpy_relocate_pool)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (call_dropGluePoly16_cl)

abbrev UcSendCt1SentEkReceived (F : ShaCompress) :=
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)

abbrev UcSendCt2Sent (F : ShaCompress) :=
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent (spqrAuthApi F)

/-! ## 2. Panic-Polymorphic `SepWPp` / `SepWP` Call Combinators (`onPanic = ⌜False⌝`) -/

/-- Pull an existential `∃∗ x : α, P x` out of the spatial precondition of `SepWPp`. -/
theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x : α, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R hmx hL

/-- `SepWPp` subroutine call for a total/non-panicking specification
    (`onExit = ⌜False⌝`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`), polymorphic in `Qp` and `oom`. -/
theorem sepWPp_call_noPanic {α : Type}
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · rw [hexit_eq code sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · rw [hoom_eq sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim

/-- Frozen-invariant-preserving `SepWPp` subroutine call for a non-panicking specification. -/
theorem sepWPp_call_frozen_noPanic {α : Type} {Inv : Memory → Prop}
    (hpres : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : Inv s.mem) (hcall : subroutine_ok prog entry spec)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Inv sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hpres s.mem sm.mem hinv hsteps.keepsFrozen) R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · rw [hexit_eq code sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · rw [hoom_eq sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim

/-- Frozen-invariant-preserving `SepWP` subroutine call for a non-panicking specification. -/
theorem sepWP_call_frozen_noPanic {α : Type} {Inv : Memory → Prop}
    (hpres : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    {prog : Program} {entry ret_pc target_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : Inv s.mem) (hcall : subroutine_ok prog entry spec)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Inv sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.seq_frozen (mid := ret_pc) hpres hinv ?_
  refine SepWP.call_subroutine_frame hcall hpc hrun hsp hlr hpre
    (fun _ sf _ hm => by rw [hpan_eq sf] at hm; exact not_satisfies_false_sepConj hm)
    (fun _ code sf _ hm => by rw [hexit_eq code sf] at hm; exact not_satisfies_false_sepConj hm)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => SepWP.done hpc_sf hrun_sf fun hinv_sf =>
      hnext sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf)
    (fun _ sf _ hm => by rw [hoom_eq sf] at hm; exact (not_satisfies_false_sepConj hm).elim)

/-! ## 3. Framed Call Rules for `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (Block `347`) -/

/-- Two-envelope (`PreEnv` / `PostEnv`) framed relocatable call rule for plain Block `347`. -/
theorem call_sendCt2_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  refine sepWPp_call_noPanic hcall (x := (⟨outA, stA, st, outUc, ct2, mac⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsc, hfit⟩, hm⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hevs⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        (unchunkedCt2SentAt A.repAlloc outA outUc ∗
          (vecU8 A.repAlloc (outA + 56#64) ct2 ∗
            (vecU8 A.repAlloc (outA + 80#64) mac ∗
              (memRegion stA 128 ∗
                (unchunkedSendCt2PlacedRoAt ∗
                  (A.pool lim (M.stepEvents evs st_b) sf ∗
                    stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs

theorem call_sendCt2_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
        M A lim F K Env))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (Env ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      Env ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2_placed_ofPrePostEnv hcall outA stA st outUc ct2 mac st_b hsc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hnext

theorem call_sendCt2_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentEkReceivedSendCt2PlacedSpec
        M A lim F K))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b
      (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.UnchunkedSendCt2Env
        ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.UnchunkedSendCt2Env
        ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2_placed_ofEnv hcall outA stA st outUc ct2 mac st_b hsc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hnext

theorem call_sendCt2_placed_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget.unchunkedCt1SentEkReceivedSendCt2PlacedSpec
        M A lim F K))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (UnchunkedSendCt2PreEnv ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      UnchunkedSendCt2PostEnv ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2_placed_ofPrePostEnv hcall outA stA st outUc ct2 mac st_b hsc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hnext

/-- Two-envelope (`PreEnv` / `PostEnv`) framed relocatable `withLsCodeLoaded lsmpl` call rule
    for Block `347`, threading `LibsignalCodeLoaded lsmpl` to the next cross-block call `next_pc`. -/
theorem call_sendCt2_cl_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨outA, stA, st, outUc, ct2, mac⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsc, hfit⟩, hm⟩
  · dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hevs⟩ => ?_
    apply of_sepWP_lscl hcl_sf (mid := next_pc)
    have hassoc :
        (unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        (unchunkedCt2SentAt A.repAlloc outA outUc ∗
          (vecU8 A.repAlloc (outA + 56#64) ct2 ∗
            (vecU8 A.repAlloc (outA + 80#64) mac ∗
              (memRegion stA 128 ∗
                (unchunkedSendCt2PlacedRoAt ∗
                  (A.pool lim (M.stepEvents evs st_b) sf ∗
                    stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs

theorem call_sendCt2_cl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
          M A lim F K Env)))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (Env ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      Env ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2_cl_ofPrePostEnv hcall outA stA st outUc ct2 mac st_b hsc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hnext

theorem call_sendCt2_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.unchunkedCt1SentEkReceivedSendCt2PlacedSpec
          M A lim F K)))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b
      (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.UnchunkedSendCt2Env
        ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget.UnchunkedSendCt2Env
        ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2_cl_ofEnv hcall outA stA st outUc ct2 mac st_b hsc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hnext

theorem call_sendCt2_cl_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget.unchunkedCt1SentEkReceivedSendCt2PlacedSpec
          M A lim F K)))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (UnchunkedSendCt2PreEnv ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      UnchunkedSendCt2PostEnv ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp)) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2_cl_ofPrePostEnv hcall outA stA st outUc ct2 mac st_b hsc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hnext

theorem call_sendCt2_cl_sepWP_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (outA stA : BitVec 64) (st : UcSendCt1SentEkReceived F) (outUc : UcSendCt2Sent F)
    (ct2 : Bytes) (mac : Mac) (st_b : M.σ)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_b s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
          SepWP prog (s0.readReg64 Reg.lr) sm Pm post)) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWP_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨outA, stA, st, outUc, ct2, mac⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsc, hfit⟩, hm⟩
  · dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    apply sepWP_seq_lscl hcl_sf (mid := next_pc)
    have hassoc :
        (unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        (unchunkedCt2SentAt A.repAlloc outA outUc ∗
          (vecU8 A.repAlloc (outA + 56#64) ct2 ∗
            (vecU8 A.repAlloc (outA + 80#64) mac ∗
              (memRegion stA 128 ∗
                (unchunkedSendCt2PlacedRoAt ∗
                  (A.pool lim (M.stepEvents evs st_b) sf ∗
                    stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs

/-! ## 4. Framed Call Rules for `send_ct2_encoder` (Block `382`) -/

/-- Envelope-parametric framed call rule for plain `sendCt2EncoderSpecOfEnv M A lim Env` (Block `382`). -/
theorem call_sendCt2Encoder_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpecOfEnv M A lim Env))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
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
      Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  refine sepWPp_call_noPanic hcall (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [sendCt2EncoderSpecOfEnv]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [sendCt2EncoderSpecOfEnv]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hevs⟩ => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A.repAlloc outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs

theorem call_sendCt2Encoder [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpec M A lim))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (SendCt2EncoderEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
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
      SendCt2EncoderEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2Encoder_ofEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr hmac_ptr henc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

/-- Envelope-parametric framed relocatable call rule for
    `withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)` (Block `382`). -/
theorem call_sendCt2Encoder_cl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
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
      Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
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
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfEnv]
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

theorem call_sendCt2Encoder_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (SendCt2EncoderEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
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
      SendCt2EncoderEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
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
  call_sendCt2Encoder_cl_ofEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr hmac_ptr henc hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

theorem call_sendCt2Encoder_cl_sepWP_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
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
      Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWP_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    have hassoc :
        (polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A.repAlloc outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs hcl_sf

/-! ## 5. Framed Call Rules for `<PolyDecoder as Decoder>::add_chunk` (Block `419`) -/

/-- Framed call rule for plain `addChunkSpec M A lim` (Block `419`), bridging `SepWP` → `SepWPp`
    and back to `SepWP` after the call. -/
theorem call_addChunk
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpec M A lim))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk) (st_b : M.σ)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfit : FitsEnv M lim st_b (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st_b s ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack) ∗ Frame) post) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  refine sepWPp_call_noPanic hcall (x := (⟨decA, chunkA, dec, chunk⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [addChunkSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted, hfit⟩, hm⟩
  · dsimp only [addChunkSpec]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hacp, hevs, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs hsorted'

/-- Framed relocatable call rule for `withLsCodeLoaded lsmpl (addChunkSpec M A lim)` (Block `419`). -/
theorem call_addChunk_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk) (st_b : M.σ)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfit : FitsEnv M lim st_b (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st_b s ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack) ∗ Frame)
        post Qp) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨decA, chunkA, dec, chunk⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted, hfit⟩, hm⟩
  · dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hacp, hevs, hsorted'⟩ => ?_
    have hassoc :
        (polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs hsorted'
      hcl_sf

theorem call_addChunk_cl_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk) (st_b : M.σ)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfit : FitsEnv M lim st_b (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st_b s ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWP_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨decA, chunkA, dec, chunk⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted, hfit⟩, hm⟩
  · dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hacp, hevs, hsorted'⟩ => ?_
    have hassoc :
        (polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call addChunkStack))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs hsorted'
      hcl_sf

/-! ## 6. `SepWPp` Relocatable Call Rule for `drop_glue::<[Poly; 16]>` (Block `265`) -/

/-- `SepWP` → `SepWPp` framed relocatable call rule for
    `withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)` (Block `265`). -/
theorem call_dropGluePoly16_wpp_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)))
    (arrA : BitVec 64) (vecs : List (List GF16)) (st_b : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = arrA) (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecGF16ListOf A.repAlloc arrA vecs ∗ A.pool lim st_b s ∗
      stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → FreeOnlyEvs evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((memRegion arrA polyArrayBytes ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call dropGluePoly16Stack) ∗ Frame) post Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨arrA, vecs⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit, sepConj_assoc] at hm
    dsimp only [withLsCodeLoaded, dropGluePoly16Spec]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hlen, by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, dropGluePoly16Spec]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hacp, hevs⟩ => ?_
    have hassoc :
        (memRegion arrA polyArrayBytes ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp_call dropGluePoly16Stack) ∗ Frame =
        (memRegion arrA polyArrayBytes ∗
          (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call dropGluePoly16Stack)) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs hcl_sf

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
