/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5c
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5c: Arm 9 (`States.ct1Acknowledged`)

Defines the exact allocator event envelope `Ct1AcknowledgedEnv` and its `SpqrBoundedEvs` bridges,
the `VmPreserved` `call_memcpy_keep_relocate_wp` helper over `sessionMemcpyRegionBudgetSpec`,
and verifies Arm 9 (`States.ct1Acknowledged`, tag `11`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder Pt States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Acknowledged)
open CryptoVerification.LibsignalTripleRatchet
  (memcpyName sessionMemcpyRegionSpec tripleRatchetProgAtExt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize protoPolynomialDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (Relocatable TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   chunkedCt1Acknowledged_expose ct1AcknowledgedScratchCells
   ct1AcknowledgedScratchCells_entails_memRegions epilogueStagingCells
   memRegion_1424_split_epilogue memRegion_ct1Acknowledged_scratch_split
   memcpy_keep_relocate_recombine memcpy_keep_relocate_split outWords28
   outWords28_entails_ct1Acknowledged protoPolynomialDecoderHeap relocatedHeap
   stA_ct1Acknowledged_entails_928 stackAt_encoderIntoPb_eq_allocHook
   statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
   statesIntoPbStack vecU8CloneTail vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Relocatable
  (words12 words4_polyDecoderAt)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   FreeOnlyEvs RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv DecoderIntoPbOkExt
   decoderIntoPbAllocEnv_imp_decoderIntoPbEnv decoderIntoPbAllocEvents
   decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbVariantSpec statesIntoPbVariantSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
  (call_decoderIntoPb_expose_wp sepWPp_of_states_into_pb_exit_of_env
   states_into_pb_epilogue states_into_pb_prologue_60
   sub_ok_decoderIntoPb_raw sub_ok_memcpy_raw)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1Acknowledged_step_1812_to_1900 ct1Acknowledged_step_1904_to_1544
   ct1Acknowledged_step_376_to_424 ct1Acknowledged_step_424_to_1812_wp
   ct1Acknowledged_step_60_to_372 ct1CloneEvents ct1DeallocEvents
   freeOnlyEvs_ct1DeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

private theorem seq_vm_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 1. Allocator Event Envelope & Bounds for Arm 9 (`States.ct1Acknowledged`) -/

/-- Exact allocator event envelope of `<States>::into_pb` on Arm 9 (`States.ct1Acknowledged`):
1. `ct1CloneEvents s.uc.ct1` (cloning `s.uc.ct1`),
2. `evs_d1` (`FreeOnlyEvs`, dropping the consumed `ct1` buffer `(cap_ct1, ptr_ct1)`),
3. `evs_dec` (`DecoderIntoPbEnv s.receiving_ek`, serializing and dropping `s.receiving_ek`). -/
def Ct1AcknowledgedEnv {F : ShaCompress}
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (evs : List AllocEvent) : Prop :=
  ∃ evs_d1 evs_dec,
    evs = (ct1CloneEvents s.uc.ct1 ++ evs_d1) ++ evs_dec ∧
    FreeOnlyEvs evs_d1 ∧
    DecoderIntoPbEnv s.receiving_ek evs_dec

theorem fitsEvents_ct1Clone_of_ct1AcknowledgedEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    (cap_ct1 : BitVec 64)
    (hfit : FitsEnv M lim st (Ct1AcknowledgedEnv s)) :
    FitsEvents M lim st (ct1CloneEvents s.uc.ct1) := by
  have hwit : Ct1AcknowledgedEnv s
      ((ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1) ++
       decoderIntoPbAllocEvents s.receiving_ek) :=
    ⟨ct1DeallocEvents cap_ct1, decoderIntoPbAllocEvents s.receiving_ek, rfl,
     freeOnlyEvs_ct1DeallocEvents cap_ct1, decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  have htot := hfit _ hwit
  have h12 := ((fitsEvents_append M lim _ _ st).mp htot).1
  exact ((fitsEvents_append M lim _ _ st).mp h12).1

theorem fitsEnv_decoder_of_ct1AcknowledgedEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    (cap_ct1 : BitVec 64)
    (hfit : FitsEnv M lim st (Ct1AcknowledgedEnv s)) :
    FitsEnv M lim
      (M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st))
      (DecoderIntoPbAllocEnv s.receiving_ek) := by
  intro evs_dec hdec_eq
  unfold DecoderIntoPbAllocEnv at hdec_eq
  subst hdec_eq
  have hwit : Ct1AcknowledgedEnv s
      ((ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1) ++
       decoderIntoPbAllocEvents s.receiving_ek) :=
    ⟨ct1DeallocEvents cap_ct1, decoderIntoPbAllocEvents s.receiving_ek, rfl,
     freeOnlyEvs_ct1DeallocEvents cap_ct1, decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  have htot := hfit _ hwit
  have h2 := ((fitsEvents_append M lim
    (ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1)
    (decoderIntoPbAllocEvents s.receiving_ek) st).mp htot).2
  rwa [M.stepEvents_append] at h2

theorem spqrBoundedEvs_ct1CloneEvents (ct1 : List (BitVec 8))
    (hmax : ct1.length ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 ct1.length (ct1CloneEvents ct1) := by
  unfold ct1CloneEvents
  by_cases h0 : ct1.length = 0
  · simp only [h0, ↓reduceIte]
    exact SpqrBoundedEvs.nil 1 0
  · have h1 : 1 ≤ ct1.length := Nat.pos_of_ne_zero h0
    have hcond : (1 ≤ 16 ∧ 1 ≤ ct1.length) := ⟨by decide, h1⟩
    simp only [h0, ↓reduceIte, rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, Nat.le_refl _, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_rustAllocEvents_384_8 :
    SpqrBoundedEvs 1 384 (rustAllocEvents 384 8) := by
  have hcond : (8 ≤ 16 ∧ 8 ≤ 384) := ⟨by decide, by decide⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, Nat.le_refl 384, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_decoderIntoPbSlotEvents (pts : List Pt) {maxReq : Nat}
    (hmax : 4 * pts.length ≤ MallocngMaxAllocSize)
    (hreq : 4 * pts.length ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (decoderIntoPbSlotEvents pts) := by
  unfold decoderIntoPbSlotEvents
  cases pts with
  | nil =>
    exact SpqrBoundedEvs.nil 1 maxReq
  | cons pt rest =>
    have h1 : 1 ≤ 4 * (pt :: rest).length := by simp only [List.length_cons]; omega
    have hcond : (1 ≤ 16 ∧ 1 ≤ 4 * (pt :: rest).length) := ⟨by decide, h1⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_slots {α : Type} (f : α → List Pt) {maxReq : Nat} :
    ∀ (xs : List α),
      (∀ x ∈ xs, 4 * (f x).length ≤ MallocngMaxAllocSize ∧ 4 * (f x).length ≤ maxReq) →
      SpqrBoundedEvs xs.length maxReq (xs.flatMap (fun x => decoderIntoPbSlotEvents (f x)))
  | [], _ => SpqrBoundedEvs.nil 0 maxReq
  | x :: xs, h => by
    simp only [List.flatMap_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have htl := spqrBoundedEvs_flatMap_slots f xs
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h1 := spqrBoundedEvs_decoderIntoPbSlotEvents (f x) hx.1 hx.2
    have happ := SpqrBoundedEvs.append h1 htl
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_of_eq (Nat.max_self maxReq)) happ

private theorem nonFreeCount_rustAllocEvents (sz al : Nat) :
    nonFreeCount (rustAllocEvents sz al) = 1 := by
  unfold rustAllocEvents
  by_cases hc : al ≤ 16 ∧ al ≤ sz
  · simp [hc, nonFreeCount]
  · simp [hc, nonFreeCount]

private theorem nonFreeCount_ct1CloneEvents_le (ct1 : List (BitVec 8)) :
    nonFreeCount (ct1CloneEvents ct1) ≤ 1 := by
  unfold ct1CloneEvents
  by_cases h0 : ct1.length = 0
  · simp [h0, nonFreeCount]
  · simp [h0, nonFreeCount_rustAllocEvents]

private theorem nonFreeCount_decoderIntoPbSlotEvents_le (pts : List Pt) :
    nonFreeCount (decoderIntoPbSlotEvents pts) ≤ 1 := by
  unfold decoderIntoPbSlotEvents
  cases pts with
  | nil => simp [nonFreeCount]
  | cons _ _ => simp [nonFreeCount_rustAllocEvents]

private theorem nonFreeCount_flatMap_slots_le {α : Type} (f : α → List Pt) :
    ∀ (xs : List α),
      nonFreeCount (xs.flatMap (fun x => decoderIntoPbSlotEvents (f x))) ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.flatMap_cons, List.length_cons, nonFreeCount_append]
    have h1 := nonFreeCount_decoderIntoPbSlotEvents_le (f x)
    have h2 := nonFreeCount_flatMap_slots_le f xs
    omega

theorem nonFreeCount_ct1AcknowledgedEnv_le {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (henv : Ct1AcknowledgedEnv s evs) :
    nonFreeCount evs ≤ 2 + s.receiving_ek.pts.length := by
  rcases henv with ⟨evs_d1, evs_dec, rfl, hfree1, evs_alloc, evs_free, rfl, hdec_alloc, hfree2⟩
  unfold DecoderIntoPbAllocEnv at hdec_alloc
  subst hdec_alloc
  simp only [decoderIntoPbAllocEvents, nonFreeCount_append,
    nonFreeCount_eq_zero_of_freeOnly hfree1, nonFreeCount_eq_zero_of_freeOnly hfree2,
    nonFreeCount_rustAllocEvents]
  have h1 := nonFreeCount_ct1CloneEvents_le s.uc.ct1
  have h2 := nonFreeCount_flatMap_slots_le (fun sl => sl.vec) s.receiving_ek.pts
  omega

theorem ct1AcknowledgedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 2 + s.receiving_ek.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : Ct1AcknowledgedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with ⟨evs_d1, evs_dec, rfl, hfree1, evs_alloc, evs_free, rfl, hdec_alloc, hfree2⟩
  unfold DecoderIntoPbAllocEnv at hdec_alloc
  subst hdec_alloc
  have hclone : SpqrBoundedEvs 1 maxReq (ct1CloneEvents s.uc.ct1) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) hct1_req (spqrBoundedEvs_ct1CloneEvents s.uc.ct1 hct1_max)
  have hd1 : SpqrBoundedEvs 0 maxReq evs_d1 :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree1)
  have houter : SpqrBoundedEvs 1 maxReq (rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) h384 spqrBoundedEvs_rustAllocEvents_384_8
  have hslots : SpqrBoundedEvs s.receiving_ek.pts.length maxReq
      (s.receiving_ek.pts.flatMap (fun sl => decoderIntoPbSlotEvents sl.vec)) :=
    spqrBoundedEvs_flatMap_slots (fun sl => sl.vec) s.receiving_ek.pts hpts
  have hd2 : SpqrBoundedEvs 0 maxReq evs_free :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree2)
  have h12 := SpqrBoundedEvs.append hclone hd1
  have hdec_alloc := SpqrBoundedEvs.append houter hslots
  have hdec := SpqrBoundedEvs.append hdec_alloc hd2
  have htot := SpqrBoundedEvs.append h12 hdec
  exact SpqrBoundedEvs.mono (by omega) (by omega) htot

/-! ## 2. `VmPreserved` `call_memcpy_keep_relocate_wp` Helper -/

/-- Total-correctness (`SepWP`) call helper for `memcpy` (`sessionMemcpyRegionBudgetSpec`),
keeping `F src` (`szKeep` bytes) at `src`, relocating `G (src + off)` (`szReloc` bytes) to
`dst + off`, and transporting `A.pool lim st` via `VmPreserved`. -/
theorem call_memcpy_keep_relocate_wp
    {M : AllocCostModel} {b memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      memcpy_pc sessionMemcpyRegionBudgetSpec)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {szKeep szReloc szTotal : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 szKeep)
    (hsum : szKeep + szReloc = szTotal)
    (hF : Relocatable szKeep F)
    (hG : Relocatable szReloc G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = szTotal)
    (hsplit : P = (memRegion dst szTotal ∗ (F src ∗ G (src + off)) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      VmPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        ((((memRegion dst szKeep ∗ G (dst + off)) ∗
           (F src ∗ memRegion (src + off) szReloc)) ∗ A.pool lim st sf) ∗ Frame)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = szKeep ∧ bs2.length = szReloc ∧ (bs1 ++ bs2).length = szTotal⌝ ∗
        ((memRegion dst szTotal ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
         (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame)) := by
    rw [hsplit]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (memcpy_keep_relocate_split hoff hsum hF hG dst src)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre_split ?_
  refine SepWP.exists_elim fun bs1 => SepWP.exists_elim fun bs2 => ?_
  refine SepWP.pure_elim fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWP.call_subroutine_frame hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜VmPreserved s sf⌝ ∗ ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
      (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
        relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
       A.pool lim st s ∗ Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun hvm => SepWP.pure_elim fun ⟨_hx0_sf, htr_sf⟩ => ?_
    rw [← A.pool_transport lim st s sf hvm]
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    refine SepWP.weaken_pre (Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (show _ =
      ((((memRegion dst szKeep ∗ G (dst + off)) ∗
         (F src ∗ memRegion (src + off) szReloc)) ∗ A.pool lim st sf) ∗ Frame) by sep_ac_rfl))) ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hvm
      ⟨htr_sf.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩
  · intro _ _ _ ho
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-! ## 3. Arm 9 (`States.ct1Acknowledged`, tag `11`) Main Theorems -/

set_option maxHeartbeats 800000 in
/-- Envelope-parametric `subroutine_ok` for `<States>::into_pb` on Arm 9
(`States.ct1Acknowledged`, tag `11`,
`+0 -> +60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544 -> ret`),
valid for any `Env` containing `Ct1AcknowledgedEnv s`. -/
theorem states_into_pb_ct1Acknowledged_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : AllocContractsBudget b M A lim ext)
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct1AcknowledgedEnv s evs → Env evs) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Acknowledged s) Env) := by
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw := sub_ok_memcpy_raw hmemcpy
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, hfit⟩, hmem⟩
  have hfit_ct1 : FitsEnv M lim st (Ct1AcknowledgedEnv s) := FitsEnv.mono hEnv hfit
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ct1Acknowledged s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_of_env st s0 s0 out stA (.ct1Acknowledged s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt1Acknowledged_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro a0
  apply SepWP.exists_elim; intro a1
  apply SepWP.exists_elim; intro a2
  apply SepWP.exists_elim; intro a3
  apply SepWP.exists_elim; intro a4
  apply SepWP.exists_elim; intro a5
  apply SepWP.exists_elim; intro hdr0
  apply SepWP.exists_elim; intro hdr1
  apply SepWP.exists_elim; intro hdr2
  apply SepWP.exists_elim; intro es0
  apply SepWP.exists_elim; intro es1
  apply SepWP.exists_elim; intro es2
  apply SepWP.exists_elim; intro cap_ct1
  apply SepWP.exists_elim; intro ptr_ct1
  have hfits_clone : FitsEvents M lim st (ct1CloneEvents s.uc.ct1) :=
    fitsEvents_ct1Clone_of_ct1AcknowledgedEnv cap_ct1 hfit_ct1
  have hfit_dec : FitsEnv M lim
      (M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st))
      (DecoderIntoPbAllocEnv s.receiving_ek) :=
    fitsEnv_decoder_of_ct1AcknowledgedEnv cap_ct1 hfit_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 11#64) ∗
      ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2) ∗
      ((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 11#64) ∗ A.pool lim st s0 ∗
       (statesIntoPbJumpTableAt b ∗
        memRegion out optProtoInnerStateSize ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
         ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
         ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
        (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
         ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
         ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
        memRegion (stA + 536#64) 392)) by sep_ac_rfl]
  apply SepWP.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60 A lim st s0 out stA 11#64
    (statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc hrun hx8 hx0
  refine seq_clean_wp hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _hvm1⟩
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      memRegion (s0.sp - 1520#64) 8 ∗ memRegion (s0.sp - 1512#64) 1416 :=
    ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [hsplit_1424]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWP.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 11#64) ∗ A.pool lim st s1 ∗
          (statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
            ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
            ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
           (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
            ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
            ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
            polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           memRegion (stA + 536#64) 392) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 11#64) ∗
           statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
            ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
            ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
           (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
            ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
            ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
            polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           memRegion (stA + 536#64) 392 ∗ A.pool lim st s1) by sep_ac_rfl]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w8
  apply SepWP.exists_elim; intro w16
  apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w32
  apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w48
  apply SepWP.exists_elim; intro w64
  apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w80
  apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w96
  apply SepWP.exists_elim; intro w104
  apply SepWP.exists_elim; intro w112
  apply SepWP.exists_elim; intro w120
  apply SepWP.exists_elim; intro w128
  apply SepWP.exists_elim; intro w136
  apply SepWP.exists_elim; intro w144
  apply SepWP.exists_elim; intro w152
  apply SepWP.exists_elim; intro w160
  apply SepWP.exists_elim; intro w168
  apply SepWP.exists_elim; intro w176
  apply SepWP.exists_elim; intro w184
  apply SepWP.exists_elim; intro w192
  apply SepWP.exists_elim; intro w200
  apply SepWP.exists_elim; intro w208
  apply SepWP.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
         ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
         ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v8 : BitVec 64,
         ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
         ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
         ∃∗ y0 : BitVec 64, ∃∗ y1 : BitVec 64, ∃∗ y2 : BitVec 64,
         ∃∗ y3 : BitVec 64, ∃∗ y4 : BitVec 64, ∃∗ y5 : BitVec 64,
           ct1AcknowledgedScratchCells s0.sp
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
             w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
           memRegion (s0.sp - 1360#64) 528 ∗
           memRegion (s0.sp - 832#64) 352 ∗
           memRegion (s0.sp - 432#64) 8 ∗
           memRegion (s0.sp - 352#64) 40 ∗
           memRegion (s0.sp - 312#64) 8 ∗
           memRegion (s0.sp - 208#64) 48 ∗
           memRegion (s0.sp - 112#64) 16) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ct1Acknowledged_scratch_split s0.sp))
  refine SepWP.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u0
  apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u2
  apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u4
  apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro v0
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro y0
  apply SepWP.exists_elim; intro y1
  apply SepWP.exists_elim; intro y2
  apply SepWP.exists_elim; intro y3
  apply SepWP.exists_elim; intro y4
  apply SepWP.exists_elim; intro y5
  have hpre1 := ct1Acknowledged_step_60_to_372 s0 s1 out stA
    (epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     ct1AcknowledgedScratchCells s0.sp
       u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
       w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
     memRegion (s0.sp - 1360#64) 528 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s1)
    hb_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine seq_vm_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hpre1) ?_
  intro s2 hpc2 hrun2 hvm2
    ⟨_hacp2, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx20_2, hx19_2, htr2⟩
  rw [← A.pool_transport lim st s1 s2 hvm2]
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ hdr0) ∗ ((a + 56#64) ↦₆₄ hdr1) ∗ ((a + 64#64) ↦₆₄ hdr2) ∗
    ((a + 72#64) ↦₆₄ es0) ∗ ((a + 80#64) ↦₆₄ es1) ∗ ((a + 88#64) ↦₆₄ es2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ cap_ct1) ∗ ((a + 8#64) ↦₆₄ ptr_ct1) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
    ((a + 24#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 32#64) s.receiving_ek
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 96#64) =
      (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 96#64) =
      (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
       ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 96#64 = stA + 104#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_wp hmemcpy_raw A lim st
    (szKeep := 96) (szReloc := 432) (szTotal := 528) (off := 96#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (words12 a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2)
    (words4_polyDecoderAt A.repAlloc cap_ct1 ptr_ct1
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.receiving_ek)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      statesIntoPbJumpTableAt b ∗
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      ct1AcknowledgedScratchCells s0.sp
        u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
      memRegion (s0.sp - 832#64) 352 ∗
      memRegion (s0.sp - 432#64) 8 ∗
      memRegion (s0.sp - 352#64) 40 ∗
      memRegion (s0.sp - 312#64) 8 ∗
      memRegion (s0.sp - 208#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 11#64) ∗
      memRegion out optProtoInnerStateSize ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hstep2 := ct1Acknowledged_step_376_to_424 s0 s3 out stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
    w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5
    (memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s3)
    hsp0_align hlen hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx20_3 hx19_3 htr3
  refine seq_vm_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2) ?_
  intro s4 hpc4 hrun4 hvm4
    ⟨_hacp4, hsp4, hx29_4, hx28_4, hx27_4, hx26_4, hx24_4, hx23_4,
     hx21_4, hx20_4, hx19_4, htr4⟩
  rw [← A.pool_transport lim st s3 s4 hvm4]
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  have hstep3 := ct1Acknowledged_step_424_to_1812_wp hA s0 s4 st out stA cap_ct1 ptr_ct1
    s.uc.epoch s.uc.ct1
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     ct1AcknowledgedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
       w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hfits_clone hsp0_align hlen hpc4 hrun4 hsp4 hx29_4 hx28_4 hx27_4 hx26_4 hx24_4 hx23_4
    hx21_4 hx20_4 hx19_4 htr4
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep3) ?_
  intro s5 _Pm5 hpc5 hrun5
    ⟨ptr_new, hPm5, hsp5, hx29_5, hx28_5, hx27_5, hx26_5,
     hx24_5, hx23_5, hx22_5, hx21_5, hx20_5, hx19_5, htr5⟩
  refine SepWP.weaken_pre hPm5 ?_
  have hstep4 := ct1Acknowledged_step_1812_to_1900 hA s0 s5
    (M.stepEvents (ct1CloneEvents s.uc.ct1) st)
    out stA cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    v0 v1 v2 v3 v4 v5 v6 v7 v8
    w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5
    (vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx28_5 hx27_5 hx26_5 hx24_5 hx23_5
    hx22_5 hx21_5 hx20_5 hx19_5 htr5
  refine seq_clean_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep4) ?_
  intro s6 hpc6 hrun6
    ⟨_hacp6, hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx27_6, hx26_6, hx22_6, hx21_6, hx19_6, htr6⟩
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  refine call_decoderIntoPb_expose_wp hdec_raw
    (M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st))
    (s0.sp - 352#64) (s0.sp - 1232#64) s.receiving_ek
    (Frame :=
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
      ct1AcknowledgedScratchCells s0.sp
        a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
        (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
      (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
       ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
      memRegion (s0.sp - 1360#64) 96 ∗
      memRegion (stA + 104#64) 432 ∗
      statesIntoPbJumpTableAt b ∗
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      memRegion (s0.sp - 832#64) 352 ∗
      memRegion (s0.sp - 432#64) 8 ∗
      memRegion (s0.sp - 312#64) 8 ∗
      memRegion (s0.sp - 208#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 11#64) ∗
      memRegion out optProtoInnerStateSize ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392)
    hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6 hfit_dec
    (by
      rw [← hrecomb_stack]
      dsimp only [protoPolynomialDecoderSize]
      sep_ac_rfl)
    fun s7 evs_dec d0 d1 d2 d3 d4 hpc7 hrun7 hsp7 hcs7 _hacp7 htr7 henv_dec => ?_
  dsimp only [LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget.protoPolynomialDecoderHeap]
  have hx19_7 : s7.readReg64 .x19 = out := hcs7.1.trans hx19_6
  have hx21_7 : s7.readReg64 .x21 = BitVec.ofNat 64 s.uc.ct1.length := hcs7.2.2.1.trans hx21_6
  have hx22_7 : s7.readReg64 .x22 = ptr_new := hcs7.2.2.2.1.trans hx22_6
  have hx26_7 : s7.readReg64 .x26 = s0.sp - 480#64 := hcs7.2.2.2.2.2.2.2.1.trans hx26_6
  have hx27_7 : s7.readReg64 .x27 = s.uc.epoch := hcs7.2.2.2.2.2.2.2.2.1.trans hx27_6
  have hx29_7 : s7.readReg64 .x29 = s0.sp - 96#64 := hcs7.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  simp only [arm64_norm]
  have hstep5 := ct1Acknowledged_step_1904_to_1544 s0 s7 out ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    d0 d1 d2 d3 d4
    v0 v1 v2 v3 v4 v5 v6 v7 v8
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     memRegion (s0.sp - 1232#64) polyDecoderSize ∗
     A.pool lim
       (M.stepEvents evs_dec
         (M.stepEvents (ct1DeallocEvents cap_ct1)
           (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s7 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc7 hrun7 hsp7 hx29_7 hx27_7 hx26_7 hx22_7 hx21_7 hx19_7 htr7
  refine seq_vm_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep5) ?_
  intro s8 hpc8 hrun8 hvm8 ⟨_hacp8, hsp8, hx29_8, hx19_8, hx21_8, hx22_8, htr8⟩
  rw [← A.pool_transport lim
    (M.stepEvents evs_dec
      (M.stepEvents (ct1DeallocEvents cap_ct1)
        (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s7 s8 hvm8]
  have hscratch := ct1AcknowledgedScratchCells_entails_memRegions s0.sp
    hdr0 hdr1 hdr2 es0 es1 es2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    d0 d1 d2 d3 d4
  have hstA := stA_ct1Acknowledged_entails_928 stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
  have hpre_epi :
      ct1AcknowledgedScratchCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
       ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
       ((s0.sp - 320#64) ↦₆₄ d4)) ∗
      epilogueStagingCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch d0 d1 d2 d3 d4 w176 w184
        w192 w200 w208 w216 ∗
      (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       memRegion (s0.sp - 1232#64) polyDecoderSize ∗
       A.pool lim
         (M.stepEvents evs_dec
           (M.stepEvents (ct1DeallocEvents cap_ct1)
             (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s8 ∗
       stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       memRegion (stA + 104#64) 432 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 11#64) ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch d0 d1 d2 d3 d4 w176 w184
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim
        (M.stepEvents evs_dec
          (M.stepEvents (ct1DeallocEvents cap_ct1)
            (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s8 ∗
      (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b) := by
    dsimp only [polyDecoderSize] at *
    refine Entails.trans (Entails.of_eq (show _ =
      (ct1AcknowledgedScratchCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
        ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
        ((s0.sp - 320#64) ↦₆₄ d4)) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       memRegion (s0.sp - 1232#64) 400 ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗
      ((stA ↦₆₄ 11#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       memRegion (stA + 104#64) 432 ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch d0 d1 d2 d3 d4 w176 w184
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       A.pool lim
         (M.stepEvents evs_dec
           (M.stepEvents (ct1DeallocEvents cap_ct1)
             (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s8 ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTableAt b) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := states_into_pb_epilogue A lim
    (M.stepEvents evs_dec
      (M.stepEvents (ct1DeallocEvents cap_ct1)
        (M.stepEvents (ct1CloneEvents s.uc.ct1) st)))
    s0 s8 out
    hdr0 hdr1 hdr2 es0 es1 es2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch d0 d1 d2 d3 d4 w176 w184
    w192 w200 w208 w216
    (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc8 hrun8 hsp8 hx29_8 hx19_8 htr8
  rw [hx22_8, hx21_8] at hep
  refine SepWP.mono (SepWP.weaken_pre hpre_epi hep)
    fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf, _hvmf⟩ => ?_
  refine ⟨⟨(ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1) ++ evs_dec,
    hEnv _ ⟨ct1DeallocEvents cap_ct1, evs_dec, rfl,
      freeOnlyEvs_ct1DeallocEvents cap_ct1, henv_dec⟩, ?_⟩,
    hspf, hcsf, htrf⟩
  rw [M.stepEvents_append, M.stepEvents_append]
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_ct1Acknowledged A.repAlloc out
    hdr0 hdr1 hdr2 es0 es1 es2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    d0 d1 d2 d3 d4
    w176 w184 w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       0x8000000000000009#64
       hdr0 hdr1 hdr2 es0 es1 es2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       d0 d1 d2 d3 d4 w176 w184
       w192 w200 w208 w216 ∗
     protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗
     A.pool lim
       (M.stepEvents evs_dec
         (M.stepEvents (ct1DeallocEvents cap_ct1)
           (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) sf ∗
     stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

/-- Tight `Ct1AcknowledgedEnv` `subroutine_ok` for Arm 9 (`States.ct1Acknowledged`). -/
theorem states_into_pb_ct1Acknowledged_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Acknowledged s) (Ct1AcknowledgedEnv s)) :=
  states_into_pb_ct1Acknowledged_of_env hA hdec hmemcpy s (fun _ h => h)

theorem states_into_pb_ct1Acknowledged_env_of_alloc
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Acknowledged s) (Ct1AcknowledgedEnv s)) :=
  states_into_pb_ct1Acknowledged_env hA hdec hA.session_memcpy_region s

/-- Default `statesIntoPbVariantSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`) `subroutine_ok`
for Arm 9 (`States.ct1Acknowledged`) under explicit payload/slot size bounds. -/
theorem states_into_pb_ct1Acknowledged_of_bounds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + s.receiving_ek.pts.length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧
      4 * sl.vec.length ≤
        2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b (.ct1Acknowledged s)) :=
  states_into_pb_ct1Acknowledged_of_env hA hdec hmemcpy s
    (fun _ => ct1AcknowledgedEnv_imp_spqrBoundedEvs hcnt (by omega) hct1_max hct1_req hpts)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
