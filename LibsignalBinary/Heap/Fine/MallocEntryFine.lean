/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.FineSpecs
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
import VerifiedLibraries.Mallocng.Proofs.MemsetSym
import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Fine-Grained Placed `default_malloc` and `malloc` Verification

Lifts `LibcMallocImplFineStmt` (`blk09`) across the `default_malloc` (`blk04`) tail branch to prove
`placed_defaultMalloc_fine_of_impl` and `placed_malloc_fine_entry_ok` over `FineBudget`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `blk04 → blk09` Tail-Branch Transfer -/

private theorem b04_tail_to_b09_fine [MallocngMultiPlacement] {spec : Spec Unit}
    (h9 : subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9) (withCL mmpl spec))
    (hPrePC : ∀ s0 pc', spec.pre () (s0.setPC pc') = spec.pre () s0)
    (hPostPC : ∀ s0 pc' sf, spec.post () (s0.setPC pc') sf = spec.post () s0 sf)
    (hOomPC : ∀ s0 pc' sf, spec.onOom () (s0.setPC pc') sf = spec.onOom () s0 sf)
    (hNoPanic : ∀ s0 sf, spec.onPanic () s0 sf = ⌜False⌝)
    (hNoExit : ∀ code s0 sf, spec.onExit () code s0 sf = ⌜False⌝) :
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4) (withCL mmpl spec) := by
  apply subroutine_ok_of_sepWP_init
  intro u R s0 hpc hrun hpre hspAl0
  cases u
  have hpre_cl : s0.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗ (spec.pre () s0 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [withCL]
    rw [sepConj_comm (spec.pre () s0), sepConj_assoc]
    exact Entails.refl _
  rw [satisfies_pure_sepConj] at hpre_cl
  have hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hpre_cl.1
  refine ⟨(withCL mmpl spec).pre () s0, hpre, ?_⟩
  rw [mallocngBlockProg_eq_b04]
  have hpc0 : s0.pc = mbase 4 + 0#64 := by rw [hpc, BitVec.add_zero]
  generalize hb_eq : mbase 4 = b4 at hpc0 ⊢
  have hb4 : BlkBase 4 b4 := hb_eq.symm
  have _ := hb4
  wp_step
  subst hb_eq
  have hTarget9 : mbase 4 + (mbase 9 - mbase 4) = mbase 9 := by bv_arith
  rw [hTarget9]
  refine sepWP_of_other_mallocng_block (j := 9) (svc := msvc) (by decide) hcl0
    (fun pc => externAt?_placedProgram_rebase_none _ _ _ _ pc) rfl ?_
  refine SepWP.call_subroutine_frame (F := emp) (x := ()) (ret_pc := s0.readReg64 .lr) h9
    rfl hrun hspAl0 rfl
    (fun R' hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withCL] at hp
      rw [hNoPanic] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withCL] at he
      rw [hNoExit] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withCL] at hm ⊢
    rw [hPrePC]
    simpa [emp_sepConj] using hm
  · refine SepWP.done hpc_f hrun_f ⟨?_, hsp_f, hcs_f⟩
    intro hm
    dsimp only [withCL] at hm ⊢
    rw [hPostPC] at hm
    simpa [sepConj_emp] using hm
  · dsimp only [withCL] at ho ⊢
    rw [hOomPC] at ho
    simpa [emp_sepConj] using ho

/-! ## `DefaultMallocFineStmt` and Cross-Block Lifts -/

theorem placed_defaultMalloc_fine_of_impl (hImpl : LibcMallocImplFineStmt) :
    DefaultMallocFineStmt := by
  intro _ γ tp brkStart b ivs0 req
  exact b04_tail_to_b09_fine (hImpl γ tp brkStart b ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem call_placed_defaultMalloc_fine [MallocngMultiPlacement] (h : DefaultMallocFineStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 4) (libcMallocImplFineSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 4) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem call_placed_libcMallocImpl_fine_raw [MallocngMultiPlacement] (h : LibcMallocImplFineRawStmt)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplFineRawSpec γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

/-! ## `FinePostEnv` Packing and `placed_malloc_fine_entry_ok` -/

theorem pack_finePostEnv [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bf : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (st' : MallocngSt)
    (alignMap' : BitVec 64 → Option Nat) (live' peak' : Nat) (s0 sf : State)
    (hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart) :
    (MallocngRoTablesA maddrs ∗
     FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
       (dynamicRootRegions st') alignMap' live' peak' st' ∗
     MallocngRuntime maddrs tp) ⊢
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
  have hEx :
      FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
        (dynamicRootRegions st') alignMap' live' peak' st' ⊢
      ∃∗ st : MallocngSt,
      ∃∗ alignMap : BitVec 64 → Option Nat,
      ∃∗ liveCost : Nat,
      ∃∗ peakCost : Nat,
        FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
          (dynamicRootRegions st') alignMap liveCost peakCost st :=
    Entails.sepExists_right st'
      (Entails.sepExists_right alignMap'
        (Entails.sepExists_right live'
          (Entails.sepExists_right peak' (Entails.refl _))))
  have hHeap :
      (MallocngRoTablesA maddrs ∗
       FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
         (dynamicRootRegions st') alignMap' live' peak' st' ∗
       MallocngRuntime maddrs tp) ⊢
      FineHeapImpl γ maddrs tp brkStart sf.brk bf (dynamicRootRegions st') := by
    rw [FineHeapImpl_eq, FineCoreImpl_eq, ← sepConj_assoc]
    exact sepConj_mono_left (sepConj_mono_right hEx)
  unfold FinePostEnv FineEnv
  exact Entails.sepExists_right (dynamicRootRegions st')
    (Entails.pure_right hNoOrph (Entails.pure_right ⟨htp, hbrks⟩ hHeap))

private theorem stackFrameAt_1024_split_704 (s0 : State) :
    stackFrameAt s0.sp mallocngStackBytes =
      (stackFrame s0 704 ∗ stackFrameAt (s0.sp - 704#64) 320) := by
  change stackFrameAt s0.sp (704 + 320) = _
  rw [stackFrameAt_split s0.sp 704 320, stackFrameAt_eq_memRegion s0.sp 704]

theorem fineStepReserve_alloc_ite (ok : Bool) (n : Nat) (b : FineBudget) :
    (if ok then fineStepReserve (.alloc n) b else fineStepReserve (.alloc 0) b) =
      fineStepReserve (if ok then .alloc n else .alloc 0) b := by
  cases ok <;> rfl

private theorem mallocFine_success_post_entails [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : BitVec 64) (s0 sf : State)
    (hReq : req.toNat ≤ MallocngMaxAllocSize) :
    let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
    let bf := if ok then FineBudget.stepAlloc req.toNat b else b
    (∃∗ p : BitVec 64,
     ∃∗ bs : List (BitVec 8),
     ∃∗ st' : MallocngSt,
     ∃∗ alignMap' : BitVec 64 → Option Nat,
     ∃∗ live' : Nat,
     ∃∗ peak' : Nat,
       ⌜sf.readReg64 .x0 = p ∧
        sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
        MallocngBlockWf p req.toNat ∧
        bs.length = req.toNat ∧
        MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
        ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
          g'.slots[idx]'hIdx = .liveUser p req.toNat (max req.toNat MallocngMinBlockCost) ∧
          p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
          (g'.isMmapped = true → bs = List.replicate req.toNat 0#8)⌝ ∗
       MallocngRoTablesA maddrs ∗
       FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
         (dynamicRootRegions st') alignMap' live' peak' st' ∗
       MallocngRuntime maddrs tp ∗
       (p ↦ₛ bs) ∗
       FineBlock γ p req.toNat 16) ⊢
      ⌜(OptOwn (FineBlockSem γ)).pureWf (sf.readReg64 .x0)
        (if ok then some (req.toNat, 16) else none)⌝ ∗
      (OptOwn (FineBlockSem γ)).interp (sf.readReg64 .x0)
        (if ok then some (req.toNat, 16) else none) ∗
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
  intro ok bf
  have hOkTrue : ok = true := decide_eq_true hReq
  apply Entails.sepExists_elim; intro p
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro st'
  apply Entails.sepExists_elim; intro alignMap'
  apply Entails.sepExists_elim; intro live'
  apply Entails.sepExists_elim; intro peak'
  apply Entails.pure_left
  rintro ⟨hx0_f, htp_f, hbrkS_f, ⟨hp_ne, hp_al, hp_48, _⟩, hbs_len, hNoOrph, _⟩
  have hp_64 : p.toNat + req.toNat < 2 ^ 64 := by omega
  rw [hOkTrue]
  simp only [↓reduceIte, OptOwn_pureWf_some, OptOwn_interp_some, FineBlockSem]
  rw [hx0_f]
  refine Entails.pure_right ⟨hp_ne, hp_ne, hp_al, hp_64⟩ ?_
  have hBsReg : (p ↦ₛ bs) ⊢ memRegion p req.toNat := by
    rw [← hbs_len]
    exact pointsToBytes_entails_memRegion p bs
  have hPostEnv := pack_finePostEnv γ tp brkStart bf ivs0 st' alignMap' live' peak'
    s0 sf hNoOrph htp_f hbrkS_f
  have hRearr :
      MallocngRoTablesA maddrs ∗
        FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
          (dynamicRootRegions st') alignMap' live' peak' st' ∗
        MallocngRuntime maddrs tp ∗
        (p ↦ₛ bs) ∗
        FineBlock γ p req.toNat 16 =
      (FineBlock γ p req.toNat 16 ∗ (p ↦ₛ bs)) ∗
        (MallocngRoTablesA maddrs ∗
         FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
           (dynamicRootRegions st') alignMap' live' peak' st' ∗
         MallocngRuntime maddrs tp) := by
    generalize MallocngRoTablesA maddrs = pRo,
      FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
        (dynamicRootRegions st') alignMap' live' peak' st' = pCr,
      MallocngRuntime maddrs tp = pRt,
      (p ↦ₛ bs) = pBs,
      FineBlock γ p req.toNat 16 = pBlk
    ac_rfl
  rw [hRearr]
  exact sepConj_mono (sepConj_mono_right hBsReg) hPostEnv

private theorem mallocFine_withCL_of_defaultMalloc [MallocngMultiPlacement]
    (hDef : DefaultMallocFineStmt) (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (withCL mmpl (fineMallocSpec msvc γ maddrs (mbase 4))) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hspAl0
  rcases x with ⟨req, sp, tp, brkStart, b, ivs0⟩
  have hPurePre : s0.readReg64 .x0 = req ∧ s0.sp = sp := by
    have hp := hpre
    dsimp only [withCL, fineMallocSpec] at hp
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp1 := hp.1
    simp only [ctype_simp, and_true] at hp1
    exact hp1
  rcases hPurePre with ⟨hx0, hsp⟩
  subst hsp
  refine ⟨(withCL mmpl (fineMallocSpec msvc γ maddrs (mbase 4))).pre
    (req, s0.sp, tp, brkStart, b, ivs0) s0, hpre, ?_⟩
  refine SepWP.call_subroutine_frame
    (F := stackFrameAt (s0.sp - 704#64) 320)
    (x := ()) (ret_pc := s0.readReg64 .lr)
    (hDef γ tp brkStart b ivs0 req.toNat)
    hpc hrun hspAl0 rfl
    (fun R' hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withCL, libcMallocImplFineSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withCL, libcMallocImplFineSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [withCL, fineMallocSpec, libcMallocImplFineSpec]
    simp only [ctype_simp]
    rw [stackFrameAt_1024_split_704 s0, sepConj_assoc]
    apply Entails.pure_left; intro _
    have hx0_nat : (s0.readReg64 .x0).toNat = req.toNat := by rw [hx0]
    refine Entails.trans (Entails.pure_right hx0_nat (Entails.refl _)) ?_
    generalize ⌜(s0.readReg64 .x0).toNat = req.toNat⌝ = pReq,
      FineEnv γ maddrs tp brkStart b ivs0 s0 = pEnv,
      stackFrame s0 704 = pSf1,
      stackFrameAt (s0.sp - 704#64) 320 = pSf2,
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ = pCl
    exact Entails.of_eq (by ac_rfl)
  · refine SepWP.done hpc_f hrun_f ⟨?_, hsp_f, hcs_f⟩
    intro hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [withCL, fineMallocSpec, libcMallocImplFineSpec, MallocngCallAccounting, FineBudget.step]
    rw [fineStepReserve_alloc_ite]
    have hPostRearr : ∀ (pAcc pSf1 br pCl pSf2 : SepProp),
        ((pAcc ∗ pSf1 ∗ br) ∗ pCl) ∗ pSf2 = (pAcc ∗ (br ∗ (pSf1 ∗ pSf2))) ∗ pCl := by
      intros; ac_rfl
    rw [hPostRearr]
    refine sepConj_mono_left ?_
    rw [← stackFrameAt_1024_split_704 s0]
    apply Entails.pure_left; intro hAcc
    have hBr :
        (if req.toNat ≤ MallocngMaxAllocSize then
          ∃∗ p : BitVec 64,
          ∃∗ bs : List (BitVec 8),
          ∃∗ st' : MallocngSt,
          ∃∗ alignMap' : BitVec 64 → Option Nat,
          ∃∗ live' : Nat,
          ∃∗ peak' : Nat,
            ⌜sf.readReg64 .x0 = p ∧
             sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
             MallocngBlockWf p req.toNat ∧
             bs.length = req.toNat ∧
             MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
             ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
               g'.slots[idx]'hIdx = .liveUser p req.toNat (max req.toNat MallocngMinBlockCost) ∧
               p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
               (g'.isMmapped = true → bs = List.replicate req.toNat 0#8)⌝ ∗
            MallocngRoTablesA maddrs ∗
            FineCoreStInflightA 0 γ maddrs brkStart sf.brk
              (if decide (req.toNat ≤ MallocngMaxAllocSize) then FineBudget.stepAlloc req.toNat b else b)
              (dynamicRootRegions st') alignMap' live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            (p ↦ₛ bs) ∗
            FineBlock γ p req.toNat 16
        else
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          FinePostEnv γ maddrs tp brkStart
            (if decide (req.toNat ≤ MallocngMaxAllocSize) then FineBudget.stepAlloc req.toNat b else b)
            ivs0 s0 sf) ⊢
        ⌜(OptOwn (FineBlockSem γ)).pureWf (sf.readReg64 .x0)
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then some (req.toNat, 16) else none)⌝ ∗
        (OptOwn (FineBlockSem γ)).interp (sf.readReg64 .x0)
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then some (req.toNat, 16) else none) ∗
        FinePostEnv γ maddrs tp brkStart
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then FineBudget.stepAlloc req.toNat b else b)
          ivs0 s0 sf := by
      by_cases hReq : req.toNat ≤ MallocngMaxAllocSize
      · have hM := mallocFine_success_post_entails γ tp brkStart b ivs0 req s0 sf hReq
        dsimp only at hM
        simp only [hReq, ↓reduceIte] at hM ⊢
        exact hM
      · simp only [hReq, decide_false, Bool.false_eq_true, ↓reduceIte,
          OptOwn_pureWf_none, OptOwn_interp_none]
        exact Entails.pure_right trivial (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hBr) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hPureWf
    refine Entails.pure_right ⟨hPureWf, hAcc⟩ ?_
    rw [sepConj_assoc]
    exact Entails.refl _
  · dsimp only [withCL, fineMallocSpec, libcMallocImplFineSpec] at ho ⊢
    rw [fineStepReserve_alloc_ite]
    rw [← sepConj_assoc, sepConj_comm _ (stackFrameAt (s0.sp - 704#64) 320), sepConj_assoc] at ho
    exact Satisfies.drop_left ho

/-- Multi-block placed `malloc(req)` (`blk04`) satisfies `fineMallocSpec`. -/
theorem placed_malloc_fine_entry_ok (hImpl : LibcMallocImplFineStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (fineMallocSpec svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPlace, hSvc⟩
  refine ⟨by decide, 4, 0, rfl, ?_⟩
  rw [fnAddr_malloc mpl]
  exact withCL_to_withCodeLoaded
    (mallocFine_withCL_of_defaultMalloc (placed_defaultMalloc_fine_of_impl hImpl) γ)

/-! ## Entrypoint Accounting and Zero-Fill Helpers -/

namespace EntryHelpers

theorem mappedDelta_congr_perm {k nb : Nat} {m0 m0' mf mf' : Memory}
    (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hd : MallocngMappedDelta k nb m0' mf') : MallocngMappedDelta k nb m0 mf := by
  obtain ⟨ivs, hlen, hsum, hcov⟩ := hd; refine ⟨ivs, hlen, hsum, fun a ha => ?_⟩
  rw [hf] at ha; rcases hcov a ha with hm0' | hiv
  · left; rwa [← h0]
  · right; exact hiv

theorem noOrphanMappings_congr_perm {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m0' mf mf' : Memory} (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hno : MallocngNoOrphanMappings ivs0 ivsf m0' mf') : MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  intro a ha hsrc; rw [hf] at ha; rw [← h0] at hsrc; exact hno a ha hsrc

theorem fineOomCond_of_pre_perm {svc : State → State} {stepB : Nat} {s0 s1 sf : State}
    (hfs : s1.fs = s0.fs) (htr : s1.trace = s0.trace) (hsig : s1.sigActions = s0.sigActions)
    (hperm : s1.mem.perm = s0.mem.perm) (hoom : FineStepOomCond svc stepB s1 sf) :
    FineStepOomCond svc stepB s0 sf := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hoom
  exact ⟨h1.trans hfs, h2.trans htr, h3.trans hsig, mappedDelta_congr_perm hperm rfl h4, h5⟩

theorem procPreserved_trans {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) : CalleeSavedPreserved s0 s2 := by
  obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av⟩ := h01
  obtain ⟨b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv⟩ := h12
  exact ⟨b19.trans a19, b20.trans a20, b21.trans a21, b22.trans a22, b23.trans a23, b24.trans a24,
    b25.trans a25, b26.trans a26, b27.trans a27, b28.trans a28, b29.trans a29, bv.trans av⟩

theorem sepWP_false_oom {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P post (fun _ => ⌜False⌝)) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  refine reaches_pc_seq (SepWP.to_reaches_pc h hm) ?_
    (fun _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro sf hpc hrun ⟨P_f, hmf, hpost⟩
  exact SepWP.to_reaches_pc (SepWP.done hpc hrun hpost) hmf

theorem postEnv_congr_pre_post [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bf : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (s0 s_bl sm sf : State)
    (hperm0 : s_bl.mem.perm = s0.mem.perm) (hmemf : sf.mem = sm.mem)
    (hbrkf : sf.brk = sm.brk) (htpf : sf.tpidrEl0 = sm.tpidrEl0)
    (hbrksf : sf.brkStart = sm.brkStart) :
    FinePostEnv γ maddrs tp brkStart bf ivs0 s_bl sm ⊢
      FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf := by
  unfold FinePostEnv FineEnv
  refine Entails.sepExists_mono fun ivsf => ?_
  rw [hbrkf, htpf, hbrksf]
  exact sepConj_mono_left (Entails.pure_mono fun h =>
    noOrphanMappings_congr_perm hperm0 (congrArg Memory.perm hmemf) h)

private theorem readBytes_of_prefixFilled' {m₀ mf : Memory} {dst c : BitVec 64} {n : Nat}
    (hfc : PrefixFilled m₀ mf dst c n n) : mf.readBytes dst n = List.replicate n (c.truncate 8) := by
  have go : ∀ k off, off + k ≤ n →
      mf.readBytes (dst + BitVec.ofNat 64 off) k = List.replicate k (c.truncate 8) := by
    intro k; induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro off hk; simp only [Memory.readBytes, List.replicate_succ]
      rw [hfc.2 off (by omega),
          show dst + BitVec.ofNat 64 off + 1#64 = dst + BitVec.ofNat 64 (off + 1) by bv_omega,
          ih (off + 1) (by omega)]
  simpa using go n 0 (by omega)

theorem placed_memsetZero_perm_ok [MallocngMultiPlacement] {P : Program}
    (dst : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hbsLen : bs.length = n) (hn48 : n ≤ 2 ^ 48)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 21) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg32 .x1 = 0#32 ∧ (s0.readReg64 .x2).toNat = n⌝ ∗ (dst ↦ₛ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
         sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ List.replicate n 0#8)
    }) := by
  refine subroutine_ok_block_to_block_plain (j := 21) (by decide) ?_ hext hsvc
  have hw := hasWords_blk_relocFree (i := 21) (by decide) (ws := memsetWordsSym) (by decide +kernel)
  have hc : (mallocngBlockProg mmpl 21 msvc).hasCode (mbase 21) memsetWordsSym := hw
  apply subroutine_ok_outcome_intro; intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx1_32, hx2⟩, hmem⟩ := hpre
  have htrunc : (s0.readReg64 .x1).truncate 8 = 0#8 := by
    have h32 : (s0.readReg64 .x1).truncate 32 = 0#32 := hx1_32
    revert h32; generalize s0.readReg64 .x1 = v; intro h32; bv_bits
  refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
  by_cases hn96 : n ≤ 96
  · have hc_ns : ((mallocngBlockProg mmpl 21 msvc).withSvc mallocngFaultSvc).hasCode (mbase 21) memsetWordsSym :=
      Program.hasWords_withSvc hc
    have hwp := SepWP.lift_noSyscalls (prog := mallocngBlockProg mmpl 21 msvc) (oom := fun _ => ⌜False⌝) rfl rfl
      (memset_sepWP_le96 _ (mbase 21) hc_ns s0 dst (s0.readReg64 .x1) (s0.readReg64 .x2) bs
        hpc hrun hx0 rfl rfl (by omega) (by omega))
    refine reaches_pc_mono (SepWP.to_reaches_pc hwp hmem) ?_ (fun _ _ h => not_satisfies_false_sepConj h)
    rintro sf _ _ ⟨P_f, hmf, ⟨⟨hx0_f, hsp_f, hcs_f, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩, hent⟩, hperm⟩
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ List.replicate n 0#8) ∗ R := by
      have hm' := Satisfies.mono (sepConj_mono_left hent) hmf; rwa [htrunc, hx2] at hm'
    refine ⟨?_, hsp_f, hcs_f⟩; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hperm, hx0_f⟩, hpost_mem⟩
  · have hreg : s0.mem ⊨ memRegion dst n ∗ R := by
      have hent := (IsBlock.pointsToBytes dst bs).entails_memRegion; rw [hbsLen] at hent
      exact Satisfies.mono (sepConj_mono_left hent) hmem
    have hrw : s0.mem.RW dst (s0.readReg64 .x2).toNat := by
      rw [hx2]; exact (IsBlock.memRegion dst n).rw hreg
    refine memset_sym_large (mallocngBlockProg mmpl 21 msvc) (mbase 21) hc s0 _
      dst (s0.readReg64 .x1) (s0.readReg64 .x2) hpc hrun hx0 rfl rfl hrw (by omega) (by omega) ?_
    rintro sf _ _ hx0_f ⟨hcc, _hlr, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩ hfc
    let zbs := List.replicate n 0#8
    have hzlen : zbs.length = n := List.length_replicate
    have hdst_bytes : sf.mem.readBytes dst zbs.length = zbs := by
      rw [hzlen]; have hrb := readBytes_of_prefixFilled' hfc; rwa [htrunc, hx2] at hrb
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ zbs) ∗ R :=
      (IsBlock.memRegion dst n).update (IsBlock.pointsToBytes dst zbs)
        (Nat.le_of_eq hzlen) hreg (by simpa [hx2] using hfc.1) ⟨by omega, hdst_bytes⟩
    refine ⟨?_, hcc⟩; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hfc.perm_eq, hx0_f⟩, hpost_mem⟩

end EntryHelpers

end LibsignalBinary.Heap.Fine
