/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.CType
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplProof
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cost.TokSpecs
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0

/-!
# Placed `default_malloc` / `malloc` Entry Proof

Lifts the `__libc_malloc_impl` (`blk09`) contracts across the tail-branch stub `default_malloc`
(`blk04`, `b __libc_malloc_impl`) and packages them into the public `mallocngMultiEntryOk`
contracts (`mallocngMallocTokSpec`, `mallocngMallocTightSpec`, `mallocngMallocSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.ProgramReflection VerifiedLibraries.Mallocng

/-! ## Tail-branch transfer from `blk04` to `blk09` -/

private theorem b04_tail_to_b09 [MallocngMultiPlacement] {spec : Spec Unit}
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

/-! ## Internal `DefaultMallocPlacedStmt` contracts -/

theorem placed_defaultMalloc24_of_impl (hImpl24 : LibcMallocImplPlaced24B2Stmt) :
    ∀ [MallocngMultiPlacement]
      (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
      (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
      subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
        (libcMallocImplPlacedSpec24B2 γ tp brkStart b ivs0 req) := by
  intro _ γ tp brkStart b ivs0 req
  exact b04_tail_to_b09 (hImpl24 γ tp brkStart b ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem placed_defaultMalloc24_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv) :
    ∀ [MallocngMultiPlacement]
      (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
      (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
      subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
        (libcMallocImplPlacedSpec24B2 γ tp brkStart b ivs0 req) :=
  placed_defaultMalloc24_of_impl (placed_libcMallocImpl24B2_ok hMeta hSlot hMetaInv)

theorem placed_defaultMalloc_tight_of_impl (hImpl : LibcMallocImplPlacedTightStmt) :
    DefaultMallocPlacedTightStmt := by
  intro _ γ tp brkStart b ivs0 req
  exact b04_tail_to_b09 (hImpl γ tp brkStart b ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem placed_defaultMalloc_tok_of_impl {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    (hImpl : LibcMallocImplPlacedTokStmt B) : DefaultMallocPlacedTokStmt B := by
  intro _ γ tp brkStart b ivs0 req
  exact b04_tail_to_b09 (hImpl γ tp brkStart b ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem placed_defaultMalloc_of_impl (hImpl : LibcMallocImplPlacedStmt) :
    DefaultMallocPlacedStmt := by
  intro _ γ tp brkStart b ivs0 req
  exact b04_tail_to_b09 (hImpl γ tp brkStart b ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem placed_defaultMalloc_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (hMetaInv : MallocngMetaCountInv) : DefaultMallocPlacedStmt :=
  placed_defaultMalloc_of_impl (placed_libcMallocImpl_ok hMeta hSlot hMetaInv)

theorem placed_defaultMalloc24_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt) :
    ∀ [MallocngMultiPlacement]
      (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
      (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
      subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
        (libcMallocImplPlacedSpec24B2 γ tp brkStart b ivs0 req) :=
  placed_defaultMalloc24_of_impl (placed_libcMallocImpl24B2_uncond_ok hMeta hSlot)

theorem placed_defaultMalloc_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt) : DefaultMallocPlacedStmt :=
  placed_defaultMalloc_of_impl (placed_libcMallocImpl_uncond_ok hMeta hSlot)

/-! ## Bridge to public `mallocngMallocSpec` -/

private theorem stackFrameAt_1024_split (s0 : State) :
    stackFrameAt s0.sp mallocngStackBytes =
      (stackFrame s0 704 ∗ stackFrameAt (s0.sp - 704#64) 320) := by
  change stackFrameAt s0.sp (704 + 320) = _
  rw [stackFrameAt_split s0.sp 704 320, stackFrameAt_eq_memRegion s0.sp 704]

private theorem mallocPlaced_success_post_entails [MallocngMultiPlacement]
    {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : BitVec 64) (s0 sf : State)
    (hReq : req.toNat ≤ MallocngMaxAllocSize) :
    let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
    let bf := mallocngAllocBudget ok req.toNat b
    (∃∗ p : BitVec 64,
     ∃∗ bs : List (BitVec 8),
     ∃∗ st' : MallocngSt,
       ⌜sf.readReg64 .x0 = p ∧
        sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
        MallocngBlockWf p req.toNat ∧
        bs.length = req.toNat ∧
        MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
        MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
        ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
          g'.slots[idx]'hIdx = .liveUser p req.toNat (max req.toNat MallocngMinBlockCost) ∧
          p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
          (g'.isMmapped = true → bs = List.replicate req.toNat 0#8)⌝ ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
       MallocngRuntime maddrs tp ∗
       (p ↦ₛ bs) ∗
       B γ p req.toNat 16) ⊢
      ⌜(OptOwn (MallocngTokBlock (B γ))).pureWf (sf.readReg64 .x0)
        (if ok then some (req.toNat, 16) else none)⌝ ∗
      (OptOwn (MallocngTokBlock (B γ))).interp (sf.readReg64 .x0)
        (if ok then some (req.toNat, 16) else none) ∗
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf := by
  intro ok bf
  have hOkTrue : ok = true := decide_eq_true hReq
  apply Entails.sepExists_elim; intro p
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro st'
  apply Entails.pure_left
  rintro ⟨hx0_f, htp_f, hbrkS_f, ⟨hp_ne, hp_al, hp_48, _⟩, hbs_len, hNoOrph, hCnt, _⟩
  have hp_64 : p.toNat + req.toNat < 2 ^ 64 := by omega
  rw [hOkTrue]
  simp only [↓reduceIte, OptOwn_pureWf_some, OptOwn_interp_some, MallocngTokBlock]
  rw [hx0_f]
  refine Entails.pure_right ⟨hp_ne, hp_ne, hp_al, hp_64⟩ ?_
  have hBsReg : (p ↦ₛ bs) ⊢ memRegion p req.toNat := by
    rw [← hbs_len]
    exact pointsToBytes_entails_memRegion p bs
  have hPostEnv :
      MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
        MallocngRuntime maddrs tp ⊢
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf := by
    unfold MallocngPostEnv MallocngEnv
    refine Entails.trans ?_ (Entails.sepExists_intro (dynamicRootRegions st'))
    refine Entails.pure_right hNoOrph (Entails.pure_right ⟨htp_f, hbrkS_f⟩ ?_)
    change _ ⊢ MallocngHeapImpl γ maddrs tp brkStart sf.brk bf (dynamicRootRegions st')
    rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq]
    have hCoreBody :
        MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ⊢
          ∃∗ st : MallocngSt,
            ⌜MallocngCountIvsWF bf (dynamicRootRegions st') st⌝ ∗
            MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st :=
      Entails.trans (Entails.pure_right hCnt (Entails.refl _))
        (Entails.sepExists_intro
          (P := fun st =>
            ⌜MallocngCountIvsWF bf (dynamicRootRegions st') st⌝ ∗
            MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st) st')
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hCoreBody)) ?_
    generalize MallocngRoTablesA maddrs = pRo,
      (∃∗ st : MallocngSt,
        ⌜MallocngCountIvsWF bf (dynamicRootRegions st') st⌝ ∗
        MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st) = pEx,
      MallocngRuntime maddrs tp = pRt
    exact Entails.of_eq (by ac_rfl)
  have hRearr :
      MallocngRoTablesA maddrs ∗
        MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
        MallocngRuntime maddrs tp ∗
        (p ↦ₛ bs) ∗
        B γ p req.toNat 16 =
      (B γ p req.toNat 16 ∗ (p ↦ₛ bs)) ∗
        (MallocngRoTablesA maddrs ∗
         MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
         MallocngRuntime maddrs tp) := by
    generalize MallocngRoTablesA maddrs = pRo,
      MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' = pCr,
      MallocngRuntime maddrs tp = pRt,
      (p ↦ₛ bs) = pBs,
      B γ p req.toNat 16 = pBlk
    ac_rfl
  rw [hRearr]
  exact sepConj_mono (sepConj_mono_right hBsReg) hPostEnv

private theorem mallocPlaced_withCL_tok_of_defaultMalloc [MallocngMultiPlacement]
    {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (hDef : DefaultMallocPlacedTokStmt B) (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (withCL mmpl (mallocngMallocTokSpec B msvc γ maddrs (mbase 4))) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hspAl0
  rcases x with ⟨req, sp, tp, brkStart, b, ivs0⟩
  have hPurePre : s0.readReg64 .x0 = req ∧ s0.sp = sp := by
    have hp := hpre
    dsimp only [withCL, mallocngMallocTokSpec] at hp
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp1 := hp.1
    simp only [ctype_simp, and_true] at hp1
    exact hp1
  rcases hPurePre with ⟨hx0, hsp⟩
  subst hsp
  refine ⟨(withCL mmpl (mallocngMallocTokSpec B msvc γ maddrs (mbase 4))).pre
    (req, s0.sp, tp, brkStart, b, ivs0) s0, hpre, ?_⟩
  refine SepWP.call_subroutine_frame
    (F := stackFrameAt (s0.sp - 704#64) 320)
    (x := ()) (ret_pc := s0.readReg64 .lr)
    (hDef γ tp brkStart b ivs0 req.toNat)
    hpc hrun hspAl0 rfl
    (fun R' hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withCL, libcMallocImplPlacedTokSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withCL, libcMallocImplPlacedTokSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [withCL, mallocngMallocTokSpec, libcMallocImplPlacedTokSpec]
    simp only [ctype_simp]
    rw [stackFrameAt_1024_split s0, sepConj_assoc]
    apply Entails.pure_left; intro _
    have hx0_nat : (s0.readReg64 .x0).toNat = req.toNat := by rw [hx0]
    refine Entails.trans (Entails.pure_right hx0_nat (Entails.refl _)) ?_
    generalize ⌜(s0.readReg64 .x0).toNat = req.toNat⌝ = pReq,
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0 = pEnv,
      stackFrame s0 704 = pSf1,
      stackFrameAt (s0.sp - 704#64) 320 = pSf2,
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ = pCl
    exact Entails.of_eq (by ac_rfl)
  · refine SepWP.done hpc_f hrun_f ⟨?_, hsp_f, hcs_f⟩
    intro hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [withCL, mallocngMallocTokSpec, libcMallocImplPlacedTokSpec, MallocngCallAccounting]
    have hPostRearr : ∀ (pAcc pSf1 br pCl pSf2 : SepProp),
        ((pAcc ∗ pSf1 ∗ br) ∗ pCl) ∗ pSf2 = (pAcc ∗ (br ∗ (pSf1 ∗ pSf2))) ∗ pCl := by
      intros; ac_rfl
    rw [hPostRearr]
    refine sepConj_mono_left ?_
    rw [← stackFrameAt_1024_split s0]
    apply Entails.pure_left; intro hAcc
    have hBr :
        (if req.toNat ≤ MallocngMaxAllocSize then
          ∃∗ p : BitVec 64,
          ∃∗ bs : List (BitVec 8),
          ∃∗ st' : MallocngSt,
            ⌜sf.readReg64 .x0 = p ∧
             sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
             MallocngBlockWf p req.toNat ∧
             bs.length = req.toNat ∧
             MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
             MallocngCountIvsWF
               (mallocngAllocBudget (decide (req.toNat ≤ MallocngMaxAllocSize)) req.toNat b)
               (dynamicRootRegions st') st' ∧
             ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
               g'.slots[idx]'hIdx = .liveUser p req.toNat (max req.toNat MallocngMinBlockCost) ∧
               p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
               (g'.isMmapped = true → bs = List.replicate req.toNat 0#8)⌝ ∗
            MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk
              (mallocngAllocBudget (decide (req.toNat ≤ MallocngMaxAllocSize)) req.toNat b).liveCost
              (mallocngAllocBudget (decide (req.toNat ≤ MallocngMaxAllocSize)) req.toNat b).peakCost st' ∗
            MallocngRuntime maddrs tp ∗
            (p ↦ₛ bs) ∗
            B γ p req.toNat 16
        else
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart
            (mallocngAllocBudget (decide (req.toNat ≤ MallocngMaxAllocSize)) req.toNat b)
            ivs0 s0 sf) ⊢
        ⌜(OptOwn (MallocngTokBlock (B γ))).pureWf (sf.readReg64 .x0)
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then some (req.toNat, 16) else none)⌝ ∗
        (OptOwn (MallocngTokBlock (B γ))).interp (sf.readReg64 .x0)
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then some (req.toNat, 16) else none) ∗
        MallocngPostEnv mallocngIface γ maddrs tp brkStart
          (mallocngAllocBudget (decide (req.toNat ≤ MallocngMaxAllocSize)) req.toNat b)
          ivs0 s0 sf := by
      by_cases hReq : req.toNat ≤ MallocngMaxAllocSize
      · have hM := mallocPlaced_success_post_entails (B := B) γ tp brkStart b ivs0 req s0 sf hReq
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
  · dsimp only [withCL, mallocngMallocTokSpec, libcMallocImplPlacedTokSpec] at ho ⊢
    rw [← sepConj_assoc, sepConj_comm _ (stackFrameAt (s0.sp - 704#64) 320), sepConj_assoc] at ho
    exact Satisfies.drop_left ho

/-! ## Public `mallocngMultiEntryOk` contracts -/

theorem mallocPlaced_entry_tok_mmpl_ok {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    (hDef : DefaultMallocPlacedTokStmt B) :
    ∀ [MallocngMultiPlacement] (γ : GhostName),
      mallocngMultiEntryOk mmpl msvc "malloc"
        (mallocngMallocTokSpec B msvc γ (mallocngAddrsOfPlacement mmpl)) := by
  intro _ γ
  refine ⟨by decide, 4, 0, rfl, ?_⟩
  rw [fnAddr_malloc mmpl]
  exact withCL_to_withCodeLoaded (mallocPlaced_withCL_tok_of_defaultMalloc hDef γ)

/-- `malloc` entry contract parameterized over block token `B` for any valid `mpl` and `svc`. -/
theorem mallocPlaced_entry_tok_ok {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    (hDef : DefaultMallocPlacedTokStmt B)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngMallocTokSpec B svc γ (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := ⟨mpl, svc, hPl, hSvc⟩
  exact mallocPlaced_entry_tok_mmpl_ok hDef γ

theorem mallocPlaced_entry_tight_mmpl_ok_of_impl (hImpl : LibcMallocImplPlacedTightStmt) :
    ∀ [MallocngMultiPlacement] (γ : GhostName),
      mallocngMultiEntryOk mmpl msvc "malloc"
        (mallocngMallocTightSpec mallocngIface msvc γ (mallocngAddrsOfPlacement mmpl)) :=
  mallocPlaced_entry_tok_mmpl_ok (DefaultMallocPlacedTightStmt.toTok (placed_defaultMalloc_tight_of_impl hImpl))

theorem mallocPlaced_entry_tight_ok_of_impl (hImpl : LibcMallocImplPlacedTightStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngMallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := ⟨mpl, svc, hPl, hSvc⟩
  exact mallocPlaced_entry_tight_mmpl_ok_of_impl hImpl γ

/-- Tight `malloc` entry contract (`mallocngMallocTightSpec`) for any valid `mpl` and `svc`. -/
theorem mallocPlaced_entry_tight_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngMallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  mallocPlaced_entry_tight_ok_of_impl (placed_libcMallocImpl_tight_uncond_ok hMeta hSlot)
    mpl svc hPl hSvc γ

/-- Public `malloc` entry contract (`mallocngMallocSpec`) for any valid `mpl` and `svc`. -/
theorem mallocPlaced_entry_uncond_ok
    (hMeta : AllocMetaPlacedFullStmt) (hSlot : AllocSlotPlacedFullStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngMallocSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ :=
    mallocPlaced_entry_tight_uncond_ok hMeta hSlot mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngMallocTightSpec, mallocngMallocSpec,
      ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, MallocngCallAccounting.tight_to_step hq.1.2⟩, hq.2⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngMallocTightSpec, mallocngMallocSpec,
      ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

end VerifiedLibraries.Mallocng.Proofs
