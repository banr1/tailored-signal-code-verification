/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFrom
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SignalMessage>::try_from` Prologue & Epilogue

Defines the `VmPreserved`-augmented epilogue state (`EpilogueStateBudgetPlaced`), top-level
allocator event envelope (`TryFromEnvGen`), and panic-free budget specification
(`tryFromPlacedSpecGen`), and proves the relocatable `[LibsignalPlacement]` prologue, `len = 9`
fast path, and shared epilogue (`+0x440`) lemmas on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSession (SignalProtocolError SignalMessage)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec
  (protoSignalCodec emptyProtoSignalMessage)
open CryptoVerification.LibsignalTripleRatchetRepr
  (signalMessageResultAt errTag speWord noneCap)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 blkPC_85 LibsignalCodeRoLoaded logOff smallRootStack TryFromGhost)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp VRegsAt tryFromPlacedImg tryFromPlacedProg tryFromSubStack LoopRegs
   EpilogueStatePlaced spAligned_sub448 calleeSavedAt memRegion96_cells
   stackAt_smallRoot_split stackAt_smallRoot_unsplit pure_true_emp
   cond_hi_len_of_lt9 tryFrom_eq_tooShort memRegion120_split24 spe_tooShort_intro
   cond_hi_len_of_ge9 cond_cs_ver_of_lt3 tryFrom_eq_legacyVer
   memRegion120_split17 spe_legacyVer_intro
   cond_cs_ver_of_ge3 cond_ls_ver_of_gt4 tryFrom_eq_unrecognizedVer
   spe_unrecognizedVer_intro cond_ls_ver_of_le4
   memRegion16_split8_8' memRegion112_emptyMsg_cells
   emptyMsg_cells_entails_wireSignalMessageOf cond_eq_len_of_gt9
   cond_eq_len9 cond_ne_noneCap_add2 cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3
   pointsTo64_pair_entails_memRegion16 memRegion120_split16'
   cells112_entails_memRegion112 spe_invalidProto_intro'
   wireSignalMessageOf_emptyMsg_cells tryFrom_eq_len9 entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   fitsEvents_append)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (TryFromLoopEnv noPanicQp sepWPp_frame_noPanic sepWPp_bind_frame_entails_noPanic
   sepWPp_end_noPanic_placed sepWP_seg_85 sepWP_done_sync_pool_85)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cond_eq_len_of_gt9 cond_eq_len9 cond_ne_noneCap_add2
  cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3
attribute [local simp, local wp_norm]
  cond_eq_len_of_gt9 cond_eq_len9 cond_ne_noneCap_add2
  cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3

/-! ## Epilogue VM state, top-level envelope, and budget spec -/

/-- Epilogue state invariant augmented with `VmPreserved s0 s` for framing `A.pool lim st` across
pure prologue segments. -/
def EpilogueStateBudgetPlaced [LibsignalPlacement] (s0 : State) (sp' : BitVec 64) (s : State) :
    Prop :=
  EpilogueStatePlaced s0 sp' s ∧ VmPreserved s0 s

theorem EpilogueStateBudgetPlaced.of_steps [LibsignalPlacement] {s0 s1 s2 : State} {sp' : BitVec 64}
    (hcl : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsp : s2.sp = sp') (hsp0 : s1.sp = sp') (hal : s1.spAligned = true)
    (htr : s2.trace = s0.trace) (hvm0 : VmPreserved s0 s1) (hvm12 : VmPreserved s1 s2) :
    EpilogueStateBudgetPlaced s0 sp' s2 :=
  ⟨EpilogueStatePlaced.of_steps hcl hsp hsp0 hal htr, hvm0.trans hvm12⟩

theorem sepWP_done_vm_85 [LibsignalPlacement] {H : LibsignalHooks}
    {target : BitVec 64} {s0 s sm' : State} {Pm : SepProp}
    {post : State → SepProp → Prop}
    [hv : VRegsAt s sm']
    (hpost : ∀ m_real : Memory,
      VmPreserved s0 (sm'.setMem m_real) →
      LibsignalCodeRoLoaded lsmpl (sm'.setMem m_real).mem →
      post (sm'.setMem m_real) Pm)
    (hpc : sm'.pc = target := by simp only [wp_norm, arm64_norm])
    (hrun : sm'.status = .Running := by simp only [wp_norm, arm64_norm]; assumption)
    (htp : sm'.tpidrEl0 = s0.tpidrEl0 := by simp only [wp_norm, arm64_norm]) :
    ProofLib.SepWP ((blkPC_85).rebase (blkPl_85).base (hooksException H)) target sm' Pm
      (fun sm'' Pm'' =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s0 (sm''.setMem m_real) →
          ProofLib.SepWP (tryFromPlacedProg H) target (sm''.setMem m_real) Pm''
            (fun sf Pf => VRegsAt s sf ∧ (LibsignalCodeRoLoaded lsmpl sf.mem → post sf Pf))) := by
  refine ProofLib.SepWP.done hpc hrun fun m_real hnsp => ?_
  have hvm := hnsp.toVmPreserved (by cases sm'; exact htp)
  have hv_real : VRegsAt s (sm'.setMem m_real) := ⟨by cases sm'; exact hv.eq⟩
  exact ProofLib.SepWP.done (by cases sm'; exact hpc) (by cases sm'; exact hrun)
    ⟨hv_real, hpost m_real hvm⟩

/-- Top-level allocator event envelope for `<SignalMessage as TryFrom<&[u8]>>::try_from`,
parameterized by the post-loop envelope `PostEnv`. -/
inductive TryFromEnvGen (PostEnv : TryFromGhost → List AllocEvent → Prop)
    (x : TryFromGhost) : List AllocEvent → Prop where
  | nil : TryFromEnvGen PostEnv x []
  | loopOnly {evs₁ : List AllocEvent} :
      TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length evs₁ →
      TryFromEnvGen PostEnv x evs₁
  | loopPost {evs₁ evs₂ : List AllocEvent} :
      TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length evs₁ →
      PostEnv x evs₂ →
      TryFromEnvGen PostEnv x (evs₁ ++ evs₂)

theorem fitsEnv_tryFrom_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PostEnv : TryFromGhost → List AllocEvent → Prop} {x : TryFromGhost}
    (hfit : FitsEnv M lim st (TryFromEnvGen PostEnv x)) :
    FitsEnv M lim st (TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length) :=
  fun evs₁ h1 => hfit evs₁ (.loopOnly h1)

theorem fitsEnv_tryFrom_post {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {PostEnv : TryFromGhost → List AllocEvent → Prop} {x : TryFromGhost}
    {evs₁ : List AllocEvent}
    (h1 : TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length evs₁)
    (hfit : FitsEnv M lim st (TryFromEnvGen PostEnv x)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (PostEnv x) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hfit (evs₁ ++ evs₂) (.loopPost h1 h2))).2

/-- Relocatable `[LibsignalPlacement]` panic-free budget specification of
`<SignalMessage as TryFrom<&[u8]>>::try_from` (Block `85`), parameterized by `PostEnv`. -/
def tryFromPlacedSpecGen [LibsignalPlacement] {M : AllocCostModel}
    (PostEnv : TryFromGhost → List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (TryFromGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st (TryFromEnvGen PostEnv x)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
      stackAt s.sp smallRootStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜TryFromEnvGen PostEnv x evs⌝ ∗
        signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim (M.stepEvents evs st) sf)

/-! ## Shared epilogue (`+0x440`) and pure prologue segments -/

theorem epilogue_440_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {PostEnv : TryFromGhost → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent}
    {H : LibsignalHooks} {x : TryFromGhost} {s0 s : State}
    (hevs : TryFromEnvGen PostEnv x evs)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x440#64)
    (hrun : s.status = .Running) :
    SepWPp (tryFromPlacedProg H)
      (s0.readReg64 .x30) s
      (stackAt (s0.sp - 448#64) tryFromSubStack ∗
        memRegion (s0.sp - 448#64) 352 ∗
        calleeSavedAt (s0.sp - 448#64) s0 ∗
        signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool lim (M.stepEvents evs st) s)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (tryFromPlacedSpecGen PostEnv A lim).post (x, st) s0 sf))
      (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  unfold calleeSavedAt
  simp only [sepConj_assoc]
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl1 => ?_
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], hv⟩
  · dsimp only [tryFromPlacedSpecGen]
    rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    refine Entails.trans ?_ (Entails.sepExists_intro evs)
    rw [pure_true_emp hevs, emp_sepConj]
    have hstk := stackAt_smallRoot_unsplit s0.sp s0
    unfold calleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq
    sep_ac_rfl

theorem prologue_tooShort_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 : State}
    (hlt9 : x.bytes.length < 9)
    (hpc : s0.pc = (blkPl_85).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (_hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sf Pf => EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A.repAlloc [] x.ret
            (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool lim st sf))
      (noPanicQp s0) := by
  have hcond := cond_hi_len_of_lt9 hlt9
  have hout := tryFrom_eq_tooShort hlt9
  rw [stackAt_smallRoot_split s0.sp]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion120_split24 x.ret)
      (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (memRegion96_cells (s0.sp - 448#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun r2 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun m_real hcl1 => ?_
  refine ⟨⟨by simp [arm64_norm], ?_, hcl1, by simp [arm64_norm]⟩, ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using spAligned_sub448 hsp
  · have hmsg := spe_tooShort_intro A.repAlloc x.ret x.bytes.length hout
    simp only [errTag, speWord] at hmsg
    have hcs :
        ((s0.sp - 448#64 + 352#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 448#64 + 360#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 448#64 + 368#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 448#64 + 376#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 448#64 + 384#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 448#64 + 392#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 448#64 + 400#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 448#64 + 408#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 448#64 + 416#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 448#64 + 424#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 448#64 + 432#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 448#64 + 440#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
        calleeSavedAt (s0.sp - 448#64) s0 := Entails.refl _
    refine Entails.trans (Q := stackAt (s0.sp - 448#64) tryFromSubStack ∗
        memRegion (s0.sp - 448#64) 352 ∗
        (((s0.sp - 448#64 + 352#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 448#64 + 360#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 448#64 + 368#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 448#64 + 376#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 448#64 + 384#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 448#64 + 392#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 448#64 + 400#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 448#64 + 408#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 448#64 + 416#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 448#64 + 424#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 448#64 + 432#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 448#64 + 440#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ∗
        ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
          ((x.ret + 8#64) ↦₆₄ 9223372036854775811#64) ∗
          ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          memRegion (x.ret + 24#64) 96) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool lim st _)
      (by apply entails_of_eq; sep_ac_rfl) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hcs (sepConj_mono_left hmsg)))

theorem prologue_entry_ge9_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 : State}
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hpc : s0.pc = (blkPl_85).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x044#64) s0
      (memRegion (s0.sp - 448#64 + 352#64) 96)
      (fun s1 P1 =>
        (EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s1 ∧
        s1.readReg64 .x0 = x.bytesA ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x29 = s0.sp - 448#64 + 352#64) ∧
        (P1 ⊢ calleeSavedAt (s0.sp - 448#64) s0))
      (noPanicQp s0) := by
  have hcond := cond_hi_len_of_ge9 hge9 hlt
  refine SepWPp.mono_pre (memRegion96_cells (s0.sp - 448#64)) ?_
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 => ?_
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨⟨⟨⟨by simp [arm64_norm], ?_, hcl1, by simp [arm64_norm]⟩, hvm⟩,
    by simp [hx0, arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm]⟩, Entails.refl _⟩
  rw [State.spAligned]
  simpa [arm64_norm] using spAligned_sub448 hsp

theorem prologue_44_legacyVer_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length)
    (hlt3 : (b0 >>> 4) < 3#8)
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120)
      (fun sf Pf => EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes)))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  have hcond := cond_cs_ver_of_lt3 hlt3
  have hout : SignalMessage.tryFrom protoSignalCodec x.bytes =
      .error (.legacyCiphertextVersion (b0 >>> 4)) := by
    rw [hbs]
    exact tryFrom_eq_legacyVer (hbs ▸ hge9) hlt3
  have hbytes : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
    rw [hbs, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion120_split17 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b16 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]) hvm0 hvm, ?_⟩
  have hmsg := spe_legacyVer_intro A x.ret (b0 >>> 4) hout
  simp only [errTag, speWord, BitVec.reduceAdd] at hmsg
  refine Entails.trans (Q := ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
      ((x.ret + 16#64) ↦₈ (b0 >>> 4)) ∗
      memRegion (x.ret + 17#64) 103) ∗
      ((x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left hmsg

theorem prologue_44_unrecognizedVer_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hgt4 : 4#8 < (b0 >>> 4))
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120)
      (fun sf Pf => EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes)))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_gt4 hgt4
  have hout : SignalMessage.tryFrom protoSignalCodec x.bytes =
      .error (.unrecognizedCiphertextVersion (b0 >>> 4)) := by
    rw [hbs]
    exact tryFrom_eq_unrecognizedVer (hbs ▸ hge9) hge3 hgt4
  have hbytes : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
    rw [hbs, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion120_split17 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b16 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]) hvm0 hvm, ?_⟩
  have hmsg := spe_unrecognizedVer_intro A x.ret (b0 >>> 4) hout
  simp only [errTag, speWord, BitVec.reduceAdd] at hmsg
  refine Entails.trans (Q := ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
      ((x.ret + 16#64) ↦₈ (b0 >>> 4)) ∗
      memRegion (x.ret + 17#64) 103) ∗
      ((x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left hmsg

theorem prologue_44_validVer_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x088#64) s
      (x.bytesA ↦₈ b0)
      (fun s2 P2 =>
        (EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s2 ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s2.readReg64 .x21 = x.bytesA ∧
        s2.readReg64 .x23 = b0.zeroExtend 64 ∧
        s2.readReg64 .x26 = 0x8000000000000002#64 ∧
        s2.readReg64 .x29 = s0.sp - 448#64 + 352#64) ∧
        (P2 ⊢ (x.bytesA ↦₈ b0)))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_le4 hle4
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨⟨EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]) hvm0 hvm,
    by simp [hx19, arm64_norm], by simp [hx20, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx29, arm64_norm]⟩, Entails.refl _⟩

theorem prologue_88_init_wp'_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x0b8#64) s
      (memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8)
      (fun s3 P3 =>
        (EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s3 ∧
        s3.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64 ∧
        s3.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64 ∧
        s3.readReg64 .x8 = s0.sp - 448#64 + 160#64 ∧
        s3.readReg64 .x19 = x.ret ∧
        s3.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s3.readReg64 .x21 = x.bytesA ∧
        s3.readReg64 .x23 = b0.zeroExtend 64 ∧
        s3.readReg64 .x26 = 0x8000000000000002#64 ∧
        s3.readReg64 .x29 = s0.sp - 448#64 + 352#64) ∧
        (P3 ⊢ ((s0.sp - 448#64 + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
          ((s0.sp - 448#64 + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
          wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
          ((s0.sp - 448#64 + 288#64) ↦₆₄ (s0.sp - 448#64 + 160#64))))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  set sp' := s0.sp - 448#64
  rw [memRegion_eight (sp' + 288#64)]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion16_split8_8' (sp' + 160#64))
      (sepConj_mono_left (memRegion112_emptyMsg_cells sp'))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w288 =>
    SepWPp.exists_pre fun w280 => SepWPp.exists_pre fun w272 =>
    SepWPp.exists_pre fun w248 => SepWPp.exists_pre fun w224 =>
    SepWPp.exists_pre fun w200 => SepWPp.exists_pre fun w176 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨⟨EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]) hvm0 hvm,
    by simp [arm64_norm],
    by simp [BitVec.sub_eq_add_neg, arm64_norm],
    by simp [arm64_norm],
    by simp [hx19, arm64_norm],
    by simp [hx20, arm64_norm],
    by simp [hx21, arm64_norm],
    by simp [hx23, arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [hx29, arm64_norm]⟩, ?_⟩
  have hempty := emptyMsg_cells_entails_wireSignalMessageOf A sp'
  simp only [noneCap] at hempty
  refine Entails.trans (Q := ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
      ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
      (((sp' + 176#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 184#64) 16 ∗
        ((sp' + 200#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 208#64) 16 ∗
        ((sp' + 224#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 232#64) 16 ∗
        ((sp' + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 256#64) 16 ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 276#64) 4 ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 284#64) 4) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hempty))

theorem prologue_b8_gt9_to_f0_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hgt9 : 9 < x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64)
    (hx8 : s.readReg64 .x8 = s0.sp - 448#64 + 160#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x0f0#64) s
      emp
      (fun s4 P4 =>
        (LoopRegs (s0.sp - 448#64) x.ret (BitVec.ofNat 64 x.bytes.length)
          x.bytesA (b0.zeroExtend 64) s4 ∧
        EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s4 ∧
        s4.readReg64 .x28 = s0.sp - 448#64 + 160#64 ∧
        s4.readReg64 .x27 = s0.sp - 448#64 + 168#64 ∧
        s4.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64) ∧
        (P4 ⊢ emp))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  have hcond := cond_eq_len_of_gt9 hgt9 hlt
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simp [hx29, arm64_norm],
      by simp [hx26, arm64_norm], by simp [arm64_norm],
      by simp [hx23, arm64_norm], by simp [arm64_norm],
      by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
      by simp [hx19, arm64_norm]⟩,
    EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr, arm64_norm]) hvm0 hvm,
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx2, arm64_norm]⟩,
    Entails.refl _⟩

theorem prologue_b8_len9_to_460_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    {s88 s96 rkPtr ctPtr pqPtr adPtr : BitVec 64}
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 9#64 9#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x460#64) s
      (((s0.sp - 448#64 + 88#64) ↦₆₄ s88) ∗ ((s0.sp - 448#64 + 96#64) ↦₆₄ s96) ∗
        ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
        ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
        ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
        ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr))
      (fun s4 P4 =>
        (EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s4 ∧
        s4.readReg64 .x1 = noneCap ∧
        s4.readReg64 .x19 = x.ret ∧
        s4.readReg64 .x22 = noneCap ∧
        s4.readReg64 .x25 = noneCap ∧
        s4.readReg64 .x26 = 0x8000000000000002#64 ∧
        s4.readReg64 .x27 = noneCap) ∧
        (P4 ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
          ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
          ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
          ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr)))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  set sp' := s0.sp - 448#64
  dsimp only [noneCap]
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨⟨EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]) hvm0 hvm,
    by simp [arm64_norm],
    by simp [hx19, arm64_norm],
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [arm64_norm]⟩, ?_⟩
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 88#64) adPtr pqPtr
  have ha96 : sp' + 88#64 + 8#64 = sp' + 96#64 := by bv_omega
  rw [ha96] at h16
  rw [← sepConj_assoc ((sp' + 88#64) ↦₆₄ adPtr)]
  exact sepConj_mono_left h16

theorem prologue_460_len9_to_440_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    {rkPtr rkLen ctPtr ctLen pqPtr pqLen adPtr adLen : BitVec 64}
    {cVal pcVal : BitVec 32}
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x460#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = noneCap)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx25 : s.readReg64 .x25 = noneCap)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx27 : s.readReg64 .x27 = noneCap) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion x.ret 120 ∗
        ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
        ((s0.sp - 448#64 + 192#64) ↦₆₄ rkLen) ∗
        ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
        ((s0.sp - 448#64 + 216#64) ↦₆₄ ctLen) ∗
        ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
        ((s0.sp - 448#64 + 240#64) ↦₆₄ pqLen) ∗
        ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr) ∗
        ((s0.sp - 448#64 + 264#64) ↦₆₄ adLen) ∗
        ((s0.sp - 448#64 + 272#64) ↦₃₂ 0#32) ∗ ((s0.sp - 448#64 + 276#64) ↦₃₂ cVal) ∗
        ((s0.sp - 448#64 + 280#64) ↦₃₂ 0#32) ∗ ((s0.sp - 448#64 + 284#64) ↦₃₂ pcVal))
      (fun sf Pf =>
        EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          signalMessageResultAt A [] x.ret out))
      (noPanicQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hvm0⟩
  set sp' := s0.sp - 448#64
  dsimp only [noneCap] at hx1 hx22 hx25 hx27 ⊢
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion120_split16' x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun r1 => SepWPp.exists_pre fun r0 => ?_
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_vm_85 fun _ hvm hcl1 => ?_
  refine ⟨EpilogueStateBudgetPlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]) hvm0 hvm, ?_⟩
  have h112 := cells112_entails_memRegion112 sp'
    9223372036854775810#64 rkPtr rkLen
    (bv% (2 ^ 64 - 1)) ctPtr ctLen
    (bv% (2 ^ 64 - 1)) pqPtr pqLen
    (bv% (2 ^ 64 - 1)) adPtr adLen
    0#32 cVal 0#32 pcVal
  have hmsg := spe_invalidProto_intro' A x.ret hout
  simp only [errTag, speWord] at hmsg
  refine Entails.trans (Q :=
      (((sp' + 176#64) ↦₆₄ 9223372036854775810#64) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗
      ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((x.ret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
        memRegion (x.ret + 16#64) 104))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepConj_mono h112 hmsg

theorem prologue_b8_len9_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 9#64 9#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64 + 88#64) 16 ∗
        wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
        memRegion x.ret 120)
      (fun sf Pf =>
        EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          signalMessageResultAt A [] x.ret out))
      (noPanicQp s0) := by
  set sp' := s0.sp - 448#64
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion16_split8_8' (sp' + 88#64))
      (sepConj_mono_left (wireSignalMessageOf_emptyMsg_cells A sp'))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun pcVal => SepWPp.exists_pre fun cVal =>
    SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun adPtr =>
    SepWPp.exists_pre fun pqLen => SepWPp.exists_pre fun pqPtr =>
    SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun ctPtr =>
    SepWPp.exists_pre fun rkLen => SepWPp.exists_pre fun rkPtr =>
    SepWPp.exists_pre fun s96 => SepWPp.exists_pre fun s88 => ?_
  set F1 := ((sp' + 192#64) ↦₆₄ rkLen) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
    ((sp' + 240#64) ↦₆₄ pqLen) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
    ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
    ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
    memRegion x.ret 120
  refine SepWPp.mono_pre (P' :=
      (((sp' + 88#64) ↦₆₄ s88) ∗ ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr)) ∗ F1)
    (by dsimp only [F1]; apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_entails_noPanic
    (prologue_b8_len9_to_460_wp_placed hst hpc hrun hpstate hx19 hx26) ?_
  intro s4 hpc4 hrun4 ⟨hst4, hx1_4, hx19_4, hx22_4, hx25_4, hx26_4, hx27_4⟩
  dsimp only [F1]
  refine SepWPp.mono_pre (P' :=
      (memRegion x.ret 120 ∗
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
        ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗
        ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗
        ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗
        ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗ memRegion (sp' + 88#64) 16)
    (by dsimp only [sp']; apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_frame_noPanic
    (prologue_460_len9_to_440_wp_placed (A := A) hout hst4 hpc4 hrun4
      hx1_4 hx19_4 hx22_4 hx25_4 hx26_4 hx27_4)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  dsimp only [sp']
  apply entails_of_eq; sep_ac_rfl

theorem prologue_88_len9_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hlen9 : x.bytes.length = 9)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64 + 88#64) 16 ∗
        memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8 ∗
        memRegion x.ret 120)
      (fun sf Pf =>
        EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          memRegion (s0.sp - 448#64 + 160#64) 16 ∗
          memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          memRegion (s0.sp - 448#64 + 288#64) 8 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes)))
      (noPanicQp s0) := by
  set sp' := s0.sp - 448#64
  have hhead : x.bytes.headD 0#8 = b0 := by simp [hbs]
  have hout := tryFrom_eq_len9 hlen9 (hhead ▸ hge3) (hhead ▸ hle4)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8) ∗
      (memRegion (sp' + 88#64) 16 ∗ memRegion x.ret 120))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_entails_noPanic
    (prologue_88_init_wp'_placed (A := A) hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
  intro s3 hpc3 hrun3 ⟨hst3, hpstate3, _, _, hx19_3, _, _, _, hx26_3, _⟩
  have hpstate9 : s3.pstate = subsPState64 9#64 9#64 := by
    rw [hpstate3, hlen9]
  have h160 : ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
      ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ⊢
      memRegion (sp' + 160#64) 16 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo64_pair_entails_memRegion16 (sp' + 160#64)
        (x.bytesA + 1#64) (BitVec.ofNat 64 x.bytes.length - 9#64)
  have h288 := pointsTo64_entails_memRegion (sp' + 288#64) (sp' + 160#64)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 88#64) 16 ∗ wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
        memRegion x.ret 120) ∗
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 288#64) 8))
    (by
      refine Entails.trans (Q :=
          (memRegion (sp' + 88#64) 16 ∗ wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
            memRegion x.ret 120) ∗
          ((((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
            ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64))) ∗
            ((sp' + 288#64) ↦₆₄ (sp' + 160#64))))
        (by dsimp only [sp']; apply entails_of_eq; sep_ac_rfl) ?_
      exact sepConj_mono_right (sepConj_mono h160 h288)) ?_
  refine sepWPp_frame_noPanic
    (prologue_b8_len9_wp_placed hout hst3 hpc3 hrun3 hpstate9 hx19_3 hx26_3)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  dsimp only [sp']
  apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
