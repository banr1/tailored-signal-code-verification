/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Prologue, Dispatch, and Epilogues under `AllocContractsX`

Lifts the prologue, jump-table dispatch, tail-call dealloc/drop epilogues, and shared `Ok(V1Recv)`
store epilogue of `<States>::recv` to `AllocContractsX` / `DeallocOkExt` (`40,176`-byte stack budget).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local wp_norm] private theorem frozenLoaded_writeReg64_ax
    (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg64 r v) ↔ img.FrozenLoaded s := by
  have hmem : (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem frozenLoaded_setPC_ax
    (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.FrozenLoaded (s.setPC pc) ↔ img.FrozenLoaded s := by
  have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem frozenLoaded_setPState_ax
    (img : Obj.Image) (s : State) (ps : PState) :
    img.FrozenLoaded (s.setPState ps) ↔ img.FrozenLoaded s := by
  have hmem : (s.setPState ps).mem = s.mem := by cases s; rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem symtab_writeReg64_ax
    (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[local wp_norm] private theorem symtab_setPC_ax
    (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

@[local wp_norm] private theorem symtab_setPState_ax
    (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl

@[local wp_norm] private theorem exists_two_pow_zero_ax : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] private theorem exists_two_pow_one_ax : (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")

/-! ## Stack Splits & `ImgCallInv` Sequencing Combinators -/

theorem stackAt_split_callee_ax (sp : BitVec 64) (nSmall nBig : Nat)
    (hle : nSmall ≤ nBig := by decide) (hbd : nBig ≤ 131072 := by decide) :
    stackAt sp nBig =
      memRegion (sp - BitVec.ofNat 64 nBig) (nBig - nSmall) ∗ stackAt sp nSmall := by
  have hbd' : nSmall + (nBig - nSmall) ≤ 2 ^ 64 := by omega
  have h := ProofLib.stackAt_split_bottom sp nSmall (nBig - nSmall) hbd'
  rwa [Nat.add_sub_of_le hle] at h

theorem stackAt_statesRecvCalleeExt_eq_extHook_ax (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackXExt =
      memRegion (fsp - 35936#64) 19552 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 19552 (by decide)

theorem stackAt_statesRecvStackXExt_eq_extHook_ax (sp : BitVec 64) :
    stackAt sp statesRecvStackXExt =
      memRegion (sp - 40176#64) 23792 ∗ stackAt sp extHookStack :=
  ProofLib.stackAt_split_bottom sp extHookStack 23792 (by decide)

theorem seq_clean_inImage_ax {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s : State} {P P' : SepProp} {φ : State → Prop} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P') ∧ φ sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → φ sm →
      SepWP prog target sm P' post) :
    SepWP prog target s P post := by
  refine SepWP.seq_inImage (mid := mid) hinv ?_
  refine SepWP.mono h1 ?_
  intro sm Pm hpc hrun ⟨hPm, hφ⟩ hinv_m
  exact SepWP.weaken_pre hPm (h2 sm hpc hrun hinv_m hφ)

theorem sepWPp_seq_clean_inImage_ax {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P' : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P') ∧ φ sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → φ sm →
      SepWPp prog ret sm P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.of_sepWP_frozen hinv.1 hinv.2 (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hPm, hφ⟩ hF hsym
  exact SepWPp.weaken_pre hPm (h2 sm hpc hrun ⟨hF, hsym⟩ hφ)

/-! ## `AllocContractsX` `memcpy` & Shared Store/Return Epilogues -/

abbrev sessionMemcpyRegionSpecAx : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  session2MemcpySpecX

theorem session_memcpy_region_ok_at_ax {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName :=
      by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyRegionSpecAx.inImage img) :=
  memcpy_ok_at2_ext_x hAx (name := name) (k := k) hk

theorem states_recv_epilogue_19324_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hbase := @states_recv_epilogue_19324 b ext s0 s1
    (memRegion (s0.sp - 40176#64) 16384 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 htr1
  refine SepWP.weaken_pre ?_ (SepWP.mono hbase ?_)
  · rw [stackAt_statesRecvCalleeExt_eq_X]; exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp, hcs, htr⟩
    refine ⟨?_, hsp, hcs, htr⟩
    refine Entails.trans hPf ?_
    rw [stackAt_statesRecvStackXExt_eq_X]; exact Entails.of_eq (by ac_rfl)

theorem epilogue_step_19280_19324_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s : State) (fsp out : BitVec 64)
    (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376)
    (uq888 uq904 uq944 q512 q528 q544 : BitVec 128)
    (u920 u928 u936 w232 w560 : BitVec 64)
    (Frame : SepProp)
    (hin : ImgCallInv img s)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19280#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx2 : s.readReg64 .x2 = 376#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19324#64)
      s
      (stackAt fsp extHookStack ∗
       memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
       ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       ((fsp + 576#64) ↦ₛ bs576) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp extHookStack ∗
          ((out + 512#64) ↦ₛ bs576) ∗
          ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗
          ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ w232) ∗
          ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
          ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
          ((fsp + 576#64) ↦ₛ bs576) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  rcases hin with ⟨hfrozen, hsym⟩
  subst hsp hx19
  have hmemcpy := hAx.session_memcpy_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  simp only [Spec.inImage, ImgCallInv, sessionMemcpySpec] at hmemcpy ⊢
  rw [← hbs576]
  states_recv_fetches_range img.base (Rust.withPanics ext) 19280 44
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps
  wp_call hmemcpy (s.readReg64 .x19 + 512#64, s.sp + 576#64, bs576)
  wp_steps
  simp only [pointsTo128, sepConj_assoc]
  wp_done

/-! ## Tail-Call Dealloc & Drop Epilogues (`AllocContractsX` and `DeallocOkExt`) -/

private theorem fnAddr_statesRecv_rel_ax {b : BitVec 64} {ext : String → Option (State → State)}
    (targetName : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff targetName + k =
      libsignalSessionCode.fnOff statesRecvName := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).fnAddr statesRecvName - BitVec.ofNat 64 k =
      (tripleRatchetProgAtExt b ext).fnAddr targetName := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, ← hk]
  bv_omega

/-- Tail-call epilogue at `+192` (`-> b __rust_dealloc`) under `AllocContractsX img A ext`. -/
theorem states_recv_tail_dealloc_192_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hin1 : ImgCallInv img s1)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hcap : cap.toNat ≠ 0)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases hin1 with ⟨hfrozen1, hsym1⟩
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hlayout : LayoutOk cap.toNat 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
  have hstk_x : stackAt s0.sp statesRecvStackX =
      memRegion (s0.sp - 23792#64) 7408 ∗ stackAt s0.sp extHookStack :=
    ProofLib.stackAt_split_bottom s0.sp extHookStack 7408 (by decide)
  have hdealloc := hAx.dealloc_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
  simp only [Spec.inImage, ImgCallInv, rustDeallocExternSpecWithStack] at hdealloc
  states_recv_fetches_range img.base (Rust.withPanics ext) 192 36
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc1 hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hstk_x) (by sep_focus) ?_
  wp_call hdealloc (ptr, cap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq hstk_x.symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+192` (`-> b __rust_dealloc`) under `DeallocOkExt b A ext`
    (satisfied directly by `CliExternsOk.alloc` / `SpqrRecvContractsExt.hdealloc`). -/
theorem states_recv_tail_dealloc_192_dealloc
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc0 : DeallocOkExt b A ext)
    (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hcap : cap.toNat ≠ 0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := by
    refine sub_ok_of_addr_eq ?_ hdealloc0
    dsimp only [dropProgAtExt, tripleRatchetProgAtExt, statesRecvName,
      LibsignalTripleRatchet.deallocName]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
        ls_stub% "__rustc::__rust_dealloc"]
    bv_omega
  simp only [rustDeallocSpec, allocHookStack] at hdealloc
  states_recv_fetches_range b (Rust.withPanics ext) 192 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_allocHook s0.sp)) (by sep_focus) ?_
  wp_call hdealloc (ptr, cap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_allocHook s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+552` (`-> b drop_glue::<EkSentCt1Received>`) under `DeallocOkExt`. -/
theorem states_recv_tail_drop_ekSentCt1Received_552_dealloc
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedEkSentCt1ReceivedAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedEkSentCt1ReceivedSize ∗ A.pool ∗ Rest ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + (0#64 - 35624#64))
      (dropChunkedEkSentCt1ReceivedSpec A F) := by
    have hrel := fnAddr_statesRecv_rel_ax (b := b) (ext := ext) dropChunkedEkSentCt1ReceivedName 35624
    refine sub_ok_of_addr_eq ?_ (drop_chunked_ek_sent_ct1_received_ok_ext hdealloc)
    dsimp only [dropProgAtExt] at *
    rw [← hrel]; bv_omega
  simp only [dropChunkedEkSentCt1ReceivedSpec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 552 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+1168` (`-> b drop_glue::<HeaderSent>`) under `DeallocOkExt`. -/
theorem states_recv_tail_drop_headerSent_1168_dealloc
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1168#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedHeaderSentAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedHeaderSentSize ∗ A.pool ∗ Rest ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + (0#64 - 35836#64))
      (dropChunkedHeaderSentSpec A F) := by
    have hrel := fnAddr_statesRecv_rel_ax (b := b) (ext := ext) dropChunkedHeaderSentName 35836
    refine sub_ok_of_addr_eq ?_ (drop_chunked_header_sent_ok_ext hdealloc)
    dsimp only [dropProgAtExt] at *
    rw [← hrel]; bv_omega
  simp only [dropChunkedHeaderSentSpec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 1168 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+1760` (`-> b drop_glue::<[SortedSet<Pt>; 16]>`) under `DeallocOkExt`. -/
theorem states_recv_tail_drop_sortedSetPt16_1760_dealloc
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s1 : State) (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs : vecs.length = NUM_POLYS)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = arrA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A arrA vecs ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion arrA polyArrayBytes ∗ A.pool ∗ Rest ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + (0#64 - 38716#64))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel := fnAddr_statesRecv_rel_ax (b := b) (ext := ext) dropSortedSetPt16Name 38716
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    dsimp only [dropProgAtExt] at *
    rw [← hrel]; bv_omega
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 1760 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨arrA, vecs⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+10952` (`-> b drop_glue::<Ct2Sampled>`) under `DeallocOkExt`. -/
theorem states_recv_tail_drop_ct2Sampled_10952_dealloc
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10952#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedCt2SampledAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedCt2SampledSize ∗ A.pool ∗ Rest ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + (0#64 - 36040#64))
      (dropChunkedCt2SampledSpec A F) := by
    have hrel := fnAddr_statesRecv_rel_ax (b := b) (ext := ext) dropChunkedCt2SampledName 36040
    refine sub_ok_of_addr_eq ?_ (drop_chunked_ct2_sampled_ok_ext hdealloc)
    dsimp only [dropProgAtExt] at *
    rw [← hrel]; bv_omega
  simp only [dropChunkedCt2SampledSpec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 10952 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-! ## `.inImage img` & Callee Stack-Growth Contract Bundle (`StatesRecvContractsAx`) -/

theorem sub_ok_inImage_of_sub_ok_ax {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image)
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ spec.pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

/-- Grow any callee `Spec α` whose internal `stackAt` budget is `oldStack ≤ statesRecvCalleeStackXExt`
    up to the full `statesRecvCalleeStackXExt` (`35936` B) callee stack budget of `States::recv`. -/
def growToCalleeExt {α : Type} (oldStack : Nat) (spec : Spec α) : Spec α where
  pre := fun x s =>
    spec.pre x s ∗
      memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  post := fun x s0 sf =>
    spec.post x s0 sf ∗
      memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  onPanic := spec.onPanic

/-- Frame any `.inImage img` callee contract at stack `oldStack` up to `growToCalleeExt`,
    supporting both `onPanic = ⌜False⌝` and `onPanic = ⌜φ⌝ ∗ anyHeap`. -/
theorem sub_ok_inImage_growToCalleeExt_ax {α : Type} {prog : Program} {img : Obj.Image}
    {entry : BitVec 64} {spec : Spec α} (oldStack : Nat)
    (hpan : ∀ x s sf,
      spec.onPanic x s sf = ⌜False⌝ ∨ ∃ φ : Prop, spec.onPanic x s sf = (⌜φ⌝ ∗ anyHeap))
    (hexit : ∀ x code s sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ x s sf, spec.onOom x s sf = ⌜False⌝)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry ((growToCalleeExt oldStack spec).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Fr := memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
    (statesRecvCalleeStackXExt - oldStack)
  have hpre' : s0.mem ⊨ (spec.inImage img).pre x s0 ∗ (Fr ∗ R) := by
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (spec.pre x s0 ∗ Fr)) ∗ R at hpre
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ spec.pre x s0) ∗ (Fr ∗ R)
    exact Satisfies.mono (Entails.of_eq (by dsimp only [Fr]; ac_rfl)) hpre
  refine h.mono_outcome x (Fr ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    change sf.mem ⊨ spec.post x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ Fr) ∗ R
    exact Satisfies.mono (Entails.of_eq (by dsimp only [Fr]; ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    change sf.mem ⊨ spec.onPanic x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ spec.onPanic x s0 sf ∗ R
    rcases hpan x s0 sf with hpF | ⟨φ, hpA⟩
    · rw [hpF] at hpost; exact (not_satisfies_false_sepConj hpost).elim
    · rw [hpA] at hpost ⊢
      refine Satisfies.mono ?_ hpost
      exact Entails.trans
        (Entails.of_eq (show (⌜φ⌝ ∗ anyHeap) ∗ (Fr ∗ R) = (⌜φ⌝ ∗ (anyHeap ∗ Fr)) ∗ R by ac_rfl))
        (sepConj_mono_left (sepConj_mono_right (entails_anyHeap (anyHeap ∗ Fr))))
  · change sf.mem ⊨ spec.onExit x code s0 sf ∗ (Fr ∗ R) at hpost
    rw [hexit] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · change sf.mem ⊨ spec.onOom x s0 sf ∗ (Fr ∗ R) at hpost
    rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim

theorem sub_ok_growToCalleeExt_of_stack_ax {α : Type} {prog : Program} {img : Obj.Image}
    {entry : BitVec 64} {specExt spec : Spec α} (nExt oldStack : Nat)
    (hpre_imp : ∀ x s,
      (growToCalleeExt oldStack spec).pre x s ⊢
        specExt.pre x s ∗
          memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
            (statesRecvCalleeStackXExt - nExt))
    (hpost_imp : ∀ x s sf,
      specExt.post x s sf ∗
        memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - nExt) ⊢
        (growToCalleeExt oldStack spec).post x s sf)
    (hpan : ∀ x s sf,
      (specExt.onPanic x s sf = ⌜False⌝ ∧ spec.onPanic x s sf = ⌜False⌝) ∨
        ∃ φ : Prop, specExt.onPanic x s sf = (⌜φ⌝ ∗ anyHeap) ∧
          spec.onPanic x s sf = (⌜φ⌝ ∗ anyHeap))
    (hexit : ∀ x code s sf, specExt.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ x s sf, specExt.onOom x s sf = ⌜False⌝)
    (h : subroutine_ok prog entry (specExt.inImage img)) :
    subroutine_ok prog entry ((growToCalleeExt oldStack spec).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Fr := memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
    (statesRecvCalleeStackXExt - nExt)
  have hpre' : s0.mem ⊨ (specExt.inImage img).pre x s0 ∗ (Fr ∗ R) := by
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (growToCalleeExt oldStack spec).pre x s0) ∗ R at hpre
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specExt.pre x s0) ∗ (Fr ∗ R)
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (hpre_imp x s0))) ?_
    exact Entails.of_eq (by dsimp only [Fr]; ac_rfl)
  refine h.mono_outcome x (Fr ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    change sf.mem ⊨ specExt.post x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ (growToCalleeExt oldStack spec).post x s0 sf ∗ R
    refine Satisfies.mono ?_ hpost
    exact Entails.trans (Entails.of_eq (by dsimp only [Fr]; ac_rfl))
      (sepConj_mono_left (hpost_imp x s0 sf))
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    change sf.mem ⊨ specExt.onPanic x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ spec.onPanic x s0 sf ∗ R
    rcases hpan x s0 sf with ⟨hpF, _⟩ | ⟨φ, hpE, hpS⟩
    · rw [hpF] at hpost; exact (not_satisfies_false_sepConj hpost).elim
    · rw [hpE] at hpost; rw [hpS]
      refine Satisfies.mono ?_ hpost
      exact Entails.trans
        (Entails.of_eq (show (⌜φ⌝ ∗ anyHeap) ∗ (Fr ∗ R) = (⌜φ⌝ ∗ (anyHeap ∗ Fr)) ∗ R by ac_rfl))
        (sepConj_mono_left (sepConj_mono_right (entails_anyHeap (anyHeap ∗ Fr))))
  · change sf.mem ⊨ specExt.onExit x code s0 sf ∗ (Fr ∗ R) at hpost
    rw [hexit] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · change sf.mem ⊨ specExt.onOom x s0 sf ∗ (Fr ∗ R) at hpost
    rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim

/-- `.inImage img` + `statesRecvCalleeStackXExt` (`35936` B) callee `subroutine_ok` bundle
    for `<States>::recv`, uniformly accommodating both existing `StatesRecvContractsExt`
    contracts and `.inImage img` `extHookStack`-grown leaf contracts (`≤ 35936` B). -/
structure StatesRecvContractsAx (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  keysSampledRecvCt1Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      ((growToCalleeExt keysSampledRecvCt1ChunkStack
        (keysSampledRecvCt1ChunkSpec A F)).inImage img)
  headerSentRecvCt1Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      ((growToCalleeExt headerSentRecvCt1ChunkStack
        (headerSentRecvCt1ChunkSpec A F img.base)).inImage img)
  ct1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img)
  ekSentCt1ReceivedRecvCt2Chunk_ok :
    RecvCt2ChunkOkExt img K F A ext
  noHeaderReceivedRecvHdrChunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
      ((growToCalleeExt noHeaderReceivedRecvHdrChunkStackX
        (noHeaderReceivedRecvHdrChunkSpec F A img.base)).inImage img)
  polyAddChunk_ok :
    AddChunkOkX img A ext
  polyDecodedMessage_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((growToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img)
  unchunkedCt1SentRecvEk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img)
  unchunkedCt1SentEkReceivedSendCt2_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img)
  sendCt2Encoder_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack
        (sendCt2EncoderSpec A)).inImage img)
  ekReceivedCt1SampledRecvCt1Ack_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((growToCalleeExt ekReceivedCt1SampledRecvCt1AckStack
        (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)).inImage img)
  ct1AcknowledgedRecvEkChunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      ((growToCalleeExt ct1AcknowledgedRecvEkChunkStack
        (ct1AcknowledgedRecvEkChunkSpec A F K img.base)).inImage img)
  ct2SampledRecvNextEpoch_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      ((growToCalleeExt dropGluePoly16Stack
        (ct2SampledRecvNextEpochSpec A F)).inImage img)

/-- Every `StatesRecvContractsExt` bundle lifts canonically to `StatesRecvContractsAx`. -/
theorem StatesRecvContractsExt.toAx {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : StatesRecvContractsExt img A F K ext) :
    StatesRecvContractsAx img A F K ext where
  keysSampledRecvCt1Chunk_ok :=
    sub_ok_inImage_growToCalleeExt_ax keysSampledRecvCt1ChunkStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.keysSampledRecvCt1Chunk_ok)
  headerSentRecvCt1Chunk_ok :=
    sub_ok_inImage_growToCalleeExt_ax headerSentRecvCt1ChunkStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.headerSentRecvCt1Chunk_ok)
  ct1ReceivedRecvCt2Chunk_ok :=
    sub_ok_inImage_growToCalleeExt_ax ct1ReceivedRecvCt2ChunkStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.ct1ReceivedRecvCt2Chunk_ok)
  ekSentCt1ReceivedRecvCt2Chunk_ok := h.ekSentCt1ReceivedRecvCt2Chunk_ok
  noHeaderReceivedRecvHdrChunk_ok :=
    sub_ok_inImage_growToCalleeExt_ax noHeaderReceivedRecvHdrChunkStackX
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      h.noHeaderReceivedRecvHdrChunk_ok
  polyAddChunk_ok := h.polyAddChunk_ok
  polyDecodedMessage_ok :=
    sub_ok_inImage_growToCalleeExt_ax polyDecoderDecodedMessageStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.polyDecodedMessage_ok)
  unchunkedCt1SentRecvEk_ok :=
    sub_ok_inImage_growToCalleeExt_ax unchunkedRecvEkStack
      (fun _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.unchunkedCt1SentRecvEk_ok)
  unchunkedCt1SentEkReceivedSendCt2_ok :=
    sub_ok_inImage_growToCalleeExt_ax unchunkedSendCt2Stack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.unchunkedCt1SentEkReceivedSendCt2_ok)
  sendCt2Encoder_ok :=
    sub_ok_inImage_growToCalleeExt_ax sendCt2EncoderStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.sendCt2Encoder_ok)
  ekReceivedCt1SampledRecvCt1Ack_ok :=
    sub_ok_inImage_growToCalleeExt_ax ekReceivedCt1SampledRecvCt1AckStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.ekReceivedCt1SampledRecvCt1Ack_ok)
  ct1AcknowledgedRecvEkChunk_ok :=
    sub_ok_inImage_growToCalleeExt_ax ct1AcknowledgedRecvEkChunkStack
      (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.ct1AcknowledgedRecvEkChunk_ok)
  ct2SampledRecvNextEpoch_ok :=
    sub_ok_inImage_growToCalleeExt_ax dropGluePoly16Stack
      (fun _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (sub_ok_inImage_of_sub_ok_ax img h.ct2SampledRecvNextEpoch_ok)

end CryptoVerification.SpqrV1.States.Recv
