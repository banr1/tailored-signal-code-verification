/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Defs
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Callee Wrappers and Epilogue

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` callee wrappers, state
invariants, `Vec<u8>` deallocation tails, and shared epilogue (`+812 .. +836`) on Block `84`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyPairResultAt
  ls_subroutine_ok_lscro_of_block ls_subroutine_ok_lscro_of_cl ls_subroutine_ok_lscro_of_plain
  sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
  (IkpBaseStatePlaced IkpLoopRegsPlaced ikpCalleeSavedAt ikpCalleeSaved_unsplit ikpSubStack)
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.TripleRatchet
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem ikp_bytesMerge_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_block (callerProg := lsProg_84 H) d.bytesMerge

theorem ikp_varintSlice_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_84 H) d.varintSlice

theorem ikp_skipField_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 1)
      (withLsCodeRoLoaded lsmpl (skipFieldSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_84 H) d.skipField

theorem ikp_dropDecodeError_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 4)
      (withLsCodeRoLoaded lsmpl (dropDecodeErrorSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_84 H) d.dropDecodeError

theorem ikp_pkTryFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 211) (withLsCodeRoLoaded lsmpl pkTryFromPlacedSpec) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_84 H) d.pkTryFrom

theorem ikp_varintSlow_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_84 H) d.varintSlow

theorem ikp_decodeErrorFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_84 H) d.decodeErrorFrom

theorem ikp_decodeErrorPush_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl
        (decodeErrorPushBoundedExternSpecWithStack M A lim (2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_84 H) d.decodeErrorPush

theorem ikp_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  ls_dealloc_lscro_ok (callerProg := lsProg_84 H) d.dealloc

theorem epilogue_812_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : DecodeGhost} {st : M.σ} {s0 s : State} {wbuf : BitVec 64}
    (hst : IkpBaseStatePlaced s0 (s0.sp - 224#64) s)
    (hpc : s.pc = (blkPl_84).base + bv% (812)) (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_84 H) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
        memRegion (s0.sp - 224#64) 144 ∗ ((s0.sp - 224#64 + 168#64) ↦₆₄ wbuf) ∗
        ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
        identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗
        (∃∗ evs : List AllocEvent, ⌜IdentityKeyPairTryFromEnv x.bytes.length evs⌝ ∗
          A.pool lim (M.stepEvents evs st) s))
      (fun sf Pf => sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (identityKeyPairTryFromPlacedSpec A lim).post (x, st) s0 sf))
      (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx26, hx27, hx28⟩
  simp only [sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun evs => ?_
  refine Wire.SepWPp.mono_pre
    (P' := ⌜IdentityKeyPairTryFromEnv x.bytes.length evs⌝ ∗
      (memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
        memRegion (s0.sp - 224#64) 144 ∗ ((s0.sp - 224#64 + 168#64) ↦₆₄ wbuf) ∗
        ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
        identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.pure_pre fun hevs => ?_
  unfold ikpCalleeSavedAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_end_noPanic_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro _
  refine ⟨by simp_all [arm64_norm], fun hv => ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], hv⟩, ?_⟩
  dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded, identityKeyPairTryFromRawSpec]
  rw [pure_true_emp (by simp_all [arm64_norm]), emp_sepConj]
  have hstk := ikpCalleeSaved_unsplit s0.sp s0 wbuf
  unfold ikpCalleeSavedAt at hstk
  simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    sepExists_sepConj_left, sepConj_assoc]
  refine Entails.sepExists_right evs ?_
  rw [pure_true_emp hevs, emp_sepConj]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  apply entails_of_eq; ac_rfl

theorem cleanup_sk_792_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {s0 s : State}
    {sp' skCap skPtr : BitVec 64} {skBs : List (BitVec 8)}
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (792)) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (vecU8Buf A.repAlloc skCap skPtr skBs ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ (∃∗ evs : List AllocEvent, ⌜OptByteFreeEnv evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗ stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  by_cases hcap : skCap = 0#64
  · subst hcap; rw [vecU8Buf_zero]; refine Wire.SepWPp.pure_pre fun _ => ?_
    have _hsp_eq := hst.sp
    refine sepWPp_of_sepWP_end_noPanic_lscro hst.crl ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine ⟨hst.of_steps hcrl1 (by simp_all [arm64_norm]) (by simp_all [hst.trace, arm64_norm])
      (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
      (by simp_all [hst.x28, arm64_norm]), ?_⟩
    refine sepConj_mono_left ?_
    simp only [arm64_norm]
    refine Entails.sepExists_right [] ?_
    rw [pure_true_emp OptByteFreeEnv.nil, emp_sepConj, AllocCostModel.stepEvents_nil]
    exact Entails.refl _
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc skCap skPtr skBs hcap)) ?_
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_eq := hst.sp
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have _hne : (skCap == 0#64) = false := beq_false_of_ne hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (skPtr, skCap.toNat, 1, st) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (812))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool lim st s ∗ A.live skPtr skCap.toNat 1 ∗ memRegion skPtr skCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := skPtr = skPtr ∧ skCap.toNat = skCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        RustLayoutOk skCap.toNat 1 ∧ LsRetAddr624 ((blkPl_84).base + bv% (812)))
      (by simp_all [Hooks2Budget.rustDeallocExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, ⟨layoutOk_align1 hpos hlt, by decide⟩,
        lsRetAddr624_blockPlacement_base_add 84 (bv% (812)) (by decide) (by decide)⟩
      (by rw [RustCliAllocBudget.repAlloc_live, hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [Hooks2Budget.rustDeallocExternSpecWithStack,
      IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    refine sepWPp_of_sepWP_end_noPanic_lscro hcrl2 ?_
    refine Wire.SepWP.done hpc2 hrun2 ?_; intro hcrl3
    refine ⟨{
      sp := hsp2.trans (by tryFromPost_sp [hsp_eq])
      spAligned := hsp2_align
      crl := hcrl3
      trace := htr2.trans (by simp_all [hst.trace, arm64_norm])
      x26 := hcs2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x26, arm64_norm])
      x27 := hcs2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x27, arm64_norm])
      x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x28, arm64_norm])
    }, ?_⟩
    have hev_ent : A.pool lim (M.stepEvents (rustDeallocEvents skCap.toNat 1) st) s2 ⊢
        ∃∗ evs : List AllocEvent, ⌜OptByteFreeEnv evs⌝ ∗
          A.pool lim (M.stepEvents evs st) s2 := by
      refine Entails.sepExists_right (rustDeallocEvents skCap.toNat 1) ?_
      rw [pure_true_emp (OptByteFreeEnv.dealloc hpos hlt), emp_sepConj]
      exact Entails.refl _
    refine Entails.trans ?_ (sepConj_mono_left hev_ent)
    apply entails_of_eq; simp only [arm64_norm]; try rw [hsp_eq]; rw [hstack]; ac_rfl

theorem cleanup_pk_sk_772_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64} {pkBs skBs : List (BitVec 8)}
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (772)) (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (vecU8Buf A.repAlloc pkCap pkPtr pkBs ∗ vecU8Buf A.repAlloc skCap skPtr skBs ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗ stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  by_cases hcap : pkCap = 0#64
  · subst hcap; rw [vecU8Buf_zero]; refine Wire.SepWPp.pure_pre fun _ => ?_
    have _hsp_eq := hst.sp
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (792)) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_mono_post
      (Wire.SepWPp.mono_pre
        (by apply entails_of_eq; simp only [arm64_norm]; ac_rfl)
        (cleanup_sk_792_placed_wp (st := st) d
          (hst.of_steps hcrl1 (by simp_all [arm64_norm]) (by simp_all [hst.trace, arm64_norm])
            (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
            (by simp_all [hst.x28, arm64_norm]))
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf (sepConj_mono_left ?_)⟩
    refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
    refine Entails.sepExists_right evs ?_
    rw [pure_true_emp (TwoOptByteFreeEnv.single hevs), emp_sepConj]
    exact Entails.refl _
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc pkCap pkPtr pkBs hcap)) ?_
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_eq := hst.sp
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have _hne : (pkCap == 0#64) = false := beq_false_of_ne hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (pkPtr, pkCap.toNat, 1, st) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (792))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool lim st s ∗ A.live pkPtr pkCap.toNat 1 ∗ memRegion pkPtr pkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pkPtr = pkPtr ∧ pkCap.toNat = pkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        RustLayoutOk pkCap.toNat 1 ∧ LsRetAddr624 ((blkPl_84).base + bv% (792)))
      (by simp_all [Hooks2Budget.rustDeallocExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, ⟨layoutOk_align1 hpos hlt, by decide⟩,
        lsRetAddr624_blockPlacement_base_add 84 (bv% (792)) (by decide) (by decide)⟩
      (by rw [RustCliAllocBudget.repAlloc_live, hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [Hooks2Budget.rustDeallocExternSpecWithStack,
      IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst2 : IkpBaseStatePlaced s0 sp' s2 := {
      sp := hsp2.trans (by tryFromPost_sp [hsp_eq])
      spAligned := hsp2_align
      crl := hcrl2
      trace := htr2.trans (by simp_all [hst.trace, arm64_norm])
      x26 := hcs2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x26, arm64_norm])
      x27 := hcs2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x27, arm64_norm])
      x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x28, arm64_norm])
    }
    have hx21_2 : s2.readReg64 .x21 = skCap := hcs2.2.2.1.trans (by simp_all [arm64_norm])
    have hx23_2 : s2.readReg64 .x23 = skPtr := hcs2.2.2.2.2.1.trans (by simp_all [arm64_norm])
    refine Wire.SepWPp.mono_pre
      (P' := vecU8Buf A.repAlloc skCap skPtr skBs ∗
        A.pool lim (M.stepEvents (rustDeallocEvents pkCap.toNat 1) st) s2 ∗
        stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [arm64_norm]; try rw [hsp_eq]; rw [hstack]; ac_rfl) ?_
    refine sepWPp_mono_post
      (cleanup_sk_792_placed_wp d hst2 hpc2 hrun2 hx21_2 hx23_2)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf (sepConj_mono_left ?_)⟩
    refine Entails.sepExists_elim fun evs2 => Entails.pure_left fun hevs2 => ?_
    rw [← M.stepEvents_append]
    refine Entails.sepExists_right (rustDeallocEvents pkCap.toNat 1 ++ evs2) ?_
    rw [pure_true_emp (TwoOptByteFreeEnv.pair (OptByteFreeEnv.dealloc hpos hlt) hevs2), emp_sepConj]
    exact Entails.refl _

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
