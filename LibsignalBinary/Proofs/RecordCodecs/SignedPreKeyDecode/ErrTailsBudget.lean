/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SignedPreKeyRecordStructure::decode` Shared Error Exits

`RustCliAllocBudget`-threaded relocatable loop-exit error stubs targeting `+656` on Block `562`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification.RecordCodecsBinary (sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers (SpkLoopRegs SpkSavedRegs spkConvergeMem spkConvergeMem_none_intro spkErr16_pack40 spkMemRegion48_unpack16 spkOff_converge spkOff_fromCommon spkOff_fromRet spkOff_okEmpty spkOff_pushCall spkOff_pushRet spkOff_tag5FromCommon spkOff_tag5FromRet spkPointsTo112_memRegion40_entails_48 spkStructOf)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (DecodeErrorFromEnv DecodeErrorPushBoundedEnv SignedHooksPlaced SpkCaps SpkErrTailEnv
   SpkLoopBoundedEnv decodeErrorFromBudgetSpec decodeErrorPushBoundedSpec
   fitsEnv_spkLoop_errTail fitsEnv_spkLoop_pushAfterFrom)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
  (noPanicQp sepWPp_call_budget_lscro sepWPp_end_noPanic_lscro spkConvergePostPlaced
   spk_decodeErrorFrom_placed_ok spk_decodeErrorPush_placed_ok)

set_option maxRecDepth 2000000
attribute [local irreducible] Program.fetch Program.externAt?

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q₁ Q₂ Qp : Arm64.State → SepProp → Prop}
    {oom : Arm64.State → SepProp}
    (hq : ∀ sf Pf, Q₁ sf Pf → Q₂ sf Pf)
    (h : Wire.SepWPp prog ret s P Q₁ Qp oom) :
    Wire.SepWPp prog ret s P Q₂ Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq1, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hq1, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem okEmpty_392_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (hok : out = some m)
    (hpc : s.pc = (blkPl_562).base + spkOff_okEmpty)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (spkStructOf A.repAlloc sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗ memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out)
      (noPanicQp s0) := by
  refine sepWPp_end_noPanic_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine ⟨⟨by simpa [arm64_norm] using hregs.sp,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcrl1, by simp [htr, arm64_norm],
    by simpa [arm64_norm] using hregs.x24,
    by simpa [arm64_norm] using hregs.x19_eq,
    ⟨by simpa [arm64_norm] using hregs.saved.x25,
     by simpa [arm64_norm] using hregs.saved.x26,
     by simpa [arm64_norm] using hregs.saved.x27,
     by simpa [arm64_norm] using hregs.saved.x28⟩⟩, [], .done .nil, ?_⟩
  rw [hok]
  dsimp only [spkConvergeMem, AllocCostModel.stepEvents, List.foldl]
  rw [pure_true_emp (by simp [arm64_norm]), emp_sepConj]
  simp only [arm64_norm]
  exact Entails.refl _

theorem fromCommon_372_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr kind e0 : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_fromCommon)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = kind)
    (hkind : KindNoHeap kind)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ e0) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s ∗
        stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out)
      (noPanicQp s0) := by
  have hcall := spk_decodeErrorFrom_placed_ok hH
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = kind := hx8
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps_sync_pool (lsmpl.base 261)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_budget_lscro (sp' + 112#64, kind, st) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_fromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool lim st _ ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind ∧ FitsEnv M lim st DecodeErrorFromEnv)
    (by simp [decodeErrorFromBudgetSpec, hsp_eq, h29, h8, arm64_norm]; rfl)
    ⟨rfl, hkind, fitsEnv_spkLoop_errTail (fun _ => SpkErrTailEnv.of_decodeErrorFrom) hFit⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorFromBudgetSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs => ?_
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hevs => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine sepWPp_end_noPanic_lscro hcrl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcrl3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcrl3, by simp [htr2, htr, arm64_norm],
    by simp [hx24_2, arm64_norm],
    by simp [hx19_2, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩,
    evs, .done (SpkErrTailEnv.of_decodeErrorFrom hevs), ?_⟩
  have hpack := spkConvergeMem_none_intro (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
    (A.atState lim (M.stepEvents evs st) s2) sp' x19 ptr (s2.readReg64 .x0) 0 mErr bs herr herr_nz
  dsimp only [RustCliAllocBudget.atState] at hpack ⊢
  simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
  refine Entails.trans ?_ hpack
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  ac_rfl

theorem pushCall_648_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_pushCall)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = sp' + 112#64)
    (hnz : err ≠ 0#64)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ err) ∗ memRegion (sp' + 120#64) 40 ∗
        decodeErrorAtStackLen A.repAlloc err 0 ∗
        spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s ∗
        stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out)
      (noPanicQp s0) := by
  have hcall := spk_decodeErrorPush_placed_ok hH
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = sp' + 112#64 := hx0
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  let st1 := M.stepEvents (rustAllocEvents 72 8) st
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 257) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_budget_lscro (sp' + 112#64, err, 0, st1) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_pushRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
      A.pool lim st1 s ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ (0 : Nat) < 2 ^ 32 ∧ FitsEnv M lim st1 (DecodeErrorPushBoundedEnv 0))
    (by simp [decodeErrorPushBoundedSpec, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_setPC, hsp_eq, h0, arm64_norm])
    ⟨rfl, by decide, fitsEnv_spkLoop_pushAfterFrom hFit⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorPushBoundedSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs => ?_
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hevs => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine sepWPp_end_noPanic_lscro hcrl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcrl3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcrl3, by simp [htr2, htr, arm64_norm],
    by simp [hx24_2, arm64_norm],
    by simp [hx19_2, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩,
    rustAllocEvents 72 8 ++ evs, .done (.fromPush hevs), ?_⟩
  have hpack := spkConvergeMem_none_intro (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
    (A.atState lim (M.stepEvents (rustAllocEvents 72 8 ++ evs) st) s2) sp' x19 ptr err 1 mErr bs herr hnz
  dsimp only [RustCliAllocBudget.atState] at hpack ⊢
  rw [M.stepEvents_append] at hpack ⊢
  dsimp only [st1]
  simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
  refine Entails.trans ?_ hpack
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkPointsTo112_memRegion40_entails_48 sp' err))))))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  ac_rfl

theorem tag5FromPush_608_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr kind : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5FromCommon)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hkind : KindNoHeap kind)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s ∗
        stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out)
      (noPanicQp s0) := by
  have hcall := spk_decodeErrorFrom_placed_ok hH
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_budget_lscro (sp' + 112#64, kind, st) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_tag5FromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool lim st s ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind ∧ FitsEnv M lim st DecodeErrorFromEnv)
    (by simp [decodeErrorFromBudgetSpec, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_setPC, hsp_eq, h29, arm64_norm])
    ⟨rfl, hkind, fitsEnv_spkLoop_errTail (fun _ => SpkErrTailEnv.of_decodeErrorFrom) hFit⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorFromBudgetSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs₁ => ?_
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hevs1_eq : evs₁ = rustAllocEvents 72 8 := hevs₁
  subst hevs1_eq
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hregs.x19_eq, arm64_norm] using hcs2.1
  have hx24_2 : s2.readReg64 .x24 = sp' + 16#64 :=
    by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hsaved2 : SpkSavedRegs s0 s2 :=
    ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (spkMemRegion48_unpack16 sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushCall) ?_
  wp_steps_sync_pool ((blkPl_562).base + spkOff_pushCall)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcrl3
  refine Wire.SepWPp.mono_pre ?_
    (pushCall_648_placed_wp (st := st) (rem := rem) (caps := caps) hH
      (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr) (err := s2.readReg64 .x0)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      ⟨by simp [hsp2_eq, arm64_norm],
       by simp [hx29_2, arm64_norm],
       by simp [hx24_2, arm64_norm],
       by simp [hx19_2, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved2.x25,
        by simpa [arm64_norm] using hsaved2.x26,
        by simpa [arm64_norm] using hsaved2.x27,
        by simpa [arm64_norm] using hsaved2.x28⟩⟩
      (by simp [hx29_2, arm64_norm]) herr_nz
      (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
      hcrl3 (by simp [htr2, htr, arm64_norm]) hFit)
  have h40 := spkErr16_pack40 sp' e1
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left h40))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
  ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget
