/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMerge
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopError
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Field Merge Branches

`RustCliAllocBudget`-threaded relocatable CPS proofs for field 1 (`publicKey`), field 2
(`privateKey`), and unknown-tag `skip_field` on Block `84`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMergeBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
  hiding rustDeallocExternSpecWithStack decodeErrorFromSpecWithStack
    decodeErrorPushExternSpecWithStack decodeVarintSlowSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
  hiding dropDecodeErrorSpecGen dropDecodeErrorSpecX decodeVarintSliceSpecGen decodeVarintSliceSpecX
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (DecodeGhost sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers hiding ikpLoopCommonPlaced
open scoped CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents decodeVarintSliceSpecGen decodeVarintSliceSpecX)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced DecodeErrorPushBoundedEnv
   decodeErrorPushBoundedExternSpecWithStack decodeErrorPushBoundedExternBudgetSpecWithStack
   RecordCodecIterEnv RecordCodecLoopEnv fitsEnv_recordCodecLoop_head
   noPanicQp sepWPp_mono_post sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
  (ikp_varintSlice_placed_ok ikp_decodeErrorFrom_placed_ok ikp_decodeErrorPush_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
  (ikpExitPostPlaced ikpExitPostPlaced_prepend_iter decodeErr_616_placed_wp ikpLoopCommonPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section LoopMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_lm (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_lm (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_lm (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_lm (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_lm (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_lm (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_lm (s : State) : s.advancePC.sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_lm (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by
  cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_lm (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_lm (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_lm (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end LoopMergeStateSimp

theorem decodeErrorFrom_600_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hpc : s.pc = (blkPl_84).base + 600#64) (hrun : s.status = .Running)
    (hkind : KindNoHeap (s.readReg64 .x8))
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A.repAlloc (sp' + 48#64) mErr ∗
        ((sp' + 96#64) ↦₆₄ w0) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗
        lsLogOff ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hcall := ikp_decodeErrorFrom_placed_ok d
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have _hx29 := hregs.x29
  have hstack := stackAt_sub_split s.sp (2 * extHookStack) (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 261) ?_
  wp_steps_sync_pool (lsmpl.base 261)
  refine sepWPDoneWire (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (s.sp + 96#64, s.readReg64 (Reg.gpr 8#5), st) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (612))
    (by simp_all [hregs.base.trace, arm64_norm])
    (T := ((s.sp + 96#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (s.sp + 104#64) 40 ∗
      A.pool lim st _ ∗ stackAt s.sp (2 * extHookStack))
    (φ := s.sp + 96#64 = s.sp + 96#64 ∧ KindNoHeap (s.readReg64 (Reg.gpr 8#5)) ∧
      FitsEnv M lim st DecodeErrorFromEnv)
    (by simp_all [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
    ⟨rfl, hkind, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeErrorFrom) hFit⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs1 := hregs.of_steps hcrl1 (by simp_all [arm64_norm])
    (by simp_all [hregs.base.trace, arm64_norm])
    (by simp_all [hregs.base.x26, arm64_norm]) (by simp_all [hregs.base.x27, arm64_norm])
    (by simp_all [hregs.base.x28, arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [hregs.x19, arm64_norm]) (by simp_all [hregs.x21, arm64_norm])
    (by simp_all [hregs.x24, arm64_norm])
  dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  refine SepWPp.pure_pre fun ⟨_hx0_ne, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  have hregs2' := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
  refine sepWPDoneWire (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl3
  refine sepWPp_mono_post
    (SepWPp.mono_pre
      (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A.repAlloc (s.sp + 48#64) mErr ∗
        memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
        memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) _ ∗
        stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A.repAlloc (s2.readReg64 (Reg.gpr 0#5)))
      (by simp only [arm64_norm]
          rw [hstack]
          refine Entails.trans
            (sepConj_mono (decodeErrorWith_entails_at A.repAlloc (s2.readReg64 (Reg.gpr 0#5)) 0) (Entails.refl _)) ?_
          apply entails_of_eq; sep_ac_rfl)
      (decodeErr_616_placed_wp d (x := x) (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
        htry_err
        (hregs2'.base.of_steps hcrl3 (by simp_all [hregs2'.base.sp, arm64_norm])
          (by simp_all [hregs2'.base.trace, arm64_norm]) (by simp_all [hregs2'.base.x26, arm64_norm])
          (by simp_all [hregs2'.base.x27, arm64_norm]) (by simp_all [hregs2'.base.x28, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [hregs2'.x19, arm64_norm]) (by simp_all [hregs2'.x24, arm64_norm])
        (by simp_all [arm64_norm])))
    fun sf Pf h => ikpExitPostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeErrorFrom hevs) h

theorem decodeErrorPush_916_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr err : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hpc : s.pc = (blkPl_84).base + 916#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = sp' + 96#64) (herr_ne : err ≠ 0#64)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A.repAlloc (sp' + 48#64) mErr ∗
        ((sp' + 96#64) ↦₆₄ err) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗
        lsLogOff ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A.repAlloc err 0)
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hcall := ikp_decodeErrorPush_placed_ok d
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have hstack := stackAt_sub_split s.sp (2 * extHookStack) (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 257) ?_; wp_steps
  refine sepWPDoneWire (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (s.sp + 96#64, err, 0, st) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (920))
    (by simp_all [hregs.base.trace, arm64_norm])
    (T := ((s.sp + 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
      A.pool lim st s ∗ stackAt s.sp (2 * extHookStack))
    (φ := s.sp + 96#64 = s.sp + 96#64 ∧ err ≠ 0#64 ∧ 0 < 4294967296 ∧
      FitsEnv M lim st (DecodeErrorPushBoundedEnv 0))
    (by simp_all [decodeErrorPushBoundedExternSpecWithStack, decodeErrorPushBoundedExternBudgetSpecWithStack, arm64_norm])
    ⟨rfl, herr_ne, by decide, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeErrorPush0) hFit⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorPushBoundedExternSpecWithStack, decodeErrorPushBoundedExternBudgetSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun err' => ?_
  refine SepWPp.pure_pre fun _herr' => ?_
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun evs => SepWPp.pure_pre fun hevs => ?_
  have hregs1 := hregs.of_steps hcrl1 rfl
    (by simp_all [hregs.base.trace, arm64_norm])
    (by simp_all [hregs.base.x26, arm64_norm]) (by simp_all [hregs.base.x27, arm64_norm])
    (by simp_all [hregs.base.x28, arm64_norm]) (by simp_all [hregs.x29, arm64_norm])
    (by simp_all [hregs.x19, arm64_norm]) (by simp_all [hregs.x21, arm64_norm])
    (by simp_all [hregs.x24, arm64_norm])
  have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  have _hx29_2 := hregs2.x29
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
  refine sepWPDoneWire (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl3
  have hm48 := ikpPointsTo64_96_mem40_entails_mem48 s.sp err'
  refine sepWPp_mono_post
    (SepWPp.mono_pre
      (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A.repAlloc (s.sp + 48#64) mErr ∗
        memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
        memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) _ ∗
        stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A.repAlloc err')
      (by simp only [arm64_norm]
          rw [hstack]
          refine Entails.trans
            (sepConj_mono_right (sepConj_mono (decodeErrorWith_entails_at A.repAlloc err' 1) (Entails.refl _))) ?_
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm48))))
          apply entails_of_eq; sep_ac_rfl)
      (decodeErr_616_placed_wp d (x := x) (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
        htry_err
        (hregs2.base.of_steps hcrl3 (by simp_all [hregs2.base.sp, arm64_norm])
          (by simp_all [hregs2.base.trace, arm64_norm]) (by simp_all [hregs2.base.x26, arm64_norm])
          (by simp_all [hregs2.base.x27, arm64_norm]) (by simp_all [hregs2.base.x28, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [hregs2.x19, arm64_norm]) (by simp_all [hregs2.x24, arm64_norm])
        (by simp_all [arm64_norm])))
    fun sf Pf h => ikpExitPostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeErrorPush0 hevs) h

theorem decodeVarintSlice_168_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 168#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63) (hpre_slice : VarintSlicePre bs)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_84).base + 220#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 → s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s1)
        (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs
          (IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : decodeVarint bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs
        (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hcall := ikp_varintSlice_placed_ok d
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have _hsp_align := hregs.base.spAligned; have _hx29 := hregs.x29
  have _hx1' : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split s.sp decodeVarintSliceStackX (skipFieldStackX 100)
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [hstack, ikpMem48_split24 s.sp, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 76) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (⟨s.sp + 96#64, ptr, bs⟩, st) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (176))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := memRegion (s.sp + 96#64) 24 ∗ (ptr ↦ₛ bs) ∗
      A.pool lim st s ∗ stackAt s.sp decodeVarintSliceStackX)
    (φ := s.sp + 96#64 = s.sp + 96#64 ∧ bs.length < 9223372036854775808 ∧ VarintSlicePre bs ∧
      FitsEnv M lim st (DecodeVarintSliceEnv bs))
    (by simp [*, decodeVarintSliceSpecX, decodeVarintSliceSpecGen,
      decodeVarintSliceStackX, decodeErrorHookStackX, arm64_norm])
    ⟨rfl, hlen, hpre_slice, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeVarintSlice) hFit⟩
    (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs1 := hregs.of_steps hcrl1 rfl
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm]) (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = s.sp + 32#64 :=
    hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = s.sp + 40#64 :=
    hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  dsimp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, _hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
        BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]
      omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]
      omega
    rw [pointsTo64_zero_split32 (s.sp + 96#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    have hevs0 : evs = [] := by
      rw [hevs]; unfold decodeVarintSliceEvents; rw [hd]
    subst hevs0
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hx29_2 : s2.readReg64 (Reg.gpr 29#5) = s.sp + 144#64 := hregs2.x29
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (220)) ?_; wp_steps
    wp_if hcc
    · exfalso; rw [← hrest] at hcc; exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · refine ProofLib.SepWP.transport_budgetPool (s1 := s2)
        (by simp)
        (hnext := ?_)
      wp_steps_sync_pool ((blkPl_84).base + bv% (220))
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      have hscr := ikpScratch24_ok_entails_mem48 s.sp key (BitVec.ofNat 64 (bs.length - rest.length))
      refine SepWPp.mono_pre ?_
        (hcont key rest _ hd (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
            (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
            (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
            (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
            (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
      unfold sliceCursorAfter ikpLoopCommonPlaced
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
      rw [hstack]; apply entails_of_eq
      simp only [decodeVarintSliceStackX, decodeErrorHookStackX, ← hrest, hsub_bv, arm64_norm]
      sep_ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [pointsTo64_one_split32 (s.sp + 96#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => SepWPp.exists_pre fun e => ?_
    refine SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _he_ne => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hx29_2 : s2.readReg64 (Reg.gpr 29#5) = s.sp + 144#64 := hregs2.x29
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hpair := pointsTo64_pair_entails_memRegion16 (s.sp + 32#64) ptr (BitVec.ofNat 64 bs.length)
    have hscr := ikpScratch24_err_entails_mem48 s.sp e
    refine sepWPp_mono_post
      (SepWPp.mono_pre
        (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A.repAlloc (s.sp + 48#64) m ∗
          memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
          memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) _ ∗
          stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A.repAlloc e)
        (by refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono hpair
                (sepConj_mono (ikpStructLoopOf_entails_of A.repAlloc (s.sp + 48#64) bs.length m)
                  (sepConj_mono hscr
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (decodeErrorWith_entails_at A.repAlloc e 0)))))))))))
            rw [hstack]; apply entails_of_eq
            simp only [decodeVarintSliceStackX, decodeErrorHookStackX, arm64_norm]
            sep_ac_rfl)
        (decodeErr_616_placed_wp d (x := x) (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
          (hnone hd)
          (hregs2.base.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
            (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
            (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, hregs2.x19, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm])
          (by simp [*, arm64_norm])))
      fun sf Pf h => ikpExitPostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeVarintSlice hevs) h

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMergeBudget
