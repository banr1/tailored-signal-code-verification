/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMergeBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPkBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Loop
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopError
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMerge
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarint
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` Proof

Proves `identityKeyPair_tryFrom_placed_ok` (`identityKeyPairTryFromPlacedSpec`, Block `84`) under
`[LibsignalPlacement]` and `PortDepsPlaced M A lim H` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`
under `FitsEnv`).
-/

@[expose] public section

set_option autoImplicit false

open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes recursionLimit skipField)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded decodeErrorAt decodeErrorAtStackLen extract_withLsCodeRoLoaded lsLogOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost SkipFieldGhost bytesMergeCapOk_mono bytesMergeCapOk_zero bytesMergeStackX skipFieldStackX sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalTripleRatchet.Wire (SepWPp cmn_one_ne_of_lt cons_len_bv64_ne_zero decodeErrorWith_entails_at decodeKey_suffix entails_of_eq mergeBytes_suffix pointsTo64_pair_entails_memRegion16 pure_true_emp setWidth32_ofNat64 setWidth8_ofNat64 skipField_suffix stackAt_sub_split vecU8Buf vecU8Buf_zero)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure decodeFieldsLoop skipUnknown)
open CryptoVerification.RecordCodecs.Placed (blkPl_84 lsProg_84)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers (IkpBaseStatePlaced IkpLoopRegsPlaced ikpCalleeSavedAt ikpEmptyCells_entails_structAt ikpFold144 ikpMem144_prologue_cells ikpMem48_split8 ikpMem80_cells ikpRootStack_split ikpStructAt ikpStructAt_entails_loopOf ikpStructAt_entails_of ikpStructLoopOf ikpStructLoopOf_entails_of ikpStructLoopOf_mono ikpStructOf ikpSubStack ikp_decode_field_lengths ikp_mergeField_suffix spAligned_sub224 tag_ge3_conds vecU8Buf_cap_lt63)
open CryptoVerification.RustHeap (vecHeader vecU8At)

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFromBudget

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary
  (DecodeGhost identityKeyPairResultAt sepWPp_of_sepWP_lscro)
open scoped CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced RecordCodecIterEnv RecordCodecLoopEnv mergeBytes_len_bound
   fitsEnv_recordCodecLoop_head fitsEnv_recordCodecLoop_bytesHead
   fitsEnv_recordCodecLoop_tail fitsEnv_recordCodecLoop_bytesTail fitsEnv_recordCodecLoop_mono_fuel
   TwoOptByteFreeEnv IkpPostCleanupEnv IkpSubEnv IdentityKeyPairTryFromEnv
   identityKeyPairTryFromRawSpec identityKeyPairTryFromPlacedSpec
   noPanicQp sepWPp_frame_noPanic sepWPp_mono_post sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
  (ikp_bytesMerge_placed_ok ikp_skipField_placed_ok epilogue_812_placed_wp)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
  (ikpExitMemPlaced ikpExitPostPlaced ikpExitPostPlaced_prepend_iter
   ikpExitPostPlaced_prepend_bytes ikpExitPostPlaced_mono_fuel
   ikp_advance_cursor_placed decodeErr_616_placed_wp ikpLoopCommonPlaced)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMergeBudget
  (decodeErrorPush_916_placed_wp)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopBudget
  (decodeKey_124_placed_cps)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPkBudget
  (post_344_placed_wp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section TopStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_top (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_top (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_top (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_top (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_top (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_top (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_top (s : State) : s.advancePC.sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_top (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_top (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_top (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_top (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_top (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_top (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_top (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_top (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_top (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_top (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_top (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_top (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end TopStateSimp

local macro "step_ikp_regs " h:term:max c:term:max : term => `(
  (($h).of_steps $c (by simp [*, ($h).base.sp, arm64_norm])
    (by simp [*, ($h).base.trace, arm64_norm]) (by simp [*, ($h).base.x26, arm64_norm])
    (by simp [*, ($h).base.x27, arm64_norm]) (by simp [*, ($h).base.x28, arm64_norm])
    (by simp [*, ($h).x29, arm64_norm]) (by simp [*, ($h).x19, arm64_norm])
    (by simp [*, ($h).x21, arm64_norm]) (by simp [*, ($h).x24, arm64_norm])))

/-! ## 1. Field Merge CPS Lemmas (Block `84`) -/

theorem mergePubKey_264_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 264#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hlen : bs.length < 2 ^ 63) (hlen_max : bs.length ≤ maxLen)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 4) maxLen))
    (hcont : ∀ (v rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      FitsEnv M lim st1 (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A lim st1 sp' x.ret rest.length { m with publicKey := v } s1)
        (ikpExitPostPlaced A lim st1 (2 * rest.length + 2) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none →
      CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (2 * bs.length + 4) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hcall := ikp_bytesMerge_placed_ok d
  unfold ikpLoopCommonPlaced ikpStructLoopOf ikpStructAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun sk =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨hpk_ok, hsk_ok⟩ => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have h29 := hregs.x29
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 7) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hregs1 := step_ikp_regs hregs hcrl1
  let xBm : BytesMergeGhost :=
    ⟨wt, sp' + 48#64, pk.cap, pk.ptr, m.publicKey, sp' + 168#64, sp' + 32#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (BytesMergeEnv xBm) :=
    fitsEnv_recordCodecLoop_bytesHead hlen_max (by omega : 2 * bs.length + 1 ≤ 2 * bs.length + 4) hFit
  refine sepWPp_call_noPanic_lscro (xBm, st) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (276))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := vecU8At A.repAlloc (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
      ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
      sliceCursorAt (sp' + 32#64) ptr bs ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 48#64 = sp' + 48#64 ∧ sp' + 168#64 = sp' + 168#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk pk.cap bs.length ∧
      FitsEnv M lim st (BytesMergeEnv xBm))
    (by cases wt <;> simp [*, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPreBoundBudget, xBm, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, hlen, hpk_ok, hFit_call⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen, xBm]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec]
    have hlen_bound := mergeBytes_len_bound hm
    have hbud_some : (2 * rest.length + 2) + 2 * v.length + 1 ≤ 2 * bs.length + 4 := by omega
    have hFit_rest : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) :=
      fitsEnv_recordCodecLoop_bytesTail hm hlen_max hevs₁
        (fitsEnv_recordCodecLoop_mono_fuel hbud_some hFit)
    obtain ⟨k, _, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun cap' => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hcap' => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (108)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (108))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A.repAlloc (sp' + 48#64) cap' ptr' v ∗
        vecU8At A.repAlloc (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructLoopOf A.repAlloc (sp' + 48#64) rest.length { m with publicKey := v } := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_loopOf A.repAlloc ⟨cap', ptr'⟩ sk (sp' + 48#64) rest.length
          { m with publicKey := v } hcap' (bytesMergeCapOk_mono hsk_ok hrest_le)
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
        (by unfold ikpLoopCommonPlaced
            refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
            apply entails_of_eq; try rw [hstack]
            try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
            try simp only [arm64_norm]; sep_ac_rfl)
        (hcont v rest (M.stepEvents evs₁ st) _ hm hFit_rest
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (step_ikp_regs hregs2 hcrl3)))
      (fun sf Pf h => ikpExitPostPlaced_mono_fuel hbud_some (ikpExitPostPlaced_prepend_bytes hm hlen_max hevs₁ h))
  | none =>
    dsimp only; simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have _hx29_2 := hregs2.x29
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (916)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (916))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A.repAlloc (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A.repAlloc (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructOf A.repAlloc (sp' + 48#64) m := by
      simpa [ikpStructAt, BitVec.add_assoc] using ikpStructAt_entails_of A.repAlloc pk sk (sp' + 48#64) m
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
        (P' := memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A.repAlloc (sp' + 48#64) m ∗
          ((sp' + 96#64) ↦₆₄ s2.readReg64 (Reg.gpr 0#5)) ∗ memRegion (sp' + 104#64) 40 ∗
          ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs₁ st) _ ∗
          stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A.repAlloc (s2.readReg64 (Reg.gpr 0#5)) 0)
        (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
            apply entails_of_eq; try rw [hstack]
            try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
            try simp only [arm64_norm]; sep_ac_rfl)
        (decodeErrorPush_916_placed_wp d (st := M.stepEvents evs₁ st) (fuel := 2 * bs.length + 2) (maxLen := maxLen)
          (hnone hm) (step_ikp_regs hregs2 hcrl3)
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) hx0_ne
          (fitsEnv_recordCodecLoop_tail
            (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_bytesMergeErr (x := xBm) hm hevs₁)
            (fitsEnv_recordCodecLoop_mono_fuel (by omega) hFit))))
      (fun sf Pf h => ikpExitPostPlaced_mono_fuel (by omega)
        (ikpExitPostPlaced_prepend_iter
          (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_bytesMergeErr (x := xBm) hm hevs₁) h))

theorem mergePrivKey_92_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 92#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hlen : bs.length < 2 ^ 63) (hlen_max : bs.length ≤ maxLen)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 4) maxLen))
    (hcont : ∀ (v rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      FitsEnv M lim st1 (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A lim st1 sp' x.ret rest.length { m with privateKey := v } s1)
        (ikpExitPostPlaced A lim st1 (2 * rest.length + 2) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none →
      CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (2 * bs.length + 4) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hcall := ikp_bytesMerge_placed_ok d
  unfold ikpLoopCommonPlaced ikpStructLoopOf ikpStructAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun sk =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨hpk_ok, hsk_ok⟩ => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  have h29 := hregs.x29; have h21 := hregs.x21
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 7) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hregs1 := step_ikp_regs hregs hcrl1
  let xBm : BytesMergeGhost :=
    ⟨wt, sp' + 72#64, sk.cap, sk.ptr, m.privateKey, sp' + 168#64, sp' + 32#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (BytesMergeEnv xBm) :=
    fitsEnv_recordCodecLoop_bytesHead hlen_max (by omega : 2 * bs.length + 1 ≤ 2 * bs.length + 4) hFit
  refine sepWPp_call_noPanic_lscro (xBm, st) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (104))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := vecU8At A.repAlloc (sp' + 72#64) sk.cap sk.ptr m.privateKey ∗
      ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
      sliceCursorAt (sp' + 32#64) ptr bs ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 72#64 = sp' + 72#64 ∧ sp' + 168#64 = sp' + 168#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk sk.cap bs.length ∧
      FitsEnv M lim st (BytesMergeEnv xBm))
    (by cases wt <;> simp [*, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPreBoundBudget, xBm, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, hlen, hsk_ok, hFit_call⟩
    (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen, xBm]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec]
    have hlen_bound := mergeBytes_len_bound hm
    have hbud_some : (2 * rest.length + 2) + 2 * v.length + 1 ≤ 2 * bs.length + 4 := by omega
    have hFit_rest : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) :=
      fitsEnv_recordCodecLoop_bytesTail hm hlen_max hevs₁
        (fitsEnv_recordCodecLoop_mono_fuel hbud_some hFit)
    obtain ⟨k, _, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun cap' => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hcap' => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (108)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (108))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A.repAlloc (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A.repAlloc (sp' + 72#64) cap' ptr' v ⊢
        ikpStructLoopOf A.repAlloc (sp' + 48#64) rest.length { m with privateKey := v } := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_loopOf A.repAlloc pk ⟨cap', ptr'⟩ (sp' + 48#64) rest.length
          { m with privateKey := v } (bytesMergeCapOk_mono hpk_ok hrest_le) hcap'
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
        (by unfold ikpLoopCommonPlaced
            refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
            apply entails_of_eq; try rw [hstack]
            try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
            try simp only [arm64_norm]; sep_ac_rfl)
        (hcont v rest (M.stepEvents evs₁ st) _ hm hFit_rest
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (step_ikp_regs hregs2 hcrl3)))
      (fun sf Pf h => ikpExitPostPlaced_mono_fuel hbud_some (ikpExitPostPlaced_prepend_bytes hm hlen_max hevs₁ h))
  | none =>
    dsimp only; simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have _hx29_2 := hregs2.x29
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (916)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (916))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hstruct : vecU8At A.repAlloc (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A.repAlloc (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructOf A.repAlloc (sp' + 48#64) m := by
      simpa [ikpStructAt, BitVec.add_assoc] using ikpStructAt_entails_of A.repAlloc pk sk (sp' + 48#64) m
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
        (P' := memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A.repAlloc (sp' + 48#64) m ∗
          ((sp' + 96#64) ↦₆₄ s2.readReg64 (Reg.gpr 0#5)) ∗ memRegion (sp' + 104#64) 40 ∗
          ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs₁ st) _ ∗
          stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A.repAlloc (s2.readReg64 (Reg.gpr 0#5)) 0)
        (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
            apply entails_of_eq; try rw [hstack]
            try rw [hregs1.base.sp]; try rw [hregs2.base.sp]
            try simp only [arm64_norm]; sep_ac_rfl)
        (decodeErrorPush_916_placed_wp d (st := M.stepEvents evs₁ st) (fuel := 2 * bs.length + 2) (maxLen := maxLen)
          (hnone hm) (step_ikp_regs hregs2 hcrl3)
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) hx0_ne
          (fitsEnv_recordCodecLoop_tail
            (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_bytesMergeErr (x := xBm) hm hevs₁)
            (fitsEnv_recordCodecLoop_mono_fuel (by omega) hFit))))
      (fun sf Pf h => ikpExitPostPlaced_mono_fuel (by omega)
        (ikpExitPostPlaced_prepend_iter
          (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_bytesMergeErr (x := xBm) hm hevs₁) h))

theorem mergeSkipField_284_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 284#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32) (hlen : bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 2) maxLen))
    (hcont : ∀ (rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      FitsEnv M lim st1 (RecordCodecLoopEnv fuel maxLen) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A lim st1 sp' x.ret rest.length m s1)
        (ikpExitPostPlaced A lim st1 fuel maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none →
      CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (fuel + 2) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hcall := ikp_skipField_placed_ok d
  unfold ikpLoopCommonPlaced
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have h29 := hregs.x29
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 1) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hregs1 := step_ikp_regs hregs hcrl1
  let xSk : SkipFieldGhost := ⟨wt, tag, 100, sp' + 168#64, sp' + 32#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (SkipFieldEnv xSk) :=
    fitsEnv_recordCodecLoop_head (fun _ => LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_skipField)
      (fitsEnv_recordCodecLoop_mono_fuel (by omega : fuel + 1 ≤ fuel + 2) hFit)
  refine sepWPp_call_noPanic_lscro (xSk, st) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (296))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ sliceCursorAt (sp' + 32#64) ptr bs ∗
      A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 168#64 = sp' + 168#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧
      bs.length < 9223372036854775808 ∧ FitsEnv M lim st (SkipFieldEnv xSk))
    (by cases wt <;> simp [*, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecGen, xSk, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, rfl, rfl, by decide, hlen, hFit_call⟩
    (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecGen, xSk]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hiter₁ : RecordCodecIterEnv maxLen evs₁ := LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_skipField hevs₁
  have hFit1 : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (fuel + 1) maxLen) :=
    fitsEnv_recordCodecLoop_tail hiter₁ hFit
  have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  have _hsp2_eq := hregs2.base.sp; have _hsp2_align := hregs2.base.spAligned
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, _, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (108)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
        (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A lim (M.stepEvents evs₁ st) sp' x.ret rest.length m _)
        (by unfold ikpLoopCommonPlaced
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (ikpStructLoopOf_mono A.repAlloc (sp' + 48#64) m hrest_le))))
            apply entails_of_eq; rw [hregs1.base.sp]; try simp only [arm64_norm]
            sep_ac_rfl)
        (hcont rest (M.stepEvents evs₁ st) _ hs
          (fitsEnv_recordCodecLoop_mono_fuel (by omega : fuel ≤ fuel + 1) hFit1)
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (step_ikp_regs hregs2 hcrl3)))
      (fun sf Pf h => ikpExitPostPlaced_prepend_iter hiter₁ (ikpExitPostPlaced_mono_fuel (by omega) h))
  | none =>
    dsimp only; simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
        (P' := memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A.repAlloc (sp' + 48#64) m ∗
          memRegion (sp' + 96#64) 48 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
          memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs₁ st) _ ∗
          stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAt A.repAlloc (s2.readReg64 (Reg.gpr 0#5)))
        (by refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (ikpStructLoopOf_entails_of A.repAlloc (sp' + 48#64) bs.length m)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (decodeErrorWith_entails_at A.repAlloc (s2.readReg64 (Reg.gpr 0#5)) 0)))))))))))
            apply entails_of_eq; rw [hregs1.base.sp]; try simp only [arm64_norm]
            sep_ac_rfl)
        (decodeErr_616_placed_wp d (st := M.stepEvents evs₁ st) (fuel := fuel + 1) (maxLen := maxLen)
          (mErr := m) (hnone hs)
          (hregs2.base.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
            (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
            (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, hregs2.x19, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm])
          (by simp [*, arm64_norm])))
      (fun sf Pf h => ikpExitPostPlaced_prepend_iter hiter₁ h)

/-! ## 2. Tag Dispatch, Decode Loop, Prologue, and Root Proof (Block `84`) -/

theorem dispatch_tag_248_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' ret : BitVec 64} {tag : ℕ}
    {P : State → SepProp} (hP_Step : ∀ s' : State, A.pool lim st s' = A.pool lim st s → P s' = P s)
    {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_84).base + 248#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' ret s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (blkPl_84).base + 264#64 → s1.status = .Running → IkpLoopRegsPlaced s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1 (P s1) Q (noPanicQp s0))
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (blkPl_84).base + 92#64 → s1.status = .Running → IkpLoopRegsPlaced s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1 (P s1) Q (noPanicQp s0))
    (h3 : 3 ≤ tag → ∀ s1 : State,
      s1.pc = (blkPl_84).base + 284#64 → s1.status = .Running → IkpLoopRegsPlaced s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1 (P s1) Q (noPanicQp s0)) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s (P s) Q (noPanicQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  rcases tag with _ | _ | _ | n
  · omega
  · refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (264)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (entails_of_eq (hP_Step _ (by simp only [arm64_norm])).symm)
      (h1 rfl _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (step_ikp_regs hregs hcrl1) (by simp [*, arm64_norm]))
  · refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (92)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (entails_of_eq (hP_Step _ (by simp only [arm64_norm])).symm)
      (h2 rfl _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (step_ikp_regs hregs hcrl1) (by simp [*, arm64_norm]))
  · obtain ⟨hc2, hc1, hc1_ne⟩ := tag_ge3_conds (n + 3) (by omega) htag_lt
    refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (284)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (entails_of_eq (hP_Step _ (by simp only [arm64_norm])).symm)
      (h3 (by omega) _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (step_ikp_regs hregs hcrl1) (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))

theorem mergeField_248_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 248#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hlen : bs.length < 2 ^ 63) (hlen_max : bs.length ≤ maxLen)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 4) maxLen))
    (hcont : ∀ (m' : IdentityKeyPairStructure) (rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest) →
      FitsEnv M lim st1 (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) →
      s1.pc = (blkPl_84).base + 108#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A lim st1 sp' x.ret rest.length m' s1)
        (ikpExitPostPlaced A lim st1 (2 * rest.length + 2) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField m tag wt bs = none →
      CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (2 * bs.length + 4) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  refine dispatch_tag_248_placed_cps (A := A) (lim := lim) (st := st)
    (P := fun s' => sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s')
    (fun s' hp => by unfold ikpLoopCommonPlaced; rw [hp])
    hpc hrun hregs hx1 htag_ge htag_lt
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 => ?_)
  · subst htag
    exact mergePubKey_264_placed_cps d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hlen hlen_max hFit
      (fun v rest st1 s2 hm => hcont { m with publicKey := v } rest st1 s2
        (by simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField, hm]))
      (fun hm => hnone (by simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField, hm]))
  · subst htag
    exact mergePrivKey_92_placed_cps d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hlen hlen_max hFit
      (fun v rest st1 s2 hm => hcont { m with privateKey := v } rest st1 s2
        (by simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField, hm]))
      (fun hm => hnone (by simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_284_placed_cps (fuel := 2 * bs.length + 2) d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 htag_lt hlen hFit
      (fun rest st1 s2 hs hFit1 hpc2 hrun2 hregs2 => by
        obtain ⟨k, _, hrest⟩ := skipField_suffix hs
        have hle : 2 * rest.length + 2 ≤ 2 * bs.length + 2 := by rw [hrest, List.length_drop]; omega
        exact sepWPp_mono_post
          (hcont m rest st1 s2
            (by simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField, skipUnknown, recursionLimit, hs])
            (fitsEnv_recordCodecLoop_mono_fuel hle hFit1) hpc2 hrun2 hregs2)
          (fun _ _ h => ikpExitPostPlaced_mono_fuel hle h))
      (fun hs => hnone (by simp [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField, skipUnknown, recursionLimit, hs]))

theorem loopExit_708_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hlt : x.bytes.length < 2 ^ 32) (hdec : CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes = some m)
    (hpc : s.pc = (blkPl_84).base + 708#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr [] ∗ ikpLoopCommonPlaced A lim st sp' x.ret 0 m s)
      (ikpExitPostPlaced A lim st fuel maxLen s0 sp' x.ret ptr [] (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  obtain ⟨hpk_le, hsk_le⟩ := ikp_decode_field_lengths hdec
  unfold sliceCursorAt ikpLoopCommonPlaced ikpStructLoopOf ikpStructAt
  simp only [CryptoVerification.LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun sk =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun _ => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_cap_lt63 A.repAlloc pk.cap pk.ptr m.publicKey))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hpk_lt63 => ?_
  have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pk.cap hpk_lt63
  have hsp_eq := hregs.base.sp; subst hsp_eq
  let sp' := s.sp; have _hsp_align := hregs.base.spAligned
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (344)) ?_
  wp_steps_sync_pool ((blkPl_84).base + bv% (344))
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  have hm16 := pointsTo64_pair_entails_memRegion16 (sp' + 32#64) ptr 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm16
  have h144 := ikpFold144 sp' pk.cap pk.ptr (BitVec.ofNat 64 m.publicKey.length)
    sk.cap sk.ptr (BitVec.ofNat 64 m.privateKey.length)
  dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
    (sepWPp_frame_noPanic
      (F := memRegion (sp' + 32#64) 16 ∗ ((sp' + 48#64) ↦₆₄ pk.cap) ∗ ((sp' + 56#64) ↦₆₄ pk.ptr) ∗
        ((sp' + 64#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
        ((sp' + 72#64) ↦₆₄ sk.cap) ∗ ((sp' + 80#64) ↦₆₄ sk.ptr) ∗
        ((sp' + 88#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ (ptr ↦ₛ []))
      (post_344_placed_wp d (st := st) (sp' := sp')
        (pkCap := pk.cap) (pkPtr := pk.ptr) (skCap := sk.cap) (skPtr := sk.ptr)
        hdec (by omega) (by omega)
        (hregs.base.of_steps hcrl1 (by simp [*, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x29, arm64_norm]; rfl)
        (by simp [*, hregs.x24, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, by
        unfold ikpExitMemPlaced
        have hev_lift :
            (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ⊢
            ∃∗ evs : List AllocEvent, ⌜IkpSubEnv fuel maxLen evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf := by
          refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
          refine Entails.sepExists_right evs ?_
          rw [pure_true_emp (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpSubEnv.of_cleanup (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpPostCleanupEnv.of_twoOpt hevs)), emp_sepConj]
          exact Entails.refl _
        refine Entails.trans (sepConj_mono_left hentf) ?_
        refine Entails.trans (sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hev_lift)))))) ?_
        refine Entails.trans ?_ (sepConj_mono_left h144)
        apply entails_of_eq
        try simp only [arm64_norm]
        sep_ac_rfl⟩)
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hm16))
  apply entails_of_eq
  try simp only [arm64_norm]
  sep_ac_rfl

theorem loopCheck_108_empty_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hlt : x.bytes.length < 2 ^ 32) (hdec : CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes = some m)
    (hpc : s.pc = (blkPl_84).base + 108#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr [] ∗
        ikpLoopCommonPlaced A lim st sp' x.ret ([] : List (BitVec 8)).length m s)
      (ikpExitPostPlaced A lim st fuel maxLen s0 sp' x.ret ptr [] (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have _h29 := hregs.x29
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (708)) ?_
  wp_steps_sync_pool ((blkPl_84).base + bv% (708))
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
    (loopExit_708_placed_wp d hlt hdec (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (step_ikp_regs hregs hcrl1))
  unfold sliceCursorAt ikpLoopCommonPlaced; apply entails_of_eq
  simp only [List.length_nil]; sep_ac_rfl

theorem loopCheck_108_cons_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_84).base + 108#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_84).base + 124#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 → s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
          ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s1) Q (noPanicQp s0)) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s) Q (noPanicQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned; have _h29 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (124)) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
    (hcont _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (step_ikp_regs hregs hcrl1)
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
  unfold sliceCursorAt ikpLoopCommonPlaced; apply entails_of_eq; simp only [arm64_norm]; try sep_ac_rfl

theorem decodeLoop_124_step_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (ih : ∀ {st' : M.σ} {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure},
      decodeFieldsLoop CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField fuel m bs =
        CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes →
      FitsEnv M lim st' (RecordCodecLoopEnv (2 * bs.length + 2) maxLen) →
      s.pc = (blkPl_84).base + 108#64 → s.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s → bs.length ≤ fuel → bs.length ≤ maxLen → bs.length < 2 ^ 63 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
        (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st' sp' x.ret bs.length m s)
        (ikpExitPostPlaced A lim st' (2 * bs.length + 2) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hinv : decodeFieldsLoop CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * (b0 :: bs1).length + 2) maxLen))
    (hpc : s.pc = (blkPl_84).base + 124#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hmax : (b0 :: bs1).length ≤ maxLen)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s)
      (ikpExitPostPlaced A lim st (2 * (b0 :: bs1).length + 2) maxLen s0 sp' x.ret ptr (b0 :: bs1)
        (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  have hFit_dk : FitsEnv M lim st (RecordCodecLoopEnv ((2 * (b0 :: bs1).length) + 2) maxLen) := hFit
  refine decodeKey_124_placed_cps (fuel := 2 * (b0 :: bs1).length + 1) (maxLen := maxLen)
    d hpc hrun hregs hx23 hx22 hx2 hlen (fitsEnv_recordCodecLoop_mono_fuel (by omega) hFit_dk)
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom, ← hinv, decodeFieldsLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  have hbud1 : 2 * rest1.length + 4 ≤ 2 * (b0 :: bs1).length + 2 := by omega
  refine ikp_advance_cursor_placed hk1_le hrest1_eq ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k1) rest1 ∗
      ikpLoopCommonPlaced A lim st sp' x.ret rest1.length m s1)
    (sepConj_mono_right (by
      unfold ikpLoopCommonPlaced
      exact sepConj_mono_right (sepConj_mono_left
        (ikpStructLoopOf_mono A.repAlloc (sp' + 48#64) m (by omega))))) ?_
  refine sepWPp_mono_post
    (mergeField_248_placed_cps (maxLen := maxLen) (bs := rest1) (m := m)
      d hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt (by omega) (by omega)
      (fitsEnv_recordCodecLoop_mono_fuel hbud1 hFit)
      (fun m' rest2 st1 s2 hmf hFit1 hpc2 hrun2 hregs2 => ?_)
      (fun hmf_none => by simp [CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom, ← hinv, decodeFieldsLoop, hdk, hmf_none]))
    (fun _ _ h => ikpExitPostPlaced_mono_fuel hbud1 h)
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := ikp_mergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  refine ikp_advance_cursor_placed hk2_le hrest2_eq ?_
  have hinv' : decodeFieldsLoop CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField fuel m' rest2 =
      CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes := by
    simpa [decodeFieldsLoop, hdk, hmf] using hinv
  exact ih hinv' hFit1 hpc2 hrun2 hregs2 (by omega) (by omega) (by omega)

theorem decodeLoop_108_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {s0 : State} {sp' : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32) :
    ∀ (fuel : ℕ) {maxLen : ℕ} {st : M.σ} {s : State} {ptr : BitVec 64}
      {bs : List (BitVec 8)} {m : IdentityKeyPairStructure},
      decodeFieldsLoop CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField fuel m bs =
        CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes →
      FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 2) maxLen) →
      s.pc = (blkPl_84).base + 108#64 → s.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s → bs.length ≤ fuel → bs.length ≤ maxLen → bs.length < 2 ^ 63 →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
        (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
        (ikpExitPostPlaced A lim st (2 * bs.length + 2) maxLen s0 sp' x.ret ptr bs (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0)
  | 0, _, _, s, ptr, bs, m, hinv, _, hpc, hrun, hregs, hfuel, _, _ => by
    cases bs with
    | nil => exact loopCheck_108_empty_placed_wp d hlt hinv.symm hpc hrun hregs
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, _, _, s, ptr, bs, m, hinv, hFit, hpc, hrun, hregs, hfuel, hmax, hlen => by
    cases bs with
    | nil => exact loopCheck_108_empty_placed_wp d hlt hinv.symm hpc hrun hregs
    | cons b0 bs1 =>
      refine loopCheck_108_cons_placed_cps (x := x) hpc hrun hregs hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx23_1 hx22_1 hx2_1
      exact decodeLoop_124_step_placed_wp d (decodeLoop_108_placed_wp d hlt fuel)
        hinv hFit hpc1 hrun1 hregs1 hx23_1 hx22_1 hx2_1 hfuel hmax hlen

theorem ikp_entry_to_812_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_84).base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * x.bytes.length + 3) x.bytes.length)) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s0
      (memRegion (s0.sp - 224#64) 144 ∗ memRegion (s0.sp - 224#64 + 144#64) 80 ∗
        memRegion x.ret 72 ∗ (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 (s0.sp - 224#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 224#64) 144 ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          identityKeyPairResultAt A.repAlloc x.ret (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗
          (∃∗ evs : List AllocEvent, ⌜IdentityKeyPairTryFromEnv x.bytes.length evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt (s0.sp - 224#64) (skipFieldStackX 100)))
      (noPanicQp s0) := by
  have hloop := decodeLoop_108_placed_wp (A := A) (lim := lim) (H := H) (x := x) (s0 := s0)
    (sp' := s0.sp - 224#64) d hlt
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono (ikpMem144_prologue_cells (s0.sp - 224#64))
      (sepConj_mono_left (ikpMem80_cells (s0.sp - 224#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w88 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w80 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w72 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w64 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w56 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w48 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w40 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w32 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c19 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c20 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c21 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c22 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c23 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c24 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun cbuf => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c25 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c30 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c29 => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp224_b : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub224 hsp
  have _hsp224 : (s0.sp - 224#64) &&& 15#64 = 0#64 := eq_of_beq _hsp224_b
  rcases hbs : x.bytes with _ | ⟨b0, bs1⟩
  · have hx1_0 : s0.readReg64 .x1 = 0#64 := by simp [hx1, hbs]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_84).base + bv% (344)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (344))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    have hdec0 : CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes = some CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty := by
      simp [hbs, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode, decodeFieldsLoop]
    have hbase1 : IkpBaseStatePlaced s0 (s0.sp - 224#64) _ := {
      sp := by simp [*, arm64_norm]
      spAligned := by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub224 hsp
      crl := hcrl1
      trace := by simp [*, arm64_norm]
      x26 := by simp [*, arm64_norm]
      x27 := by simp [*, arm64_norm]
      x28 := by simp [*, arm64_norm]
    }
    have hm16 := pointsTo64_pair_entails_memRegion16 (s0.sp - 224#64 + 32#64) x.bytesA 0#64
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm16
    have h144 := ikpFold144 (s0.sp - 224#64) 0#64 1#64 0#64 0#64 1#64 0#64
    dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := (memRegion (s0.sp - 224#64) 32 ∗ memRegion (s0.sp - 224#64 + 96#64) 48 ∗
        memRegion x.ret 72 ∗
        vecU8Buf A.repAlloc 0#64 1#64 CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty.publicKey ∗
        vecU8Buf A.repAlloc 0#64 1#64 CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty.privateKey ∗
        lsLogOff ∗ A.pool lim st _ ∗ stackAt (s0.sp - 224#64) (skipFieldStackX 100)) ∗
        (memRegion (s0.sp - 224#64 + 32#64) 16 ∗
          ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 80#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗ (x.bytesA ↦ₛ ([] : List (BitVec 8)))))
      (by dsimp only [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty]
          simp only [vecU8Buf_zero]
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hm16))
          unfold ikpCalleeSavedAt
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          apply entails_of_eq
          sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (post_344_placed_wp d (st := st) (sp' := s0.sp - 224#64)
        (pkCap := 0#64) (pkPtr := 1#64) (skCap := 0#64) (skPtr := 1#64)
        hdec0 (by decide) (by decide) hbase1
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, speWord, arm64_norm]) (by simp [*, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    rw [hbs] at hentf
    refine Entails.trans (sepConj_mono_left hentf) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    simp only [sepConj_pure_left_comm]
    refine Entails.pure_left fun hevs => ?_
    rw [pure_true_emp (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IdentityKeyPairTryFromEnv.of_cleanup (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpPostCleanupEnv.of_twoOpt hevs)), emp_sepConj]
    refine Entails.trans ?_ (sepConj_mono_left h144)
    apply entails_of_eq
    try simp only [arm64_norm]
    sep_ac_rfl
  · have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by rw [← hbs]; omega
    obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen63
    have hx1_cons : s0.readReg64 .x1 = BitVec.ofNat 64 (b0 :: bs1).length := by simpa [hbs] using hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_84).base + bv% (124)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (124))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    have hregs1 : IkpLoopRegsPlaced s0 (s0.sp - 224#64) x.ret _ := {
      base := {
        sp := by simp [*, arm64_norm]
        spAligned := by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub224 hsp
        crl := hcrl1
        trace := by simp [*, arm64_norm]
        x26 := by simp [*, arm64_norm]
        x27 := by simp [*, arm64_norm]
        x28 := by simp [*, arm64_norm]
      }
      x29 := by simp [*, arm64_norm]
      x19 := by simp [*, arm64_norm]
      x21 := by simp [*, arm64_norm]
      x24 := by simp [*, speWord, arm64_norm]
    }
    have hemptyLoop :
        ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 80#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ⊢
          ikpStructLoopOf A.repAlloc (s0.sp - 224#64 + 48#64) (b0 :: bs1).length
            CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty :=
      Entails.trans (ikpEmptyCells_entails_structAt A.repAlloc (s0.sp - 224#64))
        (ikpStructAt_entails_loopOf A.repAlloc ⟨0#64, 1#64⟩ ⟨0#64, 1#64⟩
          (s0.sp - 224#64 + 48#64) (b0 :: bs1).length CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty
          bytesMergeCapOk_zero bytesMergeCapOk_zero)
    have hinv0 : decodeFieldsLoop CryptoVerification.RecordCodecs.IdentityKeyPairStructure.mergeField
        (bs1.length + 1) CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty (b0 :: bs1) =
        CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode x.bytes := by
      simp [hbs, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.decode]
    have hFit_loop : FitsEnv M lim st (RecordCodecLoopEnv (2 * (b0 :: bs1).length + 2) x.bytes.length) :=
      fitsEnv_recordCodecLoop_mono_fuel (by simp [hbs]) hFit
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := (sliceCursorAt (s0.sp - 224#64 + 32#64) x.bytesA (b0 :: bs1) ∗
        ikpLoopCommonPlaced A lim st (s0.sp - 224#64) x.ret (b0 :: bs1).length
          CryptoVerification.RecordCodecs.IdentityKeyPairStructure.empty _) ∗
        ikpCalleeSavedAt (s0.sp - 224#64) s0)
      (by unfold sliceCursorAt ikpLoopCommonPlaced ikpCalleeSavedAt
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
          refine Entails.trans ?_
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hemptyLoop))))
          apply entails_of_eq
          try simp only [arm64_norm]
          sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (decodeLoop_124_step_placed_wp d (decodeLoop_108_placed_wp (sp' := s0.sp - 224#64) d hlt bs1.length)
        hinv0 hFit_loop (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hregs1 (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (Nat.le_refl _) (by simp [hbs]) hlen63)
      fun sf Pf h => ?_
    have ⟨hstf, hentf⟩ := ikpExitPostPlaced_mono_fuel
      (by simp [hbs] : 2 * (b0 :: bs1).length + 2 ≤ 2 * x.bytes.length + 3) h
    refine ⟨hstf, ?_⟩
    rw [hbs] at hentf
    unfold ikpExitMemPlaced at hentf
    refine Entails.trans (sepConj_mono_left hentf) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    dsimp only [IdentityKeyPairTryFromEnv]
    apply entails_of_eq
    try simp only [arm64_norm]
    sep_ac_rfl

theorem ikp_placed_subroutine_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A lim) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [identityKeyPairTryFromRawSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hlt, hx8, hFit⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0) ∗ R := by
    ac_nf at hmem ⊢
  have h1 : SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sm Pm =>
        IkpBaseStatePlaced s0 (s0.sp - 224#64) sm ∧
        (Pm ⊢ memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack)
            (ikpSubStack - skipFieldStackX 100) ∗
          stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
          memRegion (s0.sp - 224#64) 144 ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          identityKeyPairResultAt A.repAlloc x.ret (CryptoVerification.RecordCodecs.IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗
          (∃∗ evs : List AllocEvent, ⌜IdentityKeyPairTryFromEnv x.bytes.length evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sm)))
      (noPanicQp s0) := by
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := (memRegion (s0.sp - 224#64) 144 ∗ memRegion (s0.sp - 224#64 + 144#64) 80 ∗
        memRegion x.ret 72 ∗ (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100)) ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100))
      (by rw [ikpRootStack_split s0.sp]; apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (ikp_entry_to_812_placed_wp d hlt hpc hrun hsp hcrl hx0 hx1 hx8 hFit)
      fun sm Pm ⟨hstm, hentm⟩ => ⟨hstm, ?_⟩
    refine Entails.trans (sepConj_mono_left hentm) ?_; apply entails_of_eq; sep_ac_rfl
  have hfull : SepWPp (lsProg_84 H) (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (identityKeyPairTryFromPlacedSpec A lim).post (x, st) s0 sf))
      (noPanicQp s0) := by
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind h1 fun sm Pm hpcm hrunm ⟨hstm, hentm⟩ =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hentm
        (epilogue_812_placed_wp (A := A) (lim := lim) (st := st) (x := x)
          (wbuf := s0.sp - 224#64 + 32#64) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    hfull R hmem' hL
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` meets `identityKeyPairTryFromPlacedSpec`
under any `[LibsignalPlacement]`, given `PortDepsPlaced M A lim H` (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝` under `FitsEnv`). -/
theorem identityKeyPair_tryFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A lim) :=
  ikp_placed_subroutine_ok d

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFromBudget
