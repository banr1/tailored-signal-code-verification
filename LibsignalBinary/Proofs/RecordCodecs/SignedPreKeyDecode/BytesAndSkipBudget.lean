/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkip
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SignedPreKeyRecordStructure::decode` `bytes::merge` and `skip_field`

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` proofs of `bytes::merge` (tags 2,
3, 4), error-push stubs, and `skip_field` on Block `562`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkipBudget

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
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
  (SpkBytesField SpkGhost SpkGhostCapOk SpkLoopRegs spkBytesEntryOff spkConvergeMem_none_intro
   spkErr16_pack40 spkMemRegion48_unpack16 spkOff_converge spkOff_latch spkOff_pushCall
   spkOff_skip spkOff_skipRet spkOff_tag2Ret spkOff_tag3Ret spkOff_tag4Ret
   spkStructAt_entails_of spkStructOf)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (BytesMerge3Env BytesMerge3EnvCore SignedHooksPlaced SignedPortDepsPlaced SkipField3Env
   SpkCaps SpkErrTailEnv SpkLoopBoundedEnv bmNextCap bmNextCap_lt_two_pow_63
   bytesMerge3RawBudgetSpec fitsEnv_spkLoop_bytesMerge fitsEnv_spkLoop_bytesTail
   fitsEnv_spkLoop_errTail mergeBytes_progress skipField3BudgetSpec skipField3EventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
  (SpkGhostCapsMatch noPanicQp sepWPp_call_budget_lscro sepWPp_end_noPanic_lscro
   sepWPp_frame_noPanic spkAdvanceCursor_placed spkAfterVarintCapsMem spkAfterVarintCapsMemAt
   spkBytesFieldToField spkBytesField_cap_pin_eq spkBytesField_capsMatch_update
   spkConvergePostPlaced spkConvergePostPlaced_append_prefix spkConvergePostPlaced_bytesStep
   spkConvergePostPlaced_skipStep spkLoopCapsMem spkLoopCapsMemAt
   spkStructAt_entails_loopCapsOf spkStructLoopCapsOf spkStructLoopCapsOf_entails_of
   spkStructLoopCapsOf_mono spk_bytesMerge7_placed_ok spk_skipField7_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget (pushCall_648_placed_wp sepWPp_mono_post)
attribute [local arm64_norm] BitVec.toNat_zero

attribute [local irreducible] Program.fetch Program.externAt?

theorem spkAdvanceCursor_placed_prog [CryptoVerification.LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} {caps : SpkCaps} {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} {Q0 P R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hperm : Q0 ⊢ sliceCursorAfter sp' ptr bs rest ∗ R)
    (hent : sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R ⊢ P)
    (h : Wire.SepWPp prog ret s P (spkConvergePostPlaced A lim st rem caps s0 sp' x19
      (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out) (noPanicQp s0)) :
    Wire.SepWPp prog ret s Q0 (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  refine Wire.SepWPp.mono_pre hperm ?_
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]; rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at hent h ⊢
  refine Wire.SepWPp.mono_pre (P' := P ∗ (ptr ↦ₛ bs.take k))
    (Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left hent)) ?_
  exact sepWPp_frame_noPanic h
    (fun sf Pf hqm => spkConvergePostPlaced_append_prefix A lim st rem caps s0 sp' x19 ptr bs k hkl out sf Pf hqm)

theorem spkAdvanceToLatch_placed_prog [CryptoVerification.LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} {caps : SpkCaps} {s0 s : State} {sp' x19 ptr : BitVec 64} {bs rest : List (BitVec 8)}
    {m' : SignedPreKeyRecordStructure} {out : Option SignedPreKeyRecordStructure} {Q0 : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp prog ret s
      (spkLoopCapsMem (A.atState lim st s) sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length)) caps rest m')
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (noPanicQp s0))
    (hperm : Q0 ⊢ sliceCursorAfter sp' ptr bs rest ∗ (((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗ spkStructLoopCapsOf A.repAlloc sp' rest.length caps m' ∗ memRegion x19 88 ∗
      A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))) :
    Wire.SepWPp prog ret s Q0 (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) :=
  spkAdvanceCursor_placed_prog hsuf hperm (Entails.refl _) h

theorem spkLoopRegs_of_calleeSaved {s0 s s2 : State} {sp' x19 : BitVec 64}
    (hsp2 : s2.sp = s.sp) (hcs2 : CalleeSavedPreserved s s2)
    (hregs : SpkLoopRegs s0 sp' x19 s) : SpkLoopRegs s0 sp' x19 s2 :=
  ⟨hsp2.trans hregs.sp, hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hregs.x29,
   hcs2.2.2.2.2.2.1.trans hregs.x24, hcs2.1.trans hregs.x19_eq,
   ⟨hcs2.2.2.2.2.2.2.1.trans hregs.saved.x25, hcs2.2.2.2.2.2.2.2.1.trans hregs.saved.x26,
    hcs2.2.2.2.2.2.2.2.2.1.trans hregs.saved.x27, hcs2.2.2.2.2.2.2.2.2.2.1.trans hregs.saved.x28⟩⟩

private theorem bytesField_ok_pack (f : SpkBytesField) (A : RustAlloc) (g : SpkGhost)
    (sp' x19 : BitVec 64) (caps : SpkCaps) (rest rest2 v : List (BitVec 8)) (ptr1 : BitVec 64)
    (m : SignedPreKeyRecordStructure) (cap' ptr' : BitVec 64)
    (hg : SpkGhostCapOk g rest.length) (hc : SpkGhostCapsMatch g caps)
    (hle2 : rest2.length ≤ rest.length) (hcap' : BytesMergeCapOk cap' rest2.length)
    (hcap_eq : cap'.toNat = bmNextCap (caps.get (spkBytesFieldToField f)) v.length)
    (hnext_lt : bmNextCap (caps.get (spkBytesFieldToField f)) v.length < 2 ^ 63) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗ stackAt sp' CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack ∗
      vecU8At A (sp' + f.slotOff) cap' ptr' v ∗ sliceCursorAfter sp' ptr1 rest rest2 ∗
      memRegion (sp' + 112#64) 48 ∗ f.rest A g sp' m ∗ memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
        (CryptoVerification.SpqrV1.Varint.skipField3Stack 100 - CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack) ⊢
    sliceCursorAfter sp' ptr1 rest rest2 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗
      spkStructLoopCapsOf A sp' rest2.length
        (caps.set (spkBytesFieldToField f) (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))
        (f.setBytes m v) ∗
      memRegion x19 88 ∗ A.pool ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) := by
  have hstack := stackAt_sub_split sp' CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack
    (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  have hpack : vecU8At A (sp' + f.slotOff) cap' ptr' v ∗ f.rest A g sp' m ⊢
      spkStructLoopCapsOf A sp' rest2.length
        (caps.set (spkBytesFieldToField f) (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))
        (f.setBytes m v) := by
    rw [f.unsplit_field A g sp' m ⟨cap', ptr'⟩ v]
    exact spkStructAt_entails_loopCapsOf A _ sp' rest2.length _ _
      (f.capOk_update hg hle2 hcap' (p := ⟨cap', ptr'⟩))
      (spkBytesField_capsMatch_update hc hcap_eq hnext_lt f)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack))))
  apply entails_of_eq; rw [hstack]; ac_rfl

private theorem bytesField_err_pack (f : SpkBytesField) (A : RustAlloc) (g : SpkGhost)
    (sp' x19 ptr1 err : BitVec 64) (rest : List (BitVec 8)) (m : SignedPreKeyRecordStructure) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗ stackAt sp' CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack ∗
      decodeErrorAtStackLen A err 0 ∗ vecU8At A (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
      memRegion sp' 16 ∗ (ptr1 ↦ₛ rest) ∗
      memRegion (sp' + 112#64) 48 ∗ f.rest A g sp' m ∗ memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
        (CryptoVerification.SpqrV1.Varint.skipField3Stack 100 - CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack) ⊢
    memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗
      spkStructOf A sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion x19 88 ∗ (ptr1 ↦ₛ rest) ∗ A.pool ∗
      stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) := by
  have hstack := stackAt_sub_split sp' CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack
    (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  have hof : vecU8At A (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
      f.rest A g sp' m ⊢ spkStructOf A sp' m := by
    rw [← f.split_field A g sp' m]; exact spkStructAt_entails_of A g sp' m
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))
  apply entails_of_eq; rw [hstack]; ac_rfl

private def spkBytesRetOff : SpkBytesField → BitVec 64
  | .pub => spkOff_tag2Ret | .priv => spkOff_tag3Ret | .sig => spkOff_tag4Ret

private theorem bytesField_ret_ok_step [CryptoVerification.LibsignalPlacement] {H : LibsignalHooks}
    (f : SpkBytesField) {s0 s2 : State} {sp' x19 : BitVec 64}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc2 : s2.pc = (blkPl_562).base + spkBytesRetOff f) (hrun2 : s2.status = .Running)
    (hregs2 : SpkLoopRegs s0 sp' x19 s2) (hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64)
    (hsp2_align : s2.spAligned = true) (hcrl2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (htr2 : s2.trace = s0.trace)
    (hcont : ∀ s3, s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 → s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace → VmPreserved s2 s3 →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3 P Q Qp) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s2 P Q Qp := by
  cases f <;> (
    dsimp only [spkBytesRetOff] at hpc2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_latch) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 =>
      hcont _ (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simp [htr2, arm64_norm])
        ⟨⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩,
         by simp [arm64_norm], fun _ => by simp [arm64_norm],
         fun _ _ _ => by simp [arm64_norm]⟩)

private theorem bytesField_ret_err_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (f : SpkBytesField)
    {s0 s2 : State} {sp' x19 ptr1 err : BitVec 64} {mErr : SignedPreKeyRecordStructure}
    {rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc2 : s2.pc = (blkPl_562).base + spkBytesRetOff f) (hrun2 : s2.status = .Running)
    (hregs2 : SpkLoopRegs s0 sp' x19 s2) (hx0 : s2.readReg64 (Reg.gpr 0#5) = err) (hnz : err ≠ 0#64)
    (hsp2_align : s2.spAligned = true) (hcrl2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (htr2 : s2.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s2
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr1 ↦ₛ rest) ∗
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s2 ∗
        stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr1 rest out) (noPanicQp s0) := by
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  have h29 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr (hx0 ▸ hnz)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  cases f <;> (
    dsimp only [spkBytesRetOff] at hpc2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushCall) ?_
    wp_steps_sync_pool ((blkPl_562).base + spkOff_pushCall)
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine Wire.SepWPp.mono_pre ?_
      (pushCall_648_placed_wp (st := st) (rem := rem) (caps := caps) hH
        (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr1) (err := err) (mErr := mErr) (bs := rest)
        (out := out) herr (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simp [hsp2_eq, arm64_norm], by simp [h29, arm64_norm],
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [h29, arm64_norm]) hnz
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simp [htr2, arm64_norm]) hFit)
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
    apply entails_of_eq; simp only [hsp2_eq, h29, hx0, arm64_norm]; try ac_rfl)

private theorem bytesField_entry_step [CryptoVerification.LibsignalPlacement]
    {H : LibsignalHooks} (f : SpkBytesField) {s0 s : State}
    {sp' x19 : BitVec 64} {wt : WireType} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_562).base + spkBytesEntryOff f) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hcont : ∀ s1, s1.pc = lsmpl.base 558 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat →
      s1.readReg64 .x1 = sp' + f.slotOff →
      s1.readReg64 .x2 = sp' + 104#64 →
      s1.readReg64 .x30 = (blkPl_562).base + spkBytesRetOff f →
      VmPreserved s s1 →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s P Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h24 : s.readReg64 (Reg.gpr 24#5) = sp' + 16#64 := hregs.x24
  have hwt8 : (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
    cases wt <;> decide
  cases f <;> (
    dsimp only [spkBytesEntryOff, SpkBytesField.slotOff, spkBytesRetOff] at hpc hcont
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 558) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      hcont _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
         by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr)
        (by simp [hx0, hwt8, arm64_norm]) (by simp [hsp_eq, h24, arm64_norm])
        (by simp [h29, arm64_norm]) (by simp [arm64_norm])
        ⟨⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩,
         by simp [arm64_norm], fun _ => by simp [arm64_norm],
         fun _ _ _ => by simp [arm64_norm]⟩)

theorem bytesField_merge_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H)
    (f : SpkBytesField) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63)
    (hrem : rest.length ≤ rem)
    (hpc : s.pc = (blkPl_562).base + spkBytesEntryOff f) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps))
    (hlatch : ∀ (v rest2 : List (BitVec 8)) (evs₁ : List AllocEvent) (s3 : State),
      mergeBytes wt rest = some (v, rest2) →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get (spkBytesFieldToField f))) rest →
      FitsEnv M lim (M.stepEvents evs₁ st)
        (SpkLoopBoundedEnv rest2.length
          (caps.set (spkBytesFieldToField f) (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 → s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopCapsMem (A.atState lim (M.stepEvents evs₁ st) s3) sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
            BitVec.ofNat 64 (rest.length - rest2.length))
          (caps.set (spkBytesFieldToField f) (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))
          rest2 (f.setBytes m v))
        (spkConvergePostPlaced A lim (M.stepEvents evs₁ st) rest2.length
          (caps.set (spkBytesFieldToField f) (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))
          s0 sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
            BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (noPanicQp s0))
    (hnone : mergeBytes wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintCapsMem (A.atState lim st s) sp' x19 ptr caps bs rest bs.length m)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintCapsMem spkAfterVarintCapsMemAt; refine spkAdvanceCursor_placed hsuf ?_
  let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkStructLoopCapsOf_mono A.repAlloc sp' m hle_bs))))) ?_
  unfold spkStructLoopCapsOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun ⟨hg, hc⟩ => ?_
  obtain ⟨hcap_bv, hcap_nat, hcap_lt⟩ := spkBytesField_cap_pin_eq hc f
  rw [f.split_field A.repAlloc g sp' m]; simp only [sepConj_assoc]
  have hstack := stackAt_sub_split sp' CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack
    (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  refine bytesField_entry_step f hpc hrun hregs hx0 hsp hcrl htr
    fun s1 hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx0_1 hx1_1 hx2_1 hx30_1 hvm1 => ?_
  have hsp1_eq : s1.sp = sp' := hregs1.sp
  let xbm : BytesMergeGhost :=
    ⟨wt, sp' + f.slotOff, (f.pin g).cap, (f.pin g).ptr, f.getBytes m, sp' + 104#64, sp', ptr1, rest⟩
  refine sepWPp_call_budget_lscro (xbm, st)
    (spk_bytesMerge7_placed_ok d) hpc1 hrun1 hsp1 hcrl1
    (ret_pc := (blkPl_562).base + spkBytesRetOff f) hx30_1 htr1
    (T := vecU8At A.repAlloc (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗ A.pool lim st s1 ∗
      stackAt sp' CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack)
    (φ := rest.length < 2 ^ 63 ∧ BytesMergeCapOk (f.pin g).cap rest.length ∧
      FitsEnv M lim st (BytesMerge3Env xbm))
    (by simp [bytesMerge3RawBudgetSpec, xbm, hsp1_eq, hx0_1, hx1_1, hx2_1])
    ⟨hlen_rest, f.capOk_pin hg,
     fitsEnv_spkLoop_bytesMerge (spkBytesFieldToField f) hcap_bv hcap_lt hrem hFit⟩
    (by
      dsimp only [RustCliAllocBudget.atState]
      rw [← A.pool_transport lim st s s1 hvm1, hstack]; sep_focus)
    fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 := spkLoopRegs_of_calleeSaved hsp2 hcs2 hregs1
  have hsp2_eq : s2.sp = sp' := hregs2.sp; dsimp only [bytesMerge3RawBudgetSpec, xbm]
  cases hm : mergeBytes wt rest with
  | some p =>
    rcases p with ⟨v, rest2⟩; obtain ⟨k2, hkl2, hr2, _⟩ := mergeBytes_suffix hm
    have hle2 : rest2.length ≤ rest.length := by rw [hr2]; simp
    have hprog_r : rest2.length + v.length + 1 ≤ rem := Nat.le_trans (mergeBytes_progress hm) hrem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' =>
      Wire.SepWPp.exists_pre fun evs₁ => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hevs₁ => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hcap', hcap_eq_raw⟩ => ?_
    have hcap_eq : cap'.toNat = bmNextCap (caps.get (spkBytesFieldToField f)) v.length := by
      simpa [hcap_nat] using hcap_eq_raw
    have hevs1_core : evs₁ =
        bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get (spkBytesFieldToField f))) rest := by
      dsimp only [BytesMerge3Env, BytesMerge3EnvCore] at hevs₁
      rwa [hcap_bv] at hevs₁
    have hnext_lt : bmNextCap (caps.get (spkBytesFieldToField f)) v.length < 2 ^ 63 := by
      have hb := bmNextCap_lt_two_pow_63 (f.capOk_pin hg) (by rw [hcap_nat]; exact hcap_lt) hlen_rest hm
      rwa [hcap_nat] at hb
    refine sepWPp_mono_post
      (spkConvergePostPlaced_bytesStep A lim st (spkBytesFieldToField f)
        hm hrem hprog_r hcap_lt hevs1_core s0 sp' x19 ptr1 rest out) ?_
    exact bytesField_ret_ok_step f hpc2 hrun2 hregs2 hx0_2
      hsp2_align hcrl2 (htr2.trans htr1) fun s3 hpc3 hrun3 hregs3 hsp3 hcrl3 htr3 hvm3 =>
      spkAdvanceToLatch_placed_prog ⟨k2, hkl2, hr2⟩
        (hlatch v rest2 evs₁ s3 hm hevs1_core
          (fitsEnv_spkLoop_bytesTail (spkBytesFieldToField f) hm hrem hprog_r hcap_lt hevs1_core hFit)
          hpc3 hrun3 hregs3 hsp3 hcrl3 htr3)
        (by
          have hp := bytesField_ok_pack f (A.atState lim (M.stepEvents evs₁ st) s3) g
            sp' x19 caps rest rest2 v ptr1 m cap' ptr' hg hc hle2 hcap' hcap_eq hnext_lt
          dsimp only [RustCliAllocBudget.atState] at hp ⊢
          have eq1 : vecU8At { pool := A.pool lim (M.stepEvents evs₁ st) s3, live := A.live }
              (sp' + f.slotOff) cap' ptr' v = vecU8At A.repAlloc (sp' + f.slotOff) cap' ptr' v := rfl
          have eq2 : f.rest { pool := A.pool lim (M.stepEvents evs₁ st) s3, live := A.live } g sp' m =
              f.rest A.repAlloc g sp' m := by cases f <;> rfl
          have eq3 : spkStructLoopCapsOf
              { pool := A.pool lim (M.stepEvents evs₁ st) s3, live := A.live }
              sp' rest2.length
              (caps.set (spkBytesFieldToField f)
                (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))
              (f.setBytes m v) =
              spkStructLoopCapsOf A.repAlloc sp' rest2.length
                (caps.set (spkBytesFieldToField f)
                  (bmNextCap (caps.get (spkBytesFieldToField f)) v.length))
                (f.setBytes m v) := rfl
          rw [eq1, eq2, eq3] at hp
          rw [← A.pool_transport lim (M.stepEvents evs₁ st) s2 s3 hvm3]
          simpa only [ptr1, hsp1_eq, hsp2_eq, sepConj_assoc] using hp)
  | none =>
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun evs₁ => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hevs₁ => ?_
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
    have hevs1_err : evs₁ = rustAllocEvents 72 8 := by
      dsimp only [BytesMerge3Env, BytesMerge3EnvCore] at hevs₁
      rw [hevs₁]; simp [bytesMergeEventsCore, hm]
    subst hevs1_err
    refine Wire.SepWPp.mono_pre ?_
      (bytesField_ret_err_placed_wp (st := st) (rem := rem) (caps := caps)
        hH f (mErr := m) (hnone hm) hpc2 hrun2 hregs2 rfl hx0_nz
        hsp2_align hcrl2 (htr2.trans htr1) hFit)
    have hp := bytesField_err_pack f
      (A.atState lim (M.stepEvents (rustAllocEvents 72 8) st) s2) g
      sp' x19 ptr1 (s2.readReg64 (Reg.gpr 0#5)) rest m
    dsimp only [RustCliAllocBudget.atState] at hp ⊢
    have eq1 : decodeErrorAtStackLen
        { pool := A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s2, live := A.live }
        (s2.readReg64 (Reg.gpr 0#5)) 0 =
        decodeErrorAtStackLen A.repAlloc (s2.readReg64 (Reg.gpr 0#5)) 0 := rfl
    have eq2 : vecU8At
        { pool := A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s2, live := A.live }
        (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) =
        vecU8At A.repAlloc (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) := rfl
    have eq3 : f.rest
        { pool := A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s2, live := A.live } g sp' m =
        f.rest A.repAlloc g sp' m := by cases f <;> rfl
    have eq4 : spkStructOf
        { pool := A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s2, live := A.live } sp' m =
        spkStructOf A.repAlloc sp' m := rfl
    rw [eq1, eq2, eq3, eq4] at hp
    simpa only [hsp1_eq, hsp2_eq, sepConj_assoc] using hp

theorem skip_300_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (d : SignedPortDepsPlaced M A lim H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {tag : ℕ} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63) (htag : tag < 2 ^ 32)
    (hrem : rest.length < rem)
    (hpc : s.pc = (blkPl_562).base + spkOff_skip) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps))
    (hlatch : ∀ (rest2 : List (BitVec 8)) (s3 : State), skipUnknown m tag wt rest = some (m, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 → s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace → Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopCapsMem (A.atState lim st s3) sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
          BitVec.ofNat 64 (rest.length - rest2.length)) caps rest2 m)
        (spkConvergePostPlaced A lim st rest2.length caps s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
          BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (noPanicQp s0))
    (hnone : skipUnknown m tag wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintCapsMem (A.atState lim st s) sp' x19 ptr caps bs rest bs.length m)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintCapsMem spkAfterVarintCapsMemAt; refine spkAdvanceCursor_placed hsuf ?_
  let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  let xsk : SkipFieldGhost := ⟨wt, tag, 100, sp' + 104#64, sp', ptr1, rest⟩
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0w : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  have hwt8 : (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by cases wt <;> decide
  have htag32 : (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : tag < 2 ^ 64)]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 546) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine sepWPp_call_budget_lscro (xsk, st) (spk_skipField7_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_skipRet) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
      A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
    (φ := tag < 2 ^ 32 ∧ (100 : ℕ) < 2 ^ 32 ∧ rest.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipField3Env xsk))
    (by simp [skipField3BudgetSpec, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_setPC, xsk, hsp_eq, h29, h0w, h1, hwt8, htag32, arm64_norm])
    ⟨htag, by decide, hlen_rest, fitsEnv_spkLoop_errTail (fun _ => SpkErrTailEnv.of_skipField3) hFit⟩
    (by dsimp only [RustCliAllocBudget.atState, ptr1]; sep_focus)
    fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 := spkLoopRegs_of_calleeSaved hsp2 hcs2
    ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
     by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
     ⟨by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
      by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
  have hsp2_eq : s2.sp = sp' := hregs2.sp; dsimp only [skipField3BudgetSpec, xsk]
  cases hs : skipField (2 * rest.length + 2) 100 tag wt rest with
  | some rest2 =>
    have hsu : skipUnknown m tag wt rest = some (m, rest2) := by unfold skipUnknown recursionLimit; rw [hs]; rfl
    obtain ⟨k2, hkl2, hr2⟩ := skipField_suffix hs
    have hle_r2 : rest2.length ≤ rest.length := by rw [hr2, List.length_drop]; omega
    have hlt_rem : rest2.length < rem := Nat.lt_of_le_of_lt hle_r2 hrem
    have hle2 : rest2.length ≤ bs.length := Nat.le_trans hle_r2 hle_bs
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun evs => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
    have hevs0 : evs = [] := by rw [hevs]; simp [skipField3EventsCore, hs]
    subst hevs0
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    have hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine sepWPp_mono_post
      (spkConvergePostPlaced_skipStep A lim st hlt_rem s0 sp' x19 ptr1 rest out) ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_latch) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine spkAdvanceToLatch_placed_prog ⟨k2, hkl2, hr2⟩
      (hlatch rest2 _ hsu (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simp [htr2, htr, arm64_norm])) ?_
    have eq_loop : spkStructLoopCapsOf { pool := A.pool lim st s, live := A.live } sp' bs.length caps m =
        spkStructLoopCapsOf A.repAlloc sp' bs.length caps m := rfl
    rw [eq_loop]
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkStructLoopCapsOf_mono A.repAlloc sp' m hle2)))))
    apply entails_of_eq; dsimp only [ptr1]
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC,
      hsp_eq, hsp2_eq, arm64_norm]
    ac_rfl
  | none =>
    have hsu : skipUnknown m tag wt rest = none := by unfold skipUnknown recursionLimit; rw [hs]; rfl
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun evs => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
    have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_nz
    refine sepWPp_end_noPanic_lscro hcrl2 ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcrl3, by simp [htr2, htr, arm64_norm],
      by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
      ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
       by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩,
      evs, .done (SpkErrTailEnv.of_skipField3 (x := xsk) hevs), ?_⟩
    have hpack := spkConvergeMem_none_intro (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
      (A.atState lim (M.stepEvents evs st) s2) sp' x19 ptr1 (s2.readReg64 (Reg.gpr 0#5)) 0 m rest
      (hnone hsu) hx0_nz
    dsimp only [RustCliAllocBudget.atState] at hpack ⊢
    have eq1 : spkStructOf { pool := A.pool lim (M.stepEvents evs st) s2, live := A.live } sp' m =
        spkStructOf A.repAlloc sp' m := rfl
    have eq2 : decodeErrorAtStackLen { pool := A.pool lim (M.stepEvents evs st) s2, live := A.live }
        (s2.readReg64 (Reg.gpr 0#5)) 0 =
        decodeErrorAtStackLen A.repAlloc (s2.readReg64 (Reg.gpr 0#5)) 0 := rfl
    have eq3 : spkStructLoopCapsOf { pool := A.pool lim st s, live := A.live } sp' bs.length caps m =
        spkStructLoopCapsOf A.repAlloc sp' bs.length caps m := rfl
    rw [eq1, eq2] at hpack
    rw [eq3]
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
    refine Entails.trans ?_ hpack
    refine Entails.trans ?_ (sepConj_mono_left (spkStructLoopCapsOf_entails_of A.repAlloc sp' bs.length caps m))
    apply entails_of_eq; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkipBudget
