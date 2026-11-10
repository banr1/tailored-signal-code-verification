/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Post-Loop Deserialization & Field Checks for `<SignalMessage>::try_from`

Proves relocatable `[LibsignalPlacement]` budget-threaded post-loop segments on Block `85` covering
`ratchet_key = None`, `PublicKey::deserialize` error and success paths, and `counter` / `ciphertext`
presence checks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession
  (ProtoSignalMessage PublicKey SignalMessage SignalProtocolError)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl lsRustDeallocSym)
open CryptoVerification.RustHeap (vecHeader)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_85 blkPl_85 blkLib_eq_85 extHookStack LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr
  (speAt signalMessageResultAt errTag speWord noneCap)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (dropSpeName DropSpeGhost dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (skipFieldStackX optVecU8At optU32At wireSignalMessageAt wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWPp → WSepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg PostEpilogueStatePlaced LoopExitStatePlaced
   deallocSlot vecU8Buf vecU8Buf_zero vecU8Buf_dealloc
   optVecU8At_entails_header_dealloc optU32At_entails_cells
   memRegion16_split8_8 memRegion120_split16
   pointsTo64_pair_entails_memRegion16 pointsTo32_pair_entails_memRegion8
   wireHeaders_entails_memRegion112
   spe_invalidProto_intro spe_noKeyType_intro spe_badKeyType_intro spe_badKeyLength_intro
   memRegion33_of_err_base memRegion33_of_err_badKeyType memRegion33_of_err_badKeyLength
   deserializeResult33At pkLayoutAt pkRestAt
   sevenBytesHeadAt sevenBytesTailAt sevenBytesHeadAt_eq_tailAt
   deser_ok_entails_spe_region pointsTo32_pair_eq_pointsTo64
   slt_noneCap_one cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
   stackAt_sub_split entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DropSpeOkWPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
  (blk85_noSvc0 rustLayoutOk_align1 postNoPanicQp freeOnly_rustDeallocEvents
   wpp_sync_pre wpp_frame_noPanic wpp_of_sepWP_end_noPanic_placed wpp_call_noPanic_placed
   cleanup_640_wp_placed cleanup_64c_wp_placed cleanup_668_wp_placed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one
attribute [local simp, local wp_norm]
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one

local macro "wp_steps_sync_deser85 " mid:term : tactic => `(tactic| (
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_85).rebase (blkPl_85).base (hooksException _))
    blkLib_eq_85 blk85_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done
    (by first | wp_norm_lhs | simp [arm64_norm])
    (by wp_norm_lhs) fun _m_real _hnsp => ?_
  first
    | refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
    | refine ProofLib.SepWP.transport_atStatePool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
))

theorem wpp_call_s [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (T : State → SepProp)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T s)) (hφ : φ)
    (hP : P = T s ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      WSepWPp prog ret sf (spec.post x s sf ∗ F) Q (postNoPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) :=
  wpp_call_noPanic_placed x hcall hpc hrun hsp hcl hlr hspec hφ hP hnext hexit hpan hoom_eq

/-! ## `ratchet_key = None` and `PublicKey::deserialize = Err` paths (Block `85`) -/

theorem post_rk_none_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {m' : ProtoSignalMessage} {out : Except SignalProtocolError SignalMessage}
    (hrk : m'.ratchetKey = none)
    (herr : out = .error .invalidProtobufEncoding)
    (hst : LoopExitStatePlaced s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (blkPl_85).base + 944#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = 0#64) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (wireSignalMessageOf A.repAlloc (sp' + 176#64) m' ∗
        memRegion (sp' + 88#64) 16 ∗ memRegion x19 120 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  have hnext := @cleanup_64c_wp_placed _ M A lim H hS st s0
  unfold wireSignalMessageOf
  simp only [sepExists_sepConj_left]
  refine WSepWPp.exists_pre fun g => ?_
  unfold wireSignalMessageAt
  rw [hrk]
  have hent_rk : optVecU8At A.repAlloc g.rk (sp' + 176#64) none ⊢
      ∃∗ rkLen : BitVec 64, ∃∗ rkPtr : BitVec 64,
        vecHeader (sp' + 176#64) noneCap rkPtr rkLen := by
    unfold optVecU8At vecHeader
    refine Entails.trans (sepConj_mono_right (memRegion16_split8_8 (sp' + 176#64 + 8#64))) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
    exact Entails.refl _
  have hent_wire :
      optVecU8At A.repAlloc g.rk (sp' + 176#64) none ∗
      optVecU8At A.repAlloc g.ct (sp' + 176#64 + 24#64) m'.ciphertext ∗
      optVecU8At A.repAlloc g.pq (sp' + 176#64 + 48#64) m'.pqRatchet ∗
      optVecU8At A.repAlloc g.addr (sp' + 176#64 + 72#64) m'.addresses ∗
      optU32At (sp' + 176#64 + 96#64) m'.counter ∗
      optU32At (sp' + 176#64 + 104#64) m'.previousCounter ⊢
      (∃∗ rkLen, ∃∗ rkPtr, vecHeader (sp' + 176#64) noneCap rkPtr rkLen) ∗
      (∃∗ ctCap, ∃∗ ctPtr, ∃∗ ctLen, ∃∗ ctAct,
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗ deallocSlot A.repAlloc ctCap ctPtr ctAct) ∗
      (∃∗ pqCap, ∃∗ pqPtr, ∃∗ pqLen, ∃∗ pqAct,
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗ deallocSlot A.repAlloc pqCap pqPtr pqAct) ∗
      (∃∗ adCap, ∃∗ adPtr, ∃∗ adLen, ∃∗ adAct,
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗ deallocSlot A.repAlloc adCap adPtr adAct) ∗
      (∃∗ cTag, ∃∗ cVal, ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal)) ∗
      (∃∗ pcTag, ∃∗ pcVal, ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono hent_rk
      (sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.ct (sp' + 200#64) m'.ciphertext)
        (sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.pq (sp' + 224#64) m'.pqRatchet)
          (sepConj_mono (optVecU8At_entails_header_dealloc A.repAlloc g.addr (sp' + 248#64) m'.addresses)
            (sepConj_mono (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_cells (sp' + 272#64) m'.counter)
              (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_cells (sp' + 280#64) m'.previousCounter)))))
  refine WSepWPp.mono_pre (sepConj_mono hent_wire
    (sepConj_mono (memRegion16_split8_8 (sp' + 88#64))
      (sepConj_mono_left (memRegion120_split16 x19)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 =>
    WSepWPp.exists_pre fun s96 => WSepWPp.exists_pre fun s88 =>
    WSepWPp.exists_pre fun pcTag => WSepWPp.exists_pre fun pcVal =>
    WSepWPp.exists_pre fun cTag => WSepWPp.exists_pre fun cVal =>
    WSepWPp.exists_pre fun adCap => WSepWPp.exists_pre fun adPtr =>
    WSepWPp.exists_pre fun adLen => WSepWPp.exists_pre fun adAct =>
    WSepWPp.exists_pre fun pqCap => WSepWPp.exists_pre fun pqPtr =>
    WSepWPp.exists_pre fun pqLen => WSepWPp.exists_pre fun pqAct =>
    WSepWPp.exists_pre fun ctCap => WSepWPp.exists_pre fun ctPtr =>
    WSepWPp.exists_pre fun ctLen => WSepWPp.exists_pre fun ctAct =>
    WSepWPp.exists_pre fun rkLen => WSepWPp.exists_pre fun rkPtr => ?_
  have hvh :
      vecHeader (sp' + 176#64) noneCap rkPtr rkLen =
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∧
      vecHeader (sp' + 176#64) (speWord 2) rkPtr rkLen =
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∧
      vecHeader (sp' + 200#64) ctCap ctPtr ctLen =
        ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∧
      vecHeader (sp' + 224#64) pqCap pqPtr pqLen =
        ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∧
      vecHeader (sp' + 248#64) adCap adPtr adLen =
        ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) := by
    simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, and_self]
  rcases hvh with ⟨hvh1, hvh1', hvh2, hvh3, hvh4⟩
  rw [hvh1, hvh2, hvh3, hvh4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1612#64) ?_
  wp_steps_sync_deser85 ((blkPl_85).base + 1612#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  set F_hdr := vecHeader (sp' + 176#64) (speWord 2) rkPtr rkLen ∗
    vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
    vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
    vecHeader (sp' + 248#64) adCap adPtr adLen ∗
    ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
    ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
    memRegion (x19 + 16#64) 104
  refine wpp_sync_pre (fun s1 => (deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
      deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
      A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_hdr)
    (by dsimp only [F_hdr]; apply entails_of_eq; simp only [hvh1', hvh2, hvh3, hvh4, errTag, arm64_norm]; sep_ac_rfl) ?_
  refine wpp_frame_noPanic
    (hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
    fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 88#64) adPtr pqPtr
  have ha96 : sp' + 88#64 + 8#64 = sp' + 96#64 := by bv_omega
  rw [ha96] at h16
  have hc8 : ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ⊢ memRegion (sp' + 272#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 272#64) cTag cVal
  have hpc8 : ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ⊢ memRegion (sp' + 280#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 280#64) pcTag pcVal
  have h112 := Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hc8 hpc8)))))
    (wireHeaders_entails_memRegion112 sp' (speWord 2) rkPtr rkLen ctCap ctPtr ctLen
      pqCap pqPtr pqLen adCap adPtr adLen)
  have hmsg := spe_invalidProto_intro A.repAlloc x19 herr
  dsimp only [F_hdr]
  refine Entails.trans (Q := (((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr)) ∗
      (vecHeader (sp' + 176#64) (speWord 2) rkPtr rkLen ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        (((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal)) ∗
        (((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal))) ∗
      ((x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepConj_mono h16 (sepConj_mono h112 (sepConj_mono_left hmsg))

theorem post_deser_err_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 w0 w1 w2 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (ctAct pqAct adAct : Bool)
    (e : SignalProtocolError) (_herr_deser : PublicKey.deserialize rk = .error e)
    {out : Except SignalProtocolError SignalMessage} (hout : out = .error e)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1220#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H) ((blkPl_85).base + 1088#64) s
      (deserializeResult33At (sp' + 176#64) (.error e) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
        memRegion (x19 + 24#64) 96 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion (sp' + 176#64) 33 ∗
            ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := @cleanup_640_wp_placed _ M A lim H hS st s0
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1600#64) ?_
    wp_steps_sync_deser85 ((blkPl_85).base + 1600#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (((sp' + 176#64) ↦₈ 1#8) ∗ memRegion (sp' + 177#64) 7 ∗
          ((sp' + 184#64) ↦₈ 0#8) ∗ memRegion (sp' + 185#64) 24 ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 7) ∗
          ((x19 + 16#64) ↦₆₄ (s.readReg64 (Reg.gpr 10#5) &&& 255#64)) ∗
          memRegion (x19 + 24#64) 96))
      (by apply entails_of_eq; simp only [errTag, speWord, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext rk ctAct pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    have h33 := memRegion33_of_err_base (sp' + 176#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    have hmsg := spe_noKeyType_intro A.repAlloc x19 (s.readReg64 (Reg.gpr 10#5) &&& 255#64) hout
    refine Entails.trans ?_
      (sepConj_mono h33 (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg))))))
    apply entails_of_eq; sep_ac_rfl
  | badKeyType t =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1600#64) ?_
    wp_steps_sync_deser85 ((blkPl_85).base + 1600#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (((sp' + 176#64) ↦₈ 1#8) ∗ memRegion (sp' + 177#64) 7 ∗
          ((sp' + 184#64) ↦₈ 1#8) ∗ ((sp' + 185#64) ↦₈ t) ∗ memRegion (sp' + 186#64) 23 ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 8) ∗
          ((x19 + 16#64) ↦₆₄ t.zeroExtend 64) ∗
          memRegion (x19 + 24#64) 96))
      (by apply entails_of_eq; simp only [errTag, speWord, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext rk ctAct pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    have h33 := memRegion33_of_err_badKeyType (sp' + 176#64) t
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    have hmsg := spe_badKeyType_intro A.repAlloc x19 t hout
    refine Entails.trans ?_
      (sepConj_mono h33 (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg))))))
    apply entails_of_eq; sep_ac_rfl
  | badKeyLength n =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1600#64) ?_
    wp_steps_sync_deser85 ((blkPl_85).base + 1600#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (((sp' + 176#64) ↦₈ 1#8) ∗ memRegion (sp' + 177#64) 7 ∗
          ((sp' + 184#64) ↦₈ 2#8) ∗ memRegion (sp' + 185#64) 7 ∗
          ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (sp' + 200#64) 9 ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 9) ∗
          ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
          memRegion (x19 + 24#64) 96))
      (by apply entails_of_eq; simp only [errTag, speWord, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext rk ctAct pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    have h33 := memRegion33_of_err_badKeyLength (sp' + 176#64) n
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    have hmsg := spe_badKeyLength_intro A.repAlloc x19 n hout
    refine Entails.trans ?_
      (sepConj_mono h33 (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg))))))
    apply entails_of_eq; sep_ac_rfl
  | _ =>
    dsimp only [deserializeResult33At]
    exact WSepWPp.pure_pre fun hfalse => False.elim hfalse

/-! ## `PublicKey::deserialize = Ok` and counter/ciphertext checks (Block `85`) -/

theorem post_deser_ok_head_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (st : M.σ) {s0 s : State} {sp' w104 w15 w23 : BitVec 64}
    {cTag w68 w9 w120 : BitVec 32} {w13 w124 : BitVec 16}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b112 c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1220#64)
    (hrun : s.status = .Running) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1356#64) s
      (((sp' + 176#64) ↦₈ 0#8) ∗
        pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        memRegion (sp' + 209#64) 15 ∗
        ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 104#64) ↦₆₄ w104) ∗
        ((sp' + 112#64) ↦₈ b112) ∗
        ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
        sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6 ∗
        A.pool lim st s)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pc = (blkPl_85).base + 1356#64 ∧
        sf.status = .Running ∧
        sf.pstate = subsPState32 cTag 1#32 ∧
        sf.readReg64 .x8 = w15 ∧
        sf.readReg64 .x9 = (b8.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x24 = (b7.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x26 = speWord 2 ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x26 →
          sf.readReg64 r = s.readReg64 r) ∧
        (Pf ⊢ ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          ((sp' + 64#64) ↦₆₄ (w68 ++ cTag)) ∗
          ((sp' + 104#64) ↦₆₄ w23) ∗
          ((sp' + 112#64) ↦₈ b31) ∗
          ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
          A.pool lim st sf))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  dsimp only [pkLayoutAt]
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1280#64) ?_
  dsimp only [sevenBytesHeadAt]
  wp_steps_sync_deser85 ((blkPl_85).base + 1280#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  have h177_tail :
      ((sp' + 177#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sp' + 177#64 + 4#64) ↦₈ b4) ∗
        ((sp' + 177#64 + 5#64) ↦₈ b5) ∗
        ((sp' + 177#64 + 6#64) ↦₈ b6) =
      sevenBytesTailAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 :=
    sevenBytesHeadAt_eq_tailAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6
  refine wpp_sync_pre (fun s1 =>
      ((sp' + 176#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 177#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 209#64) 15 ∗
      ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
      ((sp' + 104#64) ↦₆₄ w104) ∗
      ((sp' + 112#64) ↦₈ b112) ∗
      ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
      sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6 ∗
      A.pool lim st s1)
    (by
      rw [← h177_tail]
      dsimp only [sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl) ?_
  refine WSepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).base + 1304#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_sync_deser85 ((blkPl_85).base + 1304#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl2
  have h128_tail := sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 c4 c5 c6
  refine wpp_sync_pre (fun s2 =>
      ((sp' + 176#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 177#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 209#64) 15 ∗
      ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
      ((sp' + 104#64) ↦₆₄ w104) ∗
      ((sp' + 112#64) ↦₈ b112) ∗
      ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
      sevenBytesTailAt (sp' + 128#64) b0 b1 b2 b3 c4 c5 c6 ∗
      A.pool lim st s2)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 177#64), ← h128_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
  refine WSepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 1352#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_sync_deser85 ((blkPl_85).base + 1352#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  have hspe := deser_ok_entails_spe_region (sp' + 176#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hspe
  have h128_head := sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6
  have h64_pair := pointsTo32_pair_eq_pointsTo64 (sp' + 64#64) cTag w68
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h64_pair
  refine wpp_sync_pre (fun s3 =>
      (((sp' + 176#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗
        memRegion (sp' + 184#64) 40) ∗
      ((sp' + 64#64) ↦₆₄ (w68 ++ cTag)) ∗
      ((sp' + 104#64) ↦₆₄ w23) ∗
      ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      A.pool lim st s3)
    (by
      refine Entails.trans ?_ (sepConj_mono_left hspe)
      rw [← h64_pair, h128_head]
      dsimp only [sevenBytesTailAt, pkRestAt]
      apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
  refine wpp_of_sepWP_end_noPanic_placed hcl3 ?_
  wp_steps_sync_deser85 ((blkPl_85).base + 1356#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl4
  refine ⟨PostEpilogueStatePlaced.of_steps hcl4 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]),
    by simp [arm64_norm], by simp [hrun, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [speWord, arm64_norm],
    fun r hr8 hr9 hr10 hr11 hr24 hr26 => ?_,
    ?_⟩
  · cases r with
    | gpr idx =>
      have h8 : idx ≠ 8#5 := fun h => hr8 (congrArg Reg.gpr h)
      have h9 : idx ≠ 9#5 := fun h => hr9 (congrArg Reg.gpr h)
      have h10 : idx ≠ 10#5 := fun h => hr10 (congrArg Reg.gpr h)
      have h11 : idx ≠ 11#5 := fun h => hr11 (congrArg Reg.gpr h)
      have h24 : idx ≠ 24#5 := fun h => hr24 (congrArg Reg.gpr h)
      have h26 : idx ≠ 26#5 := fun h => hr26 (congrArg Reg.gpr h)
      simp [h8, h9, h10, h11, h24, h26, arm64_norm]
    | sp | xzr => simp [arm64_norm]
  · dsimp only [sevenBytesHeadAt]
    apply entails_of_eq; simp only [BitVec.reduceAdd, speWord, arm64_norm]; sep_ac_rfl

theorem post_counter_none_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (ctAct pqAct adAct : Bool)
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1356#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx19 : s.readReg64 .x19 = x19) (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := @cleanup_640_wp_placed _ M A lim H hS st s0
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1600#64) ?_
  wp_steps_sync_deser85 ((blkPl_85).base + 1600#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  refine wpp_sync_pre (fun s1 => (vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
      deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
      A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
      (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
  refine wpp_frame_noPanic
    (hnext rk ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
      (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
    fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hmsg := spe_invalidProto_intro A.repAlloc x19 hout
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg)))))
  apply entails_of_eq; sep_ac_rfl

theorem post_counter_some_head_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x20 x21 x22 x23 x24 x25 x27 x28 w64 w15 : BitVec 64}
    {w12 pcTag pcVal : BitVec 32} {b8 : BitVec 8}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1356#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 1#32 1#32)
    (hx8 : s.readReg64 .x8 = w15)
    (hx9 : s.readReg64 .x9 = (b8.zeroExtend 32).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = x20)
    (hx21 : s.readReg64 .x21 = x21) (hx22 : s.readReg64 .x22 = x22)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg64 .x24 = x24)
    (hx25 : s.readReg64 .x25 = x25) (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = x28) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1400#64) s
      (((sp' + 12#64) ↦₃₂ w12) ∗
        ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₆₄ w64) ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pc = (blkPl_85).base + 1400#64 ∧
        sf.status = .Running ∧
        sf.pstate = addsPState64 x27 1#64 ∧
        sf.readReg64 .x8 = (if (pcTag &&& 1#32) != 0#32 then pcVal else 0#32).zeroExtend 64 ∧
        sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
        sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = x22 ∧
        sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = x24 ∧
        sf.readReg64 .x25 = x25 ∧ sf.readReg64 .x26 = speWord 2 ∧
        sf.readReg64 .x27 = x27 ∧ sf.readReg64 .x28 = x28 ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
            ((sp' + 64#64) ↦₆₄ w15) ∗
            ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hDropSpe
  clear hDropSpe
  have hstack := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropSpeName) ?_
  wp_steps_sync_deser85 ((blkPl_85).ρ dropSpeName)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  have hspe_eq : speAt A.repAlloc [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine wpp_call_s
    (⟨⟨sp' + 176#64, [], .invalidProtobufEncoding⟩, st⟩ : DropSpeGhost × M.σ) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
    (ret_pc := (blkPl_85).base + 1376#64) (by simp [arm64_norm])
    (fun s1 => speAt A.repAlloc [] (sp' + 176#64) .invalidProtobufEncoding ∗
      A.pool lim st s1 ∗ stackAt sp' dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_85).base + 1376#64))
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    ⟨rfl, ⟨85, by decide, 1376, by decide, rfl⟩⟩
    (by rw [hspe_eq, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine WSepWPp.exists_pre fun evs => ?_
  refine WSepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_left_comm (memRegion (sp' + 176#64) 48) ⌜FreeOnlyEvs evs⌝]
  refine WSepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = x22 := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = x25 := by simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = x27 := by simp [hx27_cs, hx27, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = x28 := by simp [hx28_cs, hx28, arm64_norm]
  have h48 : memRegion (sp' + 176#64) 48 =
      (∃∗ w176 : BitVec 64, ((sp' + 176#64) ↦₆₄ w176)) ∗ memRegion (sp' + 184#64) 40 := by
    have hs := memRegion_split (sp' + 176#64) 8 40 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, memRegion_eight] at hs
    exact hs
  rw [h48]
  simp only [sepExists_sepConj_left]
  refine WSepWPp.exists_pre fun w176 => ?_
  refine wpp_of_sepWP_end_noPanic_placed hcl2 ?_
  wp_steps_sync_deser85 ((blkPl_85).base + 1400#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  refine ⟨PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2_eq]) hsp_eq hsp
      (by simp [htr2, htr, arm64_norm]),
    by simp [arm64_norm], by simp [hrun2, arm64_norm],
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx19_2, arm64_norm], by simp [hx20_2, arm64_norm],
    by simp [hx21_2, arm64_norm], by simp [hx22_2, arm64_norm],
    by simp [hx23_2, arm64_norm], by simp [hx24_2, arm64_norm],
    by simp [hx25_2, arm64_norm], by simp [hx26_2, arm64_norm],
    by simp [hx27_2, arm64_norm], by simp [hx28_2, arm64_norm],
    evs, hfree, ?_⟩
  apply entails_of_eq
  simp only [hstack, arm64_norm]
  sep_ac_rfl

theorem post_ct_none_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 w0 w1 rkCap rkPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (pqAct adAct : Bool)
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1400#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = addsPState64 noneCap 1#64)
    (hx19 : s.readReg64 .x19 = x19) (hx26 : s.readReg64 .x26 = speWord 2)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hS.alloc.dealloc
  by_cases hcap : rkCap = 0#64
  · clear hcall
    subst hcap
    rw [vecU8Buf_zero]
    refine WSepWPp.mono_pre (P' := ⌜rk = [] ∧ rkPtr ≠ 0⌝ ∗
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun _ => ?_
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1640#64) ?_
    wp_steps_sync_deser85 ((blkPl_85).base + 1640#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_sync_pre (fun s1 => (deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104))
      (by apply entails_of_eq; simp only [errTag, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (cleanup_668_wp_placed hS st pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    have hmsg := spe_invalidProto_intro A.repAlloc x19 hout
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg)))))
    apply entails_of_eq; sep_ac_rfl
  · refine WSepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc rkCap rkPtr rk hcap))))))) ?_
    simp only [sepConj_assoc]
    refine WSepWPp.mono_pre (P' := ⌜0 < rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0#64⌝ ∗
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          A.repAlloc.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗
          deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps_sync_deser85 ((blkPl_85).ρ lsRustDeallocSym)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl1
    refine wpp_call_s (rkPtr, rkCap.toNat, 1, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
      (ret_pc := (blkPl_85).base + 1640#64) (by simp [arm64_norm])
      (fun s1 => A.pool lim st s1 ∗ A.live rkPtr rkCap.toNat 1 ∗
        memRegion rkPtr rkCap.toNat ∗ stackAt sp' extHookStack)
      (φ := RustLayoutOk rkCap.toNat 1 ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_85).base + 1640#64))
      (by simp [hsp_eq, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rustLayoutOk_align1 hpos hlt, ⟨85, by decide, 1640, by decide, rfl⟩⟩
      (by rw [hstack, A.repAlloc_live_norm]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine WSepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨_, _, _, hx22_cs, _, _, hx25_cs, _⟩
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    refine WSepWPp.mono_pre (P' := (deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents rkCap.toNat 1) st) s2 ∗
        stackAt sp' (skipFieldStackX 100)) ∗
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, errTag, arm64_norm]; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (cleanup_668_wp_placed hS (M.stepEvents (rustDeallocEvents rkCap.toNat 1) st) pqAct adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx25_2 hx22_2)
      fun sf Pf ⟨hstf, evs₂, hfree₂, hent⟩ =>
        ⟨hstf, rustDeallocEvents rkCap.toNat 1 ++ evs₂,
         (freeOnly_rustDeallocEvents rkCap.toNat 1).append hfree₂, ?_⟩
    rw [M.stepEvents_append]
    refine Entails.trans (sepConj_mono_left hent) ?_
    have hmsg := spe_invalidProto_intro A.repAlloc x19 hout
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg)))))
    apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget
