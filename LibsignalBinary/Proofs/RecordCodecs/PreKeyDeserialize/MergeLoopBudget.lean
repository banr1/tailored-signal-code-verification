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
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFieldsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.PostBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKey
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFields
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded `PreKeyRecord::deserialize` Decode Loop and Post-Loop Tails

`RustCliAllocBudget`-threaded relocatable `Ok` packing, error stubs, and varint/loop helpers for
`PreKeyRecord::deserialize` (Block `65`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeLoopBudget

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
open CryptoVerification.LibsignalTripleRatchet.VarintBridge (decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers hiding pkEpilogueMem
open scoped CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromSpecWithStack decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowEvents decodeVarintSlowBudgetSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents decodeVarintSliceSpecGen decodeVarintSliceSpecX)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced DecodeErrorPushBoundedEnv
   decodeErrorPushBoundedExternSpecWithStack decodeErrorPushBoundedExternBudgetSpecWithStack
   RecordCodecIterEnv RecordCodecLoopEnv fitsEnv_recordCodecLoop_head
   noPanicQp sepWPp_mono_post sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
  (pk_varintSlice_placed_ok pk_varintSlow_placed_ok
   pk_decodeErrorFrom_placed_ok pk_decodeErrorPush_placed_ok
   pkEpiloguePostPlaced pkEpiloguePostPlaced_prepend_iter)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.PostBudget (pack_tail_190_placed_wp)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFieldsBudget (post_err_1d0_placed_wp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem post_ok_23c_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (572)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ preKeyStructOf A.repAlloc (sp' + 56#64) m ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  unfold preKeyStructOf; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun g => ?_
  rw [preKeyStructAt_split_pub A.repAlloc g sp' m,
    vecU8At_eq_header_buf A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey,
    vecU8At_eq_header_buf A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey]
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun pad32 => SepWPp.exists_pre fun w0 =>
    SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w3 => ?_
  have hpub_bounds : vecU8Buf A.repAlloc g.pub.cap g.pub.ptr m.publicKey ⊢
      ⌜g.pub.cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A.repAlloc g.pub.cap g.pub.ptr m.publicKey := by
    unfold vecU8Buf; refine Entails.pure_left fun h => ?_
    rw [pure_true_emp h, pure_true_emp h.2.1, emp_sepConj, emp_sepConj]; exact Entails.refl _
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpub_bounds)))))))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine SepWPp.pure_pre fun hpub_lt => ?_
  have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt g.pub.cap hpub_lt
  have hp104 : ((sp' + 104#64) ↦₃₂ m.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) =
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) m.id pad32
  refine SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗
      ((sp' + 56#64) ↦₆₄ g.pub.cap) ∗ ((sp' + 64#64) ↦₆₄ g.pub.ptr) ∗
      ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((sp' + 80#64) ↦₆₄ g.priv.cap) ∗ ((sp' + 88#64) ↦₆₄ g.priv.ptr) ∗
      ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) ∗ vecU8Buf A.repAlloc g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8Buf A.repAlloc g.priv.cap g.priv.ptr m.privateKey ∗ memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
    (by dsimp only [vecHeader]; rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ m.id), hp104]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; apply entails_of_eq; sep_ac_rfl) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (400)) ?_
  wp_steps_sync_pool ((blkPl_65).base + bv% (400))
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine SepWPp.mono_pre ?_
    (pack_tail_190_placed_wp (st := st) (fuel := fuel) (maxLen := maxLen)
      (g := g) (m := m) (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcrl1,
       by simp [htr, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ g.pub.cap) ∗ ((sp' + 64#64) ↦₆₄ g.pub.ptr) ∗
      ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((sp' + 80#64) ↦₆₄ g.priv.cap) ∗ ((sp' + 88#64) ↦₆₄ g.priv.ptr) ∗
      ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]; simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      pkStruct56_pack sp' g.pub.cap g.pub.ptr (BitVec.ofNat 64 m.publicKey.length)
        g.priv.cap g.priv.ptr (BitVec.ofNat 64 m.privateKey.length) m.id pad32
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56)))))))
  apply entails_of_eq; sep_ac_rfl

theorem decodeErrorFrom_1c8_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr kind : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (blkPl_65).base + bv% (456)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hkind : KindNoHeap kind)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
        preKeyStructOf A.repAlloc (sp' + 56#64) mErr ∗ memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (sp' + 112#64, kind, st) (pk_decodeErrorFrom_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (464)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
      A.pool lim st s ∗ stackAt sp' (2 * extHookStack))
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap kind ∧ FitsEnv M lim st DecodeErrorFromEnv)
    (by simp [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack,
      hsp_eq, arm64_norm])
    ⟨rfl, hkind, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeErrorFrom) hFit⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  refine SepWPp.pure_pre fun ⟨_hx0_ne, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  refine sepWPp_mono_post
    (SepWPp.mono_pre ?_
      (post_err_1d0_placed_wp d (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
        (err := s2.readReg64 .x0) (mErr := mErr) herr
        ⟨hregs2.sp, hsp2_align, hcrl2, (by simp [htr2, htr, arm64_norm]), hregs2.saved⟩
        hpc2 hrun2 rfl hregs2.x19_eq hregs2.x22))
    fun sf Pf h => pkEpiloguePostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeErrorFrom hevs) h
  have herr_mem := pkErrMem_of_structOf (A.atState lim (M.stepEvents evs st) s2)
    sp' x19 ptr (s2.readReg64 .x0) 0 mErr bs
  have hstruct_eq : preKeyStructOf (A.atState lim (M.stepEvents evs st) s2) = preKeyStructOf A.repAlloc := rfl
  have hdec_eq : decodeErrorAtStackLen (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAtStackLen A.repAlloc := rfl
  have hdecAt_eq : decodeErrorAt (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAt A.repAlloc := rfl
  rw [hstruct_eq, hdec_eq, hdecAt_eq] at herr_mem
  dsimp only [RustCliAllocBudget.atState] at herr_mem
  simp only [arm64_norm]
  refine Entails.trans ?_ herr_mem
  apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl

theorem decodeErrorFrom_1c4_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (blkPl_65).base + bv% (452)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hkind : KindNoHeap (s.readReg64 .x8))
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ w0) ∗ memRegion (sp' + 120#64) 40 ∗
        preKeyStructOf A.repAlloc (sp' + 56#64) mErr ∗ memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (456)) ?_
  wp_steps_sync_pool ((blkPl_65).base + bv% (456))
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine SepWPp.mono_pre ?_
    (decodeErrorFrom_1c8_placed_wp d (st := st) (fuel := fuel) (maxLen := maxLen)
      (kind := s.readReg64 .x8) (mErr := mErr) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcrl1 (by simpa [arm64_norm] using htr) hkind hFit)
  apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl

theorem decodeErrorPush_2cc_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (blkPl_65).base + bv% (716)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 112#64) (herr_ne : err ≠ 0#64)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ err) ∗ memRegion (sp' + 120#64) 40 ∗
        decodeErrorAtStackLen A.repAlloc err 0 ∗ preKeyStructOf A.repAlloc (sp' + 56#64) mErr ∗
        memRegion sp' 40 ∗ memRegion x19 56 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = sp' + 112#64 := hx0
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 257) ?_
  wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (sp' + 112#64, err, 0, st) (pk_decodeErrorPush_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (720)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
      A.pool lim st s ∗ stackAt sp' (2 * extHookStack))
    (φ := sp' + 112#64 = sp' + 112#64 ∧ err ≠ 0#64 ∧ 0 < 4294967296 ∧
      FitsEnv M lim st (DecodeErrorPushBoundedEnv 0))
    (by simp [decodeErrorPushBoundedExternSpecWithStack, decodeErrorPushBoundedExternBudgetSpecWithStack,
      hsp_eq, h0, arm64_norm])
    ⟨rfl, herr_ne, by decide, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeErrorPush0) hFit⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  dsimp only [decodeErrorPushBoundedExternSpecWithStack, decodeErrorPushBoundedExternBudgetSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun err' => ?_
  refine SepWPp.pure_pre fun _herr' => ?_
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun evs => SepWPp.pure_pre fun hevs => ?_
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
  wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
  refine sepWPp_mono_post
    (SepWPp.mono_pre ?_
      (post_err_1d0_placed_wp d (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
        (err := err') (mErr := mErr) herr
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hcrl3, by simpa [arm64_norm] using htr2.trans htr,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22)))
    fun sf Pf h => pkEpiloguePostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeErrorPush0 hevs) h
  have hscr := pkPointsTo112_memRegion40_entails_memRegion48 sp' err'
  have herr_mem := pkErrMem_of_structOf (A.atState lim (M.stepEvents evs st) s2)
    sp' x19 ptr err' 1 mErr bs
  have hstruct_eq : preKeyStructOf (A.atState lim (M.stepEvents evs st) s2) = preKeyStructOf A.repAlloc := rfl
  have hdec_eq : decodeErrorAtStackLen (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAtStackLen A.repAlloc := rfl
  have hdecAt_eq : decodeErrorAt (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAt A.repAlloc := rfl
  rw [hstruct_eq, hdec_eq, hdecAt_eq] at herr_mem
  dsimp only [RustCliAllocBudget.atState] at herr_mem
  simp only [arm64_norm]
  refine Entails.trans ?_ herr_mem
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  sep_ac_rfl

theorem decodeVarintSlow_15c_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (348)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st s1) sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold pkLoopMem sliceCursorAt
  have hloop_eq : preKeyStructLoopOf (A.atState lim st s) = preKeyStructLoopOf A.repAlloc := rfl
  rw [hloop_eq]; dsimp only [RustCliAllocBudget.atState]; simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 293) ?_
  wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (sp' + 184#64, sp' + 40#64, ptr, bs, st) (pk_varintSlow_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (356)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ ((sp' + 40#64) ↦₆₄ ptr) ∗
      ((sp' + 40#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool lim st s ∗ stackAt sp' (64 + 2 * extHookStack))
    (φ := sp' + 184#64 = sp' + 184#64 ∧ bs.length < 2 ^ 64 ∧ FitsEnv M lim st (DecodeVarintSlowEnv bs))
    (by simp [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack,
      hsp_eq, arm64_norm])
    ⟨rfl, by omega, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeVarintSlow) hFit⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack]
  have hd_eq := decodeVarint_eq_varintSlow bs
  rw [hd_eq]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have hevs0 : evs = [] := by
      rw [hevs]; unfold decodeVarintSlowEvents; rw [hd_eq, hd]; rfl
    subst hevs0
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (224)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine SepWPp.mono_pre ?_
      (hcont key rest _ hd (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]))
    apply entails_of_eq; unfold pkAfterVarintMem sliceCursorAfter
    have hloop_eq' : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc :=
      fun _ => rfl
    rw [hloop_eq']; dsimp only [RustCliAllocBudget.atState]
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, hstack, hsp_eq, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only [Option.map]; rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_1, _hx1_ne⟩ => ?_
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (SepWPp.mono_pre ?_
        (post_err_1d0_placed_wp d (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
          (err := s2.readReg64 (Reg.gpr 1#5)) (mErr := m) (hnone hd)
          ⟨by simpa [arm64_norm] using hregs2.sp,
           by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
           hcrl3, by simpa [arm64_norm] using htr2.trans htr,
           ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
          (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22)))
      fun sf Pf h => pkEpiloguePostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeVarintSlow hevs) h
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 40#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length)) (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    simp only [arm64_norm] at hpair
    have herr_mem := pkErrMem_of_loopOf (A.atState lim (M.stepEvents evs st) s2)
      sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) 0 bs.length m bs
    have hloop_eq2 : preKeyStructLoopOf (A.atState lim (M.stepEvents evs st) s2) = preKeyStructLoopOf A.repAlloc := rfl
    have hstruct_eq2 : preKeyStructOf (A.atState lim (M.stepEvents evs st) s2) = preKeyStructOf A.repAlloc := rfl
    have hdec_eq2 : decodeErrorAtStackLen (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAtStackLen A.repAlloc := rfl
    have hdecAt_eq2 : decodeErrorAt (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAt A.repAlloc := rfl
    rw [hloop_eq2, hstruct_eq2, hdec_eq2, hdecAt_eq2] at herr_mem
    dsimp only [RustCliAllocBudget.atState] at herr_mem
    simp only [arm64_norm]
    refine Entails.trans ?_ herr_mem
    refine Entails.trans ?_ (sepConj_mono_left hpair)
    apply entails_of_eq
    simp only [hstack, hsp_eq, arm64_norm]
    sep_ac_rfl

theorem decodeVarintSlice_0ac_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (172)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63) (hpre_slice : VarintSlicePre bs)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st s1) sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h23 : s.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := hx23
  have h21 : s.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := hx21
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' decodeVarintSliceStackX (skipFieldStackX 100)
  unfold pkLoopMem sliceCursorAt
  have hloop_eq : preKeyStructLoopOf (A.atState lim st s) = preKeyStructLoopOf A.repAlloc := rfl
  rw [hloop_eq]; dsimp only [RustCliAllocBudget.atState]
  simp only [hstack, pkMemRegion48_split24 sp', sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 76) ?_
  wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (⟨sp' + 112#64, ptr, bs⟩, st) (pk_varintSlice_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (180)) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 112#64) 24 ∗ (ptr ↦ₛ bs) ∗
      A.pool lim st s ∗ stackAt sp' decodeVarintSliceStackX)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ bs.length < 2 ^ 63 ∧ VarintSlicePre bs ∧
      FitsEnv M lim st (DecodeVarintSliceEnv bs))
    (by simp [decodeVarintSliceSpecX, decodeVarintSliceSpecGen,
      decodeVarintSliceStackX, decodeErrorHookStackX,
      hsp_eq, h1, h2, hx2_nat, arm64_norm])
    ⟨rfl, hlen, hpre_slice, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeVarintSlice) hFit⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  have h23_2 : s2.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := by simpa [arm64_norm, h23] using hcs2.2.2.2.2.1
  have h21_2 : s2.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := by simpa [arm64_norm, h21] using hcs2.2.2.1
  dsimp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
        BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]; omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]; omega
    rw [pointsTo64_zero_split32 (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    have hevs0 : evs = [] := by
      rw [hevs]; unfold decodeVarintSliceEvents; rw [hd]
    subst hevs0
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (224)) ?_
    wp_steps
    wp_if hcc
    · exfalso; rw [← hrest] at hcc; exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · refine ProofLib.SepWP.transport_budgetPool (s1 := s2)
        (by simp)
        (hnext := ?_)
      wp_steps_sync_pool ((blkPl_65).base + bv% (224))
      refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
      refine SepWPp.mono_pre ?_
        (hcont key rest _ hd (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
           by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]))
      have hscr := pkScratch24_ok_entails_memRegion48 sp' key (BitVec.ofNat 64 (bs.length - rest.length))
      unfold pkAfterVarintMem sliceCursorAfter
      have hloop_eq' : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc :=
        fun _ => rfl
      rw [hloop_eq']; dsimp only [RustCliAllocBudget.atState]
      simp only [← hrest, hsub_bv]
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr)))
      apply entails_of_eq
      simp only [decodeVarintSliceStackX, decodeErrorHookStackX, hstack, hsp_eq, arm64_norm]
      sep_ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [pointsTo64_one_split32 (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => SepWPp.exists_pre fun e => ?_
    refine SepWPp.pure_pre fun htr2 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _he_ne => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (SepWPp.mono_pre ?_
        (post_err_1d0_placed_wp d (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
          (err := e) (mErr := m) (hnone hd)
          ⟨by simpa [arm64_norm] using hregs2.sp,
           by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
           hcrl3, by simpa [arm64_norm] using htr2.trans htr,
           ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
          (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22)))
      fun sf Pf h => pkEpiloguePostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeVarintSlice hevs) h
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) ptr (BitVec.ofNat 64 bs.length)
    have hscr := pkScratch24_err_entails_memRegion48 sp' e
    simp only [arm64_norm] at hpair
    have herr_mem := pkErrMem_of_loopOf (A.atState lim (M.stepEvents evs st) s2)
      sp' x19 ptr e 0 bs.length m bs
    have hloop_eq2 : preKeyStructLoopOf (A.atState lim (M.stepEvents evs st) s2) = preKeyStructLoopOf A.repAlloc := rfl
    have hstruct_eq2 : preKeyStructOf (A.atState lim (M.stepEvents evs st) s2) = preKeyStructOf A.repAlloc := rfl
    have hdec_eq2 : decodeErrorAtStackLen (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAtStackLen A.repAlloc := rfl
    have hdecAt_eq2 : decodeErrorAt (A.atState lim (M.stepEvents evs st) s2) = decodeErrorAt A.repAlloc := rfl
    rw [hloop_eq2, hstruct_eq2, hdec_eq2, hdecAt_eq2] at herr_mem
    dsimp only [RustCliAllocBudget.atState] at herr_mem
    simp only [arm64_norm]
    refine Entails.trans ?_ herr_mem
    refine Entails.trans ?_ (sepConj_mono hpair (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
    apply entails_of_eq
    simp only [decodeVarintSliceStackX, decodeErrorHookStackX, hstack, hsp_eq, arm64_norm]
    sep_ac_rfl

theorem decodeVarintMulti_098_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (152)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hne : bs ≠ []) (hlen : bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st s1) sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  have hloop_eq : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc :=
    fun _ => rfl
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]; omega
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (172)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre ?_
      (decodeVarintSlice_0ac_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simpa [arm64_norm] using hx23) (by simpa [arm64_norm] using hx21)
        (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr) hlen (Or.inl hlen11) hFit hcont hnone)
    apply entails_of_eq; unfold pkLoopMem sliceCursorAt
    rw [hloop_eq, hloop_eq]; dsimp only [RustCliAllocBudget.atState]
    simp only [arm64_norm]
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]; omega
    have hlast_addr : ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) = ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]; exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]; bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold pkLoopMem sliceCursorAt
      rw [hloop_eq, Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (172)) ?_
      wp_steps
      refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine SepWPp.mono_pre ?_
        (decodeVarintSlice_0ac_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simpa [arm64_norm] using hx23) (by simpa [arm64_norm] using hx21)
          (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) hlen (Or.inr ⟨hne, hlast⟩) hFit hcont hnone)
      apply entails_of_eq; unfold pkLoopMem sliceCursorAt
      rw [hloop_eq, Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      dsimp only [RustCliAllocBudget.atState]
      simp only [arm64_norm, sepConj_assoc]
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold pkLoopMem sliceCursorAt
      rw [hloop_eq, Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (348)) ?_
      wp_steps
      refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine SepWPp.mono_pre ?_
        (decodeVarintSlow_15c_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) hlen hFit hcont hnone)
      apply entails_of_eq; unfold pkLoopMem sliceCursorAt
      rw [hloop_eq, Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      dsimp only [RustCliAllocBudget.atState]
      simp only [arm64_norm, sepConj_assoc]

theorem decodeVarint_080_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (128)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st s1) sp' x19 ptr (b0 :: bs1) rest (b0 :: bs1).length m)
        (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr (b0 :: bs1) out) (noPanicQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr (b0 :: bs1) out) (noPanicQp s0) := by
  have h23 : s.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := hx23
  have h21 : s.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := hx21
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  have hloop_eq : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc :=
    fun _ => rfl
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 : BitVec.ofNat 64 (bs1.length + 1) - 1#64 = BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]; bv_omega
    unfold pkLoopMem sliceCursorAt
    rw [hloop_eq, pointsToBytes_cons ptr b0 bs1]
    dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (224)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (224))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr) (by simp [hse, arm64_norm]))
    apply entails_of_eq; unfold pkAfterVarintMem sliceCursorAfter
    rw [hloop_eq, pointsToBytes_cons ptr b0 bs1]
    dsimp only [RustCliAllocBudget.atState]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm, sepConj_assoc]
    sep_ac_rfl
  · have hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold pkLoopMem sliceCursorAt
    rw [hloop_eq, pointsToBytes_cons ptr b0 bs1]
    dsimp only [RustCliAllocBudget.atState]; simp only [sepConj_assoc]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (152)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre ?_
      (decodeVarintMulti_098_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simpa [arm64_norm] using hx23) (by simpa [arm64_norm] using hx21)
        (by simp [arm64_norm]) (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr) (List.cons_ne_nil b0 bs1) hlen hFit hcont hnone)
    apply entails_of_eq; unfold pkLoopMem sliceCursorAt
    rw [hloop_eq, pointsToBytes_cons ptr b0 bs1]
    dsimp only [RustCliAllocBudget.atState]
    simp only [arm64_norm, sepConj_assoc]

end LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeLoopBudget
