/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Decode-Loop Head and Inlined `decode_key`

Allocation-budget (`RustCliAllocBudget M`) proofs of the decode-loop head, slow-varint /
`DecodeError` tail blocks, and inlined `decode_key` on `preKeyPlacedProg H` under
`SigTryFromLoopBoundedEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_eq_111 blkPC_111 blkPl_111 lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeKey decodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen extHookStack varintSlow withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (VarintSlicePre decodeErrorHookStackX decodeVarintSliceStackX skipFieldStackX
   sliceCursorAfter sliceCursorAt varintSliceResultAt)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
  (decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp VRegsAt cons_len_bv64_ne_zero decodeVarint_cons_of_le decodeVarint_suffix entails_of_eq
   key_and7_eq_wt key_and7_ule6_of_ge key_and7_ule6_of_lt
   key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge
   key_tag32_eq_zero_of_lt1 key_tag32_ne_zero_of_ge1 key_tag32_zeroExtend64_eq
   pointsTo64_one_split32 pointsTo64_pair_entails_memRegion16 pointsTo64_zero_split32
   pointsToBytes_split_last signExtend32_bit31_eq_false_iff signExtend32_bit31_eq_true_iff
   signExtend64_bit63_eq_false_iff signExtend64_bit63_eq_true_iff
   signExtend64_eq_zeroExtend64_of_le sliceCursorAfter_entails_memRegion
   sliceCursorAfter_eq_take_cursorAt stackAt_sub_split)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
   bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
   bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
   bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
   bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
   bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
   keepsFrozenInv_codeRoLoaded preKeyPlacedProg)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
  (PreKeyLoopExitStatePlaced PreKeyLoopRegs
   decodeKeyPK_err_entailsX dk_varintSlowStackX memRegion48_16_eq_64
   memRegion56_split40 memRegion64_split24 memRegion64_split8
   memRegion64_split_448_456_464 preKeyLoopExitMem preKeyLoopExitMem_append_prefix
   preKeyLoopExitMem_err_intro preKeyLoopExitMem_ok_intro
   scratch24_err_entails_memRegion64 scratch24_ok_entails_memRegion64
   wirePreKeyAt wirePreKeyOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowBudgetSpecWithStack decodeVarintSlowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromSpecWithStack decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents decodeVarintSliceSpecGen decodeVarintSliceSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
  (advance_cursorPK_placed decodeErrorAtStackLen_mk_eq preKeyLoopExitMem_err_loopCaps_intro
   preKeyLoopExitPostPlaced preKeyLoopExitPostPlaced_append_prefix
   preKeyLoopExitPostPlaced_bytesStep preKeyLoopExitPostPlaced_mono_rem
   preKeyLoopExitPostPlaced_skipStep preKeyLoopExitPostPlaced_zero_eq
   sepWP_done_sync_pool_111 sepWP_seg_111 wirePreKeyLoopCapsOf
   wirePreKeyLoopCapsOf_entails_of wirePreKeyLoopCapsOf_mk_eq wirePreKeyOf_mk_eq)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromErrTailEnv SigTryFromLoopBoundedEnv
   fitsEnv_sigLoop_errTail noPanicQp
   sepWPp_call_noPanic_placed sepWPp_end_noPanic_placed sepWPp_frame_noPanic)

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk

private theorem dk_bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem dk_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  dk_bv_sub_add_lit dk_bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## 0. Segment Pool Sync & Budget-Threaded `preKeyLoopExitPostPlaced` -/

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
  (advance_cursorPK_placed decodeErrorAtStackLen_mk_eq preKeyLoopExitMem_err_loopCaps_intro
   preKeyLoopExitPostPlaced preKeyLoopExitPostPlaced_append_prefix
   preKeyLoopExitPostPlaced_bytesStep preKeyLoopExitPostPlaced_mono_rem
   preKeyLoopExitPostPlaced_skipStep preKeyLoopExitPostPlaced_zero_eq
   sepWP_done_sync_pool_111 sepWP_seg_111 wirePreKeyLoopCapsOf
   wirePreKeyLoopCapsOf_entails_of wirePreKeyLoopCapsOf_mk_eq wirePreKeyOf_mk_eq)

/-! ## 1. Loop Head (`+0x0e4..+0x0f0`, `+0x300..+0x304`) -/

theorem loopExitEmptyPK_300_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x300#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hres : res = some m) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  subst hres
  change s.pc = (blkPl_111).base + 768#64 at hpc
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
    by simpa [arm64_norm] using hregs.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcl1, by simpa [arm64_norm] using htr⟩, [], .done .nil, ?_⟩
  simp only [M.stepEvents_nil, arm64_norm]
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (wirePreKeyLoopCapsOf_entails_of (A.atState lim st _) (sp' + 312#64) caps m))))))
      (preKeyLoopExitMem_ok_intro (A.atState lim st _) sp' ptr bs m))
  simp only [RustCliAllocBudget.atState, wirePreKeyLoopCapsOf_mk_eq]
  apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem loopCheckPK_e4_empty_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr : BitVec 64} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x0e4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hres : res = some m) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr [] res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 228#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  unfold sliceCursorAt; simp only [sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 768#64) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre ?_
    (loopExitEmptyPK_300_placed_wpX (sp' := sp') (sret := sret) (len := len) (ptr0 := ptr0)
      (vb := vb) (ptr := ptr) (bs := []) (m := m) (res := res)
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr hres)
  unfold sliceCursorAt; apply entails_of_eq; sep_ac_rfl

abbrev loopCheckPK_e4_cons_placed_cpsX :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.loopCheckPK_e4_cons_placed_cpsX

/-! ## 2. Tail Callee Blocks (`+0x120`, `+0x2ec`, `+0x324`) -/

set_option maxHeartbeats 800000 in
theorem decodeErrorFromPK_tail_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x324#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hkind : KindNoHeap (s.readReg64 .x8)) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ w0) ∗ memRegion (sp' + 456#64) 56 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyOf A.repAlloc (sp' + 312#64) mErr)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs none)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 804#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' decodeErrorHookStackX (skipFieldStackX 100)
  have hfit_from : FitsEnv M lim st DecodeErrorFromEnv :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_decodeErrorFrom) hfit
  simp only [hstack, memRegion56_split40 sp', sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 261) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st
    (sp' + 448#64, s.readReg64 (Reg.gpr 8#5), st) hFrom
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hcl1
    (ret_pc := (blkPl_111).base + 816#64) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (T := ((sp' + 448#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (sp' + 456#64) 40 ∗
      stackAt sp' decodeErrorHookStackX)
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)) ∧ FitsEnv M lim st DecodeErrorFromEnv)
    (by
      simp only [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack,
        decodeErrorHookStackX, hsp_eq, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨hkind, hfit_from⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23,
       by simpa [arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x21,
       by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  refine SepWPp.pure_pre fun ⟨hx0_ne, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  refine sepWPp_end_noPanic_placed hcl2 ?_
  apply sepWP_seg_111; intro _m_strip2
  wp_steps
  refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp_all [State.spAligned, arm64_norm], hcl3, by simp_all [arm64_norm]⟩,
    evs, .done (SigTryFromErrTailEnv.of_decodeErrorFrom hevs), ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (preKeyLoopExitMem_err_intro (A.atState lim (M.stepEvents evs st) _)
      sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 mErr)
  simp only [RustCliAllocBudget.atState, wirePreKeyOf_mk_eq, decodeErrorAtStackLen_mk_eq]
  rw [← memRegion48_16_eq_64 sp']
  apply entails_of_eq; simp only [hstack, decodeErrorHookStackX, hsp_eq, arm64_norm]; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem decodeVarintSlowPK_tail_placed_cpsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x2ec#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_111).base + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 748#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' dk_varintSlowStackX (skipFieldStackX 100)
  have hfit_slow : FitsEnv M lim st (DecodeVarintSlowEnv bs) :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_decodeVarintSlow) hfit
  unfold sliceCursorAt; simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 293) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st
    (sp' + 440#64, sp' + 296#64, ptr, bs, st) hSlow
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 756#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ ptr) ∗
      ((sp' + 296#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      stackAt sp' dk_varintSlowStackX)
    (φ := bs.length < 2 ^ 64 ∧ FitsEnv M lim st (DecodeVarintSlowEnv bs))
    (by
      simp only [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack,
        dk_varintSlowStackX, hsp_eq, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨by omega, hfit_slow⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  have h1_slow : SigTryFromErrTailEnv evs := SigTryFromErrTailEnv.of_decodeVarintSlow hevs
  have hevs' : evs = match varintSlow bs with | some _ => [] | none => _ := hevs
  rw [decodeVarint_eq_varintSlow bs] at hevs' ⊢
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩; rw [hd] at hevs'; dsimp only [Option.map] at hevs' ⊢
    subst hevs'
    simp only [M.stepEvents_nil]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub]; simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 340#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl3 => ?_
    refine SepWPp.mono_pre ?_
      (hcont key rest _ hd (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp only [arm64_norm]))
    apply entails_of_eq
    unfold sliceCursorAfter; simp only [hstack, dk_varintSlowStackX, hsp_eq, arm64_norm]; sep_ac_rfl
  | none =>
    dsimp only [Option.map]; rw [hnone hd]
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_1, hx1_ne⟩ => ?_
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine sepWPp_end_noPanic_placed hcl2 ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
      evs, .done h1_slow, ?_⟩
    simp only [arm64_norm]
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 296#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length)) (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left hpair)
        (preKeyLoopExitMem_err_loopCaps_intro (A.atState lim (M.stepEvents evs st) _)
          sp' ptr bs (s2.readReg64 (Reg.gpr 1#5)) hx1_ne 0 caps m))
    simp only [RustCliAllocBudget.atState, wirePreKeyLoopCapsOf_mk_eq, decodeErrorAtStackLen_mk_eq]
    apply entails_of_eq; simp only [hstack, dk_varintSlowStackX, hsp_eq, arm64_norm]; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem decodeVarintSlicePK_tail_placed_cpsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x120#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32) (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_111).base + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 288#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 296#64 := hx28
  have h26 : s.readReg64 (Reg.gpr 26#5) = sp' + 304#64 := hx26
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' decodeVarintSliceStackX (skipFieldStackX 100)
  have hfit_v : FitsEnv M lim st (DecodeVarintSliceEnv bs) :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_decodeVarintSlice) hfit
  unfold sliceCursorAt; simp only [hstack, memRegion64_split24 sp', sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 76) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st (⟨sp' + 448#64, ptr, bs⟩, st) hvarint
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 296#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 448#64) 24 ∗ (ptr ↦ₛ bs) ∗ stackAt sp' decodeVarintSliceStackX)
    (φ := bs.length < 2 ^ 63 ∧ VarintSlicePre bs ∧ FitsEnv M lim st (DecodeVarintSliceEnv bs))
    (by
      simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, decodeErrorHookStackX,
        decodeVarintSliceStackX, hsp_eq, h1, h2, hx2_nat, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨by omega, hpre_slice, hfit_v⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  have h28_2 : s2.readReg64 (Reg.gpr 28#5) = sp' + 296#64 := by
    simpa [arm64_norm, h28] using hcs2.2.2.2.2.2.2.2.2.2.1
  have h26_2 : s2.readReg64 (Reg.gpr 26#5) = sp' + 304#64 := by
    simpa [arm64_norm, h26] using hcs2.2.2.2.2.2.2.2.1
  dsimp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  have h1_slice : SigTryFromErrTailEnv evs := SigTryFromErrTailEnv.of_decodeVarintSlice hevs
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩; dsimp only [varintSliceResultAt]
    have hevs_nil : evs = [] := by
      rw [hevs]; unfold decodeVarintSliceEvents; rw [hd]
    subst hevs_nil
    simp only [M.stepEvents_nil]
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
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64,
        Nat.mod_eq_of_lt hsub64, decide_eq_false_iff_not]; omega
    rw [pointsTo64_zero_split32 (sp' + 448#64)]; simp only [sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 340#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps; wp_if hcc
    · exfalso; rw [← hrest] at hcc; exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl3 => ?_
      refine SepWPp.mono_pre ?_
        (hcont key rest _ hd (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
           by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
           by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
           by simpa [arm64_norm] using hregs2.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp only [arm64_norm]))
      have hscr := scratch24_ok_entails_memRegion64 sp' key (BitVec.ofNat 64 (bs.length - rest.length))
      unfold sliceCursorAfter; simp only [← hrest, hsub_bv]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr)))
      apply entails_of_eq
      simp only [hstack, decodeErrorHookStackX, decodeVarintSliceStackX, hsp_eq, arm64_norm]
      sep_ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [hnone hd, pointsTo64_one_split32 (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm]
    refine SepWPp.exists_pre fun e => SepWPp.pure_pre fun he_ne => ?_
    refine sepWPp_end_noPanic_placed hcl2 ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
      evs, .done h1_slice, ?_⟩
    simp only [arm64_norm]
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 296#64) ptr (BitVec.ofNat 64 bs.length)
    have hscr := scratch24_err_entails_memRegion64 sp' e
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (Entails.trans
        (sepConj_mono hpair (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
        (preKeyLoopExitMem_err_loopCaps_intro (A.atState lim (M.stepEvents evs st) _)
          sp' ptr bs e he_ne 0 caps m))
    simp only [RustCliAllocBudget.atState, wirePreKeyLoopCapsOf_mk_eq, decodeErrorAtStackLen_mk_eq]
    apply entails_of_eq
    simp only [hstack, decodeErrorHookStackX, decodeVarintSliceStackX, hsp_eq, arm64_norm]
    sep_ac_rfl

/-! ## 3. Inlined `decode_varint` and `decodeKeyPK_placed_cpsX` (`+0x0f4..+0x16c`) -/

set_option maxHeartbeats 800000 in
theorem decodeVarintMultiPK_placed_cpsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x10c#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hne : bs ≠ []) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_111).base + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 268#64 at hpc
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]; omega
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 288#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (by apply entails_of_eq; sep_ac_rfl)
      (decodeVarintSlicePK_tail_placed_cpsX hvarint hfit
        (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simpa [arm64_norm] using hx28) (by simpa [arm64_norm] using hx26)
        (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr) hlen (Or.inl hlen11) hcont hnone)
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]
      omega
    have hlast_addr : ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
        ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]; exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]; bv_omega
    have hlast_sub1 : ptr + BitVec.ofNat 64 (bs.length - 1) =
        ptr + BitVec.ofNat 64 bs.length - 1#64 := by
      rw [← hlast_addr]; bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [sepConj_assoc]
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
        (mid := (blkPl_111).base + 288#64) ?_
      apply sepWP_seg_111; intro _m_strip
      wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre ?_
        (decodeVarintSlicePK_tail_placed_cpsX hvarint hfit
          (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simpa [arm64_norm] using hx28) (by simpa [arm64_norm] using hx26)
          (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1 (by simpa [arm64_norm] using htr) hlen (Or.inr ⟨hne, hlast⟩) hcont hnone)
      apply entails_of_eq; unfold sliceCursorAt
      simp only [arm64_norm]; rw [pointsToBytes_split_last ptr bs hne, hlast_sub1]; sep_ac_rfl
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [sepConj_assoc]
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
        (mid := (blkPl_111).base + 748#64) ?_
      apply sepWP_seg_111; intro _m_strip
      wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre ?_
        (decodeVarintSlowPK_tail_placed_cpsX hSlow hfit
          (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1 (by simpa [arm64_norm] using htr) hlen hcont hnone)
      apply entails_of_eq; unfold sliceCursorAt
      simp only [arm64_norm]; rw [pointsToBytes_split_last ptr bs hne, hlast_sub1]; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem decodeVarintPK_inlined_placed_cpsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (blkPl_111).base + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr (b0 :: bs1) rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res)
        (noPanicQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 244#64 at hpc
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 296#64 := hx28
  have h26 : s.readReg64 (Reg.gpr 26#5) = sp' + 304#64 := hx26
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hb0_ult : b0.ult 128#8 = true := by simp [BitVec.ult]; omega
    have hbit63 : ((!(BitVec.signExtend 64 b0 >>> 56).ult 128#64) == true) = false := by
      revert hb0_ult; bv_bits
    have hbit63' := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 : BitVec.ofNat 64 (bs1.length + 1) - 1#64 = BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]; bv_omega
    unfold sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 340#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr) (by simp only [hse, arm64_norm]))
    apply entails_of_eq; unfold sliceCursorAfter; rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm]; sep_ac_rfl
  · have hb0_ult : b0.ult 128#8 = false := by simp [BitVec.ult]; omega
    have hbit63 : ((!(BitVec.signExtend 64 b0 >>> 56).ult 128#64) == true) = true := by
      revert hb0_ult; bv_bits
    have hbit63' := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 268#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (decodeVarintMultiPK_placed_cpsX hSlow hvarint hfit
        (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simpa [arm64_norm] using hx28) (by simpa [arm64_norm] using hx26)
        (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr) (List.cons_ne_nil b0 bs1) hlen hcont hnone)
    apply entails_of_eq; unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]; simp only [arm64_norm]; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem decodeKeyPK_tail_placed_cpsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (blkPl_111).base + 0x154#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = key)
    (hcont : ∀ (tag : Nat) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (blkPl_111).base + 0x170#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : decodeKey bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 340#64 at hpc
  have h24 : s.readReg64 (Reg.gpr 24#5) = key := hx24
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h27 : s.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := hregs.x27
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have hres := hnone hdk; subst hres; have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (wirePreKeyLoopCapsOf_entails_of A.repAlloc (sp' + 312#64) caps m)))))) ?_
    rw [memRegion64_split_448_456_464 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 804#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorFromPK_tail_placed_wpX hFrom (w0 := w0) (mErr := m) hfit
        (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr) (by simp only [KindNoHeap, arm64_norm]))
    refine Entails.trans ?_
      (decodeKeyPK_err_entailsX (A.atState lim st _) sp' ptr w0 key bs rest m)
    simp only [RustCliAllocBudget.atState, wirePreKeyOf_mk_eq]
    apply entails_of_eq; sep_ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hres := hnone hdk; subst hres
      have hge6 : 6 ≤ key.toNat % 8 := by
        match hk : key.toNat % 8 with
        | 0 | 1 | 2 | 3 | 4 | 5 => simp [WireType.ofNat?, hk] at hwt
        | n + 6 => omega
      have hbcs := key_and7_ule6_of_ge key hge6
      refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (wirePreKeyLoopCapsOf_entails_of A.repAlloc (sp' + 312#64) caps m)))))) ?_
      rw [memRegion64_split_448_456_464 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
        (mid := (blkPl_111).base + 804#64) ?_
      apply sepWP_seg_111; intro _m_strip
      wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre ?_
        (decodeErrorFromPK_tail_placed_wpX hFrom (w0 := w0) (mErr := m) hfit
          (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1 (by simpa [arm64_norm] using htr) (by simp only [KindNoHeap, arm64_norm]))
      refine Entails.trans ?_
        (decodeKeyPK_err_entailsX (A.atState lim st _) sp' ptr w0 (key &&& 7#64) bs rest m)
      simp only [RustCliAllocBudget.atState, wirePreKeyOf_mk_eq]
      apply entails_of_eq; sep_ac_rfl
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := by
        match hk : key.toNat % 8 with
        | 0 | 1 | 2 | 3 | 4 | 5 => omega
        | n + 6 => simp [WireType.ofNat?, hk] at hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hres := hnone hdk; subst hres; have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (wirePreKeyLoopCapsOf_entails_of A.repAlloc (sp' + 312#64) caps m)))))) ?_
        rw [memRegion64_split8 sp', ProofLib.memRegion_eight (sp' + 448#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_pre fun w0 => ?_
        refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
          (mid := (blkPl_111).base + 804#64) ?_
        apply sepWP_seg_111; intro _m_strip
        wp_steps
        refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
        refine SepWPp.mono_pre ?_
          (decodeErrorFromPK_tail_placed_wpX hFrom (w0 := w0) (mErr := m) hfit
            (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
             by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
             by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
             by simpa [arm64_norm] using hregs.x19⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hcl1 (by simpa [arm64_norm] using htr) (by simp only [KindNoHeap, arm64_norm]))
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 296#64) ptr bs rest))) ?_
        apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
          (mid := (blkPl_111).base + 368#64) ?_
        apply sepWP_seg_111; intro _m_strip
        wp_steps
        refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        refine SepWPp.mono_pre (by apply entails_of_eq; sep_ac_rfl)
          (hcont (key.toNat / 8) wt _ hdk (by simp only [arm64_norm])
            (by simp only [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
             by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
             by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
             by simpa [arm64_norm] using hregs.x19⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hcl1 (by simpa [arm64_norm] using htr)
            (by simpa only [arm64_norm] using hand7_eq)
            (by simpa only [arm64_norm] using htag_eq))

theorem decodeKeyPK_placed_cpsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))))
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ (tag : Nat) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (blkPl_111).base + 0x170#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr (b0 :: bs1) rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res)
        (noPanicQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res)
      (noPanicQp s0) :=
  decodeVarintPK_inlined_placed_cpsX hSlow hvarint hfit hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hlen
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx24_1 =>
      decodeKeyPK_tail_placed_cpsX hFrom hfit hdv hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx24_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk) hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
