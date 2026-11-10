/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.KeyAndScalar
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkip
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkipBudget
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKey
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKeyBudget
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SignedPreKeyRecordStructure::decode` Scalar Field Branches

`RustCliAllocBudget`-threaded relocatable proofs for tag 1 (`id : uint32`) and tag 5
(`timestamp : fixed64`) on Block `562`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.KeyAndScalarBudget

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
  (SpkLoopRegs spkErr16_pack40 spkErrBytes_pack40 spkMemRegion48_unpack16 spkMemRegion48_unpackBytes
   spkOff_converge spkOff_latch spkOff_pushCall spkOff_pushTag1 spkOff_tag1 spkOff_tag1BadWt
   spkOff_tag1FromRet spkOff_tag1Ret spkOff_tag5 spkOff_tag5BadWt spkOff_tag5Eof
   spkOff_tag5FromCommon spkStructAt_split_id spkStructAt_split_timestamp spkStructOf
   spk_le64_eq_pair32 spk_pointsToBytes8_cons spk_sub8_ge8)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (DecodeErrorFromEnv DecodeVarint2Env SignedHooksPlaced SignedPortDepsPlaced SpkCaps
   SpkErrTailEnv SpkLoopBoundedEnv decodeErrorFromBudgetSpec decodeVarint2BudgetSpec
   decodeVarint2Events fitsEnv_spkLoop_errTail)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkipBudget
  (spkAdvanceToLatch_placed_prog spkLoopRegs_of_calleeSaved)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
  (SpkGhostCapsMatch noPanicQp sepWPp_call_budget_lscro sepWPp_frame_noPanic
   spkAdvanceCursor_placed spkAfterVarintCapsMem spkAfterVarintCapsMemAt spkConvergePostPlaced
   spkConvergePostPlaced_append_prefix spkConvergePostPlaced_skipStep spkLoopCapsMem
   spkLoopCapsMemAt spkStructAt_entails_loopCapsOf spkStructLoopCapsOf
   spkStructLoopCapsOf_entails_of spkStructLoopCapsOf_mono spk_decodeErrorFrom_placed_ok
   spk_decodeVarint6_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTailsBudget
  (pushCall_648_placed_wp sepWPp_mono_post tag5FromPush_608_placed_wp)
attribute [local arm64_norm] BitVec.toNat_zero

/-! ### Local Helpers -/

private theorem sliceCursorAt_entails_memRegion (sp' ptr : BitVec 64) (bs : List (BitVec 8)) :
    sliceCursorAt sp' ptr bs ⊢ memRegion sp' 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAt
  rw [← sepConj_assoc]
  exact sepConj_mono_left (Wire.pointsTo64_pair_entails_memRegion16 sp' ptr (BitVec.ofNat 64 bs.length))

private theorem spkErrBytes_pack_pre (sp' k : BitVec 64) (b0 b1 : BitVec 8) (rest : SepProp) :
    ((sp' + 112#64) ↦₆₄ k) ∗ ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
      memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32 ∗ rest ⊢
    ((sp' + 112#64) ↦₆₄ k) ∗ memRegion (sp' + 120#64) 40 ∗ rest := by
  have hp :
      ((sp' + 112#64) ↦₆₄ k) ∗ ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
        memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32 ∗ rest =
      (((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
        memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32) ∗
        ((sp' + 112#64) ↦₆₄ k) ∗ rest := by
    ac_rfl
  rw [hp]
  refine Entails.trans (sepConj_mono_left (spkErrBytes_pack40 sp' b0 b1)) ?_
  apply entails_of_eq; ac_rfl

private theorem tag5Short_pack (subStack : Nat) (A : RustAlloc) (sp' x19 ptr1 : BitVec 64)
    (caps : SpkCaps) (short : List (BitVec 8)) (n : ℕ) (m : SignedPreKeyRecordStructure) :
    (sp' ↦₆₄ ptr1) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 short.length) ∗ (ptr1 ↦ₛ short) ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗
      spkStructLoopCapsOf A sp' n caps m ∗ memRegion x19 88 ∗ A.pool ∗
      stackAt sp' subStack ⊢
    memRegion (sp' + 112#64) 48 ∗ spkStructOf A sp' m ∗ memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion x19 88 ∗ (ptr1 ↦ₛ short) ∗ A.pool ∗
      stackAt sp' subStack := by
  have hp :
      (sp' ↦₆₄ ptr1) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 short.length) ∗ (ptr1 ↦ₛ short) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗
        spkStructLoopCapsOf A sp' n caps m ∗ memRegion x19 88 ∗ A.pool ∗
        stackAt sp' subStack =
      ((sp' ↦₆₄ ptr1) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 short.length)) ∗
        spkStructLoopCapsOf A sp' n caps m ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr1 ↦ₛ short) ∗ A.pool ∗
        stackAt sp' subStack := by
    ac_rfl
  rw [hp]
  refine Entails.trans
    (sepConj_mono (Wire.pointsTo64_pair_entails_memRegion16 sp' ptr1 (BitVec.ofNat 64 short.length))
      (sepConj_mono_left (spkStructLoopCapsOf_entails_of A sp' n caps m))) ?_
  apply entails_of_eq; ac_rfl

private theorem tag5_cap_peel (a1 a2 a3 a4 a5 a6 : SepProp) (p : Prop) (rest : SepProp) :
    a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ ⌜p⌝ ∗ rest =
      ⌜p⌝ ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ rest := by
  ac_rfl

/-! ### Budget-threaded proofs -/

theorem spkLoopRegs_of_unchanged {s0 s s1 : State} {sp' x19 : BitVec 64} (h : SpkLoopRegs s0 sp' x19 s)
    (hu : s1.sp = s.sp ∧ s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) ∧
      s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
      s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧ s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
      s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧ s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5)) :
    SpkLoopRegs s0 sp' x19 s1 :=
  ⟨hu.1.trans h.sp, hu.2.1.trans h.x29, hu.2.2.1.trans h.x24, hu.2.2.2.1.trans h.x19_eq,
   ⟨hu.2.2.2.2.1.trans h.saved.x25, hu.2.2.2.2.2.1.trans h.saved.x26,
    hu.2.2.2.2.2.2.1.trans h.saved.x27, hu.2.2.2.2.2.2.2.trans h.saved.x28⟩⟩

theorem pushTag1_492_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr err : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_pushTag1) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx1 : s.readReg64 .x1 = err) (hnz : err ≠ 0#64) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗ spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s ∗
        stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29; have h1 : s.readReg64 (Reg.gpr 1#5) = err := hx1
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_pushCall) ?_
  wp_steps_sync_pool ((blkPl_562).base + spkOff_pushCall)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (pushCall_648_placed_wp (st := st) (rem := rem) (caps := caps) hH
      (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr) (err := err) (mErr := mErr) (bs := bs)
      (out := out) herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm]))
      (by simp [h29, arm64_norm]) hnz (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcrl1 (by simp [htr, arm64_norm]) hFit)
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq; simp only [hsp_eq, h29, arm64_norm]; try ac_rfl

theorem tag1BadWt_460_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag1BadWt) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = w0) (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hcall := spk_decodeErrorFrom_placed_ok hH; have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29; have h0 : s.readReg64 (Reg.gpr 0#5) = w0 := hx0
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpackBytes sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun b0 => Wire.SepWPp.exists_pre fun b1 => sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps_sync_pool (lsmpl.base 261)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (spkErrBytes_pack_pre sp' (BitVec.ofNat 64 (2 ^ 63 + 6)) (w0.setWidth 8) 0#8 _)) ?_
  refine sepWPp_call_budget_lscro (sp' + 112#64, BitVec.ofNat 64 (2 ^ 63 + 6), st) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_tag1FromRet) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ BitVec.ofNat 64 (2 ^ 63 + 6)) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool lim st _ ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap (BitVec.ofNat 64 (2 ^ 63 + 6)) ∧ FitsEnv M lim st DecodeErrorFromEnv)
    (by simp [decodeErrorFromBudgetSpec, hsp_eq, h29, arm64_norm]; rfl)
    ⟨rfl, by simp [KindNoHeap], fitsEnv_spkLoop_errTail (fun _ => SpkErrTailEnv.of_decodeErrorFrom) hFit⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 := spkLoopRegs_of_calleeSaved hsp2 hcs2 (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm]))
  have hsp2_eq := hregs2.sp; dsimp only [decodeErrorFromBudgetSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs₁ => ?_
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hevs1_eq : evs₁ = rustAllocEvents 72 8 := hevs₁
  subst hevs1_eq
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushTag1) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (pushTag1_492_placed_wp (st := st) (rem := rem) (caps := caps) hH
      (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr) (err := s2.readReg64 .x0)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (spkLoopRegs_of_unchanged hregs2 (by simp [arm64_norm]))
      (by simp [arm64_norm]) herr_nz
      (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
      hcrl3 (by simp [htr2, htr, arm64_norm]) hFit)
  apply entails_of_eq; rw [hstack]
  simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, hsp_eq, hsp2_eq, arm64_norm]
  try ac_rfl

theorem tag1_276_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps} {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure} {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63) (hrem : rest.length < rem)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag1) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps))
    (hlatch : ∀ (v : BitVec 32) (rest2 : List (BitVec 8)) (s3 : State), mergeUint32 wt rest = some (v, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running → SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem → s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopCapsMem (A.atState lim st s3) sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) caps rest2 { m with id := v })
        (spkConvergePostPlaced A lim st rest2.length caps s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (noPanicQp s0))
    (hnone : mergeUint32 wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintCapsMem (A.atState lim st s) sp' x19 ptr caps bs rest bs.length m)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintCapsMem spkAfterVarintCapsMemAt; refine spkAdvanceCursor_placed hsuf ?_; let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  have hcall := spk_decodeVarint6_placed_ok d
  have hsp_eq := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  cases wt with
  | varint =>
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
    have hstack := stackAt_sub_split sp' CryptoVerification.SpqrV1.Varint.decodeVarint2Stack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100)
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 559) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    refine sepWPp_call_budget_lscro (⟨sp' + 104#64, sp', ptr1, rest⟩, st) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_tag1Ret) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
      (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗ A.pool lim st s ∗ stackAt sp' CryptoVerification.SpqrV1.Varint.decodeVarint2Stack)
      (φ := sp' + 104#64 = sp' + 104#64 ∧ rest.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env rest))
      (by simp [decodeVarint2BudgetSpec, RustCliAllocBudget.pool_writeReg64,
        RustCliAllocBudget.pool_setPC, hsp_eq, h29, arm64_norm])
      ⟨rfl, hlen_rest, fitsEnv_spkLoop_errTail (fun _ => SpkErrTailEnv.of_decodeVarint2) hFit⟩
      (by
        have hloop_eq : spkStructLoopCapsOf (A.atState lim st s) sp' bs.length caps m =
            spkStructLoopCapsOf A.repAlloc sp' bs.length caps m := rfl
        rw [hloop_eq]
        dsimp only [RustCliAllocBudget.atState]
        rw [hstack]; sep_focus)
      fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
    have hregs2 : SpkLoopRegs s0 sp' x19 s2 := spkLoopRegs_of_calleeSaved hsp2 hcs2 (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm]))
    clear hsp2 hcs2; have hsp2_eq := hregs2.sp
    have hsp'_align : (sp' &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp_eq] using hsp
    dsimp only [decodeVarint2BudgetSpec]
    cases hdv : decodeVarint rest with
    | some p =>
      rcases p with ⟨v64, rest2⟩
      have hm : mergeUint32 .varint rest = some (v64.setWidth 32, rest2) := by unfold mergeUint32; simp [hdv]
      obtain ⟨k2, hkl2, hr2⟩ := mergeUint32_suffix hm
      have hle_r2 : rest2.length ≤ rest.length := by rw [hr2, List.length_drop]; omega
      have hlt_rem : rest2.length < rem := Nat.lt_of_le_of_lt hle_r2 hrem
      have hle2 : rest2.length ≤ bs.length := Nat.le_trans hle_r2 hle_bs
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun evs => ?_
      refine Wire.SepWPp.pure_pre fun ⟨hx0_0, hx1_v⟩ => Wire.SepWPp.pure_pre fun htr2 => ?_
      simp only [sepConj_pure_left_comm, sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun hevs => ?_
      have hevs0 : evs = [] := by rw [hevs]; simp [decodeVarint2Events, hdv]
      subst hevs0
      dsimp only [AllocCostModel.stepEvents, List.foldl]
      have hw0_0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0; have hw1_v : s2.readReg64 (Reg.gpr 1#5) = v64 := hx1_v
      refine Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spkStructLoopCapsOf_mono A.repAlloc sp' m hle2))))))) ?_
      unfold spkStructLoopCapsOf; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
      refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun ⟨hg, hc⟩ => ?_
      rw [spkStructAt_split_id A.repAlloc g sp' m]; simp only [sepConj_assoc]
      refine sepWPp_mono_post
        (spkConvergePostPlaced_skipStep A lim st hlt_rem s0 sp' x19 ptr1 rest out) ?_
      refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_latch) ?_
      wp_steps_sync_pool ((blkPl_562).base + spkOff_latch)
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
      have hid : ((sp' + 96#64) ↦₃₂ v64.setWidth 32) ∗
          (vecU8At A.repAlloc (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗ vecU8At A.repAlloc (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
            vecU8At A.repAlloc (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗ ((sp' + 88#64) ↦₆₄ m.timestamp) ∗ memRegion (sp' + 100#64) 4) ⊢
          spkStructLoopCapsOf A.repAlloc sp' rest2.length caps { m with id := v64.setWidth 32 } := by
        rw [← spkStructAt_split_id A.repAlloc g sp' { m with id := v64.setWidth 32 }]
        exact spkStructAt_entails_loopCapsOf A.repAlloc g sp' rest2.length caps _ hg hc
      refine spkAdvanceToLatch_placed_prog ⟨k2, hkl2, hr2⟩
        (hlatch (v64.setWidth 32) rest2 _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (spkLoopRegs_of_unchanged hregs2 (by simp [arm64_norm]))
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align) hcrl3 (by simp [htr2, htr, arm64_norm])) ?_
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hid))))
      apply entails_of_eq; dsimp only [ptr1]; rw [hstack]; simp only [hsp_eq, hsp2_eq, hw1_v, arm64_norm]; ac_rfl
    | none =>
      have hm : mergeUint32 .varint rest = none := by unfold mergeUint32; simp [hdv]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun evs₁ => ?_
      refine Wire.SepWPp.pure_pre fun hx0_1 => Wire.SepWPp.pure_pre fun htr2 => ?_
      rw [sepConj_pure_left_comm]
      refine Wire.SepWPp.pure_pre fun hevs₁ => ?_
      simp only [sepConj_pure_left_comm, sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
      have hevs1_eq : evs₁ = rustAllocEvents 72 8 := by rw [hevs₁]; simp [decodeVarint2Events, hdv]
      subst hevs1_eq
      have hw0_1 : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1; have hbeq : (s2.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_nz
      refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushTag1) ?_
      wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
      refine Wire.SepWPp.mono_pre ?_
        (pushTag1_492_placed_wp (st := st) (rem := rem) (caps := caps) hH
          (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr1) (err := s2.readReg64 .x1) (mErr := m) (bs := rest)
          (out := out) (hnone hm) (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (spkLoopRegs_of_unchanged hregs2 (by simp [arm64_norm]))
          (by simp [arm64_norm]) hx1_nz (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simp [htr2, htr, arm64_norm]) hFit)
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spkStructLoopCapsOf_entails_of A.repAlloc sp' bs.length caps m))))))))) ?_
      apply entails_of_eq; rw [hstack]
      simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
  | sixtyFourBit | lengthDelimited | startGroup | endGroup | thirtyTwoBit =>
    have hm : out = none := hnone (by unfold mergeUint32; simp)
    have hcur := sliceCursorAt_entails_memRegion sp' ptr1 rest; have hof := spkStructLoopCapsOf_entails_of A.repAlloc sp' bs.length caps m
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = _ := hx0
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag1BadWt) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    refine Wire.SepWPp.mono_pre ?_
      (tag1BadWt_460_placed_wp (st := st) (rem := rem) (caps := caps) hH
        (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr1) (w0 := s.readReg64 (Reg.gpr 0#5)) (mErr := m)
        (bs := rest) (out := out) hm (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simp [htr, arm64_norm]) hFit)
    dsimp only [RustCliAllocBudget.atState]
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
    refine Entails.trans (sepConj_mono hcur (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))) ?_; apply entails_of_eq; ac_rfl

theorem tag5BadWt_564_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5BadWt) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = w0) (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29; have h0 : s.readReg64 (Reg.gpr 0#5) = w0 := hx0
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpackBytes sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun b0 =>
    Wire.SepWPp.exists_pre fun b1 => sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5FromCommon) ?_
  wp_steps_sync_pool ((blkPl_562).base + spkOff_tag5FromCommon)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (tag5FromPush_608_placed_wp (st := st) (rem := rem) (caps := caps) hH
      (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr) (kind := BitVec.ofNat 64 (2 ^ 63 + 6))
      (mErr := mErr) (bs := bs) (out := out) herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm])) (by simp [KindNoHeap])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcrl1 (by simp [htr, arm64_norm]) hFit)
  refine Entails.trans ?_
    (spkErrBytes_pack_pre sp' (BitVec.ofNat 64 (2 ^ 63 + 6)) (w0.setWidth 8) 1#8 _)
  simp only [h29, arm64_norm]; apply entails_of_eq; ac_rfl

theorem tag5Eof_600_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5Eof) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ spkStructOf A.repAlloc sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 =>
    sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5FromCommon) ?_
  wp_steps_sync_pool ((blkPl_562).base + spkOff_tag5FromCommon)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (tag5FromPush_608_placed_wp (st := st) (rem := rem) (caps := caps) hH
      (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr) (kind := BitVec.ofNat 64 (2 ^ 63 + 7))
      (mErr := mErr) (bs := bs) (out := out) herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm])) (by simp [KindNoHeap])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcrl1 (by simp [htr, arm64_norm]) hFit)
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq; simp only [hsp_eq, h29, arm64_norm]; try ac_rfl

private theorem tag5_short_step [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr1 : BitVec 64} {n : ℕ} {short : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure} (hm : out = none) (hlt : short.length < 8)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (h0 : s.readReg64 (Reg.gpr 0#5) = 1#64) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAt sp' ptr1 short ∗ ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗
        spkStructLoopCapsOf A.repAlloc sp' n caps m ∗ memRegion x19 88 ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr1 short out) (noPanicQp s0) := by
  have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hult : (BitVec.ofNat 64 short.length).ult 8#64 = true := by
    simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : short.length < 2 ^ 64)]; omega
  unfold sliceCursorAt; simp only [sepConj_assoc]; refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5Eof) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  have hp := tag5Short_pack (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) (A.atState lim st s) sp' x19 ptr1 caps short n m
  have hloop_eq : spkStructLoopCapsOf (A.atState lim st s) sp' n caps m = spkStructLoopCapsOf A.repAlloc sp' n caps m := rfl
  have hof_eq : spkStructOf (A.atState lim st s) sp' m = spkStructOf A.repAlloc sp' m := rfl
  rw [hloop_eq, hof_eq] at hp
  dsimp only [RustCliAllocBudget.atState] at hp
  refine Wire.SepWPp.mono_pre ?_
    (tag5Eof_600_placed_wp (st := st) (rem := rem) (caps := caps) hH
      (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := short) (out := out) hm
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm]))
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]) hFit)
  simpa only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm] using hp

theorem tag5_176_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure} (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63) (hrem : rest.length < rem)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps))
    (hlatch : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (s3 : State), mergeFixed64 wt rest = some (v, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running → SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem → s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopCapsMem (A.atState lim st s3) sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) caps rest2 { m with timestamp := v })
        (spkConvergePostPlaced A lim st rest2.length caps s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (noPanicQp s0))
    (hnone : mergeFixed64 wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintCapsMem (A.atState lim st s) sp' x19 ptr caps bs rest bs.length m)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintCapsMem spkAfterVarintCapsMemAt; refine spkAdvanceCursor_placed hsuf ?_; let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  cases wt with
  | sixtyFourBit =>
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
    by_cases hlt8 : rest.length < 8
    · exact tag5_short_step hH (hnone (by
        rcases rest with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
          (simp [mergeFixed64] at hlt8 ⊢; try omega))) hlt8 hpc hrun hregs h0 hsp hcrl htr hFit
    rcases rest with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest2⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hlt8; done)
    let restFull := b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest2
    have hm : mergeFixed64 .sixtyFourBit restFull = some (le64 b0 b1 b2 b3 b4 b5 b6 b7, rest2) := rfl
    have hge8 : 8 ≤ restFull.length := by simp [restFull]
    have hlt_rem : rest2.length < rem := by simp only [List.length_cons] at hrem; omega
    have hle2 : rest2.length ≤ bs.length := by simp only [List.length_cons] at hle_bs; omega
    have ⟨hcc_ok, hsub8⟩ := spk_sub8_ge8 hge8 hlen_rest
    have hult_false : (BitVec.ofNat 64 restFull.length).ult 8#64 = false := by simpa using hcc_ok
    have hult_false' : (BitVec.ofNat 64 (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)).ult 8#64 = false := by
      simpa only [restFull, List.length_cons] using hult_false
    have hsub8' : BitVec.ofNat 64 restFull.length - 8#64 = BitVec.ofNat 64 rest2.length := by rw [hsub8]; congr 1
    refine Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spkStructLoopCapsOf_mono A.repAlloc sp' m hle2))))) ?_
    unfold spkStructLoopCapsOf sliceCursorAt; rw [spk_pointsToBytes8_cons ptr1 b0 b1 b2 b3 b4 b5 b6 b7 rest2, spk_le64_eq_pair32 b0 b1 b2 b3 b4 b5 b6 b7]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => ?_; rw [tag5_cap_peel]; refine Wire.SepWPp.pure_pre fun ⟨hg, hc⟩ => ?_
    rw [spkStructAt_split_timestamp A.repAlloc g sp' m]; simp only [sepConj_assoc]
    refine sepWPp_mono_post
      (spkConvergePostPlaced_skipStep A lim st hlt_rem s0 sp' x19 ptr1 restFull out) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_latch) ?_
    wp_steps_sync_pool ((blkPl_562).base + spkOff_latch)
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    have h8take : (ptr1 ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) = (ptr1 ↦ₛ restFull.take 8) := by
      have hnil := (spk_pointsToBytes8_cons ptr1 b0 b1 b2 b3 b4 b5 b6 b7 []).symm; rw [pointsToBytes_nil, sepConj_emp, spk_le64_eq_pair32] at hnil; exact hnil
    have hl_app := hlatch (le64 b0 b1 b2 b3 b4 b5 b6 b7) rest2 _ hm (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm])) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
    have hlen_sub : restFull.length - rest2.length = 8 := by simp only [restFull, List.length_cons]; omega
    rw [hlen_sub, show rest2 = restFull.drop 8 from rfl] at hl_app
    refine Wire.SepWPp.mono_pre ?_ (sepWPp_frame_noPanic hl_app
      (fun sf Pf hqm => spkConvergePostPlaced_append_prefix A lim st rest2.length caps s0 sp' x19 ptr1 restFull 8 hge8 out sf Pf hqm))
    unfold spkLoopCapsMem spkLoopCapsMemAt sliceCursorAt
    have hts : ((sp' + 88#64) ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) ∗
        (vecU8At A.repAlloc (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗ vecU8At A.repAlloc (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
          vecU8At A.repAlloc (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4) ⊢
        spkStructLoopCapsOf A.repAlloc sp' rest2.length caps { m with timestamp := le64 b0 b1 b2 b3 b4 b5 b6 b7 } := by
      rw [← spkStructAt_split_timestamp A.repAlloc g sp' { m with timestamp := le64 b0 b1 b2 b3 b4 b5 b6 b7 }]
      exact spkStructAt_entails_loopCapsOf A.repAlloc g sp' rest2.length caps _ hg hc
    rw [h8take]; dsimp only [RustCliAllocBudget.atState, ptr1, restFull, List.drop, List.take]; simp only [hsp_eq, h29, List.length_cons, arm64_norm]
    erw [hsub8']
    set p1 := ptr + BitVec.ofNat 64 (bs.length - (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
    refine Entails.trans (Q := (((sp' + 88#64) ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) ∗
        (vecU8At A.repAlloc (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗ vecU8At A.repAlloc (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
          vecU8At A.repAlloc (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4)) ∗
      ((sp' ↦₆₄ (p1 + 8#64)) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 rest2.length) ∗ ((p1 + 8#64) ↦ₛ rest2) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗ memRegion x19 88 ∗ A.pool lim st _ ∗
        stackAt sp' (CryptoVerification.SpqrV1.Varint.skipField3Stack 100) ∗ (p1 ↦ₛ ([b0, b1, b2, b3, b4, b5, b6, b7] : List (BitVec 8)))))
      (by apply entails_of_eq; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)
      (Entails.trans (sepConj_mono_left hts)
        (by apply entails_of_eq; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl))
  | varint | lengthDelimited | startGroup | endGroup | thirtyTwoBit =>
    have hm : out = none := hnone (by unfold mergeFixed64; simp)
    have hcur := sliceCursorAt_entails_memRegion sp' ptr1 rest; have hof := spkStructLoopCapsOf_entails_of A.repAlloc sp' bs.length caps m
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = _ := hx0
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5BadWt) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    refine Wire.SepWPp.mono_pre ?_
      (tag5BadWt_564_placed_wp (st := st) (rem := rem) (caps := caps) hH
        (s0 := s0) (sp' := sp') (x19 := x19) (ptr := ptr1) (w0 := s.readReg64 (Reg.gpr 0#5)) (mErr := m)
        (bs := rest) (out := out) hm (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (spkLoopRegs_of_unchanged hregs (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]) hFit)
    dsimp only [RustCliAllocBudget.atState]
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
    refine Entails.trans (sepConj_mono hcur (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))) ?_; apply entails_of_eq; ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.KeyAndScalarBudget
