/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Exact-Capacity `PolynomialEncoder::encode [local#2]` (`Block 316`)

Proves the `VmPreserved` (`0`-allocation) and `RustCliAllocBudget M` `[LibsignalPlacement]`
contracts for `PolynomialEncoder::encode [local#2]` on `lsProg_316 H`, together with `vmTrackBudget`
for discharging unreachable reallocation paths and the `Block 426` callee bridges.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_289 blkPl_292 blkPl_316
   lsMemcpySym lsProg_289 lsProg_292 lsProg_316 lsmpl
   ls_subroutine_ok_of_block withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Varint
  (encodeRepeatedBytes encodeRepeatedStackOf repeatedBytesSliceAt)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialEncoderGhost protoPolynomialEncoderPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyEncoderPinnedGhost MsgEnc48CalleeSavedPlaced
   bs0_append_encodePolyEncoderMsg bs0_append_polyEncoderHeaderBytes
   bs_append_idx_of_ne_zero bs_append_idx_of_zero
   calleeSavedPreserved_setPC_placed
   encodePolyEncoderMsg encodePolyEncoderMsg_len_split idx_field_len_of_ne_zero
   msgEnc48CalleeSavedPlaced_setPC msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyEncoderElemsAt polyEncoderHeaderBytes polyEncoderHeaderBytes_len_bounds
   polyEncoderRestAt polynomialEncoderPBEncodedLen polynomialEncoderPBEncodedLen_le_msg_len
   satisfies_protoPolynomialEncoderPinnedAt_iff
   subroutine_ok_withLsCodeLoaded subroutine_ok_withMsgEnc48CSPlaced_placed_blk
   withMsgEnc48CSPlaced)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (blkPC_426 blkPl_426 cap_beq_len_false_of_lt_placed msgEnc48RepeatedStackOf_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents PoolPreserved
   RustCliAllocBudget VmPreserved rustAllocEvents rustCliAllocBudgetSpec
   rustCliReallocBudgetSpec rustReallocEvents zeroBudgetLimits)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents encodeVarintEvents_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encodeVarint4_det_placed_ok_of_doReserve encodeVarint4_fit_placed_ok_of_doReserve)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBudget
  (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
  (polynomialEncoderEncodedLenElemsOutSpec subroutine_ok_polyEncLenElemsOut_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (IsPolyEncoderEncodeEntryProg step_msg48rep_encode_varint_call_placed
   step_msg48rep_polyEncLen_call_placed step_polyEncoder_check_idx_placed
   step_polyEncoder_mov_x1_x19_68_placed step_polyEncoder_prep_polys_epilogue_placed
   step_polyEncoder_prep_pts_placed step_polyEncoder_prologue_placed
   step_polyEncoder_push_hdr_tag_placed step_polyEncoder_push_idx_tag_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf encodeRepeated59ExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
  (encode_repeated_2_59_placed_ok_of_callees
   step_msg48_encode_repeated59_exact_call_placed
   step_msg48_encode_repeated59_exact_tailcall_placed
   subroutine_ok_encodeRepeated59Exact_of_59_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyEncoderExactVmSpecOf subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyEncoderExactSpecOf)

private theorem bv_sub_add_lit (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Exact-Capacity (`0`-Allocation) `do_reserve` Elimination & `vmTrackBudget` -/

/-- Enforced `BudgetLimits` (`staticBytes = 1 > physCap = 0`) under which every allocation event
    is uninhabited (`¬ FitsEvent`), discharging unreachable `do_reserve_and_handle` calls along
    proven `0`-allocation paths without requiring allocator hooks. -/
def impossibleEnforcedLimits : BudgetLimits :=
  { staticCount := 0, staticBytes := 1, physCap := 0, enforced := true }

theorem not_fitsEvent_impossible {M : AllocCostModel} (st : M.σ) (ev : AllocEvent) :
    ¬ FitsEvent M impossibleEnforcedLimits st ev := by
  rintro ⟨_, _, hram, _⟩
  dsimp only [impossibleEnforcedLimits] at hram
  omega

theorem not_fitsEnv_doReserve_impossible {M : AllocCostModel} (st : M.σ) (x : DoReserveCall) :
    ¬ FitsEnv M impossibleEnforcedLimits st (DoReserveEnv x) := by
  rw [fitsEnv_doReserve_iff]
  dsimp only [doReserveEvents, rustAllocEvents, rustReallocEvents]
  split_ifs <;> rintro ⟨hev, _⟩ <;> exact not_fitsEvent_impossible st _ hev

theorem doReserve_impossible_ok [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel} (B : RustCliAllocBudget M) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack B impossibleEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨_, hpre⟩ := hpre
  dsimp only [doReserveSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1 with ⟨_, _, _, _, _, _, hfits⟩
  exact (not_fitsEnv_doReserve_impossible st x hfits).elim

private theorem poolPreserved_symm {s s' : State} (h : PoolPreserved s s') :
    PoolPreserved s' s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

private theorem vmPreserved_symm {s s' : State} (h : VmPreserved s s') :
    VmPreserved s' s :=
  h.symm

/-- `VmPreserved`-recording `RustCliAllocBudget M` wrapper sharing `A.live` and `A.block_valid`
    (`(vmTrackBudget A s_init).repAlloc = A.repAlloc`): at `impossibleEnforcedLimits` its `pool` is
    `⌜VmPreserved s_init s⌝`, and at `zeroBudgetLimits` its `pool` is `⌜PoolPreserved s_init s⌝`. -/
def vmTrackBudget {M : AllocCostModel} (A : RustCliAllocBudget M) (s_init : State) :
    RustCliAllocBudget M where
  pool := fun lim _ s =>
    if lim.enforced then ⌜VmPreserved s_init s⌝ else ⌜PoolPreserved s_init s⌝
  live := A.live
  block_valid := A.block_valid
  pool_transport := by
    intro lim _ s s' hvm
    cases lim.enforced
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hiff : PoolPreserved s_init s' = PoolPreserved s_init s :=
        propext ⟨fun h' => h'.trans (poolPreserved_symm hvm.1), fun hs => hs.trans hvm.1⟩
      rw [hiff]
    · simp only [↓reduceIte]
      have hiff : VmPreserved s_init s' = VmPreserved s_init s :=
        propext ⟨fun h' => h'.trans (vmPreserved_symm hvm), fun hs => hs.trans hvm⟩
      rw [hiff]
  pool_zero_transport := by
    intro _ s s' hp
    dsimp only [zeroBudgetLimits]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hiff : PoolPreserved s_init s' = PoolPreserved s_init s :=
      propext ⟨fun h' => h'.trans (poolPreserved_symm hp), fun hs => hs.trans hp⟩
    rw [hiff]

theorem encodeVarint4_fit_impossible_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (B : RustCliAllocBudget M) (H : LibsignalHooks) :
    subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack B impossibleEnforcedLimits)) :=
  encodeVarint4_fit_placed_ok_of_doReserve hres B impossibleEnforcedLimits H
    (doReserve_impossible_ok B)

theorem encode_repeated_2_59_exact_impossible_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    (B : RustCliAllocBudget M) {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_289 H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59ExactSpecOf resStack B impossibleEnforcedLimits)) :=
  subroutine_ok_encodeRepeated59Exact_of_59_placed
    (encode_repeated_2_59_placed_ok_of_callees hres
      (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
        (encodeVarint4_det_placed_ok_of_doReserve (by omega) B impossibleEnforcedLimits H
          (doReserve_impossible_ok B)))
      (doReserve_impossible_ok B)
      (spqr_hook_ok_of_mem hmc))

private theorem pool_step {M : AllocCostModel} (B : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s1 s2 : State} (h : VmPreserved s1 s2) :
    B.pool lim st s1 = B.pool lim st s2 :=
  (B.pool_of_vmPreserved h).symm

theorem sepWPp_mono {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Qf, Q1 sf Qf → Q2 sf Qf)
    (hQp : ∀ sf Pf, Qp1 sf Pf → Qp2 sf Pf)
    (h : SepWPp prog ret s P Q1 Qp1 oom) :
    SepWPp prog ret s P Q2 Qp2 oom := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨h1, h2, Qf, hmf, hq⟩ | ⟨hpan, Pf, hmf, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨h1, h2, Qf, hmf, hQ sf Qf hq⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hpan, Pf, hmf, hQp sf Pf hqp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

/-! ## 2. Budget-Threaded Exact-Capacity Stage Steppers for `Block 316` -/

private theorem step_pe_hdr_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_316 H) (lsmpl.base 401)
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_316 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (encA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (bs0 : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_316).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialEncoderPinnedAt B.repAlloc g encA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_316).base + 76#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_316 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt B.repAlloc encA g ptsElems polysElems ∗
          vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ polyEncoderHeaderBytes pb) ∗
          B.pool lim curSt sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_316 H) ret s P Q Qp := by
  have hfn : IsPolyEncoderEncodeEntryProg (lsProg_316 H) (blkPl_316).base :=
    Or.inr ⟨‹_›, H, rfl, rfl⟩
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge2⟩ := polyEncoderHeaderBytes_len_bounds pb
  have hlt0 : bs0.length < cap0.toNat := by omega
  have hcap_f : (cap0 == BitVec.ofNat 64 bs0.length) = false :=
    cap_beq_len_false_of_lt_placed hlt0
  refine step_polyEncoder_prologue_placed hres hfn encA v sp hhs0 hpc hrun hsp halign htr hx0 hx1 hcs
    (F := protoPolynomialEncoderPinnedAt B.repAlloc g encA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01, vecU8At_eq_header_sep_buf B.repAlloc v cap0 ptr0 bs0, vecHeader]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_316).base + 40#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm12 hinv1
  rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v cap0 ptr0 bs0,
    pool_step B lim curSt hvm12]
  refine step_polyEncoder_push_hdr_tag_placed B.repAlloc hfn encA v cap0 ptr0 sp bs0 hlt0
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (F := stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      protoPolynomialEncoderPinnedAt B.repAlloc g encA pb ∗ B.pool lim curSt _ ∗ F)
    (by sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3 hvm23
  rw [pool_step B lim curSt hvm23]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 401); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm3b hinv3
  rw [pool_step B lim curSt hvm3b]
  refine step_msg48rep_polyEncLen_call_placed hres128 B lim hencLen encA sp
    ((blkPl_316).base + 68#64) g pb curSt hlen_lt
    (F := vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ [0x12#8]) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by sep_ac_rfl) ?_
  intro s4 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt hpc4 hrun4 hsp4 htr4 hx0_4
    hcs34 hcs4 _
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyEncoder_mov_x1_x19_68_placed hfn
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) encA v sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5 hvm45
  rw [pool_step B lim curSt hvm45]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm5b hinv5
  rw [pool_step B lim curSt hvm5b]
  have hfit_len : (bs0 ++ [0x12#8]).length +
      (encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hevs_len :
      encodeVarintEvents
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))
          v cap0 ptr0 (bs0 ++ [0x12#8])) = [] :=
    encodeVarintEvents_of_spare hfit_len
  refine step_msg48rep_encode_varint_call_placed hres128 B lim hencVarint
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) v cap0 ptr0 sp ((blkPl_316).base + 76#64)
    (bs0 ++ [0x12#8]) curSt (Or.inl hfit_len) (by rw [hevs_len]; trivial)
    (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      polyEncoderRestAt B.repAlloc encA g ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by sep_ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = encA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [hevs_len, bs0_append_polyEncoderHeaderBytes bs0 pb]
  dsimp only [AllocCostModel.stepEvents]
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s6 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

private theorem step_pe_idx_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_316 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (encA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_idx : curBs.length + (encodeUint32Field 1#32 pb.idx).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_316).base + 76#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_316).base + 128#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_316 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeUint32Field 1#32 pb.idx) ∗
          B.pool lim curSt sm ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_316 H) ret s P Q Qp := by
  have hfn : IsPolyEncoderEncodeEntryProg (lsProg_316 H) (blkPl_316).base :=
    Or.inr ⟨‹_›, H, rfl, rfl⟩
  refine step_polyEncoder_check_idx_placed hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  cases hidx : (pb.idx == 0#32)
  · simp only [hidx, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_idx, hge2_idx⟩ := idx_field_len_of_ne_zero pb hidx
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
      cap_beq_len_false_of_lt_placed hlt0
    rw [vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_316).base + 100#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm12 hinv1
    rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs,
      pool_step B lim curSt hvm12]
    refine step_polyEncoder_push_idx_tag_placed B.repAlloc hfn encA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ B.pool lim curSt _ ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292); wp_steps
    apply sepWP_done_vm_placed
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm3b hinv3
    rw [pool_step B lim curSt hvm3b]
    have hfit_v : (curBs ++ [0x08#8]).length +
        (encodeVarint (pb.idx.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hevs_v :
        encodeVarintEvents
          (EncodeVarintGhost.mk (pb.idx.zeroExtend 64) v curCap curPtr (curBs ++ [0x08#8])) = [] :=
      encodeVarintEvents_of_spare hfit_v
    refine step_msg48rep_encode_varint_call_placed hres B lim hencVarint
      (pb.idx.zeroExtend 64) v curCap curPtr sp ((blkPl_316).base + 128#64)
      (curBs ++ [0x08#8]) curSt (Or.inl hfit_v) (by rw [hevs_v]; trivial)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by sep_ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [hevs_v, bs_append_idx_of_ne_zero curBs pb hidx]
    dsimp only [AllocCostModel.stepEvents]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hidx, ↓reduceIte] at hpc1
    rw [← bs_append_idx_of_zero curBs pb hidx]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_pe_pts_polys_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_316 H) (lsmpl.base 289)
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (encA v curCap curPtr sp sv3 : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (curBs : List (BitVec 8)) (curSt : M.σ)
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts59 : pb.pts.length < 2 ^ 59)
    (hpolys_eq : polysElems.map Prod.snd = pb.polys) (hpolys59 : pb.polys.length < 2 ^ 59)
    (hfit_pts : curBs.length + (encodeRepeatedBytes 2 pb.pts).length ≤ curCap.toNat)
    (hfit_polys : (curBs ++ encodeRepeatedBytes 2 pb.pts).length +
      (encodeRepeatedBytes 3 pb.polys).length ≤ curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_316).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        vecU8At B.repAlloc v curCap curPtr
          ((curBs ++ encodeRepeatedBytes 2 pb.pts) ++ encodeRepeatedBytes 3 pb.polys) ∗
        B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_316 H) (s0.readReg64 .lr) s P Q Qp := by
  have hfn : IsPolyEncoderEncodeEntryProg (lsProg_316 H) (blkPl_316).base :=
    Or.inr ⟨‹_›, H, rfl, rfl⟩
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hpolys_len : polysElems.length = pb.polys.length := by rw [← hpolys_eq, List.length_map]
  refine step_polyEncoder_prep_pts_placed hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 289); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm1b hinv1
  rw [pool_step B lim curSt hvm1b]
  refine step_msg48_encode_repeated59_exact_call_placed B lim hencRep 2 g.pts.ptr v curCap curPtr sp
    ((blkPl_316).base + 144#64) ptsElems curBs curSt (by decide) (by decide) (by omega)
    (by rw [hpts_eq]; exact hfit_pts)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.polys.ptr polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyEncoderElemsAt]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = encA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq]
  refine step_polyEncoder_prep_polys_epilogue_placed hfn encA v sp sv3 g pb ptsElems polysElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeRepeatedBytes 2 pb.pts) ∗
      B.pool lim curSt s2 ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by dsimp only [polyEncoderElemsAt]; sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hw0_3 hx1_3 hx2_3 hx3_3 hcc3 hcs3 hvm23
  rw [pool_step B lim curSt hvm23]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 289); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro _ hinv3
  exact step_msg48_encode_repeated59_exact_tailcall_placed
    (s := s3.setPC (lsmpl.base 289))
    hres B lim hencRep 3 g.polys.ptr v curCap curPtr sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
    (s0.readReg64 .x20) (s0.readReg64 .x19) polysElems
    (curBs ++ encodeRepeatedBytes 2 pb.pts) curSt (by decide) (by decide) (by omega)
    (by rw [hpolys_eq]; exact hfit_polys)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)
    (State.pc_setPC _ _)
    ((State.status_setPC _ _).trans hrun3)
    ((State.sp_setPC _ _).trans hsp3)
    halign
    ((State.trace_setPC _ _).trans htr3)
    ((State.readReg64_setPC _ _ _).trans hlr3)
    (by dsimp only [State.readReg32] at hw0_3 ⊢; rw [State.readReg64_setPC]; exact hw0_3)
    ((State.readReg64_setPC _ _ _).trans hx1_3)
    (by rw [State.readReg64_setPC, hpolys_len]; exact hx2_3)
    ((State.readReg64_setPC _ _ _).trans hx3_3)
    (calleeSavedPreserved_setPC_placed _ hcc3)
    (msgEnc48CalleeSavedPlaced_setPC _ hcs3 hinv3)
    (by rw [B.pool_setPC]; dsimp only [polyEncoderElemsAt]; sep_ac_rfl)
    (fun sf hpcf hrunf hspf htrf hccf hcsf => by
      rw [hpolys_eq]
      have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
      have hEq :
          ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
            vecU8At B.repAlloc v curCap curPtr
              ((curBs ++ encodeRepeatedBytes 2 pb.pts) ++ encodeRepeatedBytes 3 pb.polys) ∗
            B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
          ((repeatedBytesSliceAt g.polys.ptr polysElems ∗
            vecU8At B.repAlloc v curCap curPtr
              ((curBs ++ encodeRepeatedBytes 2 pb.pts) ++ encodeRepeatedBytes 3 pb.polys) ∗
            B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
            (((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
              ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)) := by
        dsimp only [polyEncoderElemsAt]; sep_ac_rfl
      rw [hEq] at hq
      exact hq)

/-! ## 3. Main Placed Theorems & `EncodeToVec` (`Block 426`) Bridges -/

theorem polyEncoder2_exact_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {B : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : EncodePolyEncoderPinnedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_316 H) (lsmpl.base 401)
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencV : subroutine_ok (lsProg_316 H) (lsmpl.base 292)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (hencR : subroutine_ok (lsProg_316 H) (lsmpl.base 289)
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (hpc : s0.pc = (blkPl_316).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyEncoderExactSpecOf resStack B lim).pre (x, st0) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_316 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyEncoderExactSpecOf resStack B lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyEncoderExactSpecOf resStack B lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyEncoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((protoPolynomialEncoderPinnedAt B.repAlloc x.g x.encA x.enc ∗
      vecU8At B.repAlloc x.v x.cap x.ptr x.bs ∗ B.pool lim st0 s0 ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyEncoderMsg_len_split x.enc
  have hlen_le_msg := polynomialEncoderPBEncodedLen_le_msg_len x.enc
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialEncoderPBEncodedLen x.enc < 2 ^ 64 := by omega
  refine step_pe_hdr_exact_placed hres B lim H hencLen hencV x.encA x.v x.cap x.ptr s0.sp
    x.g x.enc x.bs st0 hlen_lt (by omega) (F := emp)
    rfl hpc hrun rfl halign rfl hx0 hx1 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  have hfit_idx : (x.bs ++ polyEncoderHeaderBytes x.enc).length +
      (encodeUint32Field 1#32 x.enc.idx).length ≤ x.cap.toNat := by
    rw [List.length_append]; omega
  refine step_pe_idx_exact_placed hres128 B lim H hencV x.encA x.v x.cap x.ptr s0.sp x.g x.enc
    ptsElems polysElems (x.bs ++ polyEncoderHeaderBytes x.enc) st0 hfit_idx
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyEncoderRestAt B.repAlloc x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_idx := (x.bs ++ polyEncoderHeaderBytes x.enc) ++ encodeUint32Field 1#32 x.enc.idx
  have hfit_pts : bs_idx.length + (encodeRepeatedBytes 2 x.enc.pts).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append]; omega
  have hfit_polys : (bs_idx ++ encodeRepeatedBytes 2 x.enc.pts).length +
      (encodeRepeatedBytes 3 x.enc.polys).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pe_pts_polys_exact_placed hres B lim H hencR x.encA x.v x.cap x.ptr s0.sp sv3 x.g x.enc
    ptsElems polysElems bs_idx st0 hpts_eq (by omega) hpolys_eq (by omega) hfit_pts hfit_polys
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyEncoderRestAt B.repAlloc x.encA x.g ptsElems polysElems ∗ emp)
    (by dsimp [bs_idx]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyEncoderElemsAt x.encA x.g x.enc ptsElems polysElems ∗
      polyEncoderRestAt B.repAlloc x.encA x.g ptsElems polysElems) ∗
      (vecU8At B.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
        B.pool lim st0 sf ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyEncoderMsg x.bs x.enc]
    convert hm using 1; dsimp [bs_idx]; sep_ac_rfl
  have hm_pinned := (satisfies_protoPolynomialEncoderPinnedAt_iff B.repAlloc x.g x.encA x.enc _ sf.mem).mpr
    ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_pack⟩
  dsimp only [encodePolyEncoderExactSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; sep_ac_rfl

private theorem encode_polyEncoder_2_exact_vm_pinned_placed_ok_of_resStack [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf resStack A.repAlloc)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  let B := vmTrackBudget A s0
  have hpreB : s0.mem ⊨
      (encodePolyEncoderExactSpecOf resStack B impossibleEnforcedLimits).pre (x, M.init) s0 ∗ R := by
    dsimp only [encodePolyEncoderExactVmSpecOf] at hpre
    dsimp only [encodePolyEncoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc]
    simp only [↓reduceIte]
    have hpre1 : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
        ((⌜s0.readReg64 .x0 = x.encA ∧ s0.readReg64 .x1 = x.v ∧
            x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat⌝ ∗
          protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
          vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
          stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ R) := by
      rw [satisfies_pure_sepConj]; exact ⟨VmPreserved.refl s0, hpre⟩
    convert hpre1 using 1; sep_ac_rfl
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_exact_gen_placed_ok hres (B := B) (lim := impossibleEnforcedLimits)
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext B.repAlloc H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encodeVarint4_fit_impossible_placed_ok (by omega) B H))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_2_59_exact_impossible_placed_ok (by omega) B hmc))
    hpc hrun hpreB hsp
  refine ⟨P, R, hP, sepWPp_mono ?_ ?_ hwp⟩
  · intro sf Q ⟨hq, hspf, hccf⟩
    refine ⟨fun hm => ?_, hspf, hccf⟩
    have hpost := hq hm
    dsimp only [encodePolyEncoderExactSpecOf, B, vmTrackBudget, impossibleEnforcedLimits,
      RustCliAllocBudget.repAlloc] at hpost
    simp only [↓reduceIte] at hpost
    have hpost1 : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
        (⌜VmPreserved s0 sf⌝ ∗
          (protoPolynomialEncoderPinnedAt A.repAlloc x.g x.encA x.enc ∗
            vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
            stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R)) := by
      convert hpost using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost1
    obtain ⟨htrf, hvmp, hrest⟩ := hpost1
    dsimp only [encodePolyEncoderExactVmSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvmp, htrf⟩, by convert hrest using 1; sep_ac_rfl⟩
  · intro sf P_f hpan hm
    exact hpan hm

theorem encode_polyEncoder_2_exact_vm_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf doReserveStack A.repAlloc)) :=
  encode_polyEncoder_2_exact_vm_pinned_placed_ok_of_resStack (by decide) hmc

theorem encode_polyEncoder_2_exact_vm_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf doReserveStackX A.repAlloc)) :=
  encode_polyEncoder_2_exact_vm_pinned_placed_ok_of_resStack (by decide) hmc

theorem encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm
    (encode_polyEncoder_2_exact_vm_pinned_placed_ok hmc)

theorem encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodePolyEncoderExact_of_vm
    (encode_polyEncoder_2_exact_vm_pinned_placed_ok_x hmc)

theorem encode_polyEncoder_2_exact_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStack A lim)) :=
  encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy hmc

theorem encode_polyEncoder_2_exact_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)) :=
  encode_polyEncoder_2_exact_pinned_placed_ok_of_memcpy_x hmc

theorem etv_polyEncoderEncode_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc}
    (hpe_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf resStack A))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialEncoder := ⟨x.enc.idx, x.enc.pts, x.enc.polys⟩
  have hpb : CryptoVerification.SpqrV1.Prost.MessageEncode.ProtoPolynomialEncoder.toPB pb = x.enc := rfl
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (encodePolyEncoderExactVmSpecOf resStack A)).pre
      ⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withLsCodeLoaded, encodePolyEncoderExactVmSpecOf, etvPolyEncoderExactSpecOf,
      encodePolyEncoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpe_ok.mono_outcome ⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩
    R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodePolyEncoderExactVmSpecOf, etvPolyEncoderExactSpecOf,
      encodePolyEncoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem etv_polyEncoderEncode_exact_vm_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyEncoderEncode_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyEncoder_2_exact_vm_pinned_placed_ok hmc))

theorem etv_polyEncoderEncode_exact_vm_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyEncoderEncode_exact_of_lscl
    (ls_subroutine_ok_of_block (encode_polyEncoder_2_exact_vm_pinned_placed_ok_x hmc))

theorem etv_polyEncoderEncode_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A.repAlloc)) :=
  etv_polyEncoderEncode_exact_vm_placed_ok hmc

theorem etv_polyEncoderEncode_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (_hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (_halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (_hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A.repAlloc)) :=
  etv_polyEncoderEncode_exact_vm_placed_ok_x hmc

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
