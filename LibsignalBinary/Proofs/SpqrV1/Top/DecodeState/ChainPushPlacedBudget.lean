/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainPB` `links.push` & Tag 3

Budget-threaded relocatable `[LibsignalPlacement]` `ChainEpochPushEnv` envelope, 112-byte Q-register
copy (`+640`), `Vec<ChainEpochPB>::push` (`+624`), and `ChainPB` tag 3 (`+592`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainEpochPBAt chainEpochPBSize chainLinksVecAt optChainParamsPBAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge (mergeLoopBin takeExact_eq_take_drop)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto
  (DecodeErr checkWireType mergeFieldsLoop mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost Quads14 TraceVRegs V1InnerHeapPred
   chainEpochPBCapOkAt chainEpochPBCapOkAt_entails_chainEpochPBAt
   chainEpochPBAt_entails_quads14 chainEpochPBHeap chainPB_mergeField_tag3
   codecWireTypeToProto decodeStatePlacedEntry decodeStatePlacedProg
   memRegion_112_eq_quads14At mergeMessage_toOption_of_ne_lengthDelimited
   optProtoPqRatchetInnerCapOkAt optVersionNegotiationPBCapOkAt
   protoPqRatchetStateCapOkAt
   quads14At quads14_entails_chainEpochPBAt quads7At
   quads7At_entails_memRegion_56 quads7_entails_head_and_memRegion_48
   relocArrayAtChainEpochPB sp_sub_1392_aligned vecU8CapOkAt)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
  (protoPqRatchetStateCapOkAt_some_ch_eq_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (GrowOneStrideEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_mono
   FitsEnv.decodeStateLoop_split FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (decodeStateEnv_of_loop_from_push2_free decodeStateIterEnv_of_decodeErrorFrom
   fitsEnv_decodeErrorFrom_of_loop fitsEnv_decodeErrorPush_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
  (SepWPpIPlaced.call_growOneChainEpoch decodeStateLoopEnv_of_growOneChainEpoch
   fitsEnv_growOneChainEpoch_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
  (decodeState_err_chain_epoch_wt_53f30_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux (lift_postEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget
  (decodeState_epoch_merge_536f4_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

private theorem bv_ofNat_mul_112 (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 112#64 = ptr + BitVec.ofNat 64 (n * 112) := by
  rw [← BitVec.ofNat_mul]

private theorem bv_ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

attribute [local simp, local arm64_norm] bv_ofNat_mul_112 bv_ofNat_add_one

/-! ## `ChainEpochPushEnv` Envelope & `DecodeStateLoopEnv` Bridges -/

/-- Allocator event envelope of `Vec<ChainEpochPB>::push` (`stride = 112`, `align = 8`) at
current length `linksLen`: either `len < cap` (`[]`) or `len == cap`
(`GrowOneStrideEnv (BitVec.ofNat 64 linksLen) 112 8`). -/
def ChainEpochPushEnv (linksLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ GrowOneStrideEnv (BitVec.ofNat 64 linksLen) 112 8 evs

theorem decodeStateIterEnv_of_chainEpochPush {maxLen polyCapBound linksLen : Nat}
    {evs : List AllocEvent}
    (hlinks : linksLen ≤ 2 * maxLen + 4)
    (hevs : ChainEpochPushEnv linksLen evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  rcases hevs with rfl | hgrow
  · exact .nil
  · refine .growChainEpoch (BitVec.ofNat 64 linksLen) ?_ hgrow
    rw [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) hlinks

theorem decodeStateLoopEnv_of_chainEpochPush {maxLen polyCapBound linksLen : Nat}
    {evs : List AllocEvent}
    (hlinks : linksLen ≤ 2 * maxLen + 4)
    (hevs : ChainEpochPushEnv linksLen evs) :
    DecodeStateLoopEnv 1 maxLen polyCapBound evs :=
  DecodeStateLoopEnv.single (fuel := 0) (decodeStateIterEnv_of_chainEpochPush hlinks hevs)

theorem fitsEnv_growOneChainEpoch_of_links_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound linksLen : Nat}
    (hlinks : linksLen ≤ 2 * maxLen + 4) (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (GrowOneStrideEnv (BitVec.ofNat 64 linksLen) 112 8) :=
  fitsEnv_growOneChainEpoch_of_loop
    (by rw [BitVec.toNat_ofNat]; exact Nat.le_trans (Nat.mod_le _ _) hlinks)
    hrem hFit

theorem SepWPpIPlaced.pure_elim [LibsignalPlacement] {φ : Prop} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : φ → SepWPpIPlaced prog ret s P Q Q_err) :
    SepWPpIPlaced prog ret s (⌜φ⌝ ∗ P) Q Q_err := by
  intro hinv R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 hinv R hm.2 hL

/-! ## Pure & Spatial Helpers for `Vec<ChainEpochPB>::push` -/

private theorem proto_mergeMessage_length_lt {Msg : Type}
    {mergeField :
      Msg → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
        List (BitVec 8) → Nat → Except DecodeErr (Msg × List (BitVec 8))}
    {m m' : Msg} {bs rest : List (BitVec 8)} {depth' : Nat}
    (h : (mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = some (m', rest)) :
    rest.length < bs.length := by
  have hchk : checkWireType .lengthDelimited .lengthDelimited = .ok () := rfl
  simp only [mergeMessage, hchk, Bind.bind, Except.bind, takeExact_eq_take_drop] at h
  rcases hdv : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint bs with e | ⟨len64, restMid⟩
  · rw [hdv] at h; cases h
  · have hdv_opt : decodeVarint bs = some (len64, restMid) := by
      rw [← proto_decodeVarint_toOption, hdv]; rfl
    have hlt_mid : restMid.length < bs.length := decodeVarint_length hdv_opt
    rw [hdv] at h; dsimp only at h
    by_cases hle : len64.toNat ≤ restMid.length
    · rw [ite_eq_left_iff.mpr fun hnot => absurd hle hnot] at h; dsimp only at h
      rcases hloop : mergeFieldsLoop mergeField (restMid.take len64.toNat).length m
          (restMid.take len64.toNat) depth' with e | m''
      · rw [hloop] at h; cases h
      · rw [hloop] at h
        simp only [Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        rw [List.length_drop]
        omega
    · rw [ite_eq_right_iff.mpr fun hyes => absurd hyes hle] at h; cases h

private theorem arrayAt_append_singleton {α : Type} (elemAt : α → BitVec 64 → SepProp) (stride : Nat)
    (ptr : BitVec 64) (xs : List α) (x : α) :
    arrayAt elemAt stride ptr xs ∗ elemAt x (ptr + BitVec.ofNat 64 (xs.length * stride)) =
      arrayAt elemAt stride ptr (xs ++ [x]) := by
  induction xs generalizing ptr with
  | nil =>
    simp only [arrayAt, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.nil_append, emp_sepConj, sepConj_emp]
  | cons y ys ih =>
    simp only [arrayAt, List.cons_append, List.length_cons]
    have hadd :
        ptr + BitVec.ofNat 64 ((ys.length + 1) * stride) =
          (ptr + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (ys.length * stride) := by
      have hm : (ys.length + 1) * stride = stride + ys.length * stride := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hadd, sepConj_assoc, ih (ptr + BitVec.ofNat 64 stride)]

private theorem max_double_four_bound {cap : Nat} (hcap : cap ≤ 2 ^ 54) :
    max (2 * cap) 4 * 112 + 8 ≤ 2 ^ 63 ∧ max (2 * cap) 4 * 112 < 2 ^ 63 ∧
      cap < max (2 * cap) 4 ∧ max (2 * cap) 4 < 2 ^ 64 := by
  omega

private theorem vecBuf_chainEpochPB_expose_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; intro h
  apply Entails.pure_right h
  apply Entails.pure_right h
  exact Entails.refl _

private theorem vecBuf_chainEpochPB_of_lt (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (hlt : xs.length < cap.toNat) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((cap.toNat - xs.length) * 112) := by
  unfold vecBuf
  apply Entails.pure_left; intro _
  have hcap0 : cap ≠ 0 := by intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  exact Entails.refl _

private theorem vecBuf_chainEpochPB_to_growOne_pre (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (hfull : xs.length = cap.toNat) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = cap.toNat * 112 ∧ ptr ≠ 0#64⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        (relocArrayAtChainEpochPB A xs).1 bs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨_, _, hptr⟩
  by_cases hcap0 : cap = 0
  · subst hcap0
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero hfull
    subst hxs
    simp only [↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mul, relocArrayAtChainEpochPB]
    refine Entails.sepExists_right [] ?_
    apply Entails.pure_right ⟨rfl, hptr⟩
    simp only [sepConj_emp]
    exact Entails.refl _
  · have hcap0' : cap ≠ 0#64 := hcap0
    simp only [hcap0, hcap0', ↓reduceIte, hfull, Nat.sub_self, Nat.zero_mul, memRegion_zero,
      sepConj_emp]
    have hto := (relocArrayAtChainEpochPB A xs).2.to_bytes ptr
    refine Entails.trans (sepConj_mono_right hto) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    have hpull :
        A.live ptr (cap.toNat * 112) 8 ∗
          (⌜bs.length = xs.length * 112⌝ ∗ (ptr ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs) =
        ⌜bs.length = xs.length * 112⌝ ∗
          A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs := by
      sep_ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hbs
    have hbs' : bs.length = cap.toNat * 112 := by rw [hbs, hfull]
    apply Entails.pure_right ⟨hbs', hptr⟩
    rw [hbs']
    exact Entails.of_eq (by sep_ac_rfl)

private theorem growOne_post_to_arrayAt_chainEpochPB (A : RustAlloc) (cap p' : BitVec 64)
    (xs : List ChainEpochPB) (bs : List (BitVec 8))
    (hfull : xs.length = cap.toNat) (hbs : bs.length = cap.toNat * 112)
    (hnew_toNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4) :
    A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
      (relocArrayAtChainEpochPB A xs).1 bs ⊢
    A.live p' ((BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 p' xs ∗
      memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
        (((BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat - xs.length) * 112) := by
  rw [hnew_toNat]
  have hlen_xs : bs.length = xs.length * 112 := by rw [hbs, hfull]
  have hof := (relocArrayAtChainEpochPB A xs).2.of_bytes p' bs hlen_xs
  have hsub : max (2 * cap.toNat) 4 - cap.toNat = max (2 * cap.toNat) 4 - xs.length := by
    rw [hfull]
  rw [hlen_xs, hsub]
  have hgroup :
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
          ((max (2 * cap.toNat) 4 - xs.length) * 112) ∗
        (relocArrayAtChainEpochPB A xs).1 bs =
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
        ((p' ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs) ∗
        memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
          ((max (2 * cap.toNat) 4 - xs.length) * 112) := by sep_ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono_left hof)

private theorem quads14At_sp_688_restore (sp : BitVec 64) (q : Quads14) :
    quads14At (sp - 688#64) q ∗ memRegion (sp - 576#64) 240 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗
      memRegion (sp - 680#64) 40 ∗
      memRegion (sp - 640#64) 304 := by
  unfold quads14At Quads14.head
  have h1 := quads7_entails_head_and_memRegion_48 (sp - 688#64) q.1
  have h2 := quads7At_entails_memRegion_56 (sp - 632#64) q.2
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 688#64 + 56#64 = sp - 632#64 := by bv_omega
  rw [ha1] at h1; rw [ha2]
  refine Entails.trans (sepConj_mono (sepConj_mono h1 h2) (Entails.refl _)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
      (b' := sp - 632#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 56) (k := 240)
      (b' := sp - 576#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem memRegion_rem_split_112 (ptr : BitVec 64) (len cap : Nat)
    (hlt : len < cap) (hcap63 : cap * 112 < 2 ^ 63) :
    memRegion (ptr + BitVec.ofNat 64 (len * 112)) ((cap - len) * 112) ⊢
      (∃∗ q_dst : Quads14, quads14At (ptr + BitVec.ofNat 64 (len * 112)) q_dst) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len + 1) * 112)) ((cap - (len + 1)) * 112) := by
  have hsplit : (cap - len) * 112 = 112 + (cap - (len + 1)) * 112 := by
    have hsub : cap - len = 1 + (cap - (len + 1)) := by omega
    rw [hsub, Nat.add_mul, Nat.one_mul]
  have haddr : ptr + BitVec.ofNat 64 ((len + 1) * 112) =
      (ptr + BitVec.ofNat 64 (len * 112)) + 112#64 := by
    have hm : (len + 1) * 112 = len * 112 + 112 := by rw [Nat.add_mul, Nat.one_mul]
    rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
  rw [ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 (len * 112))
      (n := 112) (k := (cap - (len + 1)) * 112)
      (b' := ptr + BitVec.ofNat 64 ((len + 1) * 112)) hsplit haddr (by omega),
    memRegion_112_eq_quads14At (ptr + BitVec.ofNat 64 (len * 112))]
  exact Entails.refl _

private theorem vecOf_chainEpochPB_snoc_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (ep' : ChainEpochPB) (q : Quads14)
    (hlt : xs.length < cap.toNat) (hcap63 : cap.toNat * 112 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
      chainEpochPBHeap A q ep' ∗
      memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
        ((cap.toNat - (xs.length + 1)) * 112) ⊢
    chainLinksVecAt A a (xs ++ [ep']) := by
  have hcap0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hlen_app : (xs ++ [ep']).length = xs.length + 1 := by simp
  have hep_at := quads14_entails_chainEpochPBAt A (ptr + BitVec.ofNat 64 (xs.length * 112)) q ep'
  have harr := arrayAt_append_singleton (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ep'
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  simp only [hlen_app, hcap0, ↓reduceIte]
  have hgroup :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
        quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
        chainEpochPBHeap A q ep' ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
          ((cap.toNat - (xs.length + 1)) * 112) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
          (quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
            chainEpochPBHeap A q ep')) ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
          ((cap.toNat - (xs.length + 1)) * 112) := by sep_ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right hep_at)))) ?_
  rw [harr]
  have hpure :
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
        ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (cap.toNat * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep']) ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
            ((cap.toNat - (xs.length + 1)) * 112)) =
      ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
          A.live ptr (cap.toNat * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep']) ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
            ((cap.toNat - (xs.length + 1)) * 112)) := by sep_ac_rfl
  rw [hpure]
  apply Entails.pure_right ⟨by omega, hcap63, hptr⟩
  exact Entails.of_eq (by sep_ac_rfl)

private theorem fold_protoPqRatchetStateCapOkAt_snoc (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (ep' : ChainEpochPB) (inner : Option PqRatchetState.Inner)
    (hlinks_next : (ch.links ++ [ep']).length + remLen ≤ 2 ^ 54) :
    optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
      vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
      ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (sp - 928#64) ch.params ∗
      ((sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner ⊢
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen
      ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq_placed H_inner A sp remLen optVn
    { ch with links := ch.links ++ [ep'] } inner]
  dsimp only
  have hpure :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜(ch.links ++ [ep']).length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner =
      ⌜(ch.links ++ [ep']).length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner) := by sep_ac_rfl
  rw [hpure]
  apply Entails.pure_right hlinks_next
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## `decodeState_chain_push_copy_5371c_placed` (`+640..+724` -> `+508`) -/

/-- Envelope-parameterized 112-byte Q-register copy from `[sp + 0x2c0 .. sp + 0x330)`
(`s0.sp - 688#64`) into `ptr + ch.links.length * 112`, incrementing `len` at `[sp + 0x1a0]`
(`s0.sp - 976#64`) and branching to `+508`. -/
theorem decodeState_chain_push_copy_5371c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (cap ptr : BitVec 64)
    (rest2 : List (BitVec 8)) (limit : Nat)
    (hlt : ch.links.length < cap.toNat)
    (hcap63 : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 ch.links.length)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      optVersionNegotiationPBCapOkAt A.repAlloc (s0.sp - 1040#64) rest2.length optVn ∗
      ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      A.repAlloc.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr ch.links ∗
      memRegion (ptr + BitVec.ofNat 64 (ch.links.length * 112))
        ((cap.toNat - ch.links.length) * 112) ∗
      vecU8CapOkAt A.repAlloc (s0.sp - 968#64) rest2.length ch.nextRoot ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) rest2.length inner ∗
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  refine SepWP.fold (chainEpochPBAt_entails_quads14 A.repAlloc (s0.sp - 688#64) ep')
    (by sep_focus) ?_
  refine SepWP.fold (memRegion_rem_split_112 ptr ch.links.length cap.toNat hlt hcap63)
    (by sep_focus) ?_
  wp_pull_exists
  rename_i q_src q_dst
  rcases q_src with ⟨⟨s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6⟩,
                     ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6⟩⟩
  rcases q_dst with ⟨⟨d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6⟩,
                     ⟨d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6⟩⟩
  dsimp only [quads14At, quads7At]
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  have hfold_snoc := vecOf_chainEpochPB_snoc_fold A.repAlloc (s0.sp - 992#64) cap ptr ch.links ep'
    ((s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6), (s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6))
    hlt hcap63 hptr
  have ha984 : s0.sp - 992#64 + 8#64 = s0.sp - 984#64 := by bv_omega
  have ha976 : s0.sp - 992#64 + 16#64 = s0.sp - 976#64 := by bv_omega
  rw [ha984, ha976] at hfold_snoc
  dsimp only [quads14At, quads7At] at hfold_snoc
  refine SepWP.fold hfold_snoc (by sep_focus) ?_
  have hrestore := quads14At_sp_688_restore s0.sp
    ((s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6), (s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6))
  dsimp only [quads14At, quads7At, Quads14.head] at hrestore
  refine SepWP.fold hrestore (by sep_focus) ?_
  refine SepWP.fold (fold_protoPqRatchetStateCapOkAt_snoc H_inner A.repAlloc s0.sp rest2.length
    optVn ch ep' inner hlinks_next) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  exact hloop s0_0 _ _
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx20])
    (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
    (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
    (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx28])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)

theorem decodeState_chain_push_copy_5371c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (cap ptr : BitVec 64)
    (rest2 : List (BitVec 8)) (limit : Nat)
    (hlt : ch.links.length < cap.toNat)
    (hcap63 : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 ch.links.length)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      optVersionNegotiationPBCapOkAt A.repAlloc (s0.sp - 1040#64) rest2.length optVn ∗
      ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      A.repAlloc.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr ch.links ∗
      memRegion (ptr + BitVec.ofNat 64 (ch.links.length * 112))
        ((cap.toNat - ch.links.length) * 112) ∗
      vecU8CapOkAt A.repAlloc (s0.sp - 968#64) rest2.length ch.nextRoot ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) rest2.length inner ∗
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_push_copy_5371c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    x st0 st optVn ch inner ep' cap ptr rest2 limit hlt hcap63 hptr hlinks_next
    s0 s P R post hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    hP hloop

/-! ## `decodeState_chain_push_5370c_placed` (`+624..+724`, `+1200..+1208` -> `+508`) -/

private theorem bv_len_beq_cap_false {len : Nat} {cap : BitVec 64}
    (hlt : len < cap.toNat) :
    (BitVec.ofNat 64 len == cap) = false ∧ (BitVec.ofNat 64 len != cap) = true := by
  have hlt64 : len < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  have hne : BitVec.ofNat 64 len ≠ cap := by
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at hto
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Envelope-parameterized `Vec<ChainEpochPB>::push` at `+624`, handling both `len < cap`
(direct copy at `+640`, `evs_push = []`) and `len == cap` (`RawVecInner::grow_one` at
`+1200..+1208` followed by copy at `+640`), branching to `+508`. -/
theorem decodeState_chain_push_5370c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (limit : Nat)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (hfits_grow : FitsEnv M lim st (GrowOneStrideEnv (BitVec.ofNat 64 ch.links.length) 112 8))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
        ⟨optVn, some ch, inner⟩ ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (evs_push : List AllocEvent) (sf : State) (P' : SepProp),
      ChainEpochPushEnv ch.links.length evs_push →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_push st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hgrow_call := hc.growOneChainEpoch
  subst hP
  rw [protoPqRatchetStateCapOkAt_some_ch_eq_placed H_inner A.repAlloc s0.sp rest2.length optVn ch
    inner]
  have hep_drop := chainEpochPBCapOkAt_entails_chainEpochPBAt A.repAlloc (s0.sp - 688#64)
    rest2.length ep'
  have ha984 : s0.sp - 992#64 + 8#64 = s0.sp - 984#64 := by bv_omega
  have ha976 : s0.sp - 992#64 + 16#64 = s0.sp - 976#64 := by bv_omega
  have hvec_unfold :
      chainLinksVecAt A.repAlloc (s0.sp - 992#64) ch.links =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
        ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        vecBuf A.repAlloc 112 8 (fun ep addr => chainEpochPBAt A.repAlloc addr ep) cap ptr
          ch.links := by
    unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader
    simp only [ha984, ha976, sepConj_assoc]
  rw [hvec_unfold]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPpIPlaced.exists_elim; intro cap
  apply SepWPpIPlaced.exists_elim; intro ptr
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        (optVersionNegotiationPBCapOkAt A.repAlloc (s0.sp - 1040#64) rest2.length optVn ∗
          (⌜ch.links.length + rest2.length ≤ 2 ^ 54⌝ ∗
            (((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
              ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              vecBuf A.repAlloc 112 8 (fun ep addr => chainEpochPBAt A.repAlloc addr ep) cap ptr
                ch.links) ∗
            vecU8CapOkAt A.repAlloc (s0.sp - 968#64) rest2.length ch.nextRoot ∗
            ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
            ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
            optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
            ((s0.sp - 916#64) ↦₃₂ ch.direction)) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) rest2.length inner) ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s =
      ⌜ch.links.length + rest2.length ≤ 2 ^ 54⌝ ∗
        (vecBuf A.repAlloc 112 8 (fun ep addr => chainEpochPBAt A.repAlloc addr ep) cap ptr
            ch.links ∗
          (chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
            (sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
              optVersionNegotiationPBCapOkAt A.repAlloc (s0.sp - 1040#64) rest2.length optVn ∗
              ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
              ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              vecU8CapOkAt A.repAlloc (s0.sp - 968#64) rest2.length ch.nextRoot ∗
              ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
              ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
              optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
              ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
              optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) rest2.length inner ∗
              memRegion (s0.sp - 576#64) 240 ∗
              decodeStateLoopCommonPlaced A lim st x s0 s))) := by sep_ac_rfl
  rw [hreord]
  apply SepWPpIPlaced.pure_elim; intro _hlinks_cur
  have hexp := vecBuf_chainEpochPB_expose_bounds A.repAlloc cap ptr ch.links
  refine SepWPpIPlaced.mono_pre (sepConj_mono hexp (sepConj_mono_left hep_drop)) ?_
  rw [sepConj_assoc]
  apply SepWPpIPlaced.pure_elim; rintro ⟨hlen_le, hcap63, hptr⟩
  by_cases hlt : ch.links.length < cap.toNat
  · -- len < cap: direct copy at +640 (`evs_push = []`)
    have ⟨hbeq, hbne⟩ := bv_len_beq_cap_false hlt
    refine SepWPpIPlaced.mono_pre
      (sepConj_mono_left (vecBuf_chainEpochPB_of_lt A.repAlloc cap ptr ch.links hlt)) ?_
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 640#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm, hbeq, hbne]) (by simp only [arm64_norm, hrun])
    exact decodeState_chain_push_copy_5371c_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      x st0 st optVn ch inner ep' cap ptr rest2 limit
      hlt hcap63 hptr hlinks_next s0 _ _ R post hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hbeq, hbne])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      (fun w0' sf P' => hloop w0' [] sf P' (Or.inl rfl))
  · -- len == cap: grow_one at +1200 -> +640
    have heq_len : ch.links.length = cap.toNat := by omega
    have hbv : BitVec.ofNat 64 ch.links.length = cap := by
      rw [heq_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hbeq : (cap - cap == 0#64) = true := by simp
    have hbne : (!decide ((cap - cap == 0#64) = true)) = false := by simp
    have hcap_54 : cap.toNat ≤ 2 ^ 54 := by
      have : (ch.links ++ [ep']).length = ch.links.length + 1 := by simp
      omega
    have ⟨hgrow_bound, hnew_cap63_nat, hnew_lt_nat, hnew_lt64⟩ := max_double_four_bound hcap_54
    have hnew_toNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hnew_lt : ch.links.length < (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat := by omega
    have hnew_cap63 : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat * 112 < 2 ^ 63 := by omega
    have hfits_cap : FitsEnv M lim st (GrowOneStrideEnv cap 112 8) := hbv ▸ hfits_grow
    refine SepWPpIPlaced.mono_pre
      (sepConj_mono_left (vecBuf_chainEpochPB_to_growOne_pre A.repAlloc cap ptr ch.links heq_len))
      ?_
    rw [sepExists_sepConj_left]
    apply SepWPpIPlaced.exists_elim; intro bs
    rw [sepConj_assoc]
    apply SepWPpIPlaced.pure_elim; rintro ⟨hbs_len, _⟩
    rw [hbv]
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
      at hpc hgrow_call ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1200#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm, hbeq, hbne]) (by simp only [arm64_norm, hrun])
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 356)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx22_30 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
    refine SepWPpIPlaced.call_growOneChainEpoch hgrow_call
      (s0.sp - 992#64) cap ptr bs st
      (ret_pc := (blkPl_325).base + 1208#64)
      (hpc := by simp only [arm64_norm])
      (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx22, hx22_30])
      (hlen := hbs_len) (hptr := hptr) (hbound := hgrow_bound)
      (hfits := hfits_cap)
      (hP := by rw [ha984]; pool_reg_norm; sep_focus) ?_
    intro s1 p' evs_grow hptr' _ hevs_grow hpc1 hrun1 hsp1 htr1 hcs1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, _⟩
    simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
    simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    rw [← hbv] at hx27_1
    have hsp1A : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    have hpost_grow :=
      growOne_post_to_arrayAt_chainEpochPB A.repAlloc cap p' ch.links bs heq_len hbs_len hnew_toNat
    have hrestore_len :
        ((s0.sp - 976#64) ↦₆₄ cap) ⊢ ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) :=
      Entails.of_eq (by rw [hbv])
    have hpush_env : ChainEpochPushEnv ch.links.length evs_grow :=
      Or.inr (hbv.symm ▸ hevs_grow)
    rw [ha984]
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 640#64)
    refine SepWP.fold hpost_grow (by sep_focus) ?_
    refine SepWP.fold hrestore_len (by sep_focus) ?_
    wp_steps 1
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact decodeState_chain_push_copy_5371c_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      x st0 (M.stepEvents evs_grow st) optVn ch inner ep'
      (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) p' rest2 limit
      hnew_lt hnew_cap63 hptr' hlinks_next s0 _ _ R post hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      (fun w0' sf P' => hloop w0' evs_grow sf P' hpush_env)

theorem decodeState_chain_push_5370c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (limit : Nat)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (hfits_grow : FitsEnv M lim st (GrowOneStrideEnv (BitVec.ofNat 64 ch.links.length) 112 8))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
        ⟨optVn, some ch, inner⟩ ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (evs_push : List AllocEvent) (sf : State) (P' : SepProp),
      ChainEpochPushEnv ch.links.length evs_push →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_push st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_push_5370c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st optVn ch inner ep' rest2 limit hlinks_next hfits_grow
    s0 s P R post hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29
    hP hloop

theorem decodeState_chain_push_5370c_placed_loop_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxLen polyCapBound : Nat}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (limit : Nat)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (hlinks_max : ch.links.length ≤ 2 * maxLen + 4)
    (hacc : DecodeStateLoopEnv f maxLen polyCapBound evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound))
    (hrem : 1 ≤ rem)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
        ⟨optVn, some ch, inner⟩ ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (evs_push : List AllocEvent) (sf : State) (P' : SepProp),
      ChainEpochPushEnv ch.links.length evs_push →
      DecodeStateLoopEnv (f + 1) maxLen polyCapBound (evs_acc ++ evs_push) →
      M.stepEvents (evs_acc ++ evs_push) st0 = M.stepEvents evs_push st →
      FitsEnv M lim (M.stepEvents evs_push st)
        (DecodeStateLoopEnv (rem - 1) maxLen polyCapBound) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_push st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  refine decodeState_chain_push_5370c_placed_ofEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc x st0 st optVn ch inner ep' rest2 limit hlinks_next
    (fitsEnv_growOneChainEpoch_of_links_loop hlinks_max hrem hFit)
    s0 s P R post hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29 hP ?_
  intro w0' evs_push sf P' hpush
  exact hloop w0' evs_push sf P' hpush
    (hacc.append (decodeStateLoopEnv_of_chainEpochPush hlinks_max hpush))
    (by rw [M.stepEvents_append, hst])
    (FitsEnv.decodeStateLoop_tail (decodeStateIterEnv_of_chainEpochPush hlinks_max hpush)
      (FitsEnv.decodeStateLoop_mono (by omega : (rem - 1) + 1 ≤ rem)
        (Nat.le_refl _) (Nat.le_refl _) hFit))

theorem decodeState_chain_push_5370c_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (limit : Nat)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (hlinks_max : ch.links.length ≤ 2 * x.st.bytes.length + 4)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 1 ≤ rem)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
        ⟨optVn, some ch, inner⟩ ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (evs_push : List AllocEvent) (sf : State) (P' : SepProp),
      ChainEpochPushEnv ch.links.length evs_push →
      DecodeStateLoopEnv (f + 1) x.st.bytes.length (2 * x.st.bytes.length + 16)
        (evs_acc ++ evs_push) →
      M.stepEvents (evs_acc ++ evs_push) st0 = M.stepEvents evs_push st →
      FitsEnv M lim (M.stepEvents evs_push st)
        (DecodeStateLoopEnv (rem - 1) x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_push st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_push_5370c_placed_loop_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem optVn ch inner ep' rest2 limit hlinks_next hlinks_max
    hacc hst hFit hrem s0 s P R post hs0A hpc hrun hsp htr
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29 hP hloop

/-! ## Tag 3 (`ChainPB::epoch` `Vec<ChainEpochPB>::push`, `+592..+724` -> `+508`) -/

private theorem protoPqRatchetStateCapOkAt_expose_ch_links (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ ⊢
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
      protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq_placed]
  have h1 :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner =
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          (chainLinksVecAt A (sp - 992#64) ch.links ∗
            vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
            ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
            ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
            optChainParamsPBAt (sp - 928#64) ch.params ∗
            ((sp - 916#64) ↦₃₂ ch.direction)) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner) := by sep_ac_rfl
  rw [h1]
  apply Entails.pure_left; intro h
  apply Entails.pure_right h
  apply Entails.pure_right h
  exact Entails.of_eq (by sep_ac_rfl)

private theorem wt_ne_two_of_ne_lengthDelimited {iwt : WireType} (hwt : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> first | exact (hwt rfl).elim | decide

attribute [local irreducible] mergeMessage mergeLoopBin
  CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

/-- Envelope-parameterized `ChainPB` Tag 3 (`epoch`, `+592..+724`): checks `x0 == 2`
(`.lengthDelimited`), merges a `ChainEpochPB` (`decodeState_epoch_merge_536f4_placed_ofEnv`),
and pushes it onto `ch.links` (`decodeState_chain_push_5370c_placed_loop_ofEnv`), continuing to
`+508`. -/
theorem decodeState_chain_tag3_536ec_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (iwt : WireType) (rest1 : List (BitVec 8)) (limit : Nat)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks_max : ch.links.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 4 ≤ rem)
    (hf : f + 4 * rest1.length + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 592#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_tag3 : List AllocEvent) (sf : State) (P' : SepProp),
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption =
        some (ch', rest2) →
      ch'.links.length = ch.links.length + 1 →
      rest2.length < rest1.length →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length) + 1) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_tag3) →
      M.stepEvents (evs_acc ++ evs_tag3) st0 = M.stepEvents evs_tag3 st →
      FitsEnv M lim (M.stepEvents evs_tag3 st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_tag3 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  have hreord_tag3 :
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
          ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s =
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
          ⟨optVn, some ch, inner⟩ ∗
        (((s0.sp - 688#64) ↦₆₄ w0) ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
          memRegion (s0.sp - 680#64) 40 ∗
          memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A lim st x s0 s) := by sep_ac_rfl
  rw [hreord_tag3]
  refine SepWPpIPlaced.mono_pre
    (sepConj_mono_left
      (protoPqRatchetStateCapOkAt_expose_ch_links H_inner A.repAlloc s0.sp rest1.length optVn ch
        inner)) ?_
  rw [sepConj_assoc]
  apply SepWPpIPlaced.pure_elim; intro hlinks1
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  by_cases hwt : iwt = .lengthDelimited
  · -- iwt == .lengthDelimited (x0 == 2) -> +600
    have hx0_2 : s.readReg64 .x0 = 2#64 := by rw [hx0, hwt]; rfl
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 600#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm, hx0_2]) (by simp only [arm64_norm, hrun])
    refine decodeState_epoch_merge_536f4_placed_ofEnv
      (v20 := BitVec.ofNat 64 limit) (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st evs_acc f rem w0 ⟨optVn, some ch, inner⟩ rest1
      hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [chainPB_mergeField_tag3, hwt]
        dsimp only [codecWireTypeToProto]
        rw [hnone]; rfl))
      hacc hst hFit hrem hf s0 _ _ R post hpost hpost_env hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_2])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl) ?_
    intro ep' rest2 evs_em sf1 P1 hok_mm hle2 hsuf2 hacc1 hst1 hFit1
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
      hP1
    have hlt2 : rest2.length < rest1.length := proto_mergeMessage_length_lt hok_mm
    have hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54 := by
      have : (ch.links ++ [ep']).length = ch.links.length + 1 := by simp
      omega
    have hok_tag3 :
        (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption =
          some ({ ch with links := ch.links ++ [ep'] }, rest2) := by
      rw [chainPB_mergeField_tag3, hwt]
      dsimp only [codecWireTypeToProto]
      rw [hok_mm]; rfl
    refine decodeState_chain_push_5370c_placed_loop_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 (M.stepEvents evs_em st) (evs_acc ++ evs_em)
      (f + 4 * (rest1.length - rest2.length)) (rem - 4 * (rest1.length - rest2.length))
      optVn ch inner ep' rest2 limit
      hlinks_next hlinks_max hacc1 hst1 hFit1 (by omega)
      s0 sf1 P1 R post hs0A
      hpc1 hrun1 hsp1 htr1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hP1 ?_
    intro w0' evs_push sf2 P2 _hpush hacc2 hst2 hFit2
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
      hx29_2 hP2
    rw [List.append_assoc] at hacc2 hst2
    rw [← M.stepEvents_append] at hst2 hFit2 hP2
    rw [Nat.sub_sub] at hFit2
    exact hloop w0' { ch with links := ch.links ++ [ep'] } rest2 (evs_em ++ evs_push) sf2 P2
      hok_tag3 (by simp) hlt2 hle2 hsuf2 hacc2 hst2 hFit2
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
      hx29_2 hP2
  · -- iwt != .lengthDelimited -> +2708
    have ⟨hbeq, hbne⟩ := wt_ne_two_of_ne_lengthDelimited hwt
    have herr : spqrDecodeState x.st.bytes = .error .stateDecode := by
      apply herr_of_none
      rw [chainPB_mergeField_tag3,
        mergeMessage_toOption_of_ne_lengthDelimited ChainEpochPB.mergeField hwt]
      rfl
    have hfits1 : FitsEnv M lim st DecodeErrorFromEnv :=
      fitsEnv_decodeErrorFrom_of_loop (by omega) hFit
    have hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
        FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0) :=
      fun evs_fr hfr =>
        fitsEnv_decodeErrorPush_of_loop (by decide : 0 ≤ 4) (by decide : 1 ≤ 3)
          (FitsEnv.decodeStateLoop_tail (decodeStateIterEnv_of_decodeErrorFrom hfr)
            (FitsEnv.decodeStateLoop_mono (by omega : 3 + 1 ≤ rem)
              (Nat.le_refl _) (Nat.le_refl _) hFit))
    have hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
        FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1) :=
      fun evs_fr evs_p1 hfr hp1 =>
        fitsEnv_decodeErrorPush_of_loop (by decide : 1 ≤ 4) (by decide : 1 ≤ 2)
          (FitsEnv.decodeStateLoop_tail (.pushErr (by decide : 0 ≤ 4) hp1)
            (FitsEnv.decodeStateLoop_tail (decodeStateIterEnv_of_decodeErrorFrom hfr)
              (FitsEnv.decodeStateLoop_mono (by omega : 3 + 1 ≤ rem)
                (Nat.le_refl _) (Nat.le_refl _) hFit)))
    have henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
        DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
        FreeOnlyEvs evs_f →
        ∃ evs, PostEnv x evs ∧
          M.stepEvents evs st0 =
            M.stepEvents evs_f
              (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))) :=
      fun evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree =>
        lift_postEnv hpost_env
          (decodeStateEnv_of_loop_from_push2_free (by omega) hacc hst
            evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree)
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2708#64)
    refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest1 rest1.length
      ⟨optVn, some ch, inner⟩ s0 s) (by sep_focus) ?_
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm, hx0, hbeq, hbne]) (by simp only [arm64_norm, hrun])
    exact SepWPpIPlaced.of_sepWPp
      (decodeState_err_chain_epoch_wt_53f30_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc.toDecodeStateCalleeContractsPlaced
        x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post hpost herr
        hfits1 hfits2 hfits3 henv
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0, hbeq, hbne])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx29])
        (by unfold decodeStateErrFramePlaced; pool_reg_norm; sep_ac_rfl))

theorem decodeState_chain_tag3_536ec_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (iwt : WireType) (rest1 : List (BitVec 8)) (limit : Nat)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks_max : ch.links.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 4 ≤ rem)
    (hf : f + 4 * rest1.length + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 592#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_tag3 : List AllocEvent) (sf : State) (P' : SepProp),
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption =
        some (ch', rest2) →
      ch'.links.length = ch.links.length + 1 →
      rest2.length < rest1.length →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length) + 1) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_tag3) →
      M.stepEvents (evs_acc ++ evs_tag3) st0 = M.stepEvents evs_tag3 st →
      FitsEnv M lim (M.stepEvents evs_tag3 st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_tag3 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_tag3_536ec_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 optVn ch inner iwt rest1 limit
    hrest1_le hrest1_suf hlen_bound hlinks_max herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29 hP hloop

theorem decodeState_chain_tag3_536ec_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (iwt : WireType) (rest1 : List (BitVec 8)) (limit : Nat)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks_max : ch.links.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 4 ≤ rem)
    (hf : f + 4 * rest1.length + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 592#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_tag3 : List AllocEvent) (sf : State) (P' : SepProp),
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption =
        some (ch', rest2) →
      ch'.links.length = ch.links.length + 1 →
      rest2.length < rest1.length →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length) + 1) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_tag3) →
      M.stepEvents (evs_acc ++ evs_tag3) st0 = M.stepEvents evs_tag3 st →
      FitsEnv M lim (M.stepEvents evs_tag3 st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_tag3 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_tag3_536ec_placed
    hc x st0 st evs_acc f rem w0 optVn ch inner iwt rest1 limit
    hrest1_le hrest1_suf hlen_bound hlinks_max herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost hs0A
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29 hP hloop

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlacedBudget
