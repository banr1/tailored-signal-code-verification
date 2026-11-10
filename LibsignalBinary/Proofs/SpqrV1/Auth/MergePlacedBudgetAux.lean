/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget Envelopes and Step Lemmas for `Authenticator::merge` (Block `295`)

Defines bounded allocator event envelopes (`AuthPlacedMergeIterEnv`, `AuthPlacedMergeLoopEnv`,
`AuthPlacedMergeEnv`, `AuthPlacedMergePostEnv`), the budget-threaded specification `authMergeSpec`,
and code-loaded `[LibsignalPlacement]` exit and field step lemmas for Block `295`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_295 blkPl_295 lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost HighCalleeSaved IsDropSuffix SkipFieldGhost
   bytesMergeCapOk_mono pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3 skipBelow3_err skipBelow3_err_entails skipField3Stack stackAt_skipField3)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro codecWireTypeToProto
   decodeErrorWith_one_entails_le1 decodeErrorWith_zero_entails_le1
   pointsTo64_memRegion40_entails_48 skipBelow3_bytesMerge3 skipBelow3_bytesMerge3_entails)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost SepWPp.pure_elim SepWPp.pure_elim2 WppPost authMergeStack
   authenticatorPBAt_entails_exists authenticatorPBCapAt
   authenticatorPBCapAt_entails_authenticatorPBAt authenticatorPBCapAt_mono bv64_add_zero
   bv64_sub_zero memRegion8_memRegion40_entails_48 memRegion_48_split_96 mergeBytes_length
   setWidth8_ofNat64_wt skipBelow3_97_eq_stackAt_96)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env BytesMerge3EnvCore WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## Allocation Envelopes and Budget Specification -/

theorem stepEvents_append {M : AllocCostModel} (evs₁ evs₂ : List AllocEvent) (st : M.σ) :
    M.stepEvents (evs₁ ++ evs₂) st = M.stepEvents evs₂ (M.stepEvents evs₁ st) := by
  simp only [AllocCostModel.stepEvents, List.foldl_append]

private theorem mergeBytes_val_length {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    v.length ≤ bs.length := by
  unfold mergeBytes at h
  split at h
  · contradiction
  · rcases hdv : decodeVarint bs with _ | ⟨len, r0⟩
    · rw [hdv] at h; contradiction
    · rw [hdv] at h; dsimp only at h
      split at h
      · contradiction
      · injection h with hpair; injection hpair with hv _
        subst hv
        have hlt := decodeVarint_length hdv
        rw [List.length_take]
        omega

/-- Single-leaf allocator event envelope inside `prost::encoding::message::merge::<Authenticator, _>`
on an input slice of length at most `maxLen`, backed by exact deterministic `BytesMerge3EnvCore`
plus explicit `bytesTmpCopy` when `valCap > 2 * maxLen + 64` (so `doReserveClearEvents = []`). -/
inductive AuthPlacedMergeIterEnv (maxLen : Nat) : List AllocEvent → Prop where
  | nil : AuthPlacedMergeIterEnv maxLen []
  | fromErr : AuthPlacedMergeIterEnv maxLen (rustAllocEvents 72 8)
  | pushErr {n : Nat} {evs : List AllocEvent} :
      n ≤ 1 → DecodeErrorPushEnv n evs → AuthPlacedMergeIterEnv maxLen evs
  | bytesTmpCopy {n : Nat} :
      n ≤ maxLen →
      AuthPlacedMergeIterEnv maxLen (rustAllocEvents n 1 ++ rustDeallocEvents n 1)
  | bytesMerge (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) {evs : List AllocEvent} :
      bs.length ≤ maxLen → valCap.toNat ≤ 2 * maxLen + 64 →
      BytesMerge3EnvCore wt valCap bs evs → AuthPlacedMergeIterEnv maxLen evs

theorem AuthPlacedMergeIterEnv.mono {maxLen₁ maxLen₂ : Nat} {evs : List AllocEvent}
    (hlen : maxLen₁ ≤ maxLen₂) (h : AuthPlacedMergeIterEnv maxLen₁ evs) :
    AuthPlacedMergeIterEnv maxLen₂ evs := by
  cases h with
  | nil => exact .nil
  | fromErr => exact .fromErr
  | pushErr hn hp => exact .pushErr hn hp
  | bytesTmpCopy hn => exact .bytesTmpCopy (Nat.le_trans hn hlen)
  | bytesMerge wt valCap bs hbs hcap hb =>
    exact .bytesMerge wt valCap bs (Nat.le_trans hbs hlen) (Nat.le_trans hcap (by omega)) hb

theorem AuthPlacedMergeIterEnv.of_decodeErrorFrom {maxLen : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) : AuthPlacedMergeIterEnv maxLen evs := by
  rw [h]; exact .fromErr

theorem AuthPlacedMergeIterEnv.of_decodeErrorPush0 {maxLen : Nat} {evs : List AllocEvent}
    (h : DecodeErrorPushEnv 0 evs) : AuthPlacedMergeIterEnv maxLen evs :=
  .pushErr (Nat.zero_le 1) h

theorem AuthPlacedMergeIterEnv.of_decodeVarint2 {maxLen : Nat} {bs : List (BitVec 8)}
    {evs : List AllocEvent} (h : DecodeVarint2Env bs evs) :
    AuthPlacedMergeIterEnv maxLen evs := by
  change DecodeVarintSliceEnv bs evs at h
  rw [h]; unfold decodeVarintSliceEvents
  cases decodeVarint bs
  · exact .fromErr
  · exact .nil

theorem AuthPlacedMergeIterEnv.of_skipField3 {maxLen : Nat} {x : SkipFieldGhost}
    {evs : List AllocEvent} (h : SkipField3Env x evs) :
    AuthPlacedMergeIterEnv maxLen evs := by
  change SkipFieldEnv x evs at h
  rw [h]; unfold skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs
  · exact .fromErr
  · exact .nil

theorem AuthPlacedMergeIterEnv.of_bytesMerge3 {maxLen : Nat} {x : BytesMergeGhost}
    {evs : List AllocEvent} (hlen : x.bs.length ≤ maxLen) (h : BytesMerge3Env x evs) :
    AuthPlacedMergeIterEnv maxLen evs := by
  by_cases hcap : x.valCap.toNat ≤ 2 * maxLen + 64
  · exact .bytesMerge x.wt x.valCap x.bs hlen hcap h
  · change evs = bytesMergeEventsCore x.wt x.valCap x.bs at h
    rw [h]; unfold bytesMergeEventsCore
    cases hmb : mergeBytes x.wt x.bs with
    | none => exact .fromErr
    | some p =>
      rcases p with ⟨v, rest⟩
      dsimp only
      by_cases hv0 : v.length = 0
      · simp only [hv0, ↓reduceIte]; exact .nil
      · simp only [hv0, ↓reduceIte]
        have hv_le_bs : v.length ≤ x.bs.length := mergeBytes_val_length hmb
        have hv_le_cap : v.length ≤ x.valCap.toNat := by omega
        have hdrc : doReserveClearEvents x.valCap.toNat v.length = [] := by
          unfold doReserveClearEvents; simp only [hv_le_cap, ↓reduceIte]
        simp only [hdrc, List.append_nil]
        exact .bytesTmpCopy (Nat.le_trans hv_le_bs hlen)

/-- Bounded-fuel sequential closure of `AuthPlacedMergeIterEnv maxLen`. -/
inductive AuthPlacedMergeLoopEnv : Nat → Nat → List AllocEvent → Prop where
  | nil {fuel maxLen : Nat} : AuthPlacedMergeLoopEnv fuel maxLen []
  | step {fuel maxLen : Nat} {evs₁ evs₂ : List AllocEvent} :
      AuthPlacedMergeIterEnv maxLen evs₁ →
      AuthPlacedMergeLoopEnv fuel maxLen evs₂ →
      AuthPlacedMergeLoopEnv (fuel + 1) maxLen (evs₁ ++ evs₂)

theorem AuthPlacedMergeLoopEnv.single {fuel maxLen : Nat} {evs : List AllocEvent}
    (h : AuthPlacedMergeIterEnv maxLen evs) :
    AuthPlacedMergeLoopEnv (fuel + 1) maxLen evs := by
  simpa using AuthPlacedMergeLoopEnv.step (fuel := fuel) h .nil

theorem AuthPlacedMergeLoopEnv.mono_fuel {fuel₁ fuel₂ maxLen : Nat} {evs : List AllocEvent}
    (hle : fuel₁ ≤ fuel₂) (h : AuthPlacedMergeLoopEnv fuel₁ maxLen evs) :
    AuthPlacedMergeLoopEnv fuel₂ maxLen evs := by
  induction h generalizing fuel₂ with
  | nil => exact .nil
  | @step fuel _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 1 := ⟨fuel₂ - 1, by omega⟩
    exact .step h1 (ih (by omega))

theorem AuthPlacedMergeLoopEnv.mono {f₁ f₂ maxLen₁ maxLen₂ : Nat} {evs : List AllocEvent}
    (hf : f₁ ≤ f₂) (hlen : maxLen₁ ≤ maxLen₂)
    (h : AuthPlacedMergeLoopEnv f₁ maxLen₁ evs) :
    AuthPlacedMergeLoopEnv f₂ maxLen₂ evs := by
  induction h generalizing f₂ with
  | nil => exact .nil
  | @step fuel _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
    exact .step (h1.mono hlen) (ih (by omega) hlen)

theorem AuthPlacedMergeLoopEnv.append {f₁ f₂ maxLen : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : AuthPlacedMergeLoopEnv f₁ maxLen evs₁)
    (h₂ : AuthPlacedMergeLoopEnv f₂ maxLen evs₂) :
    AuthPlacedMergeLoopEnv (f₁ + f₂) maxLen (evs₁ ++ evs₂) := by
  induction h₁ with
  | @nil fuel _ =>
    simpa using h₂.mono_fuel (Nat.le_add_left f₂ fuel)
  | @step fuel _ e₁ e₂ head _ ih =>
    rw [List.append_assoc, show fuel + 1 + f₂ = (fuel + f₂) + 1 by omega]
    exact .step head (ih h₂)

theorem FitsEnv.authPlacedMergeLoop_head {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen : Nat} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → AuthPlacedMergeIterEnv maxLen evs)
    (hFit : FitsEnv M lim st (AuthPlacedMergeLoopEnv (fuel + 1) maxLen)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (AuthPlacedMergeLoopEnv.single (hsub evs he))

theorem FitsEnv.authPlacedMergeLoop_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ maxLen : Nat} {evs₁ : List AllocEvent}
    (h₁ : AuthPlacedMergeLoopEnv f₁ maxLen evs₁)
    (hFit : FitsEnv M lim st (AuthPlacedMergeLoopEnv (f₁ + f₂) maxLen)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (AuthPlacedMergeLoopEnv f₂ maxLen) :=
  fun evs₂ h₂ =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (h₁.append h₂))).2

/-- Precondition allocation envelope of placed `Authenticator::merge` (Block `295`, depth `97`). -/
def AuthPlacedMergeEnv (x : AuthMergeGhost) (evs : List AllocEvent) : Prop :=
  AuthPlacedMergeLoopEnv (4 * x.bs.length + 8) x.bs.length evs

/-- Postcondition allocation envelope of placed `Authenticator::merge` (Block `295`). -/
def AuthPlacedMergePostEnv (x : AuthMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption with
  | some (_, rest) => AuthPlacedMergeLoopEnv (4 * (x.bs.length - rest.length)) x.bs.length evs
  | none => AuthPlacedMergeLoopEnv (4 * x.bs.length + 8) x.bs.length evs

theorem authPlacedMergePostEnv_imp_pre {x : AuthMergeGhost} {evs : List AllocEvent}
    (h : AuthPlacedMergePostEnv x evs) :
    AuthPlacedMergeEnv x evs := by
  dsimp only [AuthPlacedMergePostEnv, AuthPlacedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Budget-threaded specification of `Authenticator::merge` (Block `295`). -/
def authMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (AuthMergeGhost × M.σ) :=
  authMergeSpecOfEnv A lim AuthPlacedMergeEnv AuthPlacedMergePostEnv

/-! ## Loop and Error-Exit Spatial Bundles -/

abbrev authBudgetLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : ProtoAuthenticator) (bs cur : List (BitVec 8)) : SepProp :=
  authenticatorPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool lim st s ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelow3 s0.sp 97

abbrev authBudgetErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : ProtoAuthenticator) (bs : List (BitVec 8)) : SepProp :=
  authenticatorPBAt A.repAlloc msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗
    memRegion slot 16 ∗
    (ptr ↦ₛ bs) ∗
    A.pool lim st s ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

/-! ## Code-Loaded Exit and Field Step Lemmas -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_err0_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hevs : ∃ evs, PostEnv x evs ∧ st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hevs with ⟨evs, hevs_post, rfl⟩
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpecOfEnv
  simp only [hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide), authBudgetErrFrame,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_from_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {w v_stk0 : BitVec 64}
    (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hw : KindNoHeap w)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_from : ∀ evs_f, DecodeErrorFromEnv evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = w)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authBudgetErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 96#64, w, st_cur))
    (ret_pc := (blkPl_295).base + 112#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], hw, hfits_from⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpecOfEnv
  simp only [decodeErrorFromBudgetSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨_herr, htrm⟩
  wp_focus_pure; intro hevs_f
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_from evs_f hevs_f
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc _) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_push_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 436#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 97 ∗
        authBudgetErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authBudgetErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorPushBudgetSpec M A lim)
    (x := (s0.sp - 96#64, err, 0, st_cur))
    (ret_pc := (blkPl_295).base + 440#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, hfits_push⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpecOfEnv
  simp only [decodeErrorPushBudgetSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_push evs_p hevs_p
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_skip_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hfits_sf : FitsEnv M lim st_cur
      (SkipField3Env ⟨iwt, tag, 96, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hevs_sf_err : skipField (2 * rest.length + 2) 96 tag iwt rest = none →
      ∀ evs_sf,
        SkipField3Env ⟨iwt, tag, 96, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_sf →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_sf st_cur = M.stepEvents evs st0)
    (hnone_of_sf : skipField (2 * rest.length + 2) 96 tag iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 96 tag iwt rest = some rest' →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [authBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_97_eq_stackAt_96 s0.sp]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := skipField3Spec A lim)
    (x := (⟨iwt, tag, 96, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 152#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx1], htag_lt,
     by simp only [arm64_norm, hsp, hx19],
     by simp only [arm64_norm, hsp], (by decide : 96 < 2 ^ 32), hrest_lt, hfits_sf⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 96 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 116#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_97_eq_stackAt_96,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr rest.length m) (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 116#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_err0_ret_exit_placed hnone (hevs_sf_err hsf evs_sf hevs_sf) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm]) hsm0
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩)
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_97_eq_stackAt_96,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    have hevs_nil : evs_sf = [] := by
      change SkipFieldEnv _ evs_sf at hevs_sf
      simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using hevs_sf
    subst hevs_nil
    conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_mono A.repAlloc x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont rest' _ hsf
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_tag1_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_bm : ∀ cap1 ptr1 : BitVec 64, BytesMergeCapOk cap1 rest.length →
      FitsEnv M lim st_cur
        (BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hfits_push : ∀ (cap1 ptr1 : BitVec 64) (evs_bm : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (DecodeErrorPushEnv 0))
    (hevs_bm_err : ∀ (cap1 ptr1 : BitVec 64) (evs_bm evs_p : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      DecodeErrorPushEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p (M.stepEvents evs_bm st_cur) = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (cap1 ptr1 : BitVec 64) (v rest' : List (BitVec 8))
      (evs_bm : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  conv =>
    arg 4
    rw [authBudgetLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 264#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap1, hfits_bm cap1 ptr1 hcap1⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
        vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A.repAlloc x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 436#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_push_err_exit_cl_placed hPushCall hnone hsm0
        (hfits_push cap1 ptr1 evs_bm hmb hevs_bm)
        (fun evs_p hp => hevs_bm_err cap1 ptr1 evs_bm evs_p hmb hevs_bm hp)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap2' : BytesMergeCapOk cap2 rest'.length := bytesMergeCapOk_mono hcap2 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap1'
    apply SepWP.exists_elim; intro ptr1'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap1'
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A.repAlloc x.msgPtr cap1' ptr1' v ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with rootKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont cap1 ptr1 v rest' evs_bm _ hmb hevs_bm
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_tag2_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_bm : ∀ cap2 ptr2 : BitVec 64, BytesMergeCapOk cap2 rest.length →
      FitsEnv M lim st_cur
        (BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hfits_push : ∀ (cap2 ptr2 : BitVec 64) (evs_bm : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (DecodeErrorPushEnv 0))
    (hevs_bm_err : ∀ (cap2 ptr2 : BitVec 64) (evs_bm evs_p : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      DecodeErrorPushEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p (M.stepEvents evs_bm st_cur) = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (cap2 ptr2 : BitVec 64) (v rest' : List (BitVec 8))
      (evs_bm : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  conv =>
    arg 4
    rw [authBudgetLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 240#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap2, hfits_bm cap2 ptr2 hcap2⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
        vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A.repAlloc x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 436#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_push_err_exit_cl_placed hPushCall hnone hsm0
        (hfits_push cap2 ptr2 evs_bm hmb hevs_bm)
        (fun evs_p hp => hevs_bm_err cap2 ptr2 evs_bm evs_p hmb hevs_bm hp)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap1' : BytesMergeCapOk cap1 rest'.length := bytesMergeCapOk_mono hcap1 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap2'
    apply SepWP.exists_elim; intro ptr2'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap2'
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
          vecU8At A.repAlloc (x.msgPtr + 24#64) cap2' ptr2' v ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with macKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont cap2 ptr2 v rest' evs_bm _ hmb hevs_bm
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

end LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
