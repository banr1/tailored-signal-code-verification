/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SignalMessage>::try_from` Loop Envelopes & Error Tails

Defines the slice- and capacity-indexed decode loop envelope `SigTryFromLoopBoundedEnv`
(`TryFromLoopEnv`), ghost capacity invariants, panic-free `SepWPp` combinators, shared error tails
(`decodeErrorFrom_tail_wp_placed`, `decodeErrorPush_tail_wp_placed`), and `fineCostModel`
non-vacuity witnesses for Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession (ProtoSignalMessage)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeUint32 mergeBytes skipField emptyProtoSignalMessage)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_85 blkPl_85 blkLib_eq_85 extHookStack varintSlow
   LibsignalCodeRoLoaded withLsCodeRoLoaded
   KindNoHeap decodeErrorAtStackLen decodeErrorFromName decodeErrorPushName reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SkipFieldGhost Int32MergeGhost BytesMergeGhost BytesMergeCapOk
   bytesMergeCapOk_zero bytesMergeCapOk_reserveCap_bound
   WireSignalMessageGhost wireSignalMessageAt
   optVecU8At optU32At
   skipFieldStackX wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp tryFromPlacedProg LoopRegs LoopExitStatePlaced VRegsAt tryFromQp
   WireGhostCapOk wireSignalMessageLoopOf wireSignalMessageAt_entails_loopOf
   wireSignalMessageAt_entails_of
   wireSignalMessageAt_split_addr wireSignalMessageAt_split_rk
   wireSignalMessageAt_split_ct wireSignalMessageAt_split_pq
   sepExists_intro pure_true_emp
   decodeVarint_suffix
   loopExitMem loopExitMem_append_prefix loopExitMem_err_intro
   stackAt_sub_split memRegion48_split8 entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents rustDeallocEvents rustReallocEvents fitsEvents_append)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv
   decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm sepWPp_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents
   Int32MergeEnv int32MergeEvents
   SkipFieldEnv skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (DecodeErrorPushBoundedEnv decodeErrorPushBoundedSpecWithStack bmNextCap
   TripleRatchetHooksWPlaced IntoBoxedSliceOkPlaced TryCloneFromRefOkPlaced
   DecodeVarintSliceOkWPlaced Int32MergeOkWPlaced SkipFieldOkWPlaced
   DropDecodeErrorOkWPlaced BytesMergeOkWPlaced DropSpeOkWPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit

/-! ## Slice- and capacity-indexed loop envelope (`SigTryFromLoopBoundedEnv`, `TryFromLoopEnv`) -/

export LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (DecodeErrorPushBoundedEnv bmNextCap)

/-- Length-delimited `ProtoSignalMessage` `Vec<u8>` field selector. -/
inductive SigTryFromField where
  | rk | ct | pq | ad

/-- Per-field `Vec<u8>` capacities tracked across `SignalMessage::try_from`'s decode loop. -/
structure SigTryFromCaps where
  rk : Nat
  ct : Nat
  pq : Nat
  ad : Nat

def SigTryFromCaps.zero : SigTryFromCaps := ⟨0, 0, 0, 0⟩

def SigTryFromCaps.get (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => c.rk | .ct => c.ct | .pq => c.pq | .ad => c.ad

def SigTryFromCaps.set (c : SigTryFromCaps) : SigTryFromField → Nat → SigTryFromCaps
  | .rk, v => { c with rk := v }
  | .ct, v => { c with ct := v }
  | .pq, v => { c with pq := v }
  | .ad, v => { c with ad := v }

/-- Terminal allocator event envelope at loop exit (`Ok` `[]`, `DecodeError::from` only, or
`DecodeError::from` followed by `<DecodeError>::push` at `stack.len = 0`). -/
inductive SigTryFromErrTailEnv : List AllocEvent → Prop where
  | nil : SigTryFromErrTailEnv []
  | fromOnly : SigTryFromErrTailEnv (rustAllocEvents 72 8)
  | fromPush {evs_p : List AllocEvent} :
      DecodeErrorPushBoundedEnv 0 evs_p →
      SigTryFromErrTailEnv (rustAllocEvents 72 8 ++ evs_p)

/-- Slice-budgeted protobuf decode loop envelope for `SignalMessage::try_from`:
indexed by remaining input byte count `rem` and the 4 `ProtoSignalMessage` `Vec<u8>` field
capacities `(rk, ct, pq, ad)`. -/
inductive SigTryFromLoopBoundedEnv : Nat → SigTryFromCaps → List AllocEvent → Prop where
  | done {rem : Nat} {caps : SigTryFromCaps} {evs : List AllocEvent} :
      SigTryFromErrTailEnv evs →
      SigTryFromLoopBoundedEnv rem caps evs
  | skipStep {rem rem' : Nat} {caps : SigTryFromCaps} {evs : List AllocEvent} :
      rem' < rem →
      SigTryFromLoopBoundedEnv rem' caps evs →
      SigTryFromLoopBoundedEnv rem caps evs
  | bytesStep (f : SigTryFromField) {rem rem' : Nat} {caps : SigTryFromCaps}
      (wt : WireType) (bs v rest : List (BitVec 8)) {evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ rem →
      rem' + v.length + 1 ≤ rem →
      caps.get f < 2 ^ 63 →
      SigTryFromLoopBoundedEnv rem'
        (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
        evs₂ →
      SigTryFromLoopBoundedEnv rem caps
        (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂)

/-- Top-level loop envelope starting from zeroed `Option<Vec<u8>>` fields on a slice of `rem`
bytes (retaining the legacy `_fuel` parameter solely for caller signature compatibility). -/
abbrev TryFromLoopEnv (_fuel rem : Nat) : List AllocEvent → Prop :=
  SigTryFromLoopBoundedEnv rem SigTryFromCaps.zero

/-- `mergeBytes wt bs = some (v, rest)` consumes at least `1 + v.length` bytes (`1 ≤ k_varint`). -/
theorem mergeBytes_progress {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    rest.length + v.length + 1 ≤ bs.length := by
  unfold mergeBytes at h
  split_ifs at h
  cases hd : decodeVarint bs with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨len, r1⟩
    simp only [hd] at h
    split_ifs at h with hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨k1, hk1_pos, hk1_le, hr1⟩ := decodeVarint_suffix hd
    have hr1_len : r1.length = bs.length - k1 := by simp [hr1]
    have hv_len : (r1.take len.toNat).length = len.toNat := by simp; omega
    have hrest_len : (r1.drop len.toNat).length = r1.length - len.toNat := by simp
    omega

theorem SigTryFromLoopBoundedEnv.mono_rem {rem₁ rem₂ : Nat} {caps : SigTryFromCaps}
    {evs : List AllocEvent} (hle : rem₁ ≤ rem₂)
    (h : SigTryFromLoopBoundedEnv rem₁ caps evs) :
    SigTryFromLoopBoundedEnv rem₂ caps evs := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact h
  · exact .skipStep hlt h

theorem SigTryFromErrTailEnv.of_decodeErrorFrom {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) : SigTryFromErrTailEnv evs := by
  rw [h]; exact .fromOnly

theorem SigTryFromErrTailEnv.of_decodeVarintSlice {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DecodeVarintSliceEnv bs evs) : SigTryFromErrTailEnv evs := by
  rw [h]; unfold decodeVarintSliceEvents
  cases decodeVarint bs
  · exact .fromOnly
  · exact .nil

theorem SigTryFromErrTailEnv.of_decodeVarintSlow {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DecodeVarintSlowEnv bs evs) : SigTryFromErrTailEnv evs := by
  rw [h]; unfold decodeVarintSlowEvents
  cases varintSlow bs
  · exact .fromOnly
  · exact .nil

theorem SigTryFromErrTailEnv.of_int32Merge {x : Int32MergeGhost} {evs : List AllocEvent}
    (h : Int32MergeEnv x evs) : SigTryFromErrTailEnv evs := by
  rw [h]; unfold int32MergeEvents
  cases mergeUint32 x.wt x.bs
  · exact .fromOnly
  · exact .nil

theorem SigTryFromErrTailEnv.of_skipField {x : SkipFieldGhost} {evs : List AllocEvent}
    (h : SkipFieldEnv x evs) : SigTryFromErrTailEnv evs := by
  rw [h]; unfold skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs
  · exact .fromOnly
  · exact .nil

theorem fitsEnv_sigLoop_errTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → SigTryFromErrTailEnv evs)
    (hFit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (.done (hsub evs he))

theorem fitsEnv_sigLoop_pushAfterFrom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    (hFit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps)) :
    FitsEnv M lim (M.stepEvents (rustAllocEvents 72 8) st) (DecodeErrorPushBoundedEnv 0) :=
  fun evs_p hp =>
    ((fitsEvents_append M lim (rustAllocEvents 72 8) evs_p st).mp
      (hFit (rustAllocEvents 72 8 ++ evs_p) (.done (.fromPush hp)))).2

theorem fitsEnv_sigLoop_bytesMerge {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (f : SigTryFromField) {rem : Nat} {caps : SigTryFromCaps} {x : BytesMergeGhost}
    (hcap_eq : x.valCap = BitVec.ofNat 64 (caps.get f))
    (hcap_lt : caps.get f < 2 ^ 63)
    (hbs_le : x.bs.length ≤ rem)
    (hFit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps)) :
    FitsEnv M lim st (BytesMergeEnv x) := by
  intro evs hevs
  rw [BytesMergeEnv, hcap_eq] at hevs
  subst hevs
  cases hm : mergeBytes x.wt x.bs with
  | none =>
    have heq : bytesMergeEventsCore x.wt (BitVec.ofNat 64 (caps.get f)) x.bs =
        rustAllocEvents 72 8 := by simp [bytesMergeEventsCore, hm]
    rw [heq]
    exact hFit _ (.done .fromOnly)
  | some p =>
    rcases p with ⟨v, rest⟩
    have hprog := mergeBytes_progress hm
    have hstep : SigTryFromLoopBoundedEnv rem caps
        (bytesMergeEventsCore x.wt (BitVec.ofNat 64 (caps.get f)) x.bs ++ []) :=
      .bytesStep f (rem' := rest.length) x.wt x.bs v rest hm hbs_le (by omega) hcap_lt (.done .nil)
    rw [List.append_nil] at hstep
    exact hFit _ hstep

theorem fitsEnv_sigLoop_bytesTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (f : SigTryFromField) {rem rem' : Nat} {caps : SigTryFromCaps}
    {wt : WireType} {bs v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest))
    (hbs_le : bs.length ≤ rem)
    (hprog : rem' + v.length + 1 ≤ rem)
    (hcap_lt : caps.get f < 2 ^ 63)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs)
    (hFit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps)) :
    FitsEnv M lim (M.stepEvents evs₁ st)
      (SigTryFromLoopBoundedEnv rem' (caps.set f (bmNextCap (caps.get f) v.length))) := by
  subst hevs₁
  intro evs₂ h2
  exact ((fitsEvents_append M lim _ evs₂ st).mp
    (hFit _ (.bytesStep f wt bs v rest hm hbs_le hprog hcap_lt h2))).2

theorem fitsEnv_sigLoop_skipStep {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem rem' : Nat} {caps : SigTryFromCaps} (hlt : rem' < rem)
    (hFit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps)) :
    FitsEnv M lim st (SigTryFromLoopBoundedEnv rem' caps) :=
  fun evs h => hFit evs (.skipStep hlt h)

theorem fitsEnv_sigLoop_mono_rem {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem₁ rem₂ : Nat} {caps : SigTryFromCaps} (hle : rem₁ ≤ rem₂)
    (hFit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem₂ caps)) :
    FitsEnv M lim st (SigTryFromLoopBoundedEnv rem₁ caps) :=
  fun evs h => hFit evs (h.mono_rem hle)

/-! ### Ghost Capacity Match Invariant (`WireGhostCapsMatch`, `wireSignalMessageLoopCapsOf`) -/

def optFieldCapMatch (u : Option (List (BitVec 8))) (pin : VecPin) (c : Nat) : Prop :=
  c < 2 ^ 63 ∧
  match u with
  | none => c = 0
  | some _ => pin.cap.toNat = c

theorem optFieldCapMatch_init {u : Option (List (BitVec 8))} {pin : VecPin} {c : Nat}
    {cap0 : BitVec 64} {bsLen : Nat}
    (hc : optFieldCapMatch u pin c)
    (hpin : BytesMergeCapOk pin.cap bsLen)
    (hcap0 : match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) :
    BytesMergeCapOk cap0 bsLen ∧ cap0 = BitVec.ofNat 64 c ∧ cap0.toNat = c ∧ c < 2 ^ 63 := by
  rcases hc with ⟨hlt, hm⟩
  cases u with
  | none =>
    dsimp only at hm hcap0
    subst hm; subst hcap0
    exact ⟨bytesMergeCapOk_zero, rfl, rfl, hlt⟩
  | some _ =>
    dsimp only at hm hcap0
    subst hcap0; subst hm
    exact ⟨hpin, by apply BitVec.eq_of_toNat_eq; simp, rfl, hlt⟩

theorem bmNextCap_lt_two_pow_63 {cap0 : BitVec 64} {wt : WireType} {bs v rest : List (BitVec 8)}
    (hcap0_ok : BytesMergeCapOk cap0 bs.length) (hcap0_lt : cap0.toNat < 2 ^ 63)
    (hbs_lt : bs.length < 2 ^ 63) (hm : mergeBytes wt bs = some (v, rest)) :
    bmNextCap cap0.toNat v.length < 2 ^ 63 := by
  unfold bmNextCap
  split_ifs with hle
  · exact hcap0_lt
  · have hprog := mergeBytes_progress hm
    have hb := bytesMergeCapOk_reserveCap_bound (vLen := v.length) (restLen := rest.length)
      hcap0_ok (by omega) (by omega) hbs_lt
    omega

structure WireGhostCapsMatch (g : WireSignalMessageGhost) (m : ProtoSignalMessage)
    (caps : SigTryFromCaps) : Prop where
  rk : optFieldCapMatch m.ratchetKey g.rk caps.rk
  ct : optFieldCapMatch m.ciphertext g.ct caps.ct
  pq : optFieldCapMatch m.pqRatchet g.pq caps.pq
  ad : optFieldCapMatch m.addresses g.addr caps.ad

def wireSignalMessageLoopCapsOf (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) : SepProp :=
  ∃∗ g : WireSignalMessageGhost,
    ⌜WireGhostCapOk g n ∧ WireGhostCapsMatch g m caps⌝ ∗ wireSignalMessageAt A g a m

theorem wireSignalMessageAt_entails_loopCapsOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (a : BitVec 64) (n : Nat) (caps : SigTryFromCaps) (m : ProtoSignalMessage)
    (hg : WireGhostCapOk g n) (hc : WireGhostCapsMatch g m caps) :
    wireSignalMessageAt A g a m ⊢ wireSignalMessageLoopCapsOf A a n caps m := by
  unfold wireSignalMessageLoopCapsOf
  refine Entails.trans ?_ (sepExists_intro _ g)
  rw [pure_true_emp ⟨hg, hc⟩, emp_sepConj]
  exact Entails.refl _

theorem wireSignalMessageLoopCapsOf_entails_loopOf (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) :
    wireSignalMessageLoopCapsOf A a n caps m ⊢ wireSignalMessageLoopOf A a n m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun ⟨hg, _⟩ => wireSignalMessageAt_entails_loopOf A g a n m hg

theorem wireSignalMessageLoopCapsOf_entails_of (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) :
    wireSignalMessageLoopCapsOf A a n caps m ⊢ wireSignalMessageOf A a m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun _ => wireSignalMessageAt_entails_of A g a m

theorem wireSignalMessageLoopCapsOf_mono (A : RustAlloc) (a : BitVec 64) {m n : Nat}
    {caps : SigTryFromCaps} (msg : ProtoSignalMessage) (hle : m ≤ n) :
    wireSignalMessageLoopCapsOf A a n caps msg ⊢ wireSignalMessageLoopCapsOf A a m caps msg :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun ⟨hg, hc⟩ =>
      wireSignalMessageAt_entails_loopCapsOf A g a m caps msg (hg.mono hle) hc

theorem wireSignalMessageOf_emptyMsg_entails_loopCapsOf (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    wireSignalMessageOf A a emptyProtoSignalMessage ⊢
      wireSignalMessageLoopCapsOf A a n SigTryFromCaps.zero emptyProtoSignalMessage := by
  refine Entails.sepExists_elim fun g => ?_
  have h0 : WireGhostCapOk ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ n :=
    ⟨bytesMergeCapOk_zero, bytesMergeCapOk_zero, bytesMergeCapOk_zero, bytesMergeCapOk_zero⟩
  have hc0 : WireGhostCapsMatch ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩
      emptyProtoSignalMessage SigTryFromCaps.zero :=
    ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩
  have heq : wireSignalMessageAt A g a emptyProtoSignalMessage =
      wireSignalMessageAt A ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ a
        emptyProtoSignalMessage := rfl
  rw [heq]
  exact wireSignalMessageAt_entails_loopCapsOf A _ a n SigTryFromCaps.zero
    emptyProtoSignalMessage h0 hc0

theorem loopExitMem_err_loopCaps_intro (A : RustAlloc) (sp' ptr : BitVec 64)
    (bs : List (BitVec 8)) (x24 : BitVec 64) (hx24 : x24 ≠ 0#64) (n k : Nat)
    (caps : SigTryFromCaps) (mErr : ProtoSignalMessage) :
    memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ memRegion (sp' + 296#64) 48 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      decodeErrorAtStackLen A x24 n ∗ wireSignalMessageLoopCapsOf A (sp' + 176#64) k caps mErr ⊢
      loopExitMem A sp' ptr bs x24 none := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right
        (wireSignalMessageLoopCapsOf_entails_of A (sp' + 176#64) k caps mErr))))))))
    (loopExitMem_err_intro A sp' ptr bs x24 hx24 n mErr)

theorem vecU8At_addr_entails_wireSignalMessageLoopCapsOf (A : RustAlloc)
    (g : WireSignalMessageGhost) (sp' cap' ptr' : BitVec 64) (len : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hc : WireGhostCapsMatch g m caps)
    (hcap' : BytesMergeCapOk cap' len) (hcap_eq : cap'.toNat = bmNextCap caps.ad v.length)
    (hnext_lt : bmNextCap caps.ad v.length < 2 ^ 63) :
    vecU8At A (sp' + 248#64) cap' ptr' v ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopCapsOf A (sp' + 176#64) len
        (caps.set .ad (bmNextCap caps.ad v.length)) { m with addresses := some v } := by
  refine Entails.trans ?_
    (wireSignalMessageAt_entails_loopCapsOf A { g with addr := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      (caps.set .ad (bmNextCap caps.ad v.length)) { m with addresses := some v }
      ⟨hg.rk, hg.ct, hg.pq, hcap'⟩ ⟨hc.rk, hc.ct, hc.pq, ⟨hnext_lt, hcap_eq⟩⟩)
  rw [wireSignalMessageAt_split_addr A { g with addr := ⟨cap', ptr'⟩ } sp'
    { m with addresses := some v }]
  exact Entails.refl _

theorem vecU8At_rk_entails_wireSignalMessageLoopCapsOf (A : RustAlloc)
    (g : WireSignalMessageGhost) (sp' cap' ptr' : BitVec 64) (len : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hc : WireGhostCapsMatch g m caps)
    (hcap' : BytesMergeCapOk cap' len) (hcap_eq : cap'.toNat = bmNextCap caps.rk v.length)
    (hnext_lt : bmNextCap caps.rk v.length < 2 ^ 63) :
    vecU8At A (sp' + 176#64) cap' ptr' v ∗
      (optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopCapsOf A (sp' + 176#64) len
        (caps.set .rk (bmNextCap caps.rk v.length)) { m with ratchetKey := some v } := by
  refine Entails.trans ?_
    (wireSignalMessageAt_entails_loopCapsOf A { g with rk := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      (caps.set .rk (bmNextCap caps.rk v.length)) { m with ratchetKey := some v }
      ⟨hcap', hg.ct, hg.pq, hg.addr⟩ ⟨⟨hnext_lt, hcap_eq⟩, hc.ct, hc.pq, hc.ad⟩)
  rw [wireSignalMessageAt_split_rk A { g with rk := ⟨cap', ptr'⟩ } sp'
    { m with ratchetKey := some v }]
  exact Entails.refl _

theorem vecU8At_ct_entails_wireSignalMessageLoopCapsOf (A : RustAlloc)
    (g : WireSignalMessageGhost) (sp' cap' ptr' : BitVec 64) (len : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hc : WireGhostCapsMatch g m caps)
    (hcap' : BytesMergeCapOk cap' len) (hcap_eq : cap'.toNat = bmNextCap caps.ct v.length)
    (hnext_lt : bmNextCap caps.ct v.length < 2 ^ 63) :
    vecU8At A (sp' + 200#64) cap' ptr' v ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopCapsOf A (sp' + 176#64) len
        (caps.set .ct (bmNextCap caps.ct v.length)) { m with ciphertext := some v } := by
  refine Entails.trans ?_
    (wireSignalMessageAt_entails_loopCapsOf A { g with ct := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      (caps.set .ct (bmNextCap caps.ct v.length)) { m with ciphertext := some v }
      ⟨hg.rk, hcap', hg.pq, hg.addr⟩ ⟨hc.rk, ⟨hnext_lt, hcap_eq⟩, hc.pq, hc.ad⟩)
  rw [wireSignalMessageAt_split_ct A { g with ct := ⟨cap', ptr'⟩ } sp'
    { m with ciphertext := some v }]
  exact Entails.refl _

theorem vecU8At_pq_entails_wireSignalMessageLoopCapsOf (A : RustAlloc)
    (g : WireSignalMessageGhost) (sp' cap' ptr' : BitVec 64) (len : Nat)
    (caps : SigTryFromCaps) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hc : WireGhostCapsMatch g m caps)
    (hcap' : BytesMergeCapOk cap' len) (hcap_eq : cap'.toNat = bmNextCap caps.pq v.length)
    (hnext_lt : bmNextCap caps.pq v.length < 2 ^ 63) :
    vecU8At A (sp' + 224#64) cap' ptr' v ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopCapsOf A (sp' + 176#64) len
        (caps.set .pq (bmNextCap caps.pq v.length)) { m with pqRatchet := some v } := by
  refine Entails.trans ?_
    (wireSignalMessageAt_entails_loopCapsOf A { g with pq := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      (caps.set .pq (bmNextCap caps.pq v.length)) { m with pqRatchet := some v }
      ⟨hg.rk, hg.ct, hcap', hg.addr⟩ ⟨hc.rk, hc.ct, ⟨hnext_lt, hcap_eq⟩, hc.ad⟩)
  rw [wireSignalMessageAt_split_pq A { g with pq := ⟨cap', ptr'⟩ } sp'
    { m with pqRatchet := some v }]
  exact Entails.refl _

/-! ## Budget-threaded `TryFromDepsPlaced` and panic-free `SepWPp` combinators -/

structure TryFromDepsPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  intoBoxed : IntoBoxedSliceOkPlaced A lim H
  tryClone : TryCloneFromRefOkPlaced A lim H
  varintSlice : DecodeVarintSliceOkWPlaced A lim H
  int32Merge : Int32MergeOkWPlaced A lim H
  skipField : SkipFieldOkWPlaced A lim H
  dropDecodeError : DropDecodeErrorOkWPlaced A lim H
  bytesMerge : BytesMergeOkWPlaced A lim H
  dropSpe : DropSpeOkWPlaced A lim H

/-- Total-correctness panic postcondition (`False`) for `FitsEnv`-guarded `SepWPp` proofs. -/
def noPanicQp (_s0 : State) : State → SepProp → Prop :=
  fun _ _ => False

theorem sepWPp_to_tryFromQp {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (noPanicQp s0)) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hqp
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_frame_noPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Q' : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q' (noPanicQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    SepWPp prog ret s (P ∗ F) Q (noPanicQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm, hv⟩⟩
  · exact False.elim hqp
  · exact (not_satisfies_false_sepConj hoom).elim

abbrev sepWP_done_vregs := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done

theorem sepWPp_bind_frame_entails_noPanic {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P F P2' : SepProp} {R1 : State → Prop}
    {Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P (fun sm Pm => R1 sm ∧ (Pm ⊢ P2')) (noPanicQp s0))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → R1 sm →
      SepWPp prog ret sm (P2' ∗ F) Q (noPanicQp s0)) :
    SepWPp prog ret s (P ∗ F) Q (noPanicQp s0) := by
  refine SepWPp.bind (Qm := fun sm Pm => R1 sm ∧ (Pm ⊢ P2' ∗ F))
    (sepWPp_frame_noPanic h1 fun sm Pm ⟨hr, hent⟩ => ⟨hr, sepConj_mono_left hent⟩) ?_
  intro sm Pm hpcm hrunm ⟨hr, hent⟩
  exact SepWPp.mono_pre hent (h2 sm hpcm hrunm hr)

theorem sepWPp_end_noPanic_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : ProofLib.SepWP prog ret s P
      (fun sf Pf => VRegsAt s sf ∧ (LibsignalCodeRoLoaded lsmpl sf.mem → Q sf Pf))) :
    SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq (hcl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_call_noPanic_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (_htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ A.pool lim st s ∗ T)) (hφ : φ)
    (hP : P = (A.pool lim st s ∗ T) ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (noPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hpan sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom; rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## Budget-threaded `loopExitPostPlaced` and shared error tails (Block `85`) -/

def loopExitPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (rem : Nat) (caps : SigTryFromCaps)
    (s0 : State) (sp' x19 x20 x21 x23 ptr : BitVec 64) (bs : List (BitVec 8))
    (res : Option ProtoSignalMessage) (sf : State) (P : SepProp) : Prop :=
  LoopExitStatePlaced s0 sp' x19 x20 x21 x23 sf ∧
    ∃ evs : List AllocEvent, SigTryFromLoopBoundedEnv rem caps evs ∧
      (P ⊢ loopExitMem (A.atState lim (M.stepEvents evs st) sf) sp' ptr bs (sf.readReg64 .x24) res)

theorem loopExitPostPlaced_mono_rem [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem₁ rem₂ : Nat}
    {caps : SigTryFromCaps} (hle : rem₁ ≤ rem₂) {s0 sf : State}
    {sp' x19 x20 x21 x23 ptr : BitVec 64} {bs : List (BitVec 8)}
    {res : Option ProtoSignalMessage} {Pm : SepProp}
    (h : loopExitPostPlaced A lim st rem₁ caps s0 sp' x19 x20 x21 x23 ptr bs res sf Pm) :
    loopExitPostPlaced A lim st rem₂ caps s0 sp' x19 x20 x21 x23 ptr bs res sf Pm := by
  rcases h with ⟨hst, evs, hevs, hent⟩
  exact ⟨hst, evs, hevs.mono_rem hle, hent⟩

theorem loopExitPostPlaced_skipStep [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem rem' : Nat}
    {caps : SigTryFromCaps} (hlt : rem' < rem) {s0 sf : State}
    {sp' x19 x20 x21 x23 ptr : BitVec 64} {bs : List (BitVec 8)}
    {res : Option ProtoSignalMessage} {Pm : SepProp}
    (h : loopExitPostPlaced A lim st rem' caps s0 sp' x19 x20 x21 x23 ptr bs res sf Pm) :
    loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res sf Pm := by
  rcases h with ⟨hst, evs, hevs, hent⟩
  exact ⟨hst, evs, .skipStep hlt hevs, hent⟩

theorem loopExitPostPlaced_bytesStep [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (f : SigTryFromField) {rem rem' : Nat} {caps : SigTryFromCaps}
    {wt : WireType} {bs_m v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs_m = some (v, rest))
    (hbs_le : bs_m.length ≤ rem)
    (hprog : rem' + v.length + 1 ≤ rem)
    (hcap_lt : caps.get f < 2 ^ 63)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs_m)
    {s0 sf : State} {sp' x19 x20 x21 x23 ptr : BitVec 64} {bs : List (BitVec 8)}
    {res : Option ProtoSignalMessage} {Pm : SepProp}
    (h : loopExitPostPlaced A lim (M.stepEvents evs₁ st) rem'
      (caps.set f (bmNextCap (caps.get f) v.length))
      s0 sp' x19 x20 x21 x23 ptr bs res sf Pm) :
    loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res sf Pm := by
  subst hevs₁
  rcases h with ⟨hst, evs₂, hevs₂, hent⟩
  refine ⟨hst, _ ++ evs₂, .bytesStep f wt bs_m v rest hm hbs_le hprog hcap_lt hevs₂, ?_⟩
  rwa [M.stepEvents_append]

theorem loopExitPostPlaced_append_prefix [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {s0 sf : State} {sp' x19 x20 x21 x23 ptr : BitVec 64} {bs : List (BitVec 8)}
    {k : ℕ} (hk : k ≤ bs.length) {res : Option ProtoSignalMessage} {Pm : SepProp}
    (h : loopExitPostPlaced A lim st rem caps
      s0 sp' x19 x20 x21 x23 (ptr + BitVec.ofNat 64 k) (bs.drop k) res sf Pm) :
    loopExitPostPlaced A lim st rem caps
      s0 sp' x19 x20 x21 x23 ptr bs res sf (Pm ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, evs, hevs, hent⟩
  refine ⟨hst, evs, hevs, ?_⟩
  rw [← loopExitMem_append_prefix (A.atState lim (M.stepEvents evs st) sf)
    sp' ptr bs k hk (sf.readReg64 .x24) res]
  exact sepConj_mono_left hent

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hq : ∀ sf Pf, Q₁ sf Pf → Q₂ sf Pf)
    (h : SepWPp prog ret s P Q₁ Qp oom) :
    SepWPp prog ret s P Q₂ Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq1, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hq1, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem sepWP_seg_85 [LibsignalPlacement] {H : LibsignalHooks}
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      ProofLib.SepWP ((blkPC_85).rebase (blkPl_85).base (hooksException H)) target (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            ProofLib.SepWP (tryFromPlacedProg H) target (sm'.setMem m_real) Pm post oom)) :
    ProofLib.SepWP (tryFromPlacedProg H) target s Pre post oom :=
  sepWP_seg_ls_vm blkLib_eq_85 (by rfl) hseg

theorem sepWP_done_sync_pool_85 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {H : LibsignalHooks}
    {target : BitVec 64} {s0 s sm' : State} {Pm F : SepProp}
    {post : State → SepProp → Prop}
    [hv : VRegsAt s sm']
    (hpost : ∀ m_real : Memory,
      LibsignalCodeRoLoaded lsmpl (sm'.setMem m_real).mem →
      post (sm'.setMem m_real) (A.pool lim st (sm'.setMem m_real) ∗ F))
    (hpc : sm'.pc = target := by simp only [wp_norm, arm64_norm])
    (hrun : sm'.status = .Running := by simp only [wp_norm, arm64_norm]; assumption)
    (htp : sm'.tpidrEl0 = s0.tpidrEl0 := by simp only [wp_norm, arm64_norm])
    (hPm : Pm = A.pool lim st s0 ∗ F := by sep_focus) :
    ProofLib.SepWP ((blkPC_85).rebase (blkPl_85).base (hooksException H)) target sm' Pm
      (fun sm'' Pm'' =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s0 (sm''.setMem m_real) →
          ProofLib.SepWP (tryFromPlacedProg H) target (sm''.setMem m_real) Pm''
            (fun sf Pf => VRegsAt s sf ∧ (LibsignalCodeRoLoaded lsmpl sf.mem → post sf Pf))) := by
  refine ProofLib.SepWP.done hpc hrun fun m_real hnsp => ?_
  have hvm := hnsp.toVmPreserved (by cases sm'; exact htp)
  rw [hPm, ← A.pool_transport lim st s0 (sm'.setMem m_real) hvm]
  have hv_real : VRegsAt s (sm'.setMem m_real) := ⟨by cases sm'; exact hv.eq⟩
  exact ProofLib.SepWP.done (by cases sm'; exact hpc) (by cases sm'; exact hrun)
    ⟨hv_real, hpost m_real⟩

theorem decodeErrorFrom_tail_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} (hS : TripleRatchetHooksWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x2bc#64) (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x3b0#64) s
      (memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        ((sp' + 296#64) ↦₆₄ w0) ∗ memRegion (sp' + 304#64) 40 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A.repAlloc (sp' + 176#64) mErr)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs none)
      (noPanicQp s0) := by
  have hcall := hS.decodeErrorFrom
  have hfit_from : FitsEnv M lim st DecodeErrorFromEnv :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_decodeErrorFrom) hfit
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ decodeErrorFromName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st (sp' + 296#64, s.readReg64 (Reg.gpr 8#5), st) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hcl1
    (ret_pc := (blkPl_85).base + 712#64) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (T := ((sp' + 296#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (sp' + 304#64) 40 ∗
      stackAt sp' (2 * extHookStack))
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)) ∧ FitsEnv M lim st DecodeErrorFromEnv)
    (by
      simp only [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack,
        hsp_eq, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨hkind, hfit_from⟩ (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩ hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromBudgetSpecWithStack]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  refine SepWPp.pure_pre fun ⟨hx0_ne, htr2⟩ => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  refine sepWPp_end_noPanic_placed hcl2 ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
    by simpa [arm64_norm] using hregs2.x19_eq⟩,
    by simp_all [State.spAligned, arm64_norm], hcl3, by simp_all [arm64_norm]⟩,
    evs, .done (SigTryFromErrTailEnv.of_decodeErrorFrom hevs), ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (loopExitMem_err_intro (A.atState lim (M.stepEvents evs st) _)
      sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 mErr)
  dsimp only [RustCliAllocBudget.atState]
  apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; sep_ac_rfl

/-- Shared `<DecodeError>::push` error tail (`+0x3a8 → +0x3b0`) entered immediately after a failed
field merge emitted `rustAllocEvents 72 8` (`stack.len = 0`). -/
theorem decodeErrorPush_tail_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} (hS : TripleRatchetHooksWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr err : BitVec 64}
    {bs : List (BitVec 8)} {mErr : ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x3a8#64) (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 296#64) (herr : err ≠ 0#64) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x3b0#64) s
      (memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        ((sp' + 296#64) ↦₆₄ err) ∗ memRegion (sp' + 304#64) 40 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s ∗ stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A.repAlloc err 0 ∗
        wireSignalMessageOf A.repAlloc (sp' + 176#64) mErr)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs none)
      (noPanicQp s0) := by
  let st1 := M.stepEvents (rustAllocEvents 72 8) st
  have hcall := hS.decodeErrorPush
  have hfit_push : FitsEnv M lim st1 (DecodeErrorPushBoundedEnv 0) :=
    fitsEnv_sigLoop_pushAfterFrom hfit
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ decodeErrorPushName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st1 fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st1 (sp' + 296#64, err, 0, st1) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [State.spAligned, arm64_norm]) hcl1
    (ret_pc := (blkPl_85).base + 940#64) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (T := ((sp' + 296#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
      stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ 0 < 2 ^ 32 ∧ FitsEnv M lim st1 (DecodeErrorPushBoundedEnv 0))
    (by
      have hx0' : s.readReg64 (Reg.gpr 0#5) = sp' + 296#64 := hx0
      simp only [decodeErrorPushBoundedSpecWithStack, hsp_eq, hx0', arm64_norm, true_and]
      sep_ac_rfl)
    ⟨herr, by decide, hfit_push⟩ (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
  dsimp only [decodeErrorPushBoundedSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  refine SepWPp.exists_pre fun err' => ?_
  refine SepWPp.pure_pre fun herr' => ?_
  refine SepWPp.pure_pre fun hevs => ?_
  refine sepWPp_end_noPanic_placed hcl2 ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st1) fun _ hcl3 => ?_
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
    by simpa [arm64_norm] using hregs2.x19_eq⟩,
    by simp_all [State.spAligned, arm64_norm], hcl3, by simp_all [arm64_norm]⟩,
    rustAllocEvents 72 8 ++ evs, .done (.fromPush hevs), ?_⟩
  rw [M.stepEvents_append]
  dsimp only [st1]
  simp only [arm64_norm]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 296#64) err'))) ?_
  refine Entails.trans ?_
    (loopExitMem_err_intro (A.atState lim (M.stepEvents evs (M.stepEvents (rustAllocEvents 72 8) st)) _)
      sp' ptr bs err' herr' 1 mErr)
  dsimp only [RustCliAllocBudget.atState]
  apply entails_of_eq
  simp only [hstack, hsp_eq, memRegion48_split8 sp', arm64_norm]
  sep_ac_rfl

/-! ## `FitsEnv fineCostModel` non-vacuity witness (`1 GiB`) -/

/-- Concrete `1 GiB` (`physCap = 2 ^ 30`) `BudgetLimits` for `tryFromLoopEnv_fitsEnv_witness`. -/
def tryFromNonVacLimits : BudgetLimits where
  staticCount := 16
  staticBytes := 16 * 1024 * 1024
  physCap := 2 ^ 30
  enforced := true

private def SigTryFromCaps.MaxLe (caps : SigTryFromCaps) (B : Nat) : Prop :=
  caps.rk ≤ B ∧ caps.ct ≤ B ∧ caps.pq ≤ B ∧ caps.ad ≤ B

private theorem SigTryFromCaps.get_le_of_maxLe {caps : SigTryFromCaps} {B : Nat}
    (h : caps.MaxLe B) (f : SigTryFromField) : caps.get f ≤ B := by
  rcases h with ⟨hrk, hct, hpq, had⟩
  cases f <;> simp only [SigTryFromCaps.get] <;> omega

private theorem SigTryFromCaps.maxLe_set {caps : SigTryFromCaps} {B v : Nat}
    (h : caps.MaxLe B) (hv : v ≤ B) (f : SigTryFromField) :
    (caps.set f v).MaxLe B := by
  rcases h with ⟨hrk, hct, hpq, had⟩
  cases f <;> exact ⟨by simpa [SigTryFromCaps.set], by simpa [SigTryFromCaps.set],
    by simpa [SigTryFromCaps.set], by simpa [SigTryFromCaps.set]⟩

private theorem sigTryFromErrTail_phaseCredit :
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
      fineCostModel SigTryFromErrTailEnv 19590 0 0 128 := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  open LibsignalBinary.Heap.Fine.ClientBounds in
  have hmax : 128 ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h72 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 9683 0 0 72 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 72)
      (by decide) (by omega)).mono
      (Nat.le_trans (smallAllocCost_le_two_mul_add 72) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
  have hpush0 : PhaseCreditSpec fineCostModel (DecodeErrorPushBoundedEnv 0) 9795 0 0 128 := by
    have h128 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 128 8) 9795 0 0 128 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 128)
        (by decide) hmax).mono
        (Nat.le_trans (smallAllocCost_le_two_mul_add 128) (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
    have hnil : PhaseCreditSpec fineCostModel (· = []) 9795 0 0 128 :=
      (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    exact (hnil.or h128).of_imp fun evs hp => by
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
  have hfp : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents 72 8) (DecodeErrorPushBoundedEnv 0)) 19590 0 0 128 :=
    (h72.concat hpush0).mono (by decide) (by decide) (by decide) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 19590 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  have h72' : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 19590 0 0 128 :=
    h72.mono (by decide) (by decide) (by decide) (by decide)
  exact ((hnil.or h72').or hfp).of_imp fun evs he => by
    cases he with
    | nil => exact Or.inl (Or.inl rfl)
    | fromOnly => exact Or.inl (Or.inr rfl)
    | fromPush hp => exact Or.inr (ConcatEnv.append rfl hp)

private theorem bytesMergeStep_small_phaseCredit {wt : WireType} {bs v rest : List (BitVec 8)}
    {c : Nat} (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 63) (hc : c ≤ 128) :
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
      fineCostModel (· = bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs) 19590 0 0 128 := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  open LibsignalBinary.Heap.Fine.ClientBounds in
  have hmax : 128 ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcore : bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs =
      if v.length = 0 then []
      else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
        rustDeallocEvents v.length 1 := by
    simp [bytesMergeEventsCore, hm, hc_toNat]
  rw [show (· = bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs) =
      (· = if v.length = 0 then []
        else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
          rustDeallocEvents v.length 1) by rw [hcore]]
  split_ifs with hv0
  · exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  · have hv_pos : 0 < v.length := by omega
    have halloc : PhaseCreditSpec fineCostModel (· = rustAllocEvents v.length 1) 9665 0 0 128 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
        (by decide) (by omega)).mono
        (Nat.le_trans (smallAllocCost_le_two_mul_add v.length) (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    have hres : PhaseCreditSpec fineCostModel (· = doReserveClearEvents c v.length) 9795 0 0 128 := by
      unfold doReserveClearEvents
      split_ifs with hle hc0
      · exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
      · have hnc_le : reserveCap c 0 v.length ≤ 128 := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1)
          (req := reserveCap c 0 v.length) (by decide) (by omega)).mono
          (Nat.le_trans (smallAllocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hnc_le : reserveCap c 0 v.length ≤ 128 := by
          dsimp only [reserveCap]; omega
        have hnc_pos : 1 ≤ reserveCap c 0 v.length := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := c)
          (new := reserveCap c 0 v.length) (al := 1) (by decide) hnc_pos (by omega) (by omega)
          hnc_pos (by omega)).mono
          (Nat.le_trans (smallReallocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    exact (((halloc.concat hres).concat hfree).mono
      (by decide) (by decide) (by decide) (by decide)).of_imp fun evs he => by
        subst he
        exact ConcatEnv.append (ConcatEnv.append rfl rfl) rfl

private theorem sigTryFromLoop_small_phaseCredit :
    ∀ (rem : Nat) {caps : SigTryFromCaps},
      rem ≤ 64 → caps.MaxLe 128 →
      LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
        fineCostModel (SigTryFromLoopBoundedEnv rem caps) (19590 * (rem + 1)) 0 0 128 := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro caps hrem hcaps
    open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
    refine {
      req_align := fun evs he => ?_
      credit_le := fun st0 {_} he => ?_
    }
    · cases he with
      | done herr => exact sigTryFromErrTail_phaseCredit.req_align evs herr
      | @skipStep _ rem' _ _ hlt hnext =>
        exact (ih rem' hlt (by omega) hcaps).req_align evs hnext
      | @bytesStep f _ rem' _ wt bs v rest evs₂ hm hbs_le hprog _ hnext =>
        have hc : caps.get f ≤ 128 := SigTryFromCaps.get_le_of_maxLe hcaps f
        have hnc : (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length) ≤ 128 := by
          split_ifs
          · exact hc
          · dsimp only [reserveCap]; omega
        have h1 := bytesMergeStep_small_phaseCredit hm (by omega) hc
        have h2 := ih rem' (by omega) (by omega) (SigTryFromCaps.maxLe_set hcaps hnc f)
        exact (h1.concat h2).req_align _ (ConcatEnv.append rfl hnext)
    · cases he with
      | done herr =>
        have h := sigTryFromErrTail_phaseCredit.credit_le st0 herr
        omega
      | @skipStep _ rem' _ _ hlt hnext =>
        have h := (ih rem' hlt (by omega) hcaps).credit_le st0 hnext
        have hmul : 19590 * (rem' + 1) ≤ 19590 * (rem + 1) :=
          Nat.mul_le_mul_left 19590 (by omega)
        omega
      | @bytesStep f _ rem' _ wt bs v rest evs₂ hm hbs_le hprog _ hnext =>
        have hc : caps.get f ≤ 128 := SigTryFromCaps.get_le_of_maxLe hcaps f
        have hnc : (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length) ≤ 128 := by
          split_ifs
          · exact hc
          · dsimp only [reserveCap]; omega
        have h1 := bytesMergeStep_small_phaseCredit hm (by omega) hc
        have h2 := ih rem' (by omega) (by omega) (SigTryFromCaps.maxLe_set hcaps hnc f)
        have h := (h1.concat h2).credit_le st0 (ConcatEnv.append rfl hnext)
        have hmul : 19590 + 19590 * (rem' + 1) ≤ 19590 * (rem + 1) := by
          have : rem' + 2 ≤ rem + 1 := by omega
          calc 19590 + 19590 * (rem' + 1) = 19590 * (rem' + 2) := by omega
            _ ≤ 19590 * (rem + 1) := Nat.mul_le_mul_left 19590 this
        omega

/-- Non-trivial inhabitation witness: `TryFromLoopEnv 130 64` admits a non-empty `bytesStep`
trace (`mergeBytes .lengthDelimited [1, 42] = some ([42], [])`, `3` allocator events). -/
theorem tryFromLoopEnv_inhabited_nontrivial :
    ∃ evs : List AllocEvent, TryFromLoopEnv 130 64 evs ∧ evs.length = 3 := by
  have hm : mergeBytes .lengthDelimited [1#8, 42#8] = some ([42#8], []) := rfl
  refine ⟨bytesMergeEventsCore .lengthDelimited 0#64 [1#8, 42#8] ++ [],
    SigTryFromLoopBoundedEnv.bytesStep .rk (rem' := 0) .lengthDelimited [1#8, 42#8] [42#8] []
      hm (by decide) (by decide) (by decide) (.done .nil), ?_⟩
  decide

/-- Non-vacuity witness: `TryFromLoopEnv 130 64` satisfies `FitsEnv fineCostModel`
from `fineCostModel.init` under `tryFromNonVacLimits` (`1 GiB` RAM cap). -/
theorem tryFromLoopEnv_fitsEnv_witness :
    FitsEnv fineCostModel tryFromNonVacLimits fineCostModel.init (TryFromLoopEnv 130 64) := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  open LibsignalBinary.Heap.Fine in
  open LibsignalBinary.Heap.Fine.ClientBounds in
  have hspec := sigTryFromLoop_small_phaseCredit 64 (caps := SigTryFromCaps.zero) (by decide)
    ⟨by decide, by decide, by decide, by decide⟩
  exact fitsEnv_fineCostModel_of_phaseCredit hspec (by decide) rfl (by decide) (by decide)

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
