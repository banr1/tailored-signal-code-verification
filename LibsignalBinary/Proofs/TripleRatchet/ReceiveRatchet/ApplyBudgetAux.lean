/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Apply
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Definitions and Tail Segments for Budget-Threaded `TripleRatchet::apply_to_session_state`

Bounded allocator-event envelopes (`trApplyAllocPrefix`, `TrApplyBoundedEnv`), `A.live` spatial
congruences, cross-block call wrappers, and tail drop segments for `apply_to_session_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession
  (ChainKey MessageKeyGenerator PublicKey RatchetState ReceiverChain SenderChain SessionState
   TripleRatchet)
open CryptoVerification
  (LibsignalPlacement blkPC_58 blkPl_58 extract_withLsCodeLoaded
   lsRustDeallocSym lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.RustHeap
  (LayoutOk RustAlloc arrayAt vecAt vecBuf vecU8 vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr
  (ChainGhost MessageKeyGhost RatchetGhost VecGhost VecPin
   chainAt messageKeyAt optChainKeyAt ratchetAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet
  (TrApplyGhost TrGhost boxU8Buf extHookStack trApplyStack trApplyStackX trAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (DropVecChainGhost DropVecMessageKeyGhost dropVecChainStackX)
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply
  (LsClInv memRegion_24_unpack optSenderChainAt_none_expose optSenderChainAt_some_expose
   spAligned_sub_224 stackAt_switch_gen stackAt_to_ext_gen
   vecAt_chains_fold vecU8Buf_dealloc vecU8Buf_eq_zero_entails_emp)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SenderChainGhost SessionGhost TailVecGhost optSenderChainAt optTailVecAt sessionStateAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk SeqEnv allocMemcpyVmSpec rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv framelessMemcpyBudgetSpec noAllocShimBudgetSpec
   publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
  (publicKeySerializeSpecWithStack rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
  (PrivSerializeEnv privSerializeEvents privSerializeSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
  (TrApplyEnv TrApplySenderAllocEnv)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Bounded allocator event envelopes and target specifications -/

/-- Exact deterministic allocation prefix of `<TripleRatchet>::apply_to_session_state` before
    trailing `FreeOnlyEvs` drops. -/
def trApplyAllocPrefix (x : TrApplyGhost) : List AllocEvent :=
  let base := rustAllocEvents 32 1 ++ rustDeallocEvents x.G.root.cap.toNat 1
  match x.tr.ratchet.senderChain with
  | none => base
  | some _ =>
      base ++ publicKeySerializeEvents ++ rustAllocEvents 33 1 ++
        privSerializeEvents ++ rustAllocEvents 32 1 ++ rustAllocEvents 32 1

/-- Precondition budget envelope of `<TripleRatchet>::apply_to_session_state`:
    exact equality with `trApplyAllocPrefix x`. -/
def TrApplyPreEnv (x : TrApplyGhost) (evs : List AllocEvent) : Prop :=
  evs = trApplyAllocPrefix x

/-- Postcondition allocator event envelope of `<TripleRatchet>::apply_to_session_state`:
    `trApplyAllocPrefix x` followed by trailing `FreeOnlyEvs` deallocations. -/
def TrApplyBoundedEnv (x : TrApplyGhost) : List AllocEvent → Prop :=
  SeqEnv (TrApplyPreEnv x) FreeOnlyEvs

@[simp]
theorem fitsEnv_trApplyPre_iff {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : TrApplyGhost} :
    FitsEnv M lim st (TrApplyPreEnv x) ↔ FitsEvents M lim st (trApplyAllocPrefix x) :=
  FitsEnv.eq_iff

theorem fitsEnv_trApplyPre_of_bounded {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : TrApplyGhost}
    (h : FitsEnv M lim st (TrApplyBoundedEnv x)) :
    FitsEnv M lim st (TrApplyPreEnv x) :=
  FitsEnv.seq_left h

theorem trApplyEnv_of_prefix_append_free (x : TrApplyGhost) {evsFree : List AllocEvent}
    (hfree : FreeOnlyEvs evsFree) :
    TrApplyEnv (trApplyAllocPrefix x ++ evsFree) := by
  unfold trApplyAllocPrefix
  dsimp only
  cases hsc : x.tr.ratchet.senderChain
  · have heq :
        (rustAllocEvents 32 1 ++ rustDeallocEvents x.G.root.cap.toNat 1) ++ evsFree =
        rustAllocEvents 32 1 ++
          (rustDeallocEvents x.G.root.cap.toNat 1 ++ ([] ++ evsFree)) := by
      simp only [List.append_assoc, List.nil_append]
    rw [heq]
    exact SeqEnv.append rfl
      (SeqEnv.append (FreeOnlyEvs.singleton 1 x.G.root.cap.toNat)
        (SeqEnv.append (Or.inl rfl) hfree))
  · let evsSnd : List AllocEvent :=
      rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))
    have hsnd : TrApplySenderAllocEnv evsSnd :=
      SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append rfl rfl)))
    have heq :
        (((((rustAllocEvents 32 1 ++ rustDeallocEvents x.G.root.cap.toNat 1) ++
          publicKeySerializeEvents) ++ rustAllocEvents 33 1) ++
          privSerializeEvents) ++ rustAllocEvents 32 1) ++ rustAllocEvents 32 1 ++ evsFree =
        rustAllocEvents 32 1 ++
          (rustDeallocEvents x.G.root.cap.toNat 1 ++ (evsSnd ++ evsFree)) := by
      simp only [evsSnd, publicKeySerializeEvents, privSerializeEvents, List.append_assoc]
    rw [heq]
    exact SeqEnv.append rfl
      (SeqEnv.append (FreeOnlyEvs.singleton 1 x.G.root.cap.toNat)
        (SeqEnv.append (Or.inr hsnd) hfree))

theorem trApplyEnv_trApplyAllocPrefix (x : TrApplyGhost) :
    TrApplyEnv (trApplyAllocPrefix x) := by
  simpa only [List.append_nil] using trApplyEnv_of_prefix_append_free x FreeOnlyEvs.nil

theorem trApplyEnv_of_trApplyBoundedEnv {x : TrApplyGhost} {evs : List AllocEvent}
    (h : TrApplyBoundedEnv x evs) :
    TrApplyEnv evs := by
  rcases h with hpre | ⟨evs₁, evs₂, rfl, hpre, hfree⟩
  · exact hpre ▸ trApplyEnv_trApplyAllocPrefix x
  · exact hpre ▸ trApplyEnv_of_prefix_append_free x hfree

theorem fitsEnv_trApplyPre_of_trApplyEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (x : TrApplyGhost)
    (h : FitsEnv M lim st TrApplyEnv) :
    FitsEnv M lim st (TrApplyPreEnv x) :=
  FitsEnv.mono (fun _ heq => heq ▸ trApplyEnv_trApplyAllocPrefix x) h

/-- Stack-parameterized budget specification of `drop_glue<Vec<chain::MessageKey>>`. -/
def dropVecMessageKeySpecAt [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (mkStack : Nat) : Spec (DropVecMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim st s ∗ stackAt s.sp mkStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp mkStack

/-- Stack-parameterized budget specification of `drop_glue<Vec<session_structure::Chain>>`. -/
def dropVecChainSpecAt [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (chStack : Nat) : Spec (DropVecChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim st s ∗ stackAt s.sp chStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chStack

/-- Stack-parameterized budget specification of `<TripleRatchet>::apply_to_session_state`
    (`224 + calleeStack` total stack, `onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def trApplyBoundedSpecAt (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStack : Nat) : Spec (TrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (TrApplyPreEnv x) ∧ s.readReg64 .x0 = x.t ∧ s.readReg64 .x1 = x.ss⌝ ∗
      trAt A.repAlloc x.t x.trG x.tr ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗
      stackAt s.sp (224 + calleeStack) ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜TrApplyBoundedEnv x evs ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.TrApplyRel x.trG G'⌝ ∗
        sessionStateAt A.repAlloc x.ss G' (x.tr.applyToSessionState x.st)) ∗
      memRegion x.t 264 ∗
      stackAt s0.sp (224 + calleeStack) ∗
      A.pool lim (M.stepEvents evs st) sf

/-- Budget-threaded specification of `<TripleRatchet>::apply_to_session_state` at `trApplyStack`
    (`224 + extHookStack`). -/
abbrev trApplyBoundedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TrApplyGhost × M.σ) :=
  trApplyBoundedSpecAt M A lim extHookStack

/-- Budget-threaded specification of `<TripleRatchet>::apply_to_session_state` at `trApplyStackX`
    (`224 + dropVecChainStackX`). -/
abbrev trApplyBoundedSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TrApplyGhost × M.σ) :=
  trApplyBoundedSpecAt M A lim dropVecChainStackX

/-! ## Spatial `A.live` congruence and lift to `DefsBudget.trApplySpec{,X}` -/

private theorem vecU8At_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A₁ v cap ptr bs = vecU8At A₂ v cap ptr bs := by
  simp only [vecU8At, h]

private theorem vecGhostAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A₁ g v = vecGhostAt A₂ g v :=
  vecU8At_congr_live h v g.cap g.ptr g.bytes

private theorem arrayAt_congr {α : Type} {elem₁ elem₂ : α → BitVec 64 → SepProp}
    (helem : ∀ x a, elem₁ x a = elem₂ x a) (stride : Nat) (base : BitVec 64) (xs : List α) :
    arrayAt elem₁ stride base xs = arrayAt elem₂ stride base xs := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih => simp only [arrayAt, helem, ih]

private theorem vecBuf_congr_live {α : Type} {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    {elem₁ elem₂ : α → BitVec 64 → SepProp} (helem : ∀ x a, elem₁ x a = elem₂ x a)
    (stride align : Nat) (cap ptr : BitVec 64) (xs : List α) :
    vecBuf A₁ stride align elem₁ cap ptr xs = vecBuf A₂ stride align elem₂ cap ptr xs := by
  simp only [vecBuf, h, arrayAt_congr helem]

private theorem vecAt_congr_live {α : Type} {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    {elem₁ elem₂ : α → BitVec 64 → SepProp} (helem : ∀ x a, elem₁ x a = elem₂ x a)
    (stride align : Nat) (v cap ptr : BitVec 64) (xs : List α) :
    vecAt A₁ stride align elem₁ v cap ptr xs = vecAt A₂ stride align elem₂ v cap ptr xs := by
  simp only [vecAt, vecBuf_congr_live h helem]

private theorem messageKeyAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A₁ gk a = messageKeyAt A₂ gk a := by
  simp only [messageKeyAt, vecU8At_congr_live h]

private theorem optChainKeyAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (pin : VecPin) (o : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A₁ pin o a = optChainKeyAt A₂ pin o a := by
  cases o <;> simp only [optChainKeyAt, vecU8At_congr_live h]

private theorem chainAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A₁ gc a = chainAt A₂ gc a := by
  simp only [chainAt, vecGhostAt_congr_live h,
    vecAt_congr_live h (messageKeyAt_congr_live h), optChainKeyAt_congr_live h]

private theorem ratchetAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (self : BitVec 64) (G : RatchetGhost) (st : RatchetState) :
    ratchetAt A₁ self G st = ratchetAt A₂ self G st := by
  simp only [ratchetAt, vecAt_congr_live h (chainAt_congr_live h)]

private theorem optSenderChainAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (a : BitVec 64) (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt A₁ a g sc = optSenderChainAt A₂ a g sc := by
  cases g <;> cases sc <;>
    simp only [optSenderChainAt, vecGhostAt_congr_live h,
      vecAt_congr_live h (messageKeyAt_congr_live h), optChainKeyAt_congr_live h]

private theorem optTailVecAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (size : Nat) (a : BitVec 64) (g : Option TailVecGhost) :
    optTailVecAt A₁ size a g = optTailVecAt A₂ size a g := by
  cases g <;> simp only [optTailVecAt, vecGhostAt_congr_live h]

theorem sessionStateAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A₁ ss G st = sessionStateAt A₂ ss G st := by
  simp only [sessionStateAt, vecGhostAt_congr_live h, vecU8At_congr_live h,
    vecAt_congr_live h (chainAt_congr_live h),
    optSenderChainAt_congr_live h, optTailVecAt_congr_live h]

theorem trAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (t : BitVec 64) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trAt A₁ t G tr = trAt A₂ t G tr := by
  simp only [trAt, ratchetAt_congr_live h, vecU8At_congr_live h]

theorem subroutine_ok_trApply_of_bounded {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {pl : Obj.MultiPlacement}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (trApplyBoundedSpec M A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl
        (LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget.trApplySpec M A lim)) := by
  refine subroutine_ok_mono h (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, trApplyBoundedSpec, trApplyBoundedSpecAt]
    dsimp only [LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget.trApplySpec,
      CryptoVerification.LibsignalTripleRatchet.trApplySpec, trApplyStack] at hpre
    rw [trAt_congr_live (A.atState_live_eq_repAlloc lim st s0),
        sessionStateAt_congr_live (A.atState_live_eq_repAlloc lim st s0),
        A.atState_pool lim st s0] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hfit, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1⟩, hm⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨fitsEnv_trApplyPre_of_trApplyEnv x hfit, hx0, hx1⟩, hm⟩
  · dsimp only [withLsCodeLoaded, trApplyBoundedSpec, trApplyBoundedSpecAt] at hq
    dsimp only [withLsCodeLoaded,
      LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget.trApplySpec,
      CryptoVerification.LibsignalTripleRatchet.trApplySpec, trApplyStack]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hbnd, htr⟩, hm⟩
    have hss_eq :
        (∃∗ G', ⌜x.G.TrApplyRel x.trG G'⌝ ∗
          sessionStateAt A.repAlloc x.ss G' (x.tr.applyToSessionState x.st)) =
        (∃∗ G', ⌜x.G.TrApplyRel x.trG G'⌝ ∗
          sessionStateAt (A.atState lim (M.stepEvents evs st) sf) x.ss G'
            (x.tr.applyToSessionState x.st)) :=
      sepExists_congr fun _ => by
        rw [← sessionStateAt_congr_live (A.atState_live_eq_repAlloc lim (M.stepEvents evs st) sf)]
    rw [hss_eq, ← A.atState_pool lim (M.stepEvents evs st) sf] at hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨trApplyEnv_of_trApplyBoundedEnv hbnd, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hm⟩

theorem subroutine_ok_trApplyX_of_bounded {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {pl : Obj.MultiPlacement}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (trApplyBoundedSpecX M A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl
        (LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget.trApplySpecX M A lim)) := by
  refine subroutine_ok_mono h (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, trApplyBoundedSpecX, trApplyBoundedSpecAt]
    dsimp only [LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget.trApplySpecX,
      CryptoVerification.LibsignalTripleRatchet.trApplySpecX, trApplyStackX] at hpre
    rw [trAt_congr_live (A.atState_live_eq_repAlloc lim st s0),
        sessionStateAt_congr_live (A.atState_live_eq_repAlloc lim st s0),
        A.atState_pool lim st s0] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hfit, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1⟩, hm⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨fitsEnv_trApplyPre_of_trApplyEnv x hfit, hx0, hx1⟩, hm⟩
  · dsimp only [withLsCodeLoaded, trApplyBoundedSpecX, trApplyBoundedSpecAt] at hq
    dsimp only [withLsCodeLoaded,
      LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget.trApplySpecX,
      CryptoVerification.LibsignalTripleRatchet.trApplySpecX, trApplyStackX]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hbnd, htr⟩, hm⟩
    have hss_eq :
        (∃∗ G', ⌜x.G.TrApplyRel x.trG G'⌝ ∗
          sessionStateAt A.repAlloc x.ss G' (x.tr.applyToSessionState x.st)) =
        (∃∗ G', ⌜x.G.TrApplyRel x.trG G'⌝ ∗
          sessionStateAt (A.atState lim (M.stepEvents evs st) sf) x.ss G'
            (x.tr.applyToSessionState x.st)) :=
      sepExists_congr fun _ => by
        rw [← sessionStateAt_congr_live (A.atState_live_eq_repAlloc lim (M.stepEvents evs st) sf)]
    rw [hss_eq, ← A.atState_pool lim (M.stepEvents evs st) sf] at hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨trApplyEnv_of_trApplyBoundedEnv hbnd, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hm⟩

/-! ## Stack folding, `FreeOnlyEvs`, cross-block call, and `HookSat` helpers -/

theorem SepWP_fold_stack_gen {prog : Program} {target : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (calleeStack stk1 stk2 : Nat)
    (hcallee : 224 + calleeStack < 2 ^ 64) (h1 : stk1 ≤ calleeStack) (h2 : stk2 ≤ calleeStack)
    (hP : P = (memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - stk1) ∗
      stackAt sp' stk1) ∗ F)
    (hsp : sp' = sp - 224#64)
    (hnext : SepWP prog target s
      ((memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - stk2) ∗
        stackAt (sp - 224#64) stk2) ∗ F) post) :
    SepWP prog target s P post :=
  SepWP.fold (stackAt_switch_gen sp sp' calleeStack stk1 stk2 hsp hcallee h1 h2) hP hnext

theorem SepWP_fold_stack_to_ext_gen {prog : Program} {target : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (calleeStack stk : Nat)
    (hcallee : 224 + calleeStack < 2 ^ 64) (hstk : stk ≤ calleeStack)
    (hP : P = (memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - stk) ∗
      stackAt sp' stk) ∗ F)
    (hsp : sp' = sp - 224#64)
    (hnext : SepWP prog target s (stackAt (sp - 224#64) calleeStack ∗ F) post) :
    SepWP prog target s P post :=
  SepWP.fold (stackAt_to_ext_gen sp sp' calleeStack stk hsp hcallee hstk) hP hnext

theorem freeOnly_dealloc (sz al : Nat) : FreeOnlyEvs (rustDeallocEvents sz al) :=
  FreeOnlyEvs.singleton al sz

theorem instantiate_trApplyBounded_post {M : AllocCostModel}
    {prog : Program} {target_pc : BitVec 64} {s s0 : State} {P R : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStack : Nat}
    (x : TrApplyGhost) (stB : M.σ) (G' : SessionGhost)
    (evsPre evsFree : List AllocEvent)
    (hpre_eq : evsPre = trApplyAllocPrefix x)
    (hfree : FreeOnlyEvs evsFree)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
          (⌜x.G.TrApplyRel x.trG G'⌝ ∗
            sessionStateAt A.repAlloc x.ss G' (x.tr.applyToSessionState x.st)) ∗
          memRegion x.t 264 ∗
          stackAt s0.sp (224 + calleeStack) ∗
          A.pool lim (M.stepEvents evsFree (M.stepEvents evsPre stB)) sf) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (trApplyBoundedSpecAt M A lim calleeStack).post (x, stB) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have henv : TrApplyBoundedEnv x (evsPre ++ evsFree) :=
    SeqEnv.append hpre_eq hfree
  refine SepWP.mono h fun sf P_f _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  have hm0 := h1 hm
  rw [← M.stepEvents_append evsPre evsFree stB] at hm0
  have hm1 : sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗
        (∃∗ G'' : SessionGhost, ⌜x.G.TrApplyRel x.trG G''⌝ ∗
          sessionStateAt A.repAlloc x.ss G'' (x.tr.applyToSessionState x.st)) ∗
        memRegion x.t 264 ∗
        stackAt s0.sp (224 + calleeStack) ∗
        A.pool lim (M.stepEvents (evsPre ++ evsFree) stB) sf) ∗ R :=
    Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro G'))))
      hm0
  have hm2 : sf.mem ⊨
      (⌜TrApplyBoundedEnv x (evsPre ++ evsFree) ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G'' : SessionGhost, ⌜x.G.TrApplyRel x.trG G''⌝ ∗
          sessionStateAt A.repAlloc x.ss G'' (x.tr.applyToSessionState x.st)) ∗
        memRegion x.t 264 ∗
        stackAt s0.sp (224 + calleeStack) ∗
        A.pool lim (M.stepEvents (evsPre ++ evsFree) stB) sf) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
    exact ⟨⟨henv, hm1.1⟩, hm1.2⟩
  exact Satisfies.mono
    (sepConj_mono_left (Entails.sepExists_intro (evsPre ++ evsFree)))
    hm2

theorem SepWP_call_lscl_frame [LibsignalPlacement] {α : Type} {prog : Program}
    {target entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {s : State} {P T F : SepProp} {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hinv : LsClInv s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsClInv sf →
      SepWP prog target sf (spec.post x s sf ∗ F) post)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog target s P post := by
  have hcall_cl : subroutine_ok prog entry
      { withLsCodeLoaded lsmpl spec with
        post := fun x s0 sf => ⌜LsClInv sf⌝ ∗ spec.post x s0 sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0 hpc0 hrun0 hpre0 hsp0 hL => ?_
    have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre0
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0 hpc0 hrun0 hpre0 hsp0 hL
    have hclf : LsClInv sf := hcl0.of_keepsFrozen hsteps.keepsFrozen
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hclf, hpost⟩
    · exact Or.inr hrest
  refine ProofLib.SepWP.call_subroutine_frame (x := x) (F := F) hcall_cl hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [withLsCodeLoaded]
    rw [hspec, sepConj_assoc, sepConj_left_comm (⌜φ⌝ ∗ T), satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hpanic_eq] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro R' code sf _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hexit_eq] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf hpcm hrunm hspm hcsm
    dsimp only
    rw [sepConj_assoc]
    exact SepWP.pure_elim (hnext sf hpcm hrunm hspm hcsm)
  · intro R' sf _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hoom_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem SepWP_call_pk_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {prog : Program} {target entry ret_pc : BitVec 64} {s0 s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {pkHookStack : Nat}
    (hpk : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecWithStack M A lim pkHookStack)))
    (hinv : LsClInv s)
    (pk : PublicKey)
    (hfit : FitsEnv M lim stB PublicKeySerializeEnv)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 224#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = s0.sp - 220#64)
    (hP : P = (((s0.sp - 220#64) ↦ₛ pk.bytes.toList) ∗ A.pool lim stB s ∗
      stackAt (s0.sp - 224#64) (pkHookStack + 32)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 224#64 → CalleeSavedPreserved s sf → LsClInv sf →
      SepWP prog target sf
        ((⌜sf.readReg64 Reg.x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
          ((s0.sp - 220#64) ↦ₛ pk.bytes.toList) ∗
          boxU8Buf A.repAlloc (sf.readReg64 Reg.x0) pk.serialize ∗
          A.pool lim (M.stepEvents publicKeySerializeEvents stB) sf ∗
          stackAt (s0.sp - 224#64) (pkHookStack + 32)) ∗ F) post) :
    SepWP prog target s P post := by
  refine SepWP_call_lscl_frame
    (x := (⟨s0.sp - 220#64, pk⟩, stB))
    (φ := s.readReg64 .x0 = s0.sp - 220#64 ∧ FitsEnv M lim stB PublicKeySerializeEnv)
    hpk hinv hpc hrun
    (spAligned_sub_224 hsp_align hsp_eq) hlr ?_ ⟨hx0, hfit⟩ hP
    (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f => ?_)
  · dsimp only [publicKeySerializeSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack]
    rw [hsp_eq]
  · dsimp only [publicKeySerializeSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack]
    rw [hsp_eq, htr]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hinv_f

theorem SepWP_call_priv_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {prog : Program} {target entry ret_pc : BitVec 64} {s0 s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {privStack : Nat}
    (hpriv : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (privSerializeSpecWithStack M A lim privStack)))
    (hinv : LsClInv s)
    (bs : List (BitVec 8))
    (hfit : FitsEnv M lim stB PrivSerializeEnv)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 224#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = s0.sp - 188#64 ∧ s.readReg64 Reg.x8 = s0.sp - 120#64 ∧ bs.length = 32)
    (hP : P = (((s0.sp - 188#64) ↦ₛ bs) ∗ memRegion (s0.sp - 120#64) 24 ∗ A.pool lim stB s ∗
      stackAt (s0.sp - 224#64) privStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 224#64 → CalleeSavedPreserved s sf → LsClInv sf →
      SepWP prog target sf
        ((⌜sf.trace = s0.trace⌝ ∗ ((s0.sp - 188#64) ↦ₛ bs) ∗
          vecU8 A.repAlloc (s0.sp - 120#64) bs ∗
          A.pool lim (M.stepEvents privSerializeEvents stB) sf ∗
          stackAt (s0.sp - 224#64) privStack) ∗ F) post) :
    SepWP prog target s P post := by
  refine SepWP_call_lscl_frame
    (x := (s0.sp - 188#64, bs, s0.sp - 120#64, stB))
    (φ := s.readReg64 .x0 = s0.sp - 188#64 ∧ s.readReg64 .x8 = s0.sp - 120#64 ∧
      bs.length = 32 ∧ FitsEnv M lim stB PrivSerializeEnv)
    hpriv hinv hpc hrun
    (spAligned_sub_224 hsp_align hsp_eq) hlr ?_ ⟨hx.1, hx.2.1, hx.2.2, hfit⟩ hP
    (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f => ?_)
  · dsimp only [privSerializeSpecWithStack]
    rw [hsp_eq]
  · dsimp only [privSerializeSpecWithStack]
    rw [hsp_eq, htr]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hinv_f

theorem SepWP_call_dropMk_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {prog : Program} {target entry ret_pc sp : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {mkStack : Nat}
    (hdropMk : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (dropVecMessageKeySpecAt M A lim mkStack)))
    (hinv : LsClInv s)
    (x : DropVecMessageKeyGhost)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = sp - 224#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 Reg.x0 = x.v)
    (hP : P = (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim stB s ∗ stackAt (sp - 224#64) mkStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp - 224#64 → CalleeSavedPreserved s sf → LsClInv sf →
      SepWP prog target sf
        ((⌜sf.trace = s.trace⌝ ∗ memRegion x.v 24 ∗
          (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs stB) sf) ∗
          stackAt (sp - 224#64) mkStack) ∗ F) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog target s P post := by
  refine SepWP_call_lscl_frame
    (x := (x, stB)) (φ := s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30))
    hdropMk hinv hpc hrun
    (spAligned_sub_224 hsp_align hsp_eq) hlr ?_
    ⟨hx0, by rw [show s.readReg64 .x30 = ret_pc from hlr]; exact hlr_ls⟩ hP
    (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f => ?_)
  · dsimp only [dropVecMessageKeySpecAt]
    rw [hsp_eq]
  · dsimp only [dropVecMessageKeySpecAt]
    rw [hsp_eq]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hinv_f

theorem SepWP_call_dropCh_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {prog : Program} {target entry ret_pc sp : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {chStack : Nat}
    (hdropCh : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (dropVecChainSpecAt M A lim chStack)))
    (hinv : LsClInv s)
    (x : DropVecChainGhost)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = sp - 224#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 Reg.x0 = x.v)
    (hP : P = (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim stB s ∗ stackAt (sp - 224#64) chStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp - 224#64 → CalleeSavedPreserved s sf → LsClInv sf →
      SepWP prog target sf
        ((⌜sf.trace = s.trace⌝ ∗ memRegion x.v 24 ∗
          (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs stB) sf) ∗
          stackAt (sp - 224#64) chStack) ∗ F) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog target s P post := by
  refine SepWP_call_lscl_frame
    (x := (x, stB)) (φ := s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30))
    hdropCh hinv hpc hrun
    (spAligned_sub_224 hsp_align hsp_eq) hlr ?_
    ⟨hx0, by rw [show s.readReg64 .x30 = ret_pc from hlr]; exact hlr_ls⟩ hP
    (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f => ?_)
  · dsimp only [dropVecChainSpecAt]
    rw [hsp_eq]
  · dsimp only [dropVecChainSpecAt]
    rw [hsp_eq]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hinv_f

theorem hookSat_sessionShim_of_noAllocShim {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym noAllocShimBudgetSpec) :
    HookSat H sym sessionShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun u R s0 hrun hpre hsp => ?_⟩
  rcases hok u R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimBudgetSpec, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1.1, hpost.2⟩
  · exact Or.inr hrest

theorem hookSat_noAllocShim_of_rustAllocShimVm {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym rustAllocShimVmSpec) :
    HookSat H sym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun u R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ rustAllocShimVmSpec.pre u s0 ∗ R := by
    simpa [rustAllocShimVmSpec, noAllocShimBudgetSpec] using hpre
  rcases hok u R s0 hrun hpre' hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocShimVmSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1.2.1, hpost.1.2⟩, hpost.2⟩
  · exact Or.inr hrest

theorem hookSat_framelessMemcpy_of_allocMemcpyVm {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym allocMemcpyVmSpec) :
    HookSat H sym framelessMemcpyBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyBudgetSpec, allocMemcpyVmSpec] at hpre ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
    have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  rcases hok (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0, hacp, hvm⟩, hm⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hacp.2.1, hvm⟩, by simpa only [sepConj_assoc] using hm⟩
  · exact Or.inr hrest

/-! ## Tail step lemmas (`drop_old_sender` and `+0x14c..+0x184`) -/

theorem SepWP_drop_old_sender_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {H : String → Option (State → State)}
    {calleeStack stubStack mkStack chStack : Nat}
    (hcallee : 224 + calleeStack < 2 ^ 64)
    (hstub_le : stubStack ≤ calleeStack)
    (hmk_le : mkStack ≤ calleeStack)
    (hch_le : chStack ≤ calleeStack)
    (hdealloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim stubStack))
    (hdropMk : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpecAt M A lim mkStack)))
    {target : BitVec 64} {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (sp ss : BitVec 64) {sp' : BitVec 64}
    {G_sender : Option SenderChainGhost} {st_sender : Option SenderChain}
    (hinv : LsClInv s)
    (hpc : s.pc = (blkPl_58).base + 208#64)
    (hrun : s.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp : s.sp = sp - 224#64)
    (hx20 : s.readReg64 .x20 = ss)
    (hGs_eq : G_sender.isSome = st_sender.isSome)
    (hP : P = (optSenderChainAt A.repAlloc (ss + 144#64) G_sender st_sender ∗
      A.pool lim stB s ∗
      memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - stubStack) ∗
      stackAt sp' stubStack) ∗ F)
    (hsp' : sp' = sp - 224#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent)
      (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) (v12 : BitVec 32),
      FreeOnlyEvs evs →
      sf.pc = (blkPl_58).base + 288#64 →
      sf.status = .Running →
      sf.sp = sp - 224#64 →
      sf.trace = s.trace →
      CalleeSavedPreserved s sf →
      LsClInv sf →
      SepWP ((blkPC_58).rebase (blkPl_58).base H) target sf
        ((((ss + 144#64) ↦₆₄ v0) ∗ ((ss + 152#64) ↦₆₄ v1) ∗ ((ss + 160#64) ↦₆₄ v2) ∗
          ((ss + 168#64) ↦₆₄ v3) ∗ ((ss + 176#64) ↦₆₄ v4) ∗ ((ss + 184#64) ↦₆₄ v5) ∗
          ((ss + 192#64) ↦₆₄ v6) ∗ ((ss + 200#64) ↦₆₄ v7) ∗ ((ss + 208#64) ↦₆₄ v8) ∗
          ((ss + 216#64) ↦₆₄ v9) ∗ ((ss + 224#64) ↦₆₄ v10) ∗ ((ss + 232#64) ↦₆₄ v11) ∗
          ((ss + 240#64) ↦₃₂ v12) ∗ memRegion (ss + 244#64) 4 ∗
          A.pool lim (M.stepEvents evs stB) sf ∗
          memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - chStack) ∗
          stackAt (sp - 224#64) chStack) ∗ F) post) :
    SepWP ((blkPC_58).rebase (blkPl_58).base H) target s P post := by
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    RustLayoutOk, LayoutOk] at hdealloc
  rw [hP, hsp']; clear hP hsp'
  cases hGs : G_sender <;> cases hsts : st_sender
  · refine SepWP.fold (optSenderChainAt_none_expose A.repAlloc ss) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat refine SepWP.exists_elim fun _ => ?_
    refine SepWP_fold_stack_gen sp calleeStack stubStack chStack hcallee hstub_le hch_le
      (by sep_focus) rfl ?_
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (288)) hinv
    wp_steps_sync_pool ((blkPl_58).base + bv% (288))
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_f
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ FreeOnlyEvs.nil
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [CalleeSavedPreserved, arm64_norm, *]) hinv_f)
  · simp [hGs, hsts] at hGs_eq
  · simp [hGs, hsts] at hGs_eq
  · rename_i sg sc0
    refine SepWP.fold (optSenderChainAt_some_expose A.repAlloc ss sg sc0) (by sep_focus) ?_
    simp only [sepConj_assoc, A.repAlloc_live_norm]
    refine SepWP.pure_elim fun ⟨hsrk_pos, hsrk_lt, hsrk_c0, hsrk_cmn, hsrk_ptr,
      hpriv_pos, hpriv_lt, hpriv_c0, hpriv_ptr, hck_pos, hck_lt, hck_slt, hck_ptr⟩ => ?_
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
    have hsrk_sum : sg.srk.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    have hpriv_sum : sg.priv.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    have hck_sum : sg.ck.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (280)) hinv
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (sg.srk.ptr, sg.srk.cap.toNat, 1, stB)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (sg.priv.ptr, sg.priv.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents sg.srk.cap.toNat 1) stB)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (sg.ck.ptr, sg.ck.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents sg.priv.cap.toNat 1)
        (M.stepEvents (rustDeallocEvents sg.srk.cap.toNat 1) stB))
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_280
    refine SepWP_fold_stack_gen sp calleeStack stubStack mkStack hcallee hstub_le hmk_le
      (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply sepWP_seq_lscl (mid := lsmpl.base 3) hinv_280
    wp_steps_sync_pool (lsmpl.base 3)
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_call_mk
    set st_pre_mk := M.stepEvents (rustDeallocEvents sg.ck.cap.toNat 1)
      (M.stepEvents (rustDeallocEvents sg.priv.cap.toNat 1)
        (M.stepEvents (rustDeallocEvents sg.srk.cap.toNat 1) stB))
    refine SepWP_call_dropMk_lscl (stB := st_pre_mk) (sp := sp) (ret_pc := (blkPl_58).base + bv% (288))
      hdropMk hinv_call_mk ⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_mk hpc_mk hrun_mk hsp_mk hcs_mk hinv_288 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun evsMk => ?_
    refine SepWP.focus_pure (by sep_focus) fun htr_mk => ?_
    refine SepWP.focus_pure (by sep_focus) fun hfree_mk => ?_
    rw [memRegion_24_unpack ss 192]
    simp only [Nat.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun d208 => SepWP.exists_elim fun d200 => SepWP.exists_elim fun d192 => ?_
    refine SepWP_fold_stack_gen sp calleeStack mkStack chStack hcallee hmk_le hch_le
      (by sep_focus) (by simp only [arm64_norm, *]) ?_
    let evsAll :=
      rustDeallocEvents sg.srk.cap.toNat 1 ++
      rustDeallocEvents sg.priv.cap.toNat 1 ++
      rustDeallocEvents sg.ck.cap.toNat 1 ++ evsMk
    have hfree_all : FreeOnlyEvs evsAll :=
      (((freeOnly_dealloc _ _).append (freeOnly_dealloc _ _)).append
        (freeOnly_dealloc _ _)).append hfree_mk
    have hstep_all : M.stepEvents evsMk st_pre_mk = M.stepEvents evsAll stB := by
      simp only [evsAll, st_pre_mk, AllocCostModel.stepEvents_append]
    rw [hstep_all]
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_mk
    rcases hcs_mk with ⟨hcs_m19, hcs_m20, hcs_m21, hcs_m22, hcs_m23, hcs_m24, hcs_m25, hcs_m26, hcs_m27, hcs_m28, hcs_m29, hcs_mv⟩
    simp only [arm64_norm, *] at hcs_m19 hcs_m20 hcs_m21 hcs_m22 hcs_m23 hcs_m24 hcs_m25 hcs_m26 hcs_m27 hcs_m28 hcs_m29 hcs_mv
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf_mk evsAll sg.srk.cap sg.srk.ptr (BitVec.ofNat 64 sg.srk.bytes.length)
        sg.priv.cap sg.priv.ptr (BitVec.ofNat 64 sg.priv.bytes.length)
        d192 d200 d208 sg.ck.cap sg.ck.ptr 32#64 sc0.chainKey.index
        hfree_all hpc_mk hrun_mk
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [CalleeSavedPreserved, arm64_norm, *]) hinv_288)

theorem SepWP_tail_14c_to_184_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {H : String → Option (State → State)}
    {calleeStack stubStack chStack : Nat}
    (hcallee : 224 + calleeStack < 2 ^ 64)
    (hstub_le : stubStack ≤ calleeStack)
    (hch_le : chStack ≤ calleeStack)
    (hdealloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim stubStack))
    {target : BitVec 64} {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (sp ss t : BitVec 64) {sp' : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    (hpc : s.pc = (blkPl_58).base + 332#64)
    (hrun : s.status = .Running)
    (_hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp : s.sp = sp - 224#64)
    (hx19 : s.readReg64 .x19 = t)
    (hx20 : s.readReg64 .x20 = ss)
    (hchains_len : trG.ratchet.chains.length = tr.ratchet.receiverChains.length)
    (hP : P = (memRegion (ss + 72#64) 24 ∗
      (t ↦₆₄ trG.ratchet.chainsCap) ∗
      ((t + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((t + 16#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc)
        trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
      ((t + 176#64) ↦₆₄ trG.pq.cap) ∗
      ((t + 184#64) ↦₆₄ trG.pq.ptr) ∗
      ((t + 192#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗
      ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
      vecU8Buf A.repAlloc G.pq.cap G.pq.ptr st.pqRatchetState ∗
      A.pool lim stB s ∗
      memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - chStack) ∗
      stackAt sp' chStack) ∗ F)
    (hsp' : sp' = sp - 224#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      sf.pc = (blkPl_58).base + 388#64 →
      sf.status = .Running →
      sf.sp = sp - 224#64 →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_58).rebase (blkPl_58).base H) target sf
        ((vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (ss + 0x48#64)
            trG.ratchet.chainsCap trG.ratchet.chainsPtr
            (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
          (t ↦₆₄ trG.ratchet.chainsCap) ∗
          ((t + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((t + 16#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
          ((t + 176#64) ↦₆₄ trG.pq.cap) ∗
          ((t + 184#64) ↦₆₄ trG.pq.ptr) ∗
          ((t + 192#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          ((ss + 120#64) ↦₆₄ trG.pq.cap) ∗
          ((ss + 128#64) ↦₆₄ trG.pq.ptr) ∗
          ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          A.pool lim (M.stepEvents evs stB) sf ∗
          stackAt (sp - 224#64) calleeStack) ∗ F) post) :
    SepWP ((blkPC_58).rebase (blkPl_58).base H) target s P post := by
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    RustLayoutOk, LayoutOk] at hdealloc
  rw [hP, hsp']; clear hP hsp'
  rw [memRegion_24_unpack ss 72]
  simp only [Nat.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  wp_steps_sync_pool ((blkPl_58).base + bv% (356))
  simp only [State.setMem_setMem]
  refine SepWP.fold (vecAt_chains_fold A.repAlloc ss trG tr hchains_len) (by sep_focus) ?_
  by_cases hpq_cap : G.pq.cap = 0
  · have hpq_beq : (G.pq.cap == 0#64) = true := by simp [hpq_cap]
    refine SepWP.fold (vecU8Buf_eq_zero_entails_emp A.repAlloc G.pq.ptr st.pqRatchetState hpq_cap)
      (by sep_focus) ?_
    simp only [emp_sepConj]
    refine SepWP_fold_stack_to_ext_gen sp calleeStack chStack hcallee hch_le
      (by sep_focus) (by simp only [arm64_norm, *]) ?_
    wp_steps_sync_pool ((blkPl_58).base + bv% (388))
    simp only [State.setMem_setMem]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext _ [] FreeOnlyEvs.nil
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
  · have hpq_beq : (G.pq.cap == 0#64) = false := beq_false_of_ne hpq_cap
    refine SepWP.fold (vecU8Buf_dealloc A.repAlloc G.pq.cap G.pq.ptr st.pqRatchetState hpq_cap)
      (by sep_focus) ?_
    simp only [sepConj_assoc, A.repAlloc_live_norm]
    refine SepWP.pure_elim fun ⟨_, hpq_pos, hpq_lt, hpq_ptr⟩ => ?_
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
    have hpq_sum : G.pq.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    refine SepWP_fold_stack_gen sp calleeStack chStack stubStack hcallee hch_le hstub_le
      (by sep_focus) (by simp only [arm64_norm, *]) ?_
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1, stB)
    wp_steps_sync_pool ((blkPl_58).base + bv% (388))
    simp only [State.setMem_setMem]
    refine SepWP_fold_stack_to_ext_gen sp calleeStack stubStack hcallee hstub_le
      (by sep_focus) (by simp only [arm64_norm, *]) ?_
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext _ (rustDeallocEvents G.pq.cap.toNat 1) (freeOnly_dealloc _ _)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))

end LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudgetAux
