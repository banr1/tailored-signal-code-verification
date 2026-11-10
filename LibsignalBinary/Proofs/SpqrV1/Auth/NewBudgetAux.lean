/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Auth.New
public meta import LibsignalBinary.Proofs.SpqrV1.Auth.New -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Auth.Update -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<spqr::authenticator::Authenticator>::new` (Block `340`)

Defines allocation-event envelopes (`AuthNewPinnedEnv`, `AuthNewEnv`), `RustCliAllocBudget`
specifications, and relocatable `[LibsignalPlacement]` proofs for `<Authenticator>::new`
(Block `340`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.NewBudgetAux

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement blkLib_eq_340 blkPC_340 blkPl_340 lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionShimSpec tripleRatchetProgAtExt withStack
)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.LibsignalSpqrV1 (Authenticator Bytes)
open CryptoVerification.SpqrV1.Auth (
  AuthNewGhost AuthNewPinnedGhost AuthUpdateGhost AuthenticatorGhost
  SepWPp.pure_left_focus
  authNewName authNewStackExt authNewStackX authUpdateStackX
  authenticatorAt authenticatorAt_eq_exists_pinned authenticatorPinAt
  authenticatorPinAt_entails_authenticatorAt authenticatorSize
  vecBufAt vecBufAt_fold vecBufAt_of_cap_ne_zero vecBufAt_of_cap_zero
  vecU8At_expose_entails
)
open CryptoVerification.SpqrV1.Auth.NewFacts (
  authenticatorAt_sp_init authenticatorPinAt_at_sp_eq_cells_heap
  authenticatorPinAt_eq_cells_heap memRegion_48_cells rejoin_stack_authNewX
  stackAt_authNewX_split stackAt_authNewX_split_extHook stackAt_authUpdateX_split_extHook
  vecHeader_entails_memRegion_24
)
open CryptoVerification.SpqrV1.Auth.UpdateFacts (replicate_32_zero_length)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv SepWP.pure_left_focus SepWPp.of_sepWP_lsCallInv
  subroutine_ok_withLsCallInv_of_plain withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk SeqEnv fitsEvents_append
  rustAllocEvents rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetSpecWithStack)
open LibsignalBinary.Heap.IfaceLemmas (subroutine_ok_frame_oom')
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (
  AuthUpdateEnv AuthUpdateLenEnv authUpdatePinnedEvents
  authUpdatePinnedEvents_mem_authUpdateLenEnv authUpdateSpec
  freeOnlyEvs_optCapDeallocEvents optCapDeallocEvents spqrBoundedEvs_of_authUpdateLenEnv
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  subroutine_ok_allocNoOomWithStack_of_budget
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomSpecWithStack rustAllocSpecWithStack
  rustDeallocExternSpecWithStack rustDeallocSpecWithStack
)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false replicate_32_zero_length List.length_append
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

/-! ## Allocation Envelopes -/

/-- Exact initial allocation events in `<Authenticator>::new` before calling `Authenticator::update`:
two `__rust_alloc_zeroed(32, 1)` allocations for the initial 32-byte zeroed `root_key` and `mac_key`. -/
def authNewInitEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustAllocEvents 32 1

def AuthNewInitAllocEnv (evs : List AllocEvent) : Prop :=
  evs = authNewInitEvents

def AuthNewDropPinEnv (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = optCapDeallocEvents cap

/-- Envelope for `<Authenticator>::new` with pinned `root_key: Vec<u8>`:
two 32-byte zeroed allocations, followed by `Authenticator::update` (`rkLen = 32`), followed by
conditional deallocation of `x.rkPin.cap`. -/
def AuthNewPinnedEnv (x : AuthNewPinnedGhost) : List AllocEvent → Prop :=
  SeqEnv
    (SeqEnv AuthNewInitAllocEnv (AuthUpdateLenEnv 32 x.rootKey.length))
    (AuthNewDropPinEnv x.rkPin.cap)

/-- Unpinned envelope for `<Authenticator>::new`:
two 32-byte zeroed allocations, followed by `Authenticator::update` (`rkLen = 32`), followed by
`FreeOnlyEvs` drop of the consumed `root_key: Vec<u8>`. -/
def AuthNewEnv (x : AuthNewGhost) : List AllocEvent → Prop :=
  SeqEnv
    (SeqEnv AuthNewInitAllocEnv (AuthUpdateLenEnv 32 x.rootKey.length))
    FreeOnlyEvs

theorem authNewPinnedEnv_intro (x : AuthNewPinnedGhost) {evsUpd : List AllocEvent}
    (hupd : AuthUpdateLenEnv 32 x.rootKey.length evsUpd) :
    AuthNewPinnedEnv x (authNewInitEvents ++ evsUpd ++ optCapDeallocEvents x.rkPin.cap) := by
  unfold AuthNewPinnedEnv
  have h1 : AuthNewInitAllocEnv authNewInitEvents := rfl
  have h2 : AuthNewDropPinEnv x.rkPin.cap (optCapDeallocEvents x.rkPin.cap) := rfl
  simpa only [List.append_assoc] using SeqEnv.append (SeqEnv.append h1 hupd) h2

theorem authNewEnv_of_pinned {x : AuthNewGhost} {rkPin : VecPin} {evs : List AllocEvent}
    (h : AuthNewPinnedEnv ⟨x.outA, x.rkVecA, rkPin, x.rootKey⟩ evs) :
    AuthNewEnv x evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, h3⟩
  · exact Or.inl h12
  · refine Or.inr ⟨e12, e3, rfl, h12, ?_⟩
    dsimp only [AuthNewDropPinEnv] at h3
    rw [h3]
    exact freeOnlyEvs_optCapDeallocEvents rkPin.cap

theorem fitsEnv_authNewPinned_of_authNew {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : AuthNewGhost} (rkPin : VecPin)
    (h : FitsEnv M lim st (AuthNewEnv x)) :
    FitsEnv M lim st (AuthNewPinnedEnv ⟨x.outA, x.rkVecA, rkPin, x.rootKey⟩) :=
  fun evs hevs => h evs (authNewEnv_of_pinned hevs)

private theorem spqrBoundedEvs_rustAlloc32 {maxReq : Nat} (hreq : 32 ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (rustAllocEvents 32 1) := by
  have hc : (1 : Nat) ≤ 16 ∧ 1 ≤ 32 := ⟨by decide, by decide⟩
  have hmax32 : (32 : Nat) ≤ MallocngMaxAllocSize := by decide
  unfold rustAllocEvents
  simp only [hc, and_self, ↓reduceIte]
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax32, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- Every trace in `AuthNewEnv x` has at most `7` allocations and per-event request size at most
`x.rootKey.length + 96`. -/
theorem spqrBoundedEvs_of_authNewEnv {x : AuthNewGhost} {evs : List AllocEvent}
    (hmax : 32 + x.rootKey.length ≤ MallocngMaxAllocSize)
    (h : AuthNewEnv x evs) :
    SpqrBoundedEvs 7 (x.rootKey.length + 96) evs := by
  let R := x.rootKey.length + 96
  have hb_init : ∀ e, AuthNewInitAllocEnv e → SpqrBoundedEvs 2 R e := by
    rintro _ rfl
    unfold authNewInitEvents
    have b32 : SpqrBoundedEvs 1 R (rustAllocEvents 32 1) := spqrBoundedEvs_rustAlloc32 (by omega)
    exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append b32 b32)
  have hb_upd : ∀ e, AuthUpdateLenEnv 32 x.rootKey.length e → SpqrBoundedEvs 5 R e := by
    intro e he
    have hb := spqrBoundedEvs_of_authUpdateLenEnv hmax he
    exact SpqrBoundedEvs.mono (Nat.le_refl 5) (by omega) hb
  have hb_s1 : ∀ e,
      SeqEnv AuthNewInitAllocEnv (AuthUpdateLenEnv 32 x.rootKey.length) e →
      SpqrBoundedEvs 7 R e := by
    rintro e (h1 | ⟨e1, e2, rfl, h1, h2⟩)
    · exact SpqrBoundedEvs.mono (by decide) (Nat.le_refl R) (hb_init e h1)
    · exact SpqrBoundedEvs.mono (by decide) (by omega)
        (SpqrBoundedEvs.append (hb_init e1 h1) (hb_upd e2 h2))
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact hb_s1 evs h1
  · exact SpqrBoundedEvs.mono (by decide) (by omega)
      (SpqrBoundedEvs.append (hb_s1 e1 h1) (SpqrBoundedEvs.of_freeOnly h2))

theorem fitsEnv_authNewPinned_unpack {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : AuthNewPinnedGhost} (sp96 : BitVec 64)
    (h : FitsEnv M lim st (AuthNewPinnedEnv x)) :
    let st1 := M.stepEvents (rustAllocEvents 32 1) st
    let st2 := M.stepEvents (rustAllocEvents 32 1) st1
    FitsEvents M lim st (rustAllocEvents 32 1) ∧
    FitsEvents M lim st1 (rustAllocEvents 32 1) ∧
    FitsEnv M lim st2
      (AuthUpdateEnv
        ⟨sp96, { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 },
          1#64, false, x.rkPin.ptr, x.rootKey⟩) := by
  let g0 : AuthenticatorGhost := ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩
  let evs0 := authUpdatePinnedEvents g0 32 x.rootKey.length
  have hmem0 : AuthUpdateLenEnv 32 x.rootKey.length evs0 :=
    authUpdatePinnedEvents_mem_authUpdateLenEnv g0 32 x.rootKey.length
  have hfit0 : FitsEvents M lim st
      (authNewInitEvents ++ evs0 ++ optCapDeallocEvents x.rkPin.cap) :=
    h _ (authNewPinnedEnv_intro x hmem0)
  rw [fitsEvents_append] at hfit0
  rcases hfit0 with ⟨hfit0, _⟩
  rw [fitsEvents_append] at hfit0
  rcases hfit0 with ⟨hfit_init, _⟩
  unfold authNewInitEvents at hfit_init
  rw [fitsEvents_append] at hfit_init
  rcases hfit_init with ⟨hf1, hf2⟩
  refine ⟨hf1, hf2, fun evsUpd hupd => ?_⟩
  have hupd' : AuthUpdateLenEnv 32 x.rootKey.length evsUpd := by
    simpa only [AuthUpdateEnv, replicate_32_zero_length] using hupd
  have hfit_u : FitsEvents M lim st
      (authNewInitEvents ++ evsUpd ++ optCapDeallocEvents x.rkPin.cap) :=
    h _ (authNewPinnedEnv_intro x hupd')
  rw [fitsEvents_append] at hfit_u
  rcases hfit_u with ⟨hfit_u, _⟩
  rw [fitsEvents_append] at hfit_u
  rcases hfit_u with ⟨_, hfit_upd⟩
  simpa only [authNewInitEvents, M.stepEvents_append] using hfit_upd

/-! ## Budget-Threaded Specifications -/

/-- Unplaced stack-parameterized budget-threaded pinned specification of `<Authenticator>::new`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def authNewPinnedSpecAtBase (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthNewPinnedEnv x)⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8At A.repAlloc x.rkVecA x.rkPin.cap x.rkPin.ptr x.rootKey ∗
      A.pool lim st s ∗
      stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthNewPinnedEnv x evs⌝ ∗
      authenticatorAt A.repAlloc x.outA (Authenticator.new F x.rootKey 1#64) ∗
      vecHeader x.rkVecA x.rkPin.cap x.rkPin.ptr (BitVec.ofNat 64 x.rootKey.length) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp stk

def authNewPinnedSpecAt [LibsignalPlacement] (stk : Nat)
    (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthNewPinnedEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8At A.repAlloc x.rkVecA x.rkPin.cap x.rkPin.ptr x.rootKey ∗
      A.pool lim st s ∗
      stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthNewPinnedEnv x evs⌝ ∗
      authenticatorAt A.repAlloc x.outA (Authenticator.new F x.rootKey 1#64) ∗
      vecHeader x.rkVecA x.rkPin.cap x.rkPin.ptr (BitVec.ofNat 64 x.rootKey.length) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp stk

/-- Unplaced stack-parameterized budget-threaded unpinned specification of `<Authenticator>::new`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def authNewSpecAtBase (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthNewEnv x)⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8 A.repAlloc x.rkVecA x.rootKey ∗
      A.pool lim st s ∗
      stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthNewEnv x evs⌝ ∗
      authenticatorAt A.repAlloc x.outA (Authenticator.new F x.rootKey 1#64) ∗
      memRegion x.rkVecA 24 ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp stk

def authNewSpecAt [LibsignalPlacement] (stk : Nat)
    (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthNewEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8 A.repAlloc x.rkVecA x.rootKey ∗
      A.pool lim st s ∗
      stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthNewEnv x evs⌝ ∗
      authenticatorAt A.repAlloc x.outA (Authenticator.new F x.rootKey 1#64) ∗
      memRegion x.rkVecA 24 ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp stk

def authNewPinnedSpecBase (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewPinnedGhost × M.σ) :=
  authNewPinnedSpecAtBase authNewStackX F M A lim

def authNewPinnedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewPinnedGhost × M.σ) :=
  authNewPinnedSpecAt authNewStackX F M A lim

def authNewSpecBase (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewGhost × M.σ) :=
  authNewSpecAtBase authNewStackX F M A lim

def authNewSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewGhost × M.σ) :=
  authNewSpecAt authNewStackX F M A lim

def authNewPinnedSpecExtBase (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewPinnedGhost × M.σ) :=
  authNewPinnedSpecAtBase authNewStackExt F M A lim

def authNewPinnedSpecExt [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewPinnedGhost × M.σ) :=
  authNewPinnedSpecAt authNewStackExt F M A lim

def authNewSpecExtBase (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewGhost × M.σ) :=
  authNewSpecAtBase authNewStackExt F M A lim

def authNewSpecExt [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthNewGhost × M.σ) :=
  authNewSpecAt authNewStackExt F M A lim

def AuthNewPlacedOk [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_340).rebase (blkPl_340).base H) (blkPl_340).base
    (withLsCallInv lsmpl (authNewSpec F M A lim))

def AuthNewOkX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
    ((authNewSpecBase F M A lim).inImage img)

def AuthNewOkExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
    ((authNewSpecExtBase F M A lim).inImage img)

/-! ## Helper Bridges -/

private theorem pure_sepConj_imp {P Q : Prop} {R : SepProp} (h : P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ R :=
  Entails.pure_left fun hp => Entails.pure_right (h hp) (Entails.refl R)

theorem deallocExtern_of_deallocWithStack [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (h : subroutine_ok P addr (rustDeallocSpecWithStack M A lim stk)) :
    subroutine_ok P addr (rustDeallocExternSpecWithStack M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp) h ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustDeallocSpecWithStack, rustDeallocExternSpecWithStack,
      rustCliDeallocBudgetSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨h0, h1, h2, _hl, hlr⟩ => ⟨h0, h1, h2, hlr⟩)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustDeallocSpecWithStack, rustDeallocExternSpecWithStack,
      rustCliDeallocBudgetSpecWithStack, rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, _⟩ => hacp.2.1)

theorem sepWPp_entails_post {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {PostConcrete PostTargetR : State → SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : ∀ sf, PostConcrete sf ∗ R ⊢ PostTargetR sf)
    (h : SepWPp prog ret s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PostConcrete sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp oom) :
    SepWPp prog ret s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PostTargetR sf)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp oom := by
  intro R' hm hL
  rcases h R' hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, h1, h2⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      fun hmR => Satisfies.mono (hent sf) (h1 hmR), h2⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `340`) -/

attribute [local irreducible] FitsEvents

set_option maxHeartbeats 1600000 in
theorem authNewPinned_placed_ok_extern [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_update : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec F M A lim)))
    (h_shim : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack (withVmPreserved sessionShimSpec) extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocSpecWithStack M A lim true extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack M A lim extHookStack)) :
    subroutine_ok ((blkPC_340).rebase (blkPl_340).base H) (blkPl_340).base
      (withLsCallInv lsmpl (authNewPinnedSpec F M A lim)) := by
  have h_allocZeroed_no := subroutine_ok_allocNoOomWithStack_of_budget h_allocZeroed
  have h_shim_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_shim
  have h_allocZeroed_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_allocZeroed_no
  wpp_init x_st s0
  rcases x_st with ⟨⟨outA, rkVecA, rkPin, rootKey⟩, st⟩
  dsimp only [authNewPinnedSpec, authNewPinnedSpecAt, withLsCallInv] at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹_›, ‹_›⟩
  have hlen_bound : 32 + rootKey.length < 2 ^ 63 := ‹_›
  have hfits_env : FitsEnv M lim st
      (AuthNewPinnedEnv ⟨outA, rkVecA, rkPin, rootKey⟩) := ‹_›
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := ‹_›
  have hlr0_gpr : LsRetAddr624 (s0.readReg64 (.gpr 30#5)) := hlr0
  obtain ⟨hf1, hf2, hfit_upd⟩ := fitsEnv_authNewPinned_unpack (s0.sp - 96#64) hfits_env
  have hx0 : s0.readReg64 (.gpr 0#5) = outA := ‹_›
  have hx1 : s0.readReg64 (.gpr 1#5) = rkVecA := ‹_›
  subst hx0 hx1
  refine SepWPp.rw_pre (by rw [stackAt_authNewX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hinv0 ?_
  refine SepWP.fold (Entails.of_eq (stackAt_authUpdateX_split_extHook (s0.sp - 96#64))) (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  change subroutine_ok _ _
    (withLsCallInv lsmpl (withStack (withVmPreserved sessionShimSpec) extHookStack)) at h_shim_inv
  wpp_call_lsCallInv_mid h_shim_inv () hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_s1, htr_s1⟩
  refine SepWPp.transport_budgetPool hvm_s1 (hnext := ?_)
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed") hF_sf ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
  have hstack_sf : stackAt (s0.sp - 96#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 96#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  change subroutine_ok _ _
    (withLsCallInv lsmpl (rustAllocNoOomSpecWithStack M A lim true extHookStack))
    at h_allocZeroed_inv
  wpp_call_lsCallInv_mid h_allocZeroed_inv (32, 1, st) hinv2
  try simp only [↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp1, hoom1, _⟩
  have htr1 : sf_1.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using hacp1.2.1
  have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sf_1 ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_lsCallInv_mid h_shim_inv () hinv3
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_s2, htr_s2⟩
  refine SepWPp.transport_budgetPool hvm_s2 (hnext := ?_)
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed") hF_sf_2 ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  wpp_call_lsCallInv_mid h_allocZeroed_inv (32, 1, st1) hinv4
  try simp only [↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp3, hoom2, _⟩
  have htr3 : sf_3.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using hacp3.2.1
  have hoom2_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom2
  let st2 := M.stepEvents (rustAllocEvents 32 1) st1
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 341) hF_sf_3 ?_
  refine SepWP.fold
    (vecU8At_expose_entails A.repAlloc (s0.readReg64 (.gpr 1#5)) rkPin.cap rkPin.ptr rootKey)
    (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hrk_le, hrk_lt, hrk_ptr⟩
  wp_steps_sync_pool (lsmpl.base 341)
  have h_auth_sp_init :=
    authenticatorAt_sp_init A.repAlloc s0.sp
      (sf_1.readReg64 Reg.x0) (sf_3.readReg64 Reg.x0) hoom1 hoom2
  rw [RustCliAllocBudget.repAlloc_live] at h_auth_sp_init
  dsimp only [Reg.x0] at h_auth_sp_init
  refine SepWP.fold h_auth_sp_init (by sep_focus) ?_
  have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt (s0.sp - 96#64) extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (stackAt_authUpdateX_split_extHook (s0.sp - 96#64)).symm) (by sep_focus) ?_
  have hstack_upd : stackAt (s0.sp - 96#64) authUpdateStackX = stackAt sf_3.sp authUpdateStackX := by
    rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
  refine SepWP.fold (Entails.of_eq hstack_upd) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv5
  have hlen_init :
      ({ rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } :
        Authenticator).rootKey.length + rootKey.length < 2 ^ 63 := by
    simpa using hlen_bound
  change subroutine_ok _ _ (withLsCallInv lsmpl (authUpdateSpec F M A lim)) at h_update
  wpp_call_lsCallInv_mid h_update
    ((⟨s0.sp - 96#64,
       { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 },
       1#64, false, rkPin.ptr, rootKey⟩ : AuthUpdateGhost), st2)
    hinv5
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evsUpd
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr4, hupd⟩
  let st3 := M.stepEvents (optCapDeallocEvents rkPin.cap) (M.stepEvents evsUpd st2)
  let evs_total := authNewInitEvents ++ evsUpd ++ optCapDeallocEvents rkPin.cap
  have hst3_eq : st3 = M.stepEvents evs_total st := by
    simp only [st3, st2, st1, evs_total, authNewInitEvents, M.stepEvents_append]
  have hupd_len : AuthUpdateLenEnv 32 rootKey.length evsUpd := by
    simpa only [AuthUpdateEnv, replicate_32_zero_length] using hupd
  have henv_total :
      AuthNewPinnedEnv ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), rkPin, rootKey⟩
        evs_total :=
    authNewPinnedEnv_intro _ hupd_len
  refine sepWPp_entails_post
    (PostConcrete := fun sf_end =>
      ⌜sf_end.trace = s0.trace⌝ ∗
      authenticatorAt A.repAlloc (s0.readReg64 (.gpr 0#5)) (Authenticator.new F rootKey 1#64) ∗
      vecHeader (s0.readReg64 (.gpr 1#5)) rkPin.cap rkPin.ptr (BitVec.ofNat 64 rootKey.length) ∗
      A.pool lim st3 sf_end ∗
      stackAt s0.sp authNewStackX)
    (fun sf_end => by
      simp only [sepConj_assoc]
      refine Entails.pure_left fun htr_end => ?_
      rw [hst3_eq]
      refine Entails.sepExists_right evs_total ?_
      exact Entails.pure_right ⟨htr_end, henv_total⟩ (Entails.refl _))
    ?_
  apply SepWPp.of_sepWP_ret
  have hnew_eq :
      authenticatorAt A.repAlloc (s0.sp - 96#64)
        (Authenticator.update F
          { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 } 1#64 rootKey) =
      authenticatorAt A.repAlloc (s0.sp - 96#64) (Authenticator.new F rootKey 1#64) := rfl
  refine SepWP.fold (Entails.of_eq hnew_eq) (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (authenticatorAt_eq_exists_pinned A.repAlloc (s0.sp - 96#64)
      (Authenticator.new F rootKey 1#64)))
    (by sep_focus) ?_
  sep_elim_exists
  rename_i g_out
  refine SepWP.fold
    (Entails.of_eq (authenticatorPinAt_at_sp_eq_cells_heap A.repAlloc g_out s0.sp
      (Authenticator.new F rootKey 1#64)))
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (memRegion_48_cells (s0.readReg64 (.gpr 0#5))))
    (by sep_focus) ?_
  sep_elim_exists
  refine SepWP.fold (vecBufAt_fold A.repAlloc rkPin.cap rkPin.ptr rootKey) (by sep_focus) ?_
  have hstack_sf4 : stackAt sf_3.sp authUpdateStackX = stackAt (s0.sp - 96#64) authUpdateStackX := by
    rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 96#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
  by_cases hcap_rk : rkPin.cap = 0#64
  · have hst3_0 : st3 = M.stepEvents evsUpd st2 := by
      simp [st3, optCapDeallocEvents, hcap_rk]
    refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_rk hrk_le) (by sep_focus) ?_
    simp only [hcap_rk, hst3_0]
    wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
    refine SepWP.fold
      (Entails.of_eq (authenticatorPinAt_eq_cells_heap A.repAlloc g_out (s0.readReg64 (.gpr 0#5))
        (Authenticator.new F rootKey 1#64)).symm)
      (by sep_focus) ?_
    refine SepWP.fold
      (authenticatorPinAt_entails_authenticatorAt A.repAlloc g_out (s0.readReg64 (.gpr 0#5))
        (Authenticator.new F rootKey 1#64))
      (by sep_focus) ?_
    refine SepWP.fold
      (rejoin_stack_authNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    dsimp only [vecHeader]
    wp_done
  · have hcap_rk_beq : (rkPin.cap == 0#64) = false := beq_false_of_ne hcap_rk
    have hst3_ne :
        st3 = M.stepEvents (rustDeallocEvents rkPin.cap.toNat 1) (M.stepEvents evsUpd st2) := by
      simp [st3, optCapDeallocEvents, hcap_rk]
    refine SepWP.fold (vecBufAt_of_cap_ne_zero A.repAlloc hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
    refine SepWP.pure_left_focus _ (by sep_focus) ?_
    intro hrk_lay
    have ⟨_, _, _⟩ := hrk_lay
    have hrk_rlay : RustLayoutOk rkPin.cap.toNat 1 := ⟨hrk_lay, by decide⟩
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    refine SepWP.fold
      (Entails.of_eq (authenticatorPinAt_eq_cells_heap A.repAlloc g_out (s0.readReg64 (.gpr 0#5))
        (Authenticator.new F rootKey 1#64)).symm)
      (by sep_focus) ?_
    refine SepWP.fold
      (authenticatorPinAt_entails_authenticatorAt A.repAlloc g_out (s0.readReg64 (.gpr 0#5))
        (Authenticator.new F rootKey 1#64))
      (by sep_focus) ?_
    refine SepWP.fold
      (rejoin_stack_authNewX s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWP.fold
      (Entails.of_eq (stackAt_authNewX_split_extHook s0.sp))
      (by sep_focus) ?_
    wp_call h_dealloc (rkPin.ptr, rkPin.cap.toNat, 1, M.stepEvents evsUpd st2)
    rw [← hst3_ne]
    refine SepWP.fold
      (Entails.of_eq (stackAt_authNewX_split_extHook s0.sp).symm)
      (by sep_focus) ?_
    dsimp only [vecHeader]
    wp_done

theorem authNewPinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_update : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec F M A lim)))
    (h_shim : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack (withVmPreserved sessionShimSpec) extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocSpecWithStack M A lim true extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    subroutine_ok ((blkPC_340).rebase (blkPl_340).base H) (blkPl_340).base
      (withLsCallInv lsmpl (authNewPinnedSpec F M A lim)) :=
  authNewPinned_placed_ok_extern h_update h_shim h_allocZeroed
    (deallocExtern_of_deallocWithStack h_dealloc)

private theorem authNew_placed_ok_of_pinned [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hpinned : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H) (blkPl_340).base
      (withLsCallInv lsmpl (authNewPinnedSpec F M A lim))) :
    AuthNewPlacedOk F M A lim H := by
  unfold AuthNewPlacedOk
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withLsCallInv, authNewSpec, authNewSpecAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlen, hfit, hlr⟩, hpre⟩
  have h1 : s0.mem ⊨ vecU8 A.repAlloc x.rkVecA x.rootKey ∗
      (memRegion x.outA authenticatorSize ∗ A.pool lim st s0 ∗ stackAt s0.sp authNewStackX ∗ R) := by
    have hEq :
        memRegion x.outA authenticatorSize ∗ vecU8 A.repAlloc x.rkVecA x.rootKey ∗
          A.pool lim st s0 ∗ stackAt s0.sp authNewStackX ∗ R =
        vecU8 A.repAlloc x.rkVecA x.rootKey ∗
          (memRegion x.outA authenticatorSize ∗ A.pool lim st s0 ∗ stackAt s0.sp authNewStackX ∗ R) := by
      sep_ac_rfl
    simpa only [sepConj_assoc, hEq] using hpre
  unfold vecU8 at h1
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨cap, h1⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨ptr, h1⟩
  let xp : AuthNewPinnedGhost := ⟨x.outA, x.rkVecA, ⟨cap, ptr⟩, x.rootKey⟩
  have hfit_pin : FitsEnv M lim st (AuthNewPinnedEnv xp) :=
    fitsEnv_authNewPinned_of_authNew ⟨cap, ptr⟩ hfit
  have hpre_pin :
      s0.mem ⊨ (withLsCallInv lsmpl (authNewPinnedSpec F M A lim)).pre (xp, st) s0 ∗ R := by
    dsimp only [withLsCallInv, authNewPinnedSpec, authNewPinnedSpecAt, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen, hfit_pin, hlr⟩, ?_⟩
    have hEq :
        (memRegion x.outA authenticatorSize ∗ vecU8At A.repAlloc x.rkVecA cap ptr x.rootKey ∗
          A.pool lim st s0 ∗ stackAt s0.sp authNewStackX) ∗ R =
        vecU8At A.repAlloc x.rkVecA cap ptr x.rootKey ∗
          (memRegion x.outA authenticatorSize ∗ A.pool lim st s0 ∗ stackAt s0.sp authNewStackX ∗ R) := by
      sep_ac_rfl
    rwa [hEq]
  refine hpinned.mono_outcome (xp, st) R s0 hpc hrun hpre_pin hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCallInv, authNewPinnedSpec, authNewPinnedSpecAt,
      authNewSpec, authNewSpecAt, xp] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hevs⟩, hrest⟩
    refine ⟨⟨htr, authNewEnv_of_pinned hevs⟩, ?_⟩
    have hent :
        vecHeader x.rkVecA cap ptr (BitVec.ofNat 64 x.rootKey.length) ⊢ memRegion x.rkVecA 24 :=
      vecHeader_entails_memRegion_24 x.rkVecA cap ptr (BitVec.ofNat 64 x.rootKey.length)
    simp only [sepConj_assoc] at hrest ⊢
    exact Satisfies.mono (sepConj_mono_right (sepConj_mono_left hent)) hrest
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Relocatable `<spqr::authenticator::Authenticator>::new` (Block `340`) meets
`AuthNewPlacedOk F M A lim H` given `rustDeallocSpecWithStack`. -/
theorem authNew_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_update : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec F M A lim)))
    (h_shim : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack (withVmPreserved sessionShimSpec) extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocSpecWithStack M A lim true extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    AuthNewPlacedOk F M A lim H :=
  authNew_placed_ok_of_pinned
    (authNewPinned_placed_ok h_update h_shim h_allocZeroed h_dealloc)

theorem authNew_placed_ok_extern [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_update : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec F M A lim)))
    (h_shim : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack (withVmPreserved sessionShimSpec) extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocSpecWithStack M A lim true extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack M A lim extHookStack)) :
    AuthNewPlacedOk F M A lim H :=
  authNew_placed_ok_of_pinned
    (authNewPinned_placed_ok_extern h_update h_shim h_allocZeroed h_dealloc)

end LibsignalBinary.Proofs.SpqrV1.Auth.NewBudgetAux
