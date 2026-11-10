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
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.Update
public meta import LibsignalBinary.Proofs.SpqrV1.Auth.Update -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<spqr::authenticator::Authenticator>::update` (Block `341`)

Defines pinned and length-indexed allocation envelopes (`AuthUpdatePinnedEnv`, `AuthUpdateLenEnv`,
`AuthUpdateEnv`), `RustCliAllocBudget` specifications, and relocatable `[LibsignalPlacement]`
proofs for `<Authenticator>::update` (Block `341`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState toBEBytes)
open CryptoVerification (LibsignalPlacement blkLib_eq_341 blkPC_341 blkPl_341 lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  ImgCallInv extHookStack sessionShimSpec tripleRatchetProgAtExt withStack
)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre memRegion_32_cells)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes Epoch HkdfFn hkdfToSliceUnchecked hkdfToVecUnchecked spqrHkdfWith
)
open CryptoVerification.SpqrV1.Auth (
  AuthUpdateGhost AuthUpdatePinnedGhost AuthenticatorGhost
  SepWPp.pure_left_focus
  authUpdateName authUpdateStackExt authUpdateStackX
  authenticatorAt authenticatorAt_eq_exists_pinned authenticatorPinAt
  authenticatorPinAt_expose_entails dealloc_vecBuf_cases
  drop_32_take_32_eq_drop_32_of_length_64 hkdfToVecUnchecked_eq_hkdfToSliceUnchecked
  pointsTo64_rev64_eq_toBEBytes pointsToBytes_64_entails_memRegion
  pointsToBytes_replicate_64_entails_memRegion toBEBytes_8_length
  vecBufAt vecBufAt_fold vecBufAt_of_cap_ne_zero vecBufAt_of_cap_zero
  vecU8At_expose_entails
)
open CryptoVerification.SpqrV1.Auth.UpdateFacts (
  authenticatorAt_of_32_32 rejoin_stack_authUpdateX replicate_32_zero_length
  rodata_updateLabel_placed stackAt_authUpdateX_split updateLabel_length
)
open CryptoVerification.SpqrV1.ChainProofs (
  HkdfToSliceGhost SliceConcat2Ghost
  bytesAt bytesAt_false bytesAt_true exists_unpack64_of_length_64_split
  hkdfToSliceSpec hkdfToSliceSpecExt hkdfToSliceSpqrSpec hkdfToSliceStackExt
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv SepWP.pure_left_focus SepWPp.of_sepWP_lsCallInv
  drop_32_take_32_length_of_64 pointsToBytes_memRegion_entails
  rodata_zeros32_placed subroutine_ok_withLsCallInv_of_plain
  subroutine_ok_withLsCallInv_rodata2_keep take_32_length_of_64 withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved fitsEvents_append rustAllocEvents
  rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  SliceConcat2Env sliceConcat2Events sliceConcat2Spec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  subroutine_ok_allocNoOomWithStack_of_budget subroutine_ok_post_entails withAllocVmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomSpecWithStack rustAllocSpecWithStack rustDeallocSpecWithStack
)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length updateLabel_length replicate_32_zero_length
  List.length_append
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

/-! ## Allocation Envelopes -/

def optCapDeallocEvents (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1

def sliceConcat2DeallocEvents (n : Nat) : List AllocEvent :=
  if n = 0 then [] else rustDeallocEvents n 1

theorem optCapDeallocEvents_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    optCapDeallocEvents (BitVec.ofNat 64 n) = sliceConcat2DeallocEvents n := by
  unfold optCapDeallocEvents sliceConcat2DeallocEvents
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  by_cases h0 : n = 0
  · subst h0; rfl
  · have hbv : BitVec.ofNat 64 n ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      exact h0 this
    simp only [hbv, h0, htoNat, ↓reduceIte]

theorem freeOnlyEvs_optCapDeallocEvents (cap : BitVec 64) :
    FreeOnlyEvs (optCapDeallocEvents cap) := by
  unfold optCapDeallocEvents
  by_cases h : cap = 0#64
  · simp only [h, ↓reduceIte]; exact FreeOnlyEvs.nil
  · simp only [h, ↓reduceIte]; exact FreeOnlyEvs.singleton 1 cap.toNat

theorem freeOnlyEvs_sliceConcat2DeallocEvents (n : Nat) :
    FreeOnlyEvs (sliceConcat2DeallocEvents n) := by
  unfold sliceConcat2DeallocEvents
  by_cases h : n = 0
  · simp only [h, ↓reduceIte]; exact FreeOnlyEvs.nil
  · simp only [h, ↓reduceIte]; exact FreeOnlyEvs.singleton 1 n

/-- Deterministic `AllocEvent` trace of `<spqr::authenticator::Authenticator>::update` for pinned
capacities `g` and slice lengths `(rkLen, kLen)`: `ikm` and 53-byte `info` concatenations, 64-byte
zeroed `kdf_out`, two 32-byte key allocations interleaved with old-key drops, and temporary drops. -/
def authUpdatePinnedEvents (g : AuthenticatorGhost) (rkLen kLen : Nat) : List AllocEvent :=
  sliceConcat2Events (rkLen + kLen) ++
    rustAllocEvents 53 1 ++
    rustAllocEvents 64 1 ++
    rustAllocEvents 32 1 ++
    optCapDeallocEvents g.rootKey.cap ++
    rustAllocEvents 32 1 ++
    optCapDeallocEvents g.macKey.cap ++
    rustDeallocEvents 64 1 ++
    rustDeallocEvents 53 1 ++
    sliceConcat2DeallocEvents (rkLen + kLen)

def AuthUpdatePinnedEnv (x : AuthUpdatePinnedGhost) (evs : List AllocEvent) : Prop :=
  evs = authUpdatePinnedEvents x.g x.auth.rootKey.length x.k.length

theorem fitsEnv_authUpdatePinned_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : AuthUpdatePinnedGhost} :
    FitsEnv M lim st (AuthUpdatePinnedEnv x) ↔
      FitsEvents M lim st (authUpdatePinnedEvents x.g x.auth.rootKey.length x.k.length) :=
  FitsEnv.eq_iff

def AuthUpdatePreAlloc1Env (rkLen kLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = sliceConcat2Events (rkLen + kLen) ++
    rustAllocEvents 53 1 ++ rustAllocEvents 64 1 ++ rustAllocEvents 32 1

def AuthUpdateAlloc2Env (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents 32 1

/-- Length-indexed unpinned allocation envelope for `<Authenticator>::update`. -/
def AuthUpdateLenEnv (rkLen kLen : Nat) : List AllocEvent → Prop :=
  SeqEnv
    (SeqEnv
      (SeqEnv (AuthUpdatePreAlloc1Env rkLen kLen) FreeOnlyEvs)
      AuthUpdateAlloc2Env)
    FreeOnlyEvs

/-- Unpinned envelope for `<Authenticator>::update`: exact allocations interleaved with
`FreeOnlyEvs` drops of the existentially quantified pre-state `Vec<u8>` buffers and temporaries. -/
abbrev AuthUpdateEnv (x : AuthUpdateGhost) : List AllocEvent → Prop :=
  AuthUpdateLenEnv x.auth.rootKey.length x.k.length

theorem authUpdatePinnedEvents_mem_authUpdateLenEnv (g : AuthenticatorGhost) (rkLen kLen : Nat) :
    AuthUpdateLenEnv rkLen kLen (authUpdatePinnedEvents g rkLen kLen) := by
  let e1 := sliceConcat2Events (rkLen + kLen) ++
    rustAllocEvents 53 1 ++ rustAllocEvents 64 1 ++ rustAllocEvents 32 1
  let e2 := optCapDeallocEvents g.rootKey.cap
  let e3 := rustAllocEvents 32 1
  let e4 := optCapDeallocEvents g.macKey.cap ++
    rustDeallocEvents 64 1 ++ rustDeallocEvents 53 1 ++ sliceConcat2DeallocEvents (rkLen + kLen)
  have h1 : AuthUpdatePreAlloc1Env rkLen kLen e1 := rfl
  have h2 : FreeOnlyEvs e2 := freeOnlyEvs_optCapDeallocEvents g.rootKey.cap
  have h3 : AuthUpdateAlloc2Env e3 := rfl
  have h4 : FreeOnlyEvs e4 :=
    FreeOnlyEvs.append
      (FreeOnlyEvs.append
        (FreeOnlyEvs.append (freeOnlyEvs_optCapDeallocEvents g.macKey.cap)
          (FreeOnlyEvs.singleton 1 64))
        (FreeOnlyEvs.singleton 1 53))
      (freeOnlyEvs_sliceConcat2DeallocEvents (rkLen + kLen))
  have hseq : AuthUpdateLenEnv rkLen kLen (((e1 ++ e2) ++ e3) ++ e4) :=
    SeqEnv.append (SeqEnv.append (SeqEnv.append h1 h2) h3) h4
  have heq : ((e1 ++ e2) ++ e3) ++ e4 = authUpdatePinnedEvents g rkLen kLen := by
    dsimp only [e1, e2, e3, e4, authUpdatePinnedEvents]
    simp only [List.append_assoc]
  rwa [heq] at hseq

theorem authUpdatePinnedEvents_mem_authUpdateEnv (g : AuthenticatorGhost) (x : AuthUpdateGhost) :
    AuthUpdateEnv x (authUpdatePinnedEvents g x.auth.rootKey.length x.k.length) :=
  authUpdatePinnedEvents_mem_authUpdateLenEnv g x.auth.rootKey.length x.k.length

theorem fitsEvents_pinned_of_fitsEnv_authUpdateEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : AuthUpdateGhost} (g : AuthenticatorGhost)
    (h : FitsEnv M lim st (AuthUpdateEnv x)) :
    FitsEvents M lim st (authUpdatePinnedEvents g x.auth.rootKey.length x.k.length) :=
  h _ (authUpdatePinnedEvents_mem_authUpdateEnv g x)

private theorem spqrBoundedEvs_rustAlloc1 {n maxReq : Nat}
    (hpos : 0 < n) (hmax : n ≤ MallocngMaxAllocSize) (hreq : n ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (rustAllocEvents n 1) := by
  have hc : (1 : Nat) ≤ 16 ∧ 1 ≤ n := ⟨by decide, hpos⟩
  unfold rustAllocEvents
  simp only [hc, and_self, ↓reduceIte]
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_sliceConcat2 {n maxReq : Nat}
    (hmax : n ≤ MallocngMaxAllocSize) (hreq : n ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (sliceConcat2Events n) := by
  unfold sliceConcat2Events
  by_cases h0 : n = 0
  · simp only [h0, ↓reduceIte]; exact SpqrBoundedEvs.nil 1 maxReq
  · simp only [h0, ↓reduceIte]
    exact spqrBoundedEvs_rustAlloc1 (Nat.pos_of_ne_zero h0) hmax hreq

/-- Every trace in `AuthUpdateLenEnv rkLen kLen` has at most `5` allocations and per-event request
size at most `rkLen + kLen + 64`. -/
theorem spqrBoundedEvs_of_authUpdateLenEnv {rkLen kLen : Nat} {evs : List AllocEvent}
    (hmax : rkLen + kLen ≤ MallocngMaxAllocSize)
    (h : AuthUpdateLenEnv rkLen kLen evs) :
    SpqrBoundedEvs 5 (rkLen + kLen + 64) evs := by
  let R := rkLen + kLen + 64
  have h64_max : (64 : Nat) ≤ MallocngMaxAllocSize := by decide
  have h53_max : (53 : Nat) ≤ MallocngMaxAllocSize := by decide
  have h32_max : (32 : Nat) ≤ MallocngMaxAllocSize := by decide
  have hb_pre1 : ∀ e, AuthUpdatePreAlloc1Env rkLen kLen e →
      SpqrBoundedEvs 4 R e := by
    rintro _ rfl
    have b0 : SpqrBoundedEvs 1 R (sliceConcat2Events (rkLen + kLen)) :=
      spqrBoundedEvs_sliceConcat2 hmax (by omega)
    have b1 : SpqrBoundedEvs 1 R (rustAllocEvents 53 1) :=
      spqrBoundedEvs_rustAlloc1 (by decide) h53_max (by omega)
    have b2 : SpqrBoundedEvs 1 R (rustAllocEvents 64 1) :=
      spqrBoundedEvs_rustAlloc1 (by decide) h64_max (by omega)
    have b3 : SpqrBoundedEvs 1 R (rustAllocEvents 32 1) :=
      spqrBoundedEvs_rustAlloc1 (by decide) h32_max (by omega)
    simpa only [Nat.max_self] using
      SpqrBoundedEvs.append (SpqrBoundedEvs.append (SpqrBoundedEvs.append b0 b1) b2) b3
  have hb_s1 : ∀ e,
      SeqEnv (AuthUpdatePreAlloc1Env rkLen kLen) FreeOnlyEvs e →
      SpqrBoundedEvs 4 R e := by
    rintro e (h1 | ⟨e1, e2, rfl, h1, h2⟩)
    · exact hb_pre1 e h1
    · simpa only [Nat.add_zero, Nat.max_zero] using
        SpqrBoundedEvs.append (hb_pre1 e1 h1) (SpqrBoundedEvs.of_freeOnly h2)
  have hb_s2 : ∀ e,
      SeqEnv (SeqEnv (AuthUpdatePreAlloc1Env rkLen kLen) FreeOnlyEvs)
        AuthUpdateAlloc2Env e →
      SpqrBoundedEvs 5 R e := by
    rintro e (h1 | ⟨e1, e2, rfl, h1, rfl⟩)
    · exact SpqrBoundedEvs.mono (by decide) (Nat.le_refl R) (hb_s1 e h1)
    · have b4 : SpqrBoundedEvs 1 R (rustAllocEvents 32 1) :=
        spqrBoundedEvs_rustAlloc1 (by decide) h32_max (by omega)
      simpa only [Nat.max_self] using SpqrBoundedEvs.append (hb_s1 e1 h1) b4
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact hb_s2 evs h1
  · simpa only [Nat.add_zero, Nat.max_zero] using
      SpqrBoundedEvs.append (hb_s2 e1 h1) (SpqrBoundedEvs.of_freeOnly h2)

theorem spqrBoundedEvs_of_authUpdateEnv {x : AuthUpdateGhost} {evs : List AllocEvent}
    (hmax : x.auth.rootKey.length + x.k.length ≤ MallocngMaxAllocSize)
    (h : AuthUpdateEnv x evs) :
    SpqrBoundedEvs 5 (x.auth.rootKey.length + x.k.length + 64) evs :=
  spqrBoundedEvs_of_authUpdateLenEnv hmax h

theorem fitsEvents_authUpdatePinned_unpack {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {g : AuthenticatorGhost} {rkLen kLen : Nat}
    (h : FitsEvents M lim st (authUpdatePinnedEvents g rkLen kLen)) :
    let st1 := M.stepEvents (sliceConcat2Events (rkLen + kLen)) st
    let st2 := M.stepEvents (rustAllocEvents 53 1) st1
    let st3 := M.stepEvents (rustAllocEvents 64 1) st2
    let st4 := M.stepEvents (rustAllocEvents 32 1) st3
    let st5 := M.stepEvents (optCapDeallocEvents g.rootKey.cap) st4
    let st6 := M.stepEvents (rustAllocEvents 32 1) st5
    let st7 := M.stepEvents (optCapDeallocEvents g.macKey.cap) st6
    let st8 := M.stepEvents (rustDeallocEvents 64 1) st7
    let st9 := M.stepEvents (rustDeallocEvents 53 1) st8
    FitsEvents M lim st (sliceConcat2Events (rkLen + kLen)) ∧
    FitsEvents M lim st1 (rustAllocEvents 53 1) ∧
    FitsEvents M lim st2 (rustAllocEvents 64 1) ∧
    FitsEvents M lim st3 (rustAllocEvents 32 1) ∧
    FitsEvents M lim st4 (optCapDeallocEvents g.rootKey.cap) ∧
    FitsEvents M lim st5 (rustAllocEvents 32 1) ∧
    FitsEvents M lim st6 (optCapDeallocEvents g.macKey.cap) ∧
    FitsEvents M lim st7 (rustDeallocEvents 64 1) ∧
    FitsEvents M lim st8 (rustDeallocEvents 53 1) ∧
    FitsEvents M lim st9 (sliceConcat2DeallocEvents (rkLen + kLen)) ∧
    M.stepEvents (sliceConcat2DeallocEvents (rkLen + kLen)) st9 =
      M.stepEvents (authUpdatePinnedEvents g rkLen kLen) st := by
  unfold authUpdatePinnedEvents at h
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf9⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf8⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf7⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf6⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf5⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf4⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf3⟩
  rw [fitsEvents_append] at h; rcases h with ⟨h, hf2⟩
  rw [fitsEvents_append] at h; rcases h with ⟨hf0, hf1⟩
  simp only [M.stepEvents_append] at hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9
  refine ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, ?_⟩
  simp only [authUpdatePinnedEvents, M.stepEvents_append]

/-! ## Budget-Threaded Specifications -/

/-- Stack-parameterized budget-threaded pinned specification of `<Authenticator>::update`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def authUpdatePinnedSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthUpdatePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
      s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
      x.auth.rootKey.length + x.k.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthUpdatePinnedEnv x)⌝ ∗
      authenticatorPinAt A.repAlloc x.g x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthUpdatePinnedEnv x evs⌝ ∗
      authenticatorAt A.repAlloc x.selfA (x.auth.update F x.ep x.k) ∗
      bytesAt x.kRO x.kA x.k ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

/-- Stack-parameterized budget-threaded unpinned specification of `<Authenticator>::update`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def authUpdateSpecAt (stk : Nat) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthUpdateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.selfA ∧ s.readReg64 .x1 = x.ep ∧
      s.readReg64 .x2 = x.kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.k.length ∧
      x.auth.rootKey.length + x.k.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthUpdateEnv x)⌝ ∗
      authenticatorAt A.repAlloc x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthUpdateEnv x evs⌝ ∗
      authenticatorAt A.repAlloc x.selfA (x.auth.update F x.ep x.k) ∗
      bytesAt x.kRO x.kA x.k ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

abbrev authUpdatePinnedSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthUpdatePinnedGhost × M.σ) :=
  authUpdatePinnedSpecAt authUpdateStackX F M A lim

abbrev authUpdateSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthUpdateGhost × M.σ) :=
  authUpdateSpecAt authUpdateStackX F M A lim

abbrev authUpdatePinnedSpecExt (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthUpdatePinnedGhost × M.σ) :=
  authUpdatePinnedSpecAt authUpdateStackExt F M A lim

abbrev authUpdateSpecExt (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthUpdateGhost × M.σ) :=
  authUpdateSpecAt authUpdateStackExt F M A lim

def AuthUpdatePlacedOk [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_341).rebase (blkPl_341).base H) (blkPl_341).base
    (withLsCallInv lsmpl (authUpdateSpec F M A lim))

def AuthUpdateOkX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
    ((authUpdateSpec F M A lim).inImage img)

def AuthUpdateOkExt (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
    ((authUpdateSpecExt F M A lim).inImage img)

/-! ## Conditional-Drop Framing Combinators -/

theorem seq_frame_lsCallInv_pool {prog : Program} {pl : Obj.MultiPlacement}
    {mid_pc ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {P_local Q_local : State → SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hframe : P = P_local s ∗ F)
    (h1 : SepWP prog mid_pc s (P_local s)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        sm.trace = s.trace ∧ (Pm ⊢ Q_local sm)))
    (h2 : ∀ sm : State, sm.pc = mid_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → sm.trace = s.trace → LsCallInv pl sm.mem →
      SepWPp prog ret_pc sm (Q_local sm ∗ F) Q Qp) :
    SepWPp prog ret_pc s P Q Qp := by
  intro R hm hL
  rw [hframe, sepConj_assoc] at hm
  rcases h1.elim (R := F ∗ R) hm hL with
    ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hPm, hsp, hcs, htr, hent⟩ | ⟨_, hoom⟩⟩
  · have hPm' : sm.mem ⊨ (Q_local sm ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hPm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      h2 sm hpc hrun hsp hcs htr (hF.of_steps hsteps1) R hPm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem seq_frame_inImage_pool {prog : Program} {img : Obj.Image}
    {mid_pc ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {P_local Q_local : State → SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hframe : P = P_local s ∗ F)
    (h1 : SepWP prog mid_pc s (P_local s)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        sm.trace = s.trace ∧ (Pm ⊢ Q_local sm)))
    (h2 : ∀ sm : State, sm.pc = mid_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → sm.trace = s.trace → ImgCallInv img sm →
      SepWPp prog ret_pc sm (Q_local sm ∗ F) Q Qp) :
    SepWPp prog ret_pc s P Q Qp := by
  intro R hm hL
  rw [hframe, sepConj_assoc] at hm
  rcases h1.elim (R := F ∗ R) hm hL with
    ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hPm, hsp, hcs, htr, hent⟩ | ⟨_, hoom⟩⟩
  · have hPm' : sm.mem ⊨ (Q_local sm ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hPm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      h2 sm hpc hrun hsp hcs htr (hF.of_steps hsteps1) R hPm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem withStack_withVmPreserved_shim_of_rustAllocShimVm {P : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok P addr rustAllocShimVmSpec) :
    subroutine_ok P addr (withStack (withVmPreserved sessionShimSpec) hookStack) := by
  have hw := CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok
    h hookStack
  refine subroutine_ok_mono hw (fun _ R s0 hpre => ?_) (fun _ R s0 sf hpost => ?_)
  · dsimp only [withStack, withVmPreserved, sessionShimSpec, rustAllocShimVmSpec] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  · dsimp only [withStack, withVmPreserved, sessionShimSpec, rustAllocShimVmSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hacp, hvm⟩, hrest⟩
    have hEq : ((⌜VmPreserved s0 sf⌝ ∗ ⌜sf.trace = s0.trace⌝) ∗ stackAt s0.sp hookStack) ∗ R =
        ⌜VmPreserved s0 sf⌝ ∗ ⌜sf.trace = s0.trace⌝ ∗ (stackAt s0.sp hookStack ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hacp.2.1, hrest⟩

theorem withLsCallInv_withVmPreserved_of_withAllocVmPreserved {pl : Obj.MultiPlacement}
    {α : Type} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P addr (withLsCallInv pl (withAllocVmPreserved spec))) :
    subroutine_ok P addr (withLsCallInv pl (withVmPreserved spec)) := by
  refine subroutine_ok_mono h (fun _ _ _ hpre => hpre) (fun x R s0 sf hpost => ?_)
  dsimp only [withLsCallInv, withAllocVmPreserved, withVmPreserved] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.2, hpost.2⟩

theorem expose_info_vecU8At (A : RustAlloc) (sp ptr : BitVec 64) (ep : BitVec 64) :
    vecU8At A (sp - 136#64) 53#64 ptr (Authenticator.updateLabel ++ toBEBytes 8 ep) ⊢
      ⌜ptr ≠ 0⌝ ∗
        ((sp - 136#64) ↦₆₄ 53#64) ∗
        ((sp - 128#64) ↦₆₄ ptr) ∗
        ((sp - 120#64) ↦₆₄ 53#64) ∗
        (ptr ↦ₛ (Authenticator.updateLabel ++ toBEBytes 8 ep)) ∗
        A.live ptr 53 1 := by
  have hlen : (Authenticator.updateLabel ++ toBEBytes 8 ep).length = 53 := by
    simp only [List.length_append, updateLabel_length, toBEBytes_8_length]
  have h53_toNat : (53#64 : BitVec 64).toNat = 53 := by decide
  have h53_ne : (53#64 : BitVec 64) ≠ 0#64 := by decide
  have ha8 : (sp - 136#64) + 8#64 = sp - 128#64 := by bv_omega
  have ha16 : (sp - 136#64) + 16#64 = sp - 120#64 := by bv_omega
  refine Entails.trans
    (vecU8At_expose_entails A (sp - 136#64) 53#64 ptr
      (Authenticator.updateLabel ++ toBEBytes 8 ep)) ?_
  simp only [hlen, BitVec.ofNat_eq_ofNat, h53_ne, ↓reduceIte, h53_toNat, Nat.sub_self,
    memRegion_zero, sepConj_emp, ha8, ha16]
  rw [show (((sp - 136#64) ↦₆₄ 53#64) ∗
      ((sp - 128#64) ↦₆₄ ptr) ∗
      ((sp - 120#64) ↦₆₄ 53#64) ∗
      ⌜53 ≤ 53 ∧ 53 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (ptr ↦ₛ (Authenticator.updateLabel ++ toBEBytes 8 ep)) ∗
      A.live ptr 53 1) =
    (⌜53 ≤ 53 ∧ 53 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      ((sp - 136#64) ↦₆₄ 53#64) ∗
      ((sp - 128#64) ↦₆₄ ptr) ∗
      ((sp - 120#64) ↦₆₄ 53#64) ∗
      (ptr ↦ₛ (Authenticator.updateLabel ++ toBEBytes 8 ep)) ∗
      A.live ptr 53 1) by sep_ac_rfl]
  refine Entails.pure_left fun ⟨_, _, hptr_ne⟩ => ?_
  exact Entails.pure_right hptr_ne (Entails.of_eq rfl)

theorem vecBufAt_fold_append (A : RustAlloc) (cap ptr : BitVec 64)
    (bs0 bs1 : List (BitVec 8)) :
    (ptr ↦ₛ (bs0 ++ bs1)) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 (bs0.length + bs1.length))
           (cap.toNat - (bs0.length + bs1.length))) ⊢
      vecBufAt A cap ptr (bs0 ++ bs1) := by
  simpa only [List.length_append] using vecBufAt_fold A cap ptr (bs0 ++ bs1)

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `341`) -/

attribute [local irreducible] FitsEvents

private def authUpdatePinnedPlacedPostConcrete [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    (AuthUpdatePinnedGhost × M.σ) → State → State → SepProp :=
  fun (x, st) s0 sf =>
    (lsρ "spqr:.rodata..Lanon.138" ↦ᵣ Authenticator.updateLabel) ∗
    (lsρ "spqr:.rodata.cst32+0x0" ↦ᵣ List.replicate 32 0#8) ∗
    ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A.repAlloc x.selfA (x.auth.update F x.ep x.k) ∗
    bytesAt x.kRO x.kA x.k ∗
    A.pool lim (M.stepEvents (authUpdatePinnedEvents x.g x.auth.rootKey.length x.k.length) st) sf ∗
    stackAt s0.sp authUpdateStackX

set_option maxHeartbeats 3200000 in
theorem authUpdatePinned_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec M A lim)))
    (h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (h_shim : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack (withVmPreserved sessionShimSpec) extHookStack))
    (h_alloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocSpecWithStack M A lim true extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    subroutine_ok ((blkPC_341).rebase (blkPl_341).base H) (blkPl_341).base
      (withLsCallInv lsmpl (authUpdatePinnedSpec F M A lim)) := by
  have h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (hkdfToSliceUnchecked F)))) :=
    h_hkdf
  have h_alloc_no := subroutine_ok_allocNoOomWithStack_of_budget h_alloc
  have h_allocZeroed_no := subroutine_ok_allocNoOomWithStack_of_budget h_allocZeroed
  have h_shim_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_shim
  have h_alloc_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_alloc_no
  have h_allocZeroed_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_allocZeroed_no
  have h_dealloc_inv := subroutine_ok_withLsCallInv_of_plain (pl := lsmpl) h_dealloc
  refine subroutine_ok_withLsCallInv_rodata2_keep rodata_updateLabel_placed rodata_zeros32_placed ?_
  refine subroutine_ok_post_entails
    (authUpdatePinnedPlacedPostConcrete F M A lim)
    (fun (x, st) s0 sf => by
      dsimp only [authUpdatePinnedPlacedPostConcrete, authUpdatePinnedSpec, authUpdatePinnedSpecAt]
      refine sepConj_mono_right (sepConj_mono_right ?_)
      refine Entails.pure_left fun htr => ?_
      refine Entails.sepExists_right
        (authUpdatePinnedEvents x.g x.auth.rootKey.length x.k.length) ?_
      exact Entails.pure_right ⟨htr, rfl⟩ (Entails.refl _))
    ?_
  wpp_init x_st s0
  rcases x_st with ⟨⟨selfA, g, auth, ep, kRO, kA, k⟩, st⟩
  dsimp only [authUpdatePinnedPlacedPostConcrete, authUpdatePinnedSpec,
    authUpdatePinnedSpecAt] at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹_›, ‹_›⟩
  have hlen_bound : auth.rootKey.length + k.length < 2 ^ 63 := ‹_›
  have hfits_env : FitsEnv M lim st
      (AuthUpdatePinnedEnv ⟨selfA, g, auth, ep, kRO, kA, k⟩) := ‹_›
  have hfits_all : FitsEvents M lim st
      (authUpdatePinnedEvents g auth.rootKey.length k.length) :=
    hfits_env _ rfl
  obtain ⟨hf0, hf1, hf2, hf3, _, hf5, _, _, _, _, hst_final⟩ :=
    fitsEvents_authUpdatePinned_unpack hfits_all
  have hx0 : s0.readReg64 (.gpr 0#5) = selfA := ‹_›
  have hx1 : s0.readReg64 (.gpr 1#5) = ep := ‹_›
  have hx2 : s0.readReg64 (.gpr 2#5) = kA := ‹_›
  subst hx0 hx1 hx2
  refine SepWPp.rw_pre (by rw [stackAt_authUpdateX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hinv0 ?_
  refine SepWP.fold
    (authenticatorPinAt_expose_entails A.repAlloc g (s0.readReg64 (.gpr 0#5)) auth)
    (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨⟨hrk_le, hrk_lt, hrk_ptr⟩, ⟨hmk_le, hmk_lt, hmk_ptr⟩⟩
  wp_steps_sync_pool (lsmpl.base 386)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  have hfit_c1 : FitsEnv M lim st
      (SliceConcat2Env
        ⟨s0.sp - 160#64, s0.sp - 112#64, false, g.rootKey.ptr, auth.rootKey,
          kRO, s0.readReg64 (.gpr 2#5), k⟩) := by
    intro evs hevs; rw [hevs]; exact hf0
  change subroutine_ok _ _ (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) at h_concat
  wpp_call_lsCallInv_mid h_concat
    ((⟨s0.sp - 160#64, s0.sp - 112#64, false, g.rootKey.ptr, auth.rootKey,
       kRO, s0.readReg64 (.gpr 2#5), k⟩ : SliceConcat2Ghost), st)
    hinv1
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs1
  apply SepWPp.exists_elim; intro ptr_ikm
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr1, _, hevs1⟩
  have hevs1_eq : evs1 = sliceConcat2Events (auth.rootKey.length + k.length) := hevs1
  subst hevs1_eq
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 386) hF_sf ?_
  wp_steps_sync_pool (lsmpl.base 386)
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 56#64) (s0.readReg64 (.gpr 1#5))))
    (by sep_focus) ?_
  have hstack_sf : stackAt (s0.sp - 160#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 160#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  let st1 := M.stepEvents (sliceConcat2Events (auth.rootKey.length + k.length)) st
  have heq53 :
      sliceConcat2Events
        (Authenticator.updateLabel.length + (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length) =
        rustAllocEvents 53 1 := by
    simp [sliceConcat2Events, updateLabel_length, toBEBytes_8_length]
  have hfit_c2 : FitsEnv M lim st1
      (SliceConcat2Env
        ⟨s0.sp - 136#64, s0.sp - 112#64,
          true, lsρ "spqr:.rodata..Lanon.138", Authenticator.updateLabel,
          false, s0.sp - 56#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5))⟩) := by
    intro evs hevs
    dsimp only [SliceConcat2Env] at hevs
    rw [hevs, heq53]
    exact hf1
  wpp_call_lsCallInv_mid h_concat
    ((⟨s0.sp - 136#64, s0.sp - 112#64,
       true, lsρ "spqr:.rodata..Lanon.138", Authenticator.updateLabel,
       false, s0.sp - 56#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5))⟩ : SliceConcat2Ghost), st1)
    hinv2
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs2
  apply SepWPp.exists_elim; intro ptr_info
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr2, _, hevs2⟩
  have hevs2_eq : evs2 = rustAllocEvents 53 1 := by
    dsimp only [SliceConcat2Env] at hevs2
    rwa [heq53] at hevs2
  subst hevs2_eq
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sf_1 ?_
  have hinfo_cap_eq :
      BitVec.ofNat 64
        (Authenticator.updateLabel.length + (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length) =
        53#64 := by
    simp [updateLabel_length, toBEBytes_8_length]
  try rw [hinfo_cap_eq]
  refine SepWP.fold
    (vecU8At_expose_entails A.repAlloc (s0.sp - 160#64)
      (BitVec.ofNat 64 (auth.rootKey.length + k.length)) ptr_ikm (auth.rootKey ++ k))
    (by sep_focus) ?_
  refine SepWP.fold
    (expose_info_vecU8At A.repAlloc s0.sp ptr_info (s0.readReg64 (.gpr 1#5)))
    (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  intro hinfo_ptr
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hikm_le, hikm_lt, hikm_ptr⟩
  have hikm_len_lt : (auth.rootKey ++ k).length < 2 ^ 63 := Nat.lt_of_le_of_lt hikm_le hikm_lt
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  change subroutine_ok _ _
    (withLsCallInv lsmpl (withStack (withVmPreserved sessionShimSpec) extHookStack)) at h_shim_inv
  wpp_call_lsCallInv_mid h_shim_inv () hinv3
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_s1, htr_s1⟩
  refine SepWPp.transport_budgetPool hvm_s1 (hnext := ?_)
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed") hF_sf_2 ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  let st2 := M.stepEvents (rustAllocEvents 53 1) st1
  have hlay64 : RustLayoutOk 64 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  change subroutine_ok _ _
    (withLsCallInv lsmpl (rustAllocNoOomSpecWithStack M A lim true extHookStack))
    at h_allocZeroed_inv
  wpp_call_lsCallInv_mid h_allocZeroed_inv (64, 1, st2) hinv4
  try simp only [↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp3, hoom64, _⟩
  have htr3 : sf_3.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using hacp3.2.1
  have hoom64_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 379) hF_sf_3 ?_
  refine SepWP.fold
    (pointsToBytes_replicate_64_entails_memRegion (sf_3.readReg64 Reg.x0)) (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 379)
  have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
    rw [‹sf_3.sp = sf_2.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv5
  have hinfo_ge :
      32 ≤ (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length := by simp
  have hinfo_lt :
      (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length < 55 := by simp
  change subroutine_ok _ _
    (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (hkdfToSliceUnchecked F))))
    at h_hkdf
  wpp_call_lsCallInv_mid h_hkdf
    (⟨true, lsρ "spqr:.rodata.cst32+0x0", List.replicate 32 0#8,
      false, ptr_ikm, auth.rootKey ++ k,
      false, ptr_info, Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
      sf_3.readReg64 Reg.x0, 64⟩ : HkdfToSliceGhost)
    hinv5
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_hkdf, hkdf_len, htr4⟩
  refine SepWPp.transport_budgetPool hvm_hkdf (hnext := ?_)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
    exists_unpack64_of_length_64_split hkdf_len
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sf_4 ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
    rw [‹sf_4.sp = sf_3.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv6
  wpp_call_lsCallInv_mid h_shim_inv () hinv6
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_s2, htr_s2⟩
  refine SepWPp.transport_budgetPool hvm_s2 (hnext := ?_)
  refine SepWPp.of_sepWP_lsCallInv
    (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hF_sf_5 ?_
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
    rw [‹sf_5.sp = sf_4.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv7
  let st3 := M.stepEvents (rustAllocEvents 64 1) st2
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  change subroutine_ok _ _
    (withLsCallInv lsmpl (rustAllocNoOomSpecWithStack M A lim false extHookStack))
    at h_alloc_inv
  wpp_call_lsCallInv_mid h_alloc_inv (32, 1, st3) hinv7
  try simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp6, hoom32_1, _⟩
  have htr6 : sf_6.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using hacp6.2.1
  have hoom32_1_beq : (sf_6.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_1
  let st4 := M.stepEvents (rustAllocEvents 32 1) st3
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_341).base + 228#64) hF_sf_6 ?_
  refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0))) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_6.readReg64 Reg.x0))) (by sep_focus) ?_
  sep_elim_exists
  wp_steps_sync_pool ((blkPl_341).base + 228#64)
  refine SepWP.fold (Entails.of_eq (hokm_take (sf_6.readReg64 Reg.x0)).symm) (by sep_focus) ?_
  refine SepWP.fold
    (vecBufAt_fold A.repAlloc g.rootKey.cap g.rootKey.ptr auth.rootKey) (by sep_focus) ?_
  have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
    rw [‹sf_6.sp = sf_5.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv8
  let st5 := M.stepEvents (optCapDeallocEvents g.rootKey.cap) st4
  refine seq_frame_lsCallInv_pool
    (mid_pc := (blkPl_341).base + 244#64)
    (P_local := fun s_cur =>
      vecBufAt A.repAlloc g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        A.pool lim st4 s_cur ∗ stackAt sf_6.sp extHookStack)
    (Q_local := fun sm1 =>
      A.pool lim st5 sm1 ∗ stackAt sf_6.sp extHookStack)
    hinv8 (by sep_focus) ?_ ?_
  · by_cases hcap_rk : g.rootKey.cap = 0#64
    · have hst5 : st5 = st4 := by simp [st5, optCapDeallocEvents, hcap_rk]
      refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_rk hrk_le) (by sep_focus) ?_
      simp only [hcap_rk, hst5]
      wp_steps_sync_pool ((blkPl_341).base + 244#64)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal,
        by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
        by wp_norm_goal, Entails.refl _⟩
    · have hcap_rk_beq : (g.rootKey.cap == 0#64) = false := beq_false_of_ne hcap_rk
      have hst5 : st5 = M.stepEvents (rustDeallocEvents g.rootKey.cap.toNat 1) st4 := by
        simp [st5, optCapDeallocEvents, hcap_rk]
      refine SepWP.fold
        (vecBufAt_of_cap_ne_zero A.repAlloc hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_
      intro hrk_lay
      have ⟨_, _, _⟩ := hrk_lay
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      wp_call h_dealloc (g.rootKey.ptr, g.rootKey.cap.toNat, 1, st4)
      have htr_rk := (‹AllocCallPreserved _ _›).2.1
      rw [← hst5]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        Entails.refl _⟩
  · intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 hcs_sm1 htr_sm1 hF_sm1
    simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm1 hcs_sm1 htr_sm1
    have hstack_sm1 : stackAt sf_6.sp extHookStack = stackAt sm1.sp extHookStack := by
      rw [hsp_sm1, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
        ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 160#64›]
    rcases hcs_sm1 with ⟨hx19_sm1, hx20_sm1, hx21_sm1, hx22_sm1, hx23_sm1, hx24_sm1,
      hx25_sm1, hx26_sm1, hx27_sm1, hx28_sm1, hx29_sm1, hvregs_sm1⟩
    refine SepWPp.of_sepWP_lsCallInv
      (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") hF_sm1 ?_
    refine SepWP.fold (Entails.of_eq hstack_sm1) (by sep_focus) ?_
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv9
    wpp_call_lsCallInv_mid h_shim_inv () hinv9
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hvm_s3, htr_s3⟩
    refine SepWPp.transport_budgetPool hvm_s3 (hnext := ?_)
    refine SepWPp.of_sepWP_lsCallInv
      (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") hF_sf_7 ?_
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    have hstack_sf7 : stackAt sm1.sp extHookStack = stackAt sf_7.sp extHookStack := by
      rw [‹sf_7.sp = sm1.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv10
    wpp_call_lsCallInv_mid h_alloc_inv (32, 1, st5) hinv10
    try simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hacp8, hoom32_2, _⟩
    have htr8 : sf_8.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, *] using hacp8.2.1
    have hoom32_2_beq : (sf_8.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_2
    let st6 := M.stepEvents (rustAllocEvents 32 1) st5
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_341).base + 292#64) hF_sf_8 ?_
    refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_8.readReg64 Reg.x0))) (by sep_focus) ?_
    sep_elim_exists
    wp_steps_sync_pool ((blkPl_341).base + 292#64)
    refine SepWP.fold (Entails.of_eq (hokm_drop (sf_8.readReg64 Reg.x0)).symm) (by sep_focus) ?_
    refine SepWP.fold
      (vecBufAt_fold A.repAlloc g.macKey.cap g.macKey.ptr auth.macKey) (by sep_focus) ?_
    have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
      rw [‹sf_8.sp = sf_7.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv11
    let st7 := M.stepEvents (optCapDeallocEvents g.macKey.cap) st6
    refine seq_frame_lsCallInv_pool
      (mid_pc := (blkPl_341).base + 308#64)
      (P_local := fun s_cur =>
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
          vecBufAt A.repAlloc g.macKey.cap g.macKey.ptr auth.macKey ∗
          A.pool lim st6 s_cur ∗ stackAt sf_8.sp extHookStack)
      (Q_local := fun sm2 =>
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
          A.pool lim st7 sm2 ∗ stackAt sf_8.sp extHookStack)
      hinv11 (by sep_focus) ?_ ?_
    · by_cases hcap_mk : g.macKey.cap = 0#64
      · have hst7 : st7 = st6 := by simp [st7, optCapDeallocEvents, hcap_mk]
        refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_mk hmk_le) (by sep_focus) ?_
        simp only [hcap_mk, hst7]
        wp_steps_sync_pool ((blkPl_341).base + 308#64)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal,
          by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
          by wp_norm_goal, Entails.of_eq (by sep_ac_rfl)⟩
      · have hcap_mk_beq : (g.macKey.cap == 0#64) = false := beq_false_of_ne hcap_mk
        have hst7 : st7 = M.stepEvents (rustDeallocEvents g.macKey.cap.toNat 1) st6 := by
          simp [st7, optCapDeallocEvents, hcap_mk]
        refine SepWP.fold
          (vecBufAt_of_cap_ne_zero A.repAlloc hcap_mk hmk_le hmk_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_
        intro hmk_lay
        have ⟨_, _, _⟩ := hmk_lay
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        wp_call h_dealloc (g.macKey.ptr, g.macKey.cap.toNat, 1, st6)
        have htr_mk := (‹AllocCallPreserved _ _›).2.1
        rw [← hst7]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by sep_ac_rfl)⟩
    · intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 hcs_sm2 htr_sm2 hF_sm2
      simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm2 hcs_sm2 htr_sm2
      have hstack_sm2 : stackAt sf_8.sp extHookStack = stackAt sm2.sp extHookStack := by
        rw [hsp_sm2, ‹sf_8.sp = sf_7.sp›, ‹sf_7.sp = sm1.sp›, hsp_sm1]
      rcases hcs_sm2 with ⟨hx19_sm2, hx20_sm2, hx21_sm2, hx22_sm2, hx23_sm2, hx24_sm2,
        hx25_sm2, hx26_sm2, hx27_sm2, hx28_sm2, hx29_sm2, hvregs_sm2⟩
      refine SepWPp.of_sepWP_lsCallInv
        (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hF_sm2 ?_
      refine SepWP.fold (Entails.of_eq hstack_sm2) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0)).symm) (by sep_focus) ?_
      refine SepWP.fold
        (pointsToBytes_64_entails_memRegion (sf_3.readReg64 Reg.x0) hkdf_len) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv12
      change subroutine_ok _ _
        (withLsCallInv lsmpl (rustDeallocSpecWithStack M A lim extHookStack)) at h_dealloc_inv
      wpp_call_lsCallInv_mid h_dealloc_inv (sf_3.readReg64 Reg.x0, 64, 1, st7) hinv12
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hacp9, _⟩
      have htr9 : sf_9.trace = s0.trace := by
        simpa only [wp_norm, arm64_norm, *] using hacp9.2.1
      let st8 := M.stepEvents (rustDeallocEvents 64 1) st7
      have h53_beq : (53#64 == 0#64) = false := by decide
      have hmr_info :
          (ptr_info ↦ₛ (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)))) ⊢
            memRegion ptr_info 53 := by
        have hlen53 :
            (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 53 := by
          simp only [List.length_append, updateLabel_length, toBEBytes_8_length]
        rw [← hlen53]
        exact pointsToBytes_entails_memRegion ptr_info _
      refine SepWPp.of_sepWP_lsCallInv
        (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hF_sf_9 ?_
      refine SepWP.fold hmr_info (by sep_focus) ?_
      have hstack_sf9 : stackAt sm2.sp extHookStack = stackAt sf_9.sp extHookStack := by
        rw [‹sf_9.sp = sm2.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv13
      wpp_call_lsCallInv_mid h_dealloc_inv (ptr_info, 53, 1, st8) hinv13
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hacp10, _⟩
      have htr10 : sf_10.trace = s0.trace := by
        simpa only [wp_norm, arm64_norm, *] using hacp10.2.1
      let st9 := M.stepEvents (rustDeallocEvents 53 1) st8
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_341).base + 360#64) hF_sf_10 ?_
      refine SepWP.fold
        (vecBufAt_fold_append A.repAlloc (BitVec.ofNat 64 (auth.rootKey.length + k.length))
          ptr_ikm auth.rootKey k) (by sep_focus) ?_
      have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
        rw [‹sf_10.sp = sf_9.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
      wp_steps_sync_pool ((blkPl_341).base + 360#64)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv14
      let st10 := M.stepEvents (sliceConcat2DeallocEvents (auth.rootKey.length + k.length)) st9
      have hopt_ikm :
          optCapDeallocEvents (BitVec.ofNat 64 (auth.rootKey.length + k.length)) =
            sliceConcat2DeallocEvents (auth.rootKey.length + k.length) :=
        optCapDeallocEvents_ofNat (by omega)
      refine seq_frame_lsCallInv_pool
        (mid_pc := (blkPl_341).base + 376#64)
        (P_local := fun s_cur =>
          vecBufAt A.repAlloc (BitVec.ofNat 64 (auth.rootKey.length + k.length))
            ptr_ikm (auth.rootKey ++ k) ∗
            A.pool lim st9 s_cur ∗ stackAt sf_10.sp extHookStack)
        (Q_local := fun sm3 =>
          A.pool lim st10 sm3 ∗ stackAt sf_10.sp extHookStack)
        hinv14 (by sep_focus) ?_ ?_
      · rcases dealloc_vecBuf_cases hikm_le with hcap_ikm | hcap_ikm
        · have hst10 : st10 = st9 := by
            simp only [st10, ← hopt_ikm, optCapDeallocEvents, hcap_ikm, ↓reduceIte,
              M.stepEvents_nil]
          refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_ikm hikm_le) (by sep_focus) ?_
          simp only [hcap_ikm, hst10]
          wp_steps_sync_pool ((blkPl_341).base + 376#64)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal,
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
            by wp_norm_goal, Entails.refl _⟩
        · have hcap_ikm_beq :
              (BitVec.ofNat 64 (auth.rootKey.length + k.length) == 0#64) = false :=
            beq_false_of_ne hcap_ikm
          have hst10 :
              st10 = M.stepEvents
                (rustDeallocEvents (BitVec.ofNat 64 (auth.rootKey.length + k.length)).toNat 1)
                st9 := by
            simp only [st10, ← hopt_ikm, optCapDeallocEvents, hcap_ikm, ↓reduceIte]
          refine SepWP.fold
            (vecBufAt_of_cap_ne_zero A.repAlloc hcap_ikm hikm_le hikm_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          intro hikm_lay
          have ⟨_, _, _⟩ := hikm_lay
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_call h_dealloc
            (ptr_ikm, (BitVec.ofNat 64 (auth.rootKey.length + k.length)).toNat, 1, st9)
          have htr_ikm := (‹AllocCallPreserved _ _›).2.1
          rw [← hst10]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by simp only [wp_norm, arm64_norm, *],
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            Entails.refl _⟩
      · intro sm3 hpc_sm3 hrun_sm3 hsp_sm3 hcs_sm3 htr_sm3 _
        have hstack_sm3 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 160#64) extHookStack := by
          rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sm2.sp›, hsp_sm2]
        simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm3 hcs_sm3 htr_sm3
        rcases hcs_sm3 with ⟨hx19_sm3, hx20_sm3, hx21_sm3, hx22_sm3, hx23_sm3, hx24_sm3,
          hx25_sm3, hx26_sm3, hx27_sm3, hx28_sm3, hx29_sm3, hvregs_sm3⟩
        apply SepWPp.of_sepWP_ret
        refine SepWP.fold (Entails.of_eq hstack_sm3) (by sep_focus) ?_
        wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
        have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
        refine SepWP.fold
          (rejoin_stack_authUpdateX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _)
          (by sep_focus) ?_
        have hrk_new_len :
            (List.take 32
              (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64)).length =
              32 :=
          take_32_length_of_64 hkdf_len
        have hmk_new_len :
            (List.take 32
              (List.drop 32
                (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                  (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64))).length =
              32 :=
          drop_32_take_32_length_of_64 hkdf_len
        have h_auth_fold :=
          authenticatorAt_of_32_32 A.repAlloc (s0.readReg64 (.gpr 0#5))
            (sf_6.readReg64 Reg.x0) (sf_8.readReg64 Reg.x0)
            _ _ hrk_new_len hmk_new_len hoom32_1 hoom32_2
        rw [RustCliAllocBudget.repAlloc_live] at h_auth_fold
        dsimp only [Reg.x0] at h_auth_fold
        refine SepWP.fold h_auth_fold (by sep_focus) ?_
        rw [drop_32_take_32_eq_drop_32_of_length_64 hkdf_len]
        have hst10_eq : st10 =
            M.stepEvents (authUpdatePinnedEvents g auth.rootKey.length k.length) st :=
          hst_final
        rw [hst10_eq]
        dsimp only [Authenticator.update, hkdfToVecUnchecked_eq_hkdfToSliceUnchecked]
        wp_done

/-- Relocatable `<spqr::authenticator::Authenticator>::update` (Block `341`) meets
`withLsCallInv lsmpl (authUpdateSpec F M A lim)` (`AuthUpdatePlacedOk`) under `[LibsignalPlacement]`. -/
theorem authUpdate_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_concat : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec M A lim)))
    (h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (h_shim : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack (withVmPreserved sessionShimSpec) extHookStack))
    (h_alloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (h_allocZeroed : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocSpecWithStack M A lim true extHookStack))
    (h_dealloc : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    AuthUpdatePlacedOk F M A lim H := by
  unfold AuthUpdatePlacedOk
  have hpinned := authUpdatePinned_placed_ok h_concat h_hkdf h_shim h_alloc h_allocZeroed h_dealloc
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withLsCallInv, authUpdateSpec, authUpdateSpecAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hfit⟩, hpre⟩
  have h1 : s0.mem ⊨ authenticatorAt A.repAlloc x.selfA x.auth ∗
      (bytesAt x.kRO x.kA x.k ∗ A.pool lim st s0 ∗ stackAt s0.sp authUpdateStackX ∗ R) := by
    have hEq :
        authenticatorAt A.repAlloc x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
          A.pool lim st s0 ∗ stackAt s0.sp authUpdateStackX ∗ R =
        authenticatorAt A.repAlloc x.selfA x.auth ∗
          (bytesAt x.kRO x.kA x.k ∗ A.pool lim st s0 ∗ stackAt s0.sp authUpdateStackX ∗ R) := by
      sep_ac_rfl
    simpa only [sepConj_assoc, hEq] using hpre
  rw [authenticatorAt_eq_exists_pinned A.repAlloc x.selfA x.auth,
    sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨g, hg⟩
  let xp : AuthUpdatePinnedGhost := ⟨x.selfA, g, x.auth, x.ep, x.kRO, x.kA, x.k⟩
  have hfit_pin : FitsEnv M lim st (AuthUpdatePinnedEnv xp) := by
    intro evs hevs
    rw [hevs]
    exact fitsEvents_pinned_of_fitsEnv_authUpdateEnv g hfit
  have hpre_pin :
      s0.mem ⊨ (withLsCallInv lsmpl (authUpdatePinnedSpec F M A lim)).pre (xp, st) s0 ∗ R := by
    dsimp only [withLsCallInv, authUpdatePinnedSpec, authUpdatePinnedSpecAt, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hlen, hfit_pin⟩, ?_⟩
    have hEq :
        (authenticatorPinAt A.repAlloc g x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
          A.pool lim st s0 ∗ stackAt s0.sp authUpdateStackX) ∗ R =
        authenticatorPinAt A.repAlloc g x.selfA x.auth ∗
          (bytesAt x.kRO x.kA x.k ∗ A.pool lim st s0 ∗ stackAt s0.sp authUpdateStackX ∗ R) := by
      sep_ac_rfl
    rwa [hEq]
  refine hpinned.mono_outcome (xp, st) R s0 hpc hrun hpre_pin hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCallInv, authUpdatePinnedSpec, authUpdatePinnedSpecAt,
      authUpdateSpec, authUpdateSpecAt, xp] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hevs⟩, hrest⟩
    rw [hevs]
    exact ⟨⟨htr, authUpdatePinnedEvents_mem_authUpdateEnv g x⟩, by rwa [← hevs]⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

end LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
