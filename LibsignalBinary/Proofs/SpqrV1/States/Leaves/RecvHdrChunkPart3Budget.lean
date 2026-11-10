/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded HMAC Call Helpers

Call-site budget specification (`libcruxHmacHdrSpec`), `LibcruxHmacEnv` sufficiency lemma,
`subroutine_ok` lifts, and Block `369` `[LibsignalPlacement]` hook discharge for `libcrux_hmac::hmac`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3Budget

open Arm64 ProofLib
open CryptoGames.HMAC (hmacWith)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_369 blkPl_369 lsProg_369 lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Authenticator LibcruxHmacCall)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost)
open CryptoVerification.SpqrV1.Auth.NewFacts (authenticatorHeapAt)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.States.Leaves (
  subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain
)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk (
  authenticatorHeapAt_expose_macKey
  authenticatorHeapAt_unexpose_macKey
  vecU8_expose_nonempty_192
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (vecU8HeapAt)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (
  LibcruxHmacEnv libcruxHmacBudgetSpec libcruxHmacSha256Events
)

/-! ## 1. `LibcruxHmacEnv` Sufficiency & Call-Site `libcrux_hmac::hmac` Specification -/

/-- `FitsEvents M lim st libcruxHmacSha256Events` unconditionally establishes
    `FitsEnv M lim st (LibcruxHmacEnv x)` (the overflow panic arm emits `[]`). -/
theorem fitsEnv_libcruxHmacEnv_of_fitsEvents {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : LibcruxHmacCall}
    (h : FitsEvents M lim st libcruxHmacSha256Events) :
    FitsEnv M lim st (LibcruxHmacEnv x) := by
  intro evs hevs
  dsimp only [LibcruxHmacEnv] at hevs
  split_ifs at hevs
  · subst hevs; exact h
  · subst hevs; trivial

/-- Budget-threaded call-site `libcrux_hmac::hmac` specification for `<NoHeaderReceived>::recv_hdr_chunk`:
    - drops `allocFailedIn` from `onPanic` (ruled out by `FitsEnv M lim st (LibcruxHmacEnv x)`);
    - eliminates the `2 ^ 32 ≤ x.data.length` panic branch via `x.data.length < 2 ^ 32` in `pre`,
      and maps `2 ^ 32 ≤ x.key.length` to `P` (`isPanic = true`);
    - pins the normal-return allocator state directly to `M.stepEvents libcruxHmacSha256Events st`. -/
def libcruxHmacHdrSpec (P : Prop) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LibcruxHmacCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      (2 ^ 32 ≤ x.key.length → P) ∧ x.data.length < 2 ^ 32 ∧
      FitsEnv M lim st (LibcruxHmacEnv x)⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜x.key.length < 2 ^ 32 ∧ sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
      A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf =>
    ⌜P ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 2. Generic & Relocatable Block-`369` `subroutine_ok` Lifts -/

/-- Lift `subroutine_ok prog entry (libcruxHmacBudgetSpec F M A lim)` to the `recv_hdr_chunk`
    call-site specification `libcruxHmacHdrSpec P F M A lim`. -/
theorem subroutine_ok_libcruxHmacHdr_of_budget {P : Prop} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hraw : subroutine_ok prog entry (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok prog entry (libcruxHmacHdrSpec P F M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacHdrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_imp, hd_lt, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ (libcruxHmacBudgetSpec F M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hfits⟩, hmem⟩
  refine hraw.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacBudgetSpec, libcruxHmacHdrSpec] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hk_lt, hd_lt', htr_eq, hevs⟩, hmem'⟩
    have hevs_eq : evs = libcruxHmacSha256Events := by
      dsimp only [LibcruxHmacEnv] at hevs
      simpa only [hk_lt, hd_lt', and_self, ↓reduceIte] using hevs
    subst hevs_eq
    exact ⟨⟨hk_lt, htr_eq⟩, hmem'⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacBudgetSpec, libcruxHmacHdrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hk_ge | hd_ge, hpref⟩, hmem'⟩
    · exact ⟨⟨hk_imp hk_ge, hpref⟩, hmem'⟩
    · omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem subroutine_ok_inImage_libcruxHmacHdr_of_budget {P : Prop} {img : Obj.Image}
    {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hraw : subroutine_ok prog entry ((libcruxHmacBudgetSpec F M A lim).inImage img)) :
    subroutine_ok prog entry ((libcruxHmacHdrSpec P F M A lim).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, libcruxHmacHdrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_imp, hd_lt, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((libcruxHmacBudgetSpec F M A lim).inImage img).pre (x, st) s0 ∗ R := by
    dsimp only [Spec.inImage, libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hfits⟩, hmem⟩
  refine (hraw.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, libcruxHmacBudgetSpec, libcruxHmacHdrSpec] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hk_lt, hd_lt', htr_eq, hevs⟩, hmem'⟩
    have hevs_eq : evs = libcruxHmacSha256Events := by
      dsimp only [LibcruxHmacEnv] at hevs
      simpa only [hk_lt, hd_lt', and_self, ↓reduceIte] using hevs
    subst hevs_eq
    exact ⟨⟨hk_lt, htr_eq⟩, hmem'⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, libcruxHmacBudgetSpec, libcruxHmacHdrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hk_ge | hd_ge, hpref⟩, hmem'⟩
    · exact ⟨⟨hk_imp hk_ge, hpref⟩, hmem'⟩
    · omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

/-- Relocatable `[LibsignalPlacement]` `libcrux_hmac::hmac` hook discharge on Block `369`
    (`withLsCodeRoLoaded lsmpl`, budget-threaded counterpart of
    `RecvHdrChunkPart3Placed.libcrux_hmac_hdr_placed_ok_at_recvHdr`). -/
theorem libcrux_hmac_hdr_placed_ok_at_recvHdr [LibsignalPlacement]
    {P : Prop} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrLibcruxHmacSym)
      (withLsCodeRoLoaded lsmpl (libcruxHmacHdrSpec P F M A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_plain
  have hraw :
      subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
        (lsρ spqrLibcruxHmacSym)
        (libcruxHmacBudgetSpec F M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hhmac
  exact subroutine_ok_libcruxHmacHdr_of_budget hraw

theorem libcrux_hmac_hdr_lsCallInv_ok_at_recvHdr [LibsignalPlacement]
    {P : Prop} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrLibcruxHmacSym)
      (withLsCallInv lsmpl (libcruxHmacHdrSpec P F M A lim)) :=
  subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded (libcrux_hmac_hdr_placed_ok_at_recvHdr hhmac)

/-! ## 3. `RustCliAllocBudget` Spatial Wrappers -/

theorem authenticatorHeapAt_expose_macKey_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (g : AuthenticatorGhost) (auth : Authenticator) :
    authenticatorHeapAt A.repAlloc g auth ⊢
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        vecU8HeapAt A.repAlloc g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length)
             (g.macKey.cap.toNat - auth.macKey.length)) :=
  authenticatorHeapAt_expose_macKey A.repAlloc g auth

theorem authenticatorHeapAt_unexpose_macKey_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (g : AuthenticatorGhost) (auth : Authenticator)
    (hle : auth.macKey.length ≤ g.macKey.cap.toNat)
    (hlt : g.macKey.cap.toNat < 2 ^ 63)
    (hptr : g.macKey.ptr ≠ 0) :
    (g.macKey.ptr ↦ₛ auth.macKey) ∗
      vecU8HeapAt A.repAlloc g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
      (if g.macKey.cap = 0 then emp
       else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
         memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length)
           (g.macKey.cap.toNat - auth.macKey.length)) ⊢
      authenticatorHeapAt A.repAlloc g auth :=
  authenticatorHeapAt_unexpose_macKey A.repAlloc g auth hle hlt hptr

theorem vecU8_expose_nonempty_192_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A.repAlloc (sp - 192#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 192#64) ↦₆₄ cap) ∗
          ((sp - 184#64) ↦₆₄ ptr) ∗
          ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 :=
  vecU8_expose_nonempty_192 A.repAlloc sp bs hpos

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3Budget
