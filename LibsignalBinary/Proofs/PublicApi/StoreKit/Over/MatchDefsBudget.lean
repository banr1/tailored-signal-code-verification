/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `VmPreserved`-Augmented `promote_matching_session` Miss Contracts

Wraps the raw and record-level relocatable `[LibsignalPlacement]` miss contracts of
`StoreKit.Over.MatchDefs` with `VmPreserved s0 sf` (`0` allocations).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (VmPreserved)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (sessionRecordAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (PromoteVerMissRawGhost PromoteLenMissRawGhost PromoteKeyMissRawGhost PromoteMissGhost
   promoteMatchingSessionMatchStackExt p2PromoteMissStackExt
   aliceBufOverAt sessionRecordMissRestAt
   sessionRecordAt_expose_miss sessionRecordAt_miss_facts aliceBufOverAt_expose_33
   promoteMissStackCellsExt_eq stackAt_promoteMatchStackExt_eq stackAt_p2PromoteMissStackExt_eq
   outRegion16_split_over ofNat_len_ne_33)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

private theorem subroutine_ok_vmPreserved_refine_frame {α β : Type}
    {prog : Program} {entry : BitVec 64}
    {inner : Spec α} {outer : Spec β}
    (h : subroutine_ok prog entry (withVmPreserved inner))
    (href : ∀ (x : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ outer.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp),
        (s0.mem ⊨ inner.pre y s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ inner.post y s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ outer.post x s0 sf ∗ R)))
    (hpanic : ∀ y R (s0 sf : State), ¬ (sf.mem ⊨ inner.onPanic y s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ y code R (s0 sf : State), ¬ (sf.mem ⊨ inner.onExit y code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y F R (s0 sf : State),
      (sf.mem ⊨ inner.onOom y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ outer.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; exact False.elim (not_satisfies_false_sepConj ho)) :
    subroutine_ok prog entry (withVmPreserved outer) := by
  refine subroutine_ok_refine_frame h (fun x R s0 hpre => ?_) hpanic hexit hoom
  obtain ⟨y, F, hy_pre, hy_post⟩ := href x R s0 hpre
  refine ⟨y, F, hy_pre, fun sf hpost => ?_⟩
  dsimp only [withVmPreserved] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hy_post sf hpost.2⟩

/-! ## 1. `VmPreserved`-Augmented Raw & Record-Level Specifications -/

def promoteMatchingSessionVerMissRawSpec : Spec PromoteVerMissRawGhost :=
  withVmPreserved
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpec

def promoteMatchingSessionLenMissRawSpec : Spec PromoteLenMissRawGhost :=
  withVmPreserved
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpec

def promoteMatchingSessionKeyMissRawSpec : Spec PromoteKeyMissRawGhost :=
  withVmPreserved
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpec

def promoteMatchingSessionMissSpec (A : RustAlloc) : Spec PromoteMissGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissSpec A)

def promoteMatchingSessionRecordOverSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A)

def promoteMatchingSessionVerMissRawSpecExt : Spec PromoteVerMissRawGhost :=
  withVmPreserved
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpecExt

def promoteMatchingSessionLenMissRawSpecExt : Spec PromoteLenMissRawGhost :=
  withVmPreserved
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpecExt

def promoteMatchingSessionKeyMissRawSpecExt : Spec PromoteKeyMissRawGhost :=
  withVmPreserved
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpecExt

def promoteMatchingSessionMissSpecExt (A : RustAlloc) : Spec PromoteMissGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissSpecExt A)

def promoteMatchingSessionRecordOverSpecExt (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpecExt A)

def promoteMatchingSessionRecordOverMatchStackSpecExt (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A)

def promoteMatchingSessionMissMatchStackSpecExt (A : RustAlloc) : Spec PromoteMissGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissMatchStackSpecExt A)

/-! ## 2. Frame-Refinement Bridges -/

theorem promoteMatchingSessionVerMissRawExt_of_raw {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry promoteMatchingSessionVerMissRawSpec) :
    subroutine_ok prog entry promoteMatchingSessionVerMissRawSpecExt := by
  refine subroutine_ok_vmPreserved_refine_frame h ?_
  intro x _ s0 hpre
  refine ⟨x, memRegion (s0.sp - 17568#64) 16320, ?_, ?_⟩
  · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpec] at hpre ⊢
    rw [promoteMissStackCellsExt_eq s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro sf hpost
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpec] at hpost ⊢
    rw [promoteMissStackCellsExt_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

set_option maxHeartbeats 400000 in
theorem promoteMatchingSessionRecordOverMatchStackExt_of_raw
    {prog : Program} {entry : BitVec 64} (A : RustAlloc)
    (hver : subroutine_ok prog entry promoteMatchingSessionVerMissRawSpecExt)
    (hlen : subroutine_ok prog entry promoteMatchingSessionLenMissRawSpecExt)
    (hkey : subroutine_ok prog entry promoteMatchingSessionKeyMissRawSpecExt) :
    subroutine_ok prog entry (promoteMatchingSessionRecordOverMatchStackSpecExt A) := by
  refine subroutine_ok_by_cases
    (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
        x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32) ?_ ?_
  · refine subroutine_ok_by_cases
      (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
        BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
          x.2.2.2.2.1.aliceBaseKey.length = 33) ?_ ?_
    · change subroutine_ok prog entry
        (withVmPreserved
          { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A with
            pre := fun x s =>
              ⌜x.2.2.2.2.1.aliceBaseKey.length = 33⌝ ∗
              (⌜x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A).pre x s) })
      refine subroutine_ok_vmPreserved_refine_frame hkey ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hlen33, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hver_eq, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, hmem⟩
      have hne_key : key ≠ sess.aliceBaseKey := fun hk => hmiss ⟨hver_eq, hk.symm⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
           stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      obtain ⟨hcap_ne, halice, hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      have hal33 : G.alice.bytes.length = 33 := by rw [halice]; exact hlen33
      have hcapnz : G.alice.cap ≠ 0 := by
        intro h0
        have h1 : G.alice.cap.toNat = 0 := by simp [h0]
        rw [h1, hal33] at hle; omega
      have habk : BitVec.ofNat 64 G.alice.bytes.length = 33#64 := by rw [hal33]
      rw [habk, aliceBufOverAt_expose_33 A G sess.aliceBaseKey halice hlen33 hcapnz] at hexp
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, sess.state.sessionVersion,
          msgVer, serPtr, outPtr, key, sess.aliceBaseKey⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗
          (A.live G.alice.ptr G.alice.cap.toNat 1 ∗
            memRegion (G.alice.ptr + 33#64) (G.alice.cap.toNat - 33)) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpecExt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_eq, hklen, hlen33, hne_key⟩, ?_⟩
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpecExt,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    · change subroutine_ok prog entry
        (withVmPreserved
          { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A with
            pre := fun x s =>
              ⌜¬ x.2.2.2.2.1.aliceBaseKey.length = 33⌝ ∗
              (⌜x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A).pre x s) })
      refine subroutine_ok_vmPreserved_refine_frame hlen ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hlen_ne, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hver_eq, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
           stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      obtain ⟨hcap_ne, halice, hle, hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      have habk_ne : BitVec.ofNat 64 G.alice.bytes.length ≠ 33#64 :=
        ofNat_len_ne_33 (Nat.lt_of_le_of_lt hle hlt) (by rw [halice]; exact hlen_ne)
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
          BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
          msgVer, serPtr, outPtr⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
          (serPtr ↦ₛ key) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpecExt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_eq, habk_ne⟩, ?_⟩
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpecExt,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · change subroutine_ok prog entry
      (withVmPreserved
        { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A with
          pre := fun x s =>
            ⌜¬ x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
              (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt A).pre x s })
    refine subroutine_ok_vmPreserved_refine_frame hver ?_
    intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hver_ne, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
    have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
        ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
         (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
         stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨hcap_ne, _halice, _hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
    have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
    refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
        BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
        msgVer, serPtr, outPtr⟩,
      sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
        (serPtr ↦ₛ key) ∗
        (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
    · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpecExt]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_ne⟩, ?_⟩
      rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp] at hrec_mem
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_mem
    · intro sf hpost
      dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpecExt,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
      rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem promoteMatchingSessionRecordOverExt_of_matchStack
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (promoteMatchingSessionRecordOverMatchStackSpecExt A)) :
    subroutine_ok prog entry (promoteMatchingSessionRecordOverSpecExt A) := by
  refine subroutine_ok_vmPreserved_refine_frame h ?_
  intro x _ s0 hpre
  refine ⟨x, memRegion (s0.sp - 17632#64) 64, ?_, ?_⟩
  · obtain ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ := x
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro sf hpost
    obtain ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ := x
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

set_option maxHeartbeats 400000 in
theorem promoteMatchingSessionMissMatchStackExt_of_recordOver
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (promoteMatchingSessionRecordOverMatchStackSpecExt A)) :
    subroutine_ok prog entry (promoteMatchingSessionMissMatchStackSpecExt A) := by
  refine subroutine_ok_vmPreserved_refine_frame h ?_
  intro x R s0 hpre
  dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissMatchStackSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hmiss, hklen⟩, hmem⟩
  have hrec_sat : s0.mem ⊨ sessionRecordAt A x.recPtr x.g x.r ∗
      ((x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
       stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hg_some : ∃ G : SessionGhost, x.g.cur = some G := by
    have hrec_l := Satisfies.of_sep_left hrec_sat
    unfold sessionRecordAt at hrec_l
    rw [hcur] at hrec_l
    cases hgc : x.g.cur with
    | none =>
      rw [hgc] at hrec_l
      have hf := Satisfies.of_sep_right hrec_l
      rw [satisfies_pure] at hf
      exact False.elim hf
    | some G => exact ⟨G, rfl⟩
  obtain ⟨G, hgc⟩ := hg_some
  have hrec_eq : sessionRecordAt A x.recPtr x.g x.r =
      sessionRecordAt A x.recPtr ⟨x.g.prevCap, x.g.prevPtr, some G⟩ ⟨some x.s⟩ := by
    unfold sessionRecordAt
    rw [hgc, hcur]
  refine ⟨(x.recPtr, x.g.prevCap, x.g.prevPtr, G, x.s, x.msgVer, x.serPtr, x.outPtr, x.serBytes),
    memRegion (x.outPtr + 9#64) 7, ?_, ?_⟩
  · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, ?_⟩
    rw [hrec_eq, outRegion16_split_over x.outPtr] at hrec_sat
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_sat
  · intro sf hpost
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverMatchStackSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissMatchStackSpecExt] at hpost ⊢
    rw [hrec_eq]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem promoteMatchingSessionMissExt_of_matchStack
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (promoteMatchingSessionMissMatchStackSpecExt A)) :
    subroutine_ok prog entry (promoteMatchingSessionMissSpecExt A) := by
  refine subroutine_ok_vmPreserved_refine_frame h ?_
  intro x _ s0 hpre
  refine ⟨x, memRegion (s0.sp - 17632#64) 64, ?_, ?_⟩
  · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissMatchStackSpecExt] at hpre ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro sf hpost
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissMatchStackSpecExt] at hpost ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefsBudget
