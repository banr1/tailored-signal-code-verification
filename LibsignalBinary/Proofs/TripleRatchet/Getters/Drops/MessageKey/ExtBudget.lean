/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Contract for `drop_glue<Vec<MessageKey>>`

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract
`dropVecMessageKeySpec` for `core::ptr::drop_glue::<alloc::vec::Vec<...::MessageKey>>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.LibsignalSessionRepr (MessageKeyGhost messageKeyAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkPC_3 blkPl_3 lsRustDeallocSym ls_hook_ok_rustDealloc
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  Saved48Preserved stackAt_dropVecMessageKey_split
  vecPinDealloc mkHeadersAt mkHeadersAt_entails_memRegion_104 messageKeyAt_entails_dealloc
  vecAt_expose_loop post_loop_weaken tail_dealloc_pre_weaken
  cap0_weaken_48_allocHook tail_dealloc_post_48_allocHook
  ofNat_succ_eq_add_one ofNat_beq_zero_false ofNat_add_one_beq_one_false
  tail_len_mul_lt cons_len_mul add_104_add_48
  sep_pull_body sep_push_body sep_rejoin_loop
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropVecMessageKeySpec)

attribute [local irreducible] Program.fetch Program.externAt?

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs (rustDeallocEvents sz al) st]
  exact Entails.sepExists_right (evs ++ rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.append hevs (FreeOnlyEvs.singleton al sz)) (Entails.refl _))

private theorem SepWP.seq_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 (fun sm _Pm hpcm hrunm ⟨hent, hq⟩ =>
    SepWP.weaken_pre hent (h2 sm hpcm hrunm hq))

private theorem SepWP.unpack_freeOnlyPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = freeOnlyPool A lim st s ∗ Frame := by sep_focus)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hf]; unfold freeOnlyPool
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem SepWP.fold_keep {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs st) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_keep A lim st hevs hvm) hf hk

private theorem SepWP.fold_dealloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs) (sz al : Nat)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_dealloc A lim st hevs sz al hvm) hf hk

private theorem SepWP.sync_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (A.pool lim st sm ∗ Frame) post) :
    SepWP prog target sm P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]
  exact hk

private theorem SepWP.mono_ac {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h1 : SepWP prog target s P' post)
    (h2 : ∀ sf Pf, sf.pc = target → sf.status = .Running → post sf Pf → post' sf Pf)
    (heq : P = P') :
    SepWP prog target s P post' :=
  SepWP.weaken_pre (Entails.of_eq heq) (SepWP.mono h1 h2)

private theorem drop_vec_message_key_placed_body [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_3).base + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_3).rebase (blkPl_3).base H)
        ((blkPl_3).base + 36#64)
        s
        (messageKeyAt A.repAlloc (pin, mk) cur ∗ freeOnlyPool A lim st s ∗
          stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 48#64) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  intro cur cnt pin mk s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_dealloc A.repAlloc cur pin mk)) ?_
  refine SepWP.seq_state (mid := (blkPl_3).base + 68#64) (P_mid := fun sm =>
    (mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.mac ∗
      vecPinDealloc A.repAlloc pin.iv ∗ vecPinDealloc A.repAlloc pin.seed) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
    ?_ ?_
  · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    dsimp only [mkHeadersAt, vecPinDealloc]
    by_cases hcap : (pin.cipher.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    · wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdealloc (pin.cipher.ptr, pin.cipher.cap.toNat, 1, M.stepEvents evs st)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs pin.cipher.cap.toNat 1 (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp]; try sep_ac_rfl)) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine SepWP.seq_state (mid := (blkPl_3).base + 88#64) (P_mid := fun sm =>
      (mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.iv ∗ vecPinDealloc A.repAlloc pin.seed) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      dsimp only [mkHeadersAt, vecPinDealloc]
      by_cases hcap : (pin.mac.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      · wp_steps
        refine SepWP.sync_pool (hk := ?_)
        rw [← hsp_1]
        wp_call hdealloc (pin.mac.ptr, pin.mac.cap.toNat, 1, M.stepEvents evs st)
        have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
        refine SepWP.fold_dealloc hevs pin.mac.cap.toNat 1 (hk := ?_)
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_1]; try sep_ac_rfl)) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine SepWP.seq_state (mid := (blkPl_3).base + 108#64) (P_mid := fun sm =>
        (mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.seed) ∗
        freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
        ?_ ?_
      · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [mkHeadersAt, vecPinDealloc]
        by_cases hcap : (pin.iv.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps
          refine SepWP.fold_keep hevs (hk := ?_)
          wp_done
        · wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_2]
          wp_call hdealloc (pin.iv.ptr, pin.iv.cap.toNat, 1, M.stepEvents evs st)
          have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
          refine SepWP.fold_dealloc hevs pin.iv.cap.toNat 1 (hk := ?_)
          refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_2]; try sep_ac_rfl)) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((blkPC_3).rebase (blkPl_3).base H) ((blkPl_3).base + 36#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.seed) ∗
              freeOnlyPool A lim st s3 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ freeOnlyPool A lim st sm ∗
                stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          dsimp only [mkHeadersAt, vecPinDealloc]
          by_cases hcap : (pin.seed.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
          · wp_steps
            refine SepWP.fold_keep hevs (hk := ?_)
            wp_done
          · wp_steps
            refine SepWP.sync_pool (hk := ?_)
            rw [← hsp_3]
            wp_call hdealloc (pin.seed.ptr, pin.seed.cap.toNat, 1, M.stepEvents evs st)
            have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_3
            wp_steps
            refine SepWP.fold_dealloc hevs pin.seed.cap.toNat 1 (hk := ?_)
            refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_3]; try sep_ac_rfl)) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_vec_message_key_placed_loop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_3).base + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_3).rebase (blkPl_3).base H)
        ((blkPl_3).base + 132#64)
        s
        (arrayAt (messageKeyAt A.repAlloc) 104 cur rest ∗ freeOnlyPool A lim st s ∗
          stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_message_key_placed_body (st := st) hdealloc s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A.repAlloc) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A.repAlloc (pin, mk) cur ∗ arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine SepWP.seq_state (mid := (blkPl_3).base + 36#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) ?_
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      apply SepWP.mono_ac
      · exact ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption)
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4 rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])
      · intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
        have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
        exact Entails.refl _
      · sep_ac_rfl

theorem drop_vec_message_key_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (blkPl_3).base
      (dropVecMessageKeySpec M A lim) := by
  simp only [dropVecMessageKeySpec]
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, mks⟩, st⟩
  have hloop := drop_vec_message_key_placed_loop (st := st) hdealloc_raw
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecMessageKey_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A.repAlloc 104 8 (messageKeyAt A.repAlloc)
      (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWP.seq_state (mid := (blkPl_3).base + 132#64)
    (P_mid := fun sm =>
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      memRegion ptr (mks.length * 104) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)) ∗
      freeOnlyPool A lim st sm ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases mks with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps_sync_pool ((blkPl_3).base + 132#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      wp_steps_sync_pool ((blkPl_3).base + 48#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
      apply SepWP.mono_ac
      · exact hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align (hd :: tl) ptr _
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          (List.cons_ne_nil _ _) hlen_lt
          rfl (by assumption)
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl rfl rfl rfl
      · intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        exact Entails.of_eq (by sep_ac_rfl)
      · sep_ac_rfl
  · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre (post_loop_weaken A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks.length hlen_le hcap_lt _) ?_
    refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (cap0_weaken_48_allocHook (s0.readReg64 (Reg.gpr 0#5)) 0#64 ptr _ s0.sp _ _ _ _ _ _)) ?_
      unfold freeOnlyPool
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.sync_pool (hk := ?_)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104))
          (A.pool lim (M.stepEvents evs st) _) s0.sp _ _ _ _ _ _)) ?_
      wp_call hdealloc (ptr, cap.toNat * 104, 8, M.stepEvents evs st)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs (cap.toNat * 104) 8 (hk := ?_)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (tail_dealloc_post_48_allocHook (s0.readReg64 (Reg.gpr 0#5)) (freeOnlyPool A lim st sf) s0.sp)) ?_
      unfold freeOnlyPool
      wp_done

theorem drop_vec_message_key_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (blkPl_3).base
      (dropVecMessageKeySpec M A lim) :=
  drop_vec_message_key_placed_ok_of_dealloc (ls_hook_ok_rustDealloc h_dealloc)

end LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget
