/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionCode

/-!
# Relocatable `[LibsignalPlacement]` Drop Glue for `[ChainEpoch]` and `Chain`

Proves relocatable `[LibsignalPlacement]` subroutine contracts for:
- Block `143`: `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]`
- Block `287`: `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]`
- Block `269`: `core::ptr::drop_glue::<spqr::chain::Chain>`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Drop.ChainEpochPlaced
open CryptoVerification.SpqrV1.Drop.Blk337_338

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Block `143`: `drop_glue::<[spqr::chain::ChainEpoch]> [local#1]` -/

private theorem drop_chain_epoch_slice_local1_placed_body [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpoch)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_143).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = cnt →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_143).rebase (blkPl_143).base H)
        ((blkPl_143).base + 28#64)
        s
        (chainEpoch A ep cur ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧
          sm.readReg64 .x20 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt ep s Frame hpc hrun hpres hx19 hx20
  rcases hpres with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainEpoch_entails_dealloc A cur ep)) ?_
  apply SepWP.exists_sepConj_left; intro g
  refine seq_clean (mid := (blkPl_143).base + 60#64) (P_mid :=
    (chainEpochHeadersAt cur g ∗
      vecCapPtrDealloc A g.send.prev.cap g.send.prev.ptr ∗
      vecCapPtrDealloc A g.recv.next.cap g.recv.next.ptr ∗
      vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
    ?_ ?_
  · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
    by_cases hcap : (g.send.next.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
    refine seq_clean (mid := (blkPl_143).base + 80#64) (P_mid :=
      (chainEpochHeadersAt cur g ∗
        vecCapPtrDealloc A g.recv.next.cap g.recv.next.ptr ∗
        vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
      ?_ ?_
    · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
      by_cases hcap : (g.send.prev.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
      refine seq_clean (mid := (blkPl_143).base + 100#64) (P_mid :=
        (chainEpochHeadersAt cur g ∗
          vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64)
        ?_ ?_
      · dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (g.recv.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
        have hstep4 : SepWP ((blkPC_143).rebase (blkPl_143).base H) ((blkPl_143).base + 28#64) s3
            ((chainEpochHeadersAt cur g ∗ vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ chainEpochHeadersAt cur g ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [chainEpochHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (g.recv.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chainEpochHeadersAt_entails_memRegion_112 cur g)), h.2⟩)

private theorem drop_chain_epoch_slice_local1_placed_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpoch) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_143).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_143).rebase (blkPl_143).base H)
        ((blkPl_143).base + 124#64)
        s
        (arrayAt (chainEpoch A) 112 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp) := by
  have hbody := drop_chain_epoch_slice_local1_placed_body hdealloc s0 fsp hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20
    rw [show arrayAt (chainEpoch A) 112 cur (ep :: tl) =
          chainEpoch A ep cur ∗ arrayAt (chainEpoch A) 112 (cur + 112#64) tl from rfl,
        sep_pull_body]
    refine seq_clean (mid := (blkPl_143).base + 28#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep s
        (arrayAt (chainEpoch A) 112 (cur + 112#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx19_4 ⊢
      wp_steps
      wp_done
    | cons ep2 tl2 =>
      have htl_ne : ep2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show (ep :: ep2 :: tl2).length = (ep2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx19_4
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 112#64) _ (memRegion cur 112 ∗ Frame)
          htl_ne htl_len rfl (by assumption)
          ⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          rfl
          (by simp only [wp_norm, arm64_norm, add_112_add_56])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul ep (ep2 :: tl2) 112
      have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
      exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#1]` (Block `143`)
meets `dropChainEpochSliceSpec A` under `[LibsignalPlacement]`. -/
theorem drop_chain_epoch_slice_local1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (blkPl_143).base (dropChainEpochSliceSpec A) := by
  simp only [dropChainEpochSliceSpec]
  have hloop := drop_chain_epoch_slice_local1_placed_loop hdealloc
  dsimp only [chainEpochSize, BitVec.ofNat_eq_ofNat] at hloop ⊢
  wp_init x s0
  rcases x with ⟨ptr, eps⟩
  have hx0 : s0.readReg64 .x0 = ptr := h_1
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 eps.length := h_2
  have hlen_lt : eps.length * 112 < 2 ^ 63 := h
  dsimp only [DropChainEpochSliceGhost.ptr, DropChainEpochSliceGhost.eps] at *
  cases eps with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj] at hx1 ⊢
    wp_steps
    wp_done
  | cons ep tl =>
    have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 32#64 (by assumption) (by decide)
    have hne0 := ofNat_beq_zero_false_112 (n := (ep :: tl).length) (by simp) hlen_lt
    nth_rw 1 [stackAt_dropStack32_split s0.sp]
    cells_unfold
    wp_pull_exists
    wp_steps
    refine seq_clean (mid := (blkPl_143).base + 124#64)
      (P_mid := memRegion ptr ((ep :: tl).length * 112) ∗ A.pool ∗
        stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64))
      ?_ ?_
    · have hpre_eq :
          (arrayAt (chainEpoch A) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (chainEpoch A) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
        ac_rfl
      rw [hpre_eq]
      exact hloop s0 (s0.sp - 32#64) hfsp_align (ep :: tl) ptr _ _
        (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl
    · intro sm hpcm hrunm ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
      wp_done

theorem drop_chain_epoch_slice_local1_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (blkPl_143).base (dropChainEpochSliceSpec A) :=
  drop_chain_epoch_slice_local1_placed_ok hdealloc

theorem drop_chain_epoch_slice_local0_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_143).rebase (blkPl_143).base H)
      (blkPl_143).base (dropChainEpochSliceSpec A) :=
  drop_chain_epoch_slice_local1_placed_ok hdealloc

/-! ## Block `287`: `drop_glue::<[spqr::chain::ChainEpoch]> [local#2]` -/

theorem drop_chain_epoch_slice_local2_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (blkPl_287).base (dropChainEpochSliceSpec A) :=
  Drop.drop_chain_epoch_slice_local2_placed_ok hdealloc

theorem drop_raw_vec_chain_epoch_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_287).rebase (blkPl_287).base H)
      (blkPl_287).base (dropChainEpochSliceSpec A) :=
  Drop.drop_chain_epoch_slice_local2_placed_ok hdealloc

/-! ## Block `269`: `drop_glue::<spqr::chain::Chain>` (48 instructions) -/

/-- Relocatable `core::ptr::drop_glue::<spqr::chain::Chain>` (Block `269`)
meets `dropSpqrChainSpec A` under `[LibsignalPlacement]`. -/
theorem drop_spqr_chain_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hslice_raw : subroutine_ok ((blkPC_269).rebase (blkPl_269).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hdealloc_raw : subroutine_ok ((blkPC_269).rebase (blkPl_269).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_269).rebase (blkPl_269).base H)
      (blkPl_269).base
      (dropSpqrChainSpec A) := by
  simp only [dropSpqrChainSpec]
  dsimp only [chainSize, dropSpqrChainStack, BitVec.ofNat_eq_ofNat] at hslice_raw hdealloc_raw ⊢
  wp_init x s0
  rcases x with ⟨a, G, c⟩
  dsimp only [DropSpqrChainGhost.a, DropSpqrChainGhost.G, DropSpqrChainGhost.c] at *
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_dealloc A a G c)) ?_
  unfold vecDequeAt vecDequeRingBuf vecDequeHeader
  nth_rw 1 [stackAt_dropStack80_split s0.sp]
  cells_unfold
  wp_pull_exists
  wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne, hhead⟩
  dsimp only [chainEpochSize, chainEpochAlign] at hcap_lt ⊢
  refine seq_clean (mid := (blkPl_269).base + 120#64)
    (P_mid :=
      vecDequeHeader a G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      (if G.linksCap = 0 then emp
       else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
         memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
      ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      memRegion (a + 48#64) 40 ∗
      vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropStack32 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x21 = G.linksPtr ∧ sm.readReg64 .x22 = G.linksCap)
    ?_ ?_
  · generalize hxs : G.epochs.zip c.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      have h0 : arrayAt (chainEpoch A) 112 G.linksPtr [] = emp := rfl
      have hnil_ent :
          (if G.linksCap = 0 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr [] 0 G.linksCap.toNat) ⊢
          (if G.linksCap = 0 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             memRegion G.linksPtr (G.linksCap.toNat * 112)) := by
        by_cases hc : G.linksCap = 0
        · simp [hc]; exact Entails.refl _
        · simp only [hc, ↓reduceIte]
          exact sepConj_mono_right (vecDequeSlotsAt_nil_entails_memRegion
            (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr hcap_lt)
      refine SepWP.focus_weaken hnil_ent (by sep_focus) ?_
      simp only [List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat]
      wp_steps
      rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
      wp_call hslice_raw ⟨G.linksPtr, []⟩
      wp_steps
      rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
      wp_call hslice_raw ⟨G.linksPtr, []⟩
      refine align_pre (by
        unfold vecDequeHeader
        simp only [List.length_nil, BitVec.ofNat_eq_ofNat, memRegion_zero, emp_sepConj, sepConj_emp,
          Nat.mul_comm, h0, *]
        ac_rfl) ?_
      wp_done
    | cons x tl =>
      have hlen_pos : 0 < (x :: tl).length := by simp
      have hlen_lt : (x :: tl).length * 112 < 2 ^ 63 := by
        have : (x :: tl).length * 112 ≤ G.linksCap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hcap_lt_pow : G.linksCap.toNat < 2 ^ 63 := by omega
      have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
      have hcap_ne : G.linksCap ≠ 0 := by
        intro hc0; rw [hc0] at hlen_le; simp at hlen_le
      simp only [hcap_ne, ↓reduceIte] at hhead ⊢
      have hult : G.linksHead.ult G.linksCap = true := ult_of_toNat_lt hhead
      have haddr1 : G.linksPtr + BitVec.ofNat 64 (G.linksHead.toNat * 112) =
          G.linksPtr + G.linksHead * 112#64 := by
        rw [← mul_112_add_ptr, BitVec.add_comm]
      by_cases hwrap : (x :: tl).length ≤ G.linksCap.toNat - G.linksHead.toNat
      · have hule := ule_sub_of_le hcap_lt_pow hhead hwrap
        obtain ⟨ys, hys_len, hys_ent⟩ := vecDequeSlotsAt_nonwrap_entails
          (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hwrap
        let eps := ys.map Prod.snd
        have heps_len : eps.length = (x :: tl).length := by simp [eps, hys_len]
        have heps_lt : eps.length * 112 < 2 ^ 63 := by rw [heps_len]; exact hlen_lt
        have hx1_eq : G.linksHead + BitVec.ofNat 64 (x :: tl).length - G.linksHead =
            BitVec.ofNat 64 eps.length := by
          rw [add_sub_cancel_left_bv, heps_len]
        have h0 : arrayAt (chainEpoch A) 112 G.linksPtr [] = emp := rfl
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A) 112 (G.linksPtr + G.linksHead * 112#64) eps ∗
            memRegion G.linksPtr (G.linksHead.toNat * 112) ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 ((G.linksHead.toNat + (x :: tl).length) * 112))
              ((G.linksCap.toNat - G.linksHead.toNat - (x :: tl).length) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A _ ys))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        wp_steps
        wp_call hslice_raw ⟨G.linksPtr + G.linksHead * 112#64, eps⟩
        wp_steps
        rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
        wp_call hslice_raw ⟨G.linksPtr, []⟩
        rw [← haddr1, heps_len]
        refine SepWP.focus_weaken
          (vecDequeSlotsAt_nonwrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
            G.linksPtr hcap_lt hhead hwrap) (by sep_focus) ?_
        refine align_pre (by
          unfold vecDequeHeader
          simp only [chainEpochSize, chainEpochAlign, Nat.mul_comm, memRegion_zero, emp_sepConj, sepConj_emp, *]
          ac_rfl) ?_
        wp_done
      · have hgt : G.linksCap.toNat - G.linksHead.toNat < (x :: tl).length := by omega
        have hnule := not_ule_sub_of_gt hcap_lt_pow hhead hlen_le hgt
        obtain ⟨ys₁, ys₂, hys₁_len, hys₂_len, hys_ent⟩ := vecDequeSlotsAt_wrap_entails
          (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hlen_le hgt
        let eps₁ := ys₁.map Prod.snd
        let eps₂ := ys₂.map Prod.snd
        have heps₁_len : eps₁.length = G.linksCap.toNat - G.linksHead.toNat := by simp [eps₁, hys₁_len]
        have heps₂_len : eps₂.length = (x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat) := by
          simp [eps₂, hys₂_len]
        have heps₁_lt : eps₁.length * 112 < 2 ^ 63 := by
          rw [heps₁_len]
          have : (G.linksCap.toNat - G.linksHead.toNat) * 112 ≤ G.linksCap.toNat * 112 :=
            Nat.mul_le_mul_right 112 (by omega)
          omega
        have heps₂_lt : eps₂.length * 112 < 2 ^ 63 := by
          rw [heps₂_len]
          have : ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112 ≤ (x :: tl).length * 112 :=
            Nat.mul_le_mul_right 112 (by omega)
          omega
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A) 112 (G.linksPtr + G.linksHead * 112#64) eps₁ ∗
            arrayAt (chainEpoch A) 112 G.linksPtr eps₂ ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 (((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112))
              ((G.linksHead.toNat - ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat))) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent
            (sepConj_mono (arrayAt_chainEpochAt_entails_chainEpoch A _ ys₁)
              (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A _ ys₂)))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        wp_steps
        have hx1_1 : G.linksCap - G.linksHead = BitVec.ofNat 64 eps₁.length := by
          rw [heps₁_len, sub_eq_ofNat_sub (by omega)]
        wp_call hslice_raw ⟨G.linksPtr + G.linksHead * 112#64, eps₁⟩
        wp_steps
        have hx1_2 : BitVec.ofNat 64 (x :: tl).length - (G.linksCap - G.linksHead) =
            BitVec.ofNat 64 eps₂.length := by
          rw [heps₂_len, ofNat_sub_sub_eq hcap_lt_pow hhead (by omega) hlen_le]
        wp_call hslice_raw ⟨G.linksPtr, eps₂⟩
        rw [← haddr1, heps₁_len, heps₂_len]
        refine SepWP.focus_weaken
          (vecDequeSlotsAt_wrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
            G.linksPtr hcap_lt hhead hlen_le hgt) (by sep_focus) ?_
        refine align_pre (by
          unfold vecDequeHeader
          simp only [chainEpochSize, chainEpochAlign, Nat.mul_comm, *]
          ac_rfl) ?_
        wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx21_1, hx22_1⟩
    have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 48#64 (by assumption) (by decide)
    refine seq_clean (mid := (blkPl_269).base + 144#64)
      (P_mid :=
        vecDequeHeader a G.linksCap G.linksPtr G.linksHead
          (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (a + 48#64) 40 ∗
        vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
        A.pool ∗
        stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc : G.linksCap = 0
      · have hc_beq : (G.linksCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22_1 ⊢
        wp_steps
        wp_done
      · have hc_beq : ¬((G.linksCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        have hsp_sub : s0.sp - 4176#64 = (s0.sp - 48#64) - 4128#64 := by bv_omega
        simp only [hc, ↓reduceIte]
        conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
        wp_steps
        wp_call hdealloc_raw (G.linksPtr, G.linksCap.toNat * 112, 8)
        refine align_pre (by
          rw [hsp_1, hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
          ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (G.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken
          (chainHeaders_entails_memRegion_88 a G.linksCap G.linksPtr G.linksHead
            (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr)
          (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · wp_steps
        refine SepWP.focus_weaken
          (chainHeaders_entails_memRegion_88 a G.linksCap G.linksPtr G.linksHead
            (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr)
          (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        rw [stackAt_dropStack80_split_bottom s0.sp]
        wp_call hdealloc_raw (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1)
        rw [← stackAt_dropStack80_split_bottom s0.sp]
        wp_done

theorem drop_spqr_chain_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hslice_raw : subroutine_ok ((blkPC_269).rebase (blkPl_269).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hdealloc_raw : subroutine_ok ((blkPC_269).rebase (blkPl_269).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_269).rebase (blkPl_269).base H)
      (blkPl_269).base
      (dropSpqrChainSpec A) :=
  drop_spqr_chain_placed_ok hslice_raw hdealloc_raw

end CryptoVerification.SpqrV1.Drop
