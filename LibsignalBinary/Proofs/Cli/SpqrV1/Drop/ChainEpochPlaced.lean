/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[ChainEpoch]` Drop Glue (Block `446`)

Proves `drop_chain_epoch_slice_local1_placed_ok` (plus `HookSat` and `withPanics` wrappers) for
`core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]` on Block `446` (`lsProg_446 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.SpqrV1.Drop.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem drop_chain_epoch_slice_local1_cli_placed_body [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpoch)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_446).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = cnt →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_446).rebase (blkPl_446).base H)
        ((blkPl_446).base + 28#64)
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
  refine seq_clean (mid := (blkPl_446).base + 60#64) (P_mid :=
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
    refine seq_clean (mid := (blkPl_446).base + 80#64) (P_mid :=
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
      refine seq_clean (mid := (blkPl_446).base + 100#64) (P_mid :=
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
        have hstep4 : SepWP ((blkPC_446).rebase (blkPl_446).base H) ((blkPl_446).base + 28#64) s3
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

private theorem drop_chain_epoch_slice_local1_cli_placed_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpoch) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_446).base + 40#64 →
      s.status = .Running →
      Saved32x20Preserved s0 s fsp →
      s.readReg64 .x19 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_446).rebase (blkPl_446).base H)
        ((blkPl_446).base + 124#64)
        s
        (arrayAt (chainEpoch A) 112 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp) := by
  have hbody := drop_chain_epoch_slice_local1_cli_placed_body hdealloc s0 fsp hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20
    rw [show arrayAt (chainEpoch A) 112 cur (ep :: tl) =
          chainEpoch A ep cur ∗ arrayAt (chainEpoch A) 112 (cur + 112#64) tl from rfl,
        sep_pull_body]
    refine seq_clean (mid := (blkPl_446).base + 28#64)
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

/-- Relocatable `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]` (Block `446`)
meets `dropChainEpochSliceSpec A` under `[LibsignalPlacement]`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed_ok
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_446).rebase (blkPl_446).base H)
      (blkPl_446).base (dropChainEpochSliceSpec A) := by
  simp only [dropChainEpochSliceSpec]
  have hloop := drop_chain_epoch_slice_local1_cli_placed_loop hdealloc
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
    refine seq_clean (mid := (blkPl_446).base + 124#64)
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

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_446 H) (blkPl_446).base (dropChainEpochSliceSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

private theorem hookSat_dealloc_withPanics {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed_x
    [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_446 (Rust.withPanics ext)) (blkPl_446).base (dropChainEpochSliceSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed
    (hookSat_dealloc_withPanics hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed_lscl
    [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed hdealloc)) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed_cl
    [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 446) (withLsCl lsmpl (dropChainEpochSliceSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_placed hdealloc) hi

end CryptoVerification.SpqrV1.Drop
