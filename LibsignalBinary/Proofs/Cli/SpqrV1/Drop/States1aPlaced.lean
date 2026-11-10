/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.TopDecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyDecoderPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyEncoderPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlaced
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Chunked `States` Drop Glue (Block `443`, Part 1/2)

Defines `dropChunkedStatesLocal1Placed*Spec` and proves the first six variant contracts
(`keysUnsampled`, `noHeaderReceived`, `headerReceived`, `ekSentCt1Received`, `ct1Acknowledged`,
`ct1Sampled`) and their `HookSat` / `withPanics` wrappers on Block `443` (`lsProg_443 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Drop

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.SpqrV1.Drop.TopPlaced

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec
    [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedStatesGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedStatesAt A x.a x.st ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec
    [LibsignalPlacement] (A : RustAlloc) {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a⌝ ∗
      chunkedStatesAt A a st ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion a chunkedStatesSize ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl {pl : MultiPlacement}
    {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl <| sepWP_mono_lscl hcl h1 fun sm _Pm hpc hrun hcl_m ⟨hent, hQ⟩ _ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hcl_m hQ)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed_raw
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_443).rebase (blkPl_443).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_443).rebase (blkPl_443).base H) (blkPl_443).base
      (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysUnsampled st)) := by
  simp only [CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedStatesAt, chunkedKeysUnsampledAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize] at hdealloc_raw ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [unchunkedKeysUnsampledAt_eq_ct2SentAt]
  refine SepWP.focus_weaken (unchunkedCt2Sent8_entails_dealloc A a { epoch := st.uc.epoch, auth := st.uc.auth })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [twoVec8HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean (mid := (blkPl_443).base + 284#64)
    (P_mid := ((a ↦₆₄ 2#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      memRegion (a + 64#64) 864) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have hjoin928 : (a ↦₆₄ 2#64) ∗ twoVec8HeadersAt a g ∗ memRegion (a + 64#64) 864 ⊢ memRegion a 928 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (twoVec8HeadersAt_entails_memRegion_56 a g))) ?_
      exact tag_and_two_regions_entails_928 a 2#64 56 864 64#64 (BitVec.add_assoc a 8#64 56#64).symm rfl
    dsimp only [twoVec8HeadersAt, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded] at hjoin928 ⊢
    by_cases hc2 : (g.v2.cap == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      wp_done
    · wp_steps
      refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      have hsplit_top : stackAt s0.sp dropStackPoly64 =
          memRegion (s0.sp - 4160#64) 64 ∗ stackAt s0.sp allocHookStack :=
        stackAt_split_bottom s0.sp allocHookStack 64 (by decide)
      refine SepWP.focus_weaken (Entails.of_eq hsplit_top) (by sep_focus) ?_
      wp_apply
      refine SepWP.focus_weaken (Entails.of_eq hsplit_top.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysUnsampled st))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed_raw hdealloc st)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysUnsampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysUnsampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_noHeaderReceived_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.noHeaderReceived st))) := by
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedNoHeaderReceivedAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw hdec_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [unchunkedNoHeaderReceivedAt_eq_ct2SentAt]
  refine SepWP.focus_weaken (unchunkedCt2Sent8_entails_dealloc A a { epoch := st.uc.epoch, auth := st.uc.auth })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder64_entails_vecs_tail A a st.receiving_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  dsimp only [twoVec8HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 448#64)
    (P_mid := ((a ↦₆₄ 7#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
      memRegion (a + 464#64) 464) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 468#64)
      (P_mid := ((a ↦₆₄ 7#64) ∗ memRegion (a + 8#64) 56 ∗
        vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
        memRegion (a + 464#64) 464) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · have hhdr56 := twoVec8HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec8HeadersAt] at hhdr56
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 _hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps_lscl (lsmpl.base 440)
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hdec_cl ⟨a + 64#64, vecs⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken (polyDecoder64_post_join a) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) polyDecoderSize ⊢
          memRegion (a + 8#64) 456 := by
        have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
        rw [← h64, show (456 : Nat) = 56 + polyDecoderSize from rfl,
            ProofLib.memRegion_split (a + 8#64) 56 polyDecoderSize (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      have hjoin928 := tag_and_two_regions_entails_928 a 7#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Sampled_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hct1 : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_444 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_444).base (dropUnchunkedCt1SentSpec A F))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Sampled st))) := by
  have hct1_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 444)
      (withLsCl lsmpl (dropUnchunkedCt1SentSpec A F)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hct1
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  dsimp only [withLsCl, dropUnchunkedCt1SentSpec, dropGluePolyEncoderSpec, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedCt1SampledAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, unchunkedCt1SentSize, polyEncoderSize,
    polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hct1_cl henc_cl hdec_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyEncoderAt_expose_tag A a st.sending_ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i w; wp_focus_pure; intro hw
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 396#64)
    (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
      unchunkedCt1SentAt A (a + 400#64) st.uc ∗
      polyDecoderAt A (a + 528#64) st.receiving_ek) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · rcases hw with rfl | rfl
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 0#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 1#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 _hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
    refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 528#64) st.receiving_ek) (by sep_focus) ?_
    wp_pull_exists; rename_i dec_vecs; wp_focus_pure; intro hdec_len
    wp_steps_lscl (lsmpl.base 444)
    wp_call hct1_cl ⟨a + 400#64, st.uc⟩
    wp_steps_lscl (lsmpl.base 441)
    wp_call henc_cl ⟨a, st.sending_ct1⟩
    wp_steps_lscl (lsmpl.base 440)
    have hsp_eq : stackAt sf.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by
      rw [hsp_sf, hsp_1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hdec_cl ⟨a + 528#64, dec_vecs⟩
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
    refine SepWP.focus_weaken (polyDecoder_post_join (a + 528#64)) (by sep_focus) ?_
    have hjoin528 : memRegion a 400 ∗ memRegion (a + 400#64) 128 ⊢ memRegion a 528 := by
      rw [show (528 : Nat) = 400 + 128 from rfl,
          ProofLib.memRegion_split a 400 128 (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
    have hjoin928 : memRegion a 528 ∗ memRegion (a + 528#64) polyDecoderSize ⊢ memRegion a 928 := by
      rw [show (928 : Nat) = 528 + polyDecoderSize from rfl,
          ProofLib.memRegion_split a 528 polyDecoderSize (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
    wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerReceived_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.headerReceived st))) := by
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedHeaderReceivedAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw hdec_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine SepWP.focus_weaken
    (unchunkedEkSent8_entails_dealloc A a { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder88_entails_vecs_tail A a st.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  dsimp only [threeVec8HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 504#64)
    (P_mid := ((a ↦₆₄ 8#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
      ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
      memRegion (a + 488#64) 440) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 524#64)
      (P_mid := ((a ↦₆₄ 8#64) ∗
        ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
        memRegion (a + 488#64) 440) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl2 (mid := (blkPl_443).base + 544#64)
        (P_mid := ((a ↦₆₄ 8#64) ∗ memRegion (a + 8#64) 80 ∗
          vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
          memRegion (a + 488#64) 440) ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · have hhdr80 := threeVec8HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec8HeadersAt] at hhdr80
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          have hsp_eq : stackAt s2.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 _hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
        wp_steps_lscl (lsmpl.base 440)
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hdec_cl ⟨a + 88#64, vecs⟩
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        refine SepWP.focus_weaken (polyDecoder88_post_join a) (by sep_focus) ?_
        have hjoin480 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) polyDecoderSize ⊢
            memRegion (a + 8#64) 480 := by
          have h88 : (a + 8#64) + 80#64 = a + 88#64 := BitVec.add_assoc a 8#64 80#64
          rw [← h88, show (480 : Nat) = 80 + polyDecoderSize from rfl,
              ProofLib.memRegion_split (a + 8#64) 80 polyDecoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin480 (by sep_focus) ?_
        have hjoin928 := tag_and_two_regions_entails_928 a 8#64 480 440 488#64
          (BitVec.add_assoc a 8#64 480#64).symm rfl
        refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
        wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekSentCt1Received_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ekSentCt1Received st))) := by
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedEkSentCt1ReceivedAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw hdec_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedEkSentCt1Received8_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hdec112 : polyDecoderAt A (a + 112#64) st.receiving_ct2 ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A (a + 112#64) vecs ∗
        memRegion (a + 496#64) 16 := by
    refine Entails.trans (polyDecoderAt_entails_vecs_tail A (a + 112#64) st.receiving_ct2) ?_
    apply Entails.sepExists_elim; intro vecs
    refine Entails.sepExists_right vecs ?_
    rw [BitVec.add_assoc a 112#64 384#64]
    exact Entails.refl _
  refine SepWP.focus_weaken hdec112 (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  dsimp only [fourVec8HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 164#64)
    (P_mid := ((a ↦₆₄ 6#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
      ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 8 ∗
      ((a + 80#64) ↦₆₄ g.v4.cap) ∗ ((a + 88#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 96#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      (if (g.v4.cap == 0#64) = true then emp
       else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
      vecPtListOf A (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
      memRegion (a + 512#64) 416) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 184#64)
      (P_mid := ((a ↦₆₄ 6#64) ∗
        ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 8 ∗
        ((a + 80#64) ↦₆₄ g.v4.cap) ∗ ((a + 88#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 96#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        (if (g.v4.cap == 0#64) = true then emp
         else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
        vecPtListOf A (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
        memRegion (a + 512#64) 416) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl2 (mid := (blkPl_443).base + 204#64)
        (P_mid := ((a ↦₆₄ 6#64) ∗
          ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
          ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
          ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 8 ∗
          ((a + 80#64) ↦₆₄ g.v4.cap) ∗ ((a + 88#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 96#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          vecPtListOf A (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
          memRegion (a + 512#64) 416) ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl3 (mid := (blkPl_443).base + 224#64)
          (P_mid := ((a ↦₆₄ 6#64) ∗ memRegion (a + 8#64) 104 ∗
            vecPtListOf A (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
            memRegion (a + 512#64) 416) ∗
            CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · have hhdr104 := fourVec8HeadersAt_entails_memRegion_104 a g
          dsimp only [fourVec8HeadersAt] at hhdr104
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            have hsp_eq : stackAt s3.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_3]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 _hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps_lscl (lsmpl.base 440)
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call hdec_cl ⟨a + 112#64, vecs⟩
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
          refine SepWP.focus_weaken (polyDecoder112_post_join a) (by sep_focus) ?_
          have hjoin504 : memRegion (a + 8#64) 104 ∗ memRegion (a + 112#64) polyDecoderSize ⊢
              memRegion (a + 8#64) 504 := by
            have h112 : (a + 8#64) + 104#64 = a + 112#64 := BitVec.add_assoc a 8#64 104#64
            rw [← h112, show (504 : Nat) = 104 + polyDecoderSize from rfl,
                ProofLib.memRegion_split (a + 8#64) 104 polyDecoderSize (by decide)]
            exact Entails.refl _
          refine SepWP.focus_weaken hjoin504 (by sep_focus) ?_
          have hjoin928 := tag_and_two_regions_entails_928 a 6#64 504 416 512#64
            (BitVec.add_assoc a 8#64 504#64).symm rfl
          refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
          wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Acknowledged_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hct1 : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_444 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_444).base (dropUnchunkedCt1SentSpec A F))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Acknowledged st))) := by
  have hct1_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 444)
      (withLsCl lsmpl (dropUnchunkedCt1SentSpec A F)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hct1
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  dsimp only [withLsCl, dropUnchunkedCt1SentSpec, dropGlueSortedSetPt16Spec, chunkedStatesAt,
    chunkedCt1AcknowledgedAt, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes,
    dropGluePoly16Stack, spqrPolyApi] at hct1_cl hdec_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 136#64) st.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps_lscl (lsmpl.base 444)
  wp_call hct1_cl ⟨a + 8#64, st.uc⟩
  wp_steps_lscl (lsmpl.base 440)
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hdec_cl ⟨a + 136#64, vecs⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (polyDecoder_post_join (a + 136#64)) (by sep_focus) ?_
  have hjoin528 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) polyDecoderSize ⊢
      memRegion (a + 8#64) 528 := by
    have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
    rw [← h136, show (528 : Nat) = 128 + polyDecoderSize from rfl,
        ProofLib.memRegion_split (a + 8#64) 128 polyDecoderSize (by decide)]
    exact Entails.refl _
  refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a 11#64 528 392 536#64
    (BitVec.add_assoc a 8#64 528#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
  wp_done

/-! ## `HookSat` & `withPanics` Per-Variant Wrappers (Part 1/2) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_noHeaderReceived_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.noHeaderReceived st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_noHeaderReceived_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_noHeaderReceived_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.noHeaderReceived st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_noHeaderReceived_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerReceived_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.headerReceived st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerReceived_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerReceived_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.headerReceived st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerReceived_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekSentCt1Received_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ekSentCt1Received st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekSentCt1Received_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekSentCt1Received_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ekSentCt1Received st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekSentCt1Received_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Acknowledged_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Acknowledged st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Acknowledged_placed_ok
    (CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Acknowledged_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Acknowledged st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Acknowledged_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Sampled_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Sampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Sampled_placed_ok
    (CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Sampled_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Sampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Sampled_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

end CryptoVerification.SpqrV1.Drop
