/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
public import LibsignalBinary.Proofs.SpqrV1.Drop.TopDecodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `spqr::v1::chunked::states::States [local#1]` (`0x35a6c`, Part 1)

**Checked by Lean.**

Defines the `.rodata` jump table at `0x7e530` and specifications for
`core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]` (`0x35a6c`, Block `140`,
181 instructions), and proves the first six variant contracts (`keysUnsampled`,
`noHeaderReceived`, `headerReceived`, `ekSentCt1Received`, `ct1Acknowledged`, `ct1Sampled`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L28

open Lean Elab Tactic Meta ProofLib

/-- Wrapper around `code_fetches` that looks up both `fnOff` lemma and byte offset by symbol name. -/
elab "code_fetches_sym " codeId:ident decPrefix:ident b:term:max H:term:max
    sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← CodeLookup.lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offLit $len))

end CryptoVerification.SpqrV1.Layout.L28

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L28

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `.rodata` Jump Table for `0x35a6c` (`States [local#1]`) at `0x7e530` -/

/-- The 10-byte jump table at `0x7e530` for `drop_glue::<States> [local#1]` (`0x35a6c`,
    base `entry + 68`, scaled by `<< 2`). -/
def chunkedStatesLocal1JumpTableBytes : List (BitVec 8) :=
  [49#8, 0#8, 61#8, 0#8, 19#8, 90#8, 104#8, 82#8, 132#8, 43#8]

/-- Read-only separation-logic assertion for the 10-byte jump table. -/
def chunkedStatesLocal1JumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x35b7c 0x35b80)) ↦ᵣ chunkedStatesLocal1JumpTableBytes

def chunkedStatesLocal1JumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_xref% 0x35b7c 0x35b80)) ↦₈ᵣ 49#8) ∗ ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 1)) ↦₈ᵣ 0#8) ∗
  ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 2)) ↦₈ᵣ 61#8) ∗ ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 3)) ↦₈ᵣ 0#8) ∗
  ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 4)) ↦₈ᵣ 19#8) ∗ ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 5)) ↦₈ᵣ 90#8) ∗
  ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 6)) ↦₈ᵣ 104#8) ∗ ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 7)) ↦₈ᵣ 82#8) ∗
  ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 8)) ↦₈ᵣ 132#8) ∗ ((b + bv% ((ls_xref% 0x35b7c 0x35b80) + 9)) ↦₈ᵣ 43#8)

abbrev chunkedStatesLocal1JumpTableSym : String :=
  "libsignal_session:.rodata.core::ptr::drop_glue::<spqr::v1::chunked::states::States>"

def chunkedStatesLocal1JumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsmpl.ρ chunkedStatesLocal1JumpTableSym) ↦ᵣ chunkedStatesLocal1JumpTableBytes

def chunkedStatesLocal1JumpTablePlacedExpanded [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym) ↦₈ᵣ 49#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 1#64) ↦₈ᵣ 0#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 2#64) ↦₈ᵣ 61#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 3#64) ↦₈ᵣ 0#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 4#64) ↦₈ᵣ 19#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 5#64) ↦₈ᵣ 90#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 6#64) ↦₈ᵣ 104#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 7#64) ↦₈ᵣ 82#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 8#64) ↦₈ᵣ 132#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 9#64) ↦₈ᵣ 43#8)

theorem fnAddr_adrp_35a98 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := by
  rw [Program.fnAddr_rebase, dropChunkedStatesLocal1_fnOff]
  revert hb; bv_bits

/-! ## Specifications for `States [local#1]` and Offset Helpers -/

def dropChunkedStatesLocal1Spec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (DropChunkedStatesGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      chunkedStatesAt A x.a x.st ∗
      chunkedStatesLocal1JumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      chunkedStatesLocal1JumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def dropChunkedStatesLocal1VariantSpec (A : RustAlloc) {F : ShaCompress} (b : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      chunkedStatesAt A a st ∗
      chunkedStatesLocal1JumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion a chunkedStatesSize ∗
      chunkedStatesLocal1JumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def dropChunkedStatesLocal1PlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedStatesGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedStatesAt A x.a x.st ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def dropChunkedStatesLocal1PlacedVariantSpec [LibsignalPlacement] (A : RustAlloc) {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a⌝ ∗
      chunkedStatesAt A a st ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion a chunkedStatesSize ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

theorem polyDecoder112_entails_vecs_tail (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A ((a + 8#64) + 104#64) dec ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A (a + 112#64) vecs ∗
        memRegion (a + 496#64) 16 := by
  have h112 : (a + 8#64) + 104#64 = a + 112#64 := BitVec.add_assoc a 8#64 104#64
  rw [h112]
  refine Entails.trans (polyDecoderAt_entails_vecs_tail A (a + 112#64) dec) ?_
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right vecs ?_
  rw [BitVec.add_assoc a 112#64 384#64]
  exact Entails.refl _

theorem polyDecoder112_post_join (a : BitVec 64) :
    memRegion (a + 112#64) polyArrayBytes ∗ memRegion (a + 496#64) 16 ⊢
      memRegion (a + 112#64) polyDecoderSize := by
  have h496 : a + 496#64 = (a + 112#64) + 384#64 := (BitVec.add_assoc a 112#64 384#64).symm
  rw [h496]
  exact polyDecoder_post_join (a + 112#64)

theorem polyDecoder488_entails_vecs_tail (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A ((a + 8#64) + 480#64) dec ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A (a + 488#64) vecs ∗
        memRegion (a + 872#64) 16 := by
  have h488 : (a + 8#64) + 480#64 = a + 488#64 := BitVec.add_assoc a 8#64 480#64
  rw [h488]
  refine Entails.trans (polyDecoderAt_entails_vecs_tail A (a + 488#64) dec) ?_
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right vecs ?_
  rw [BitVec.add_assoc a 488#64 384#64]
  exact Entails.refl _

theorem polyDecoder488_post_join (a : BitVec 64) :
    memRegion (a + 488#64) polyArrayBytes ∗ memRegion (a + 872#64) 16 ⊢
      memRegion (a + 488#64) polyDecoderSize := by
  have h872 : a + 872#64 = (a + 488#64) + 384#64 := (BitVec.add_assoc a 488#64 384#64).symm
  rw [h872]
  exact polyDecoder_post_join (a + 488#64)

/-! ## Per-Variant Proofs for `States [local#1]` (Six Variants) -/

set_option hygiene false

local macro "states1_keysUnsampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 284#64)
    (P_mid := ((a ↦₆₄ 2#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      memRegion (a + 64#64) 864) ∗
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have hjoin928 : (a ↦₆₄ 2#64) ∗ twoVec8HeadersAt a g ∗ memRegion (a + 64#64) 864 ⊢ memRegion a 928 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (twoVec8HeadersAt_entails_memRegion_56 a g))) ?_
      exact tag_and_two_regions_entails_928 a 2#64 56 864 64#64 (BitVec.add_assoc a 8#64 56#64).symm rfl
    dsimp only [twoVec8HeadersAt, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded] at hjoin928 ⊢
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
      wp_done))

/-- Variant `keysUnsampled` (`tag = 2#64`, jump index `0` -> `+264` -> ret). -/
theorem drop_chunked_states_local1_keysUnsampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.keysUnsampled st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, chunkedStatesAt,
    chunkedKeysUnsampledAt, chunkedStatesLocal1JumpTableAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_keysUnsampled_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_noHeaderReceived_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 448#64)
    (P_mid := ((a ↦₆₄ 7#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
      memRegion (a + 464#64) 464) ∗
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 468#64)
      (P_mid := ((a ↦₆₄ 7#64) ∗ memRegion (a + 8#64) 56 ∗
        vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
        memRegion (a + 464#64) 464) ∗
        $jtExp ∗
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
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hdec_raw ⟨a + 64#64, vecs⟩
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
      wp_done))

/-- Variant `noHeaderReceived` (`tag = 7#64`, jump index `5` -> `+428` -> dealloc 2 Vecs -> tail-call `0x35610`). -/
theorem drop_chunked_states_local1_noHeaderReceived {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.noHeaderReceived st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hdec_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyDecoderName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_decoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedNoHeaderReceivedAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw hdec_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_noHeaderReceived_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_headerReceived_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 504#64)
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
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 524#64)
      (P_mid := ((a ↦₆₄ 8#64) ∗
        ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
        memRegion (a + 488#64) 440) ∗
        $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 544#64)
        (P_mid := ((a ↦₆₄ 8#64) ∗ memRegion (a + 8#64) 80 ∗
          vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
          memRegion (a + 488#64) 440) ∗
          $jtExp ∗
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
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          have hsp_eq : stackAt s2.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
        wp_steps
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hdec_raw ⟨a + 88#64, vecs⟩
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
        wp_done))

/-- Variant `headerReceived` (`tag = 8#64`, jump index `6` -> `+484` -> dealloc 3 Vecs -> tail-call `0x35610`). -/
theorem drop_chunked_states_local1_headerReceived {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.headerReceived st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hdec_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyDecoderName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_decoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedHeaderReceivedAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw hdec_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_headerReceived_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_ekSentCt1Received_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 164#64)
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
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 184#64)
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
        $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 204#64)
        (P_mid := ((a ↦₆₄ 6#64) ∗
          ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
          ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
          ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 8 ∗
          ((a + 80#64) ↦₆₄ g.v4.cap) ∗ ((a + 88#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 96#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          vecPtListOf A (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
          memRegion (a + 512#64) 416) ∗
          $jtExp ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 224#64)
          (P_mid := ((a ↦₆₄ 6#64) ∗ memRegion (a + 8#64) 104 ∗
            vecPtListOf A (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
            memRegion (a + 512#64) 416) ∗
            $jtExp ∗
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
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            have hsp_eq : stackAt s3.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_3]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call hdec_raw ⟨a + 112#64, vecs⟩
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
          have hjoin112 : memRegion (a + 112#64) 384 ∗ memRegion (a + 496#64) 16 ⊢
              memRegion (a + 112#64) polyDecoderSize := by
            have h496 : a + 496#64 = (a + 112#64) + 384#64 := (BitVec.add_assoc a 112#64 384#64).symm
            rw [h496]
            exact polyDecoder_post_join (a + 112#64)
          refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
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
          wp_done))

/-- Variant `ekSentCt1Received` (`tag = 6#64`, jump index `4` -> `+144` -> dealloc 4 Vecs -> tail-call `0x35610`). -/
theorem drop_chunked_states_local1_ekSentCt1Received {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.ekSentCt1Received st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hdec_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyDecoderName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_decoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedEkSentCt1ReceivedAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw hdec_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_ekSentCt1Received_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_ct1Acknowledged_steps" : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 136#64) st.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps
  wp_call hct1_raw ⟨a + 8#64, st.uc⟩
  wp_steps
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hdec_raw ⟨a + 136#64, vecs⟩
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
  wp_done))

/-- Variant `ct1Acknowledged` (`tag = 11#64`, jump index `9` -> `+240` -> `bl 0x35d40` -> tail-call `0x35610`). -/
theorem drop_chunked_states_local1_ct1Acknowledged {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.ct1Acknowledged st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hct1_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"))
      (dropUnchunkedCt1SentSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]") (by decide))
    (drop_unchunked_ct1_sent_local1_ok_ext hdealloc)
  have hdec_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyDecoderName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_decoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropUnchunkedCt1SentSpec,
    dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedCt1AcknowledgedAt,
    chunkedStatesLocal1JumpTableAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hct1_raw hdec_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_ct1Acknowledged_steps

local macro "states1_ct1Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyEncoderAt_expose_tag A a st.sending_ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i w; wp_focus_pure; intro hw
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  refine seq_clean (mid := $entry + 396#64)
    (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
      unchunkedCt1SentAt A (a + 400#64) st.uc ∗
      polyDecoderAt A (a + 528#64) st.receiving_ek) ∗
      $jtExp ∗
      A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · rcases hw with rfl | rfl
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 0#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 1#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
    refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 528#64) st.receiving_ek) (by sep_focus) ?_
    wp_pull_exists; rename_i dec_vecs; wp_focus_pure; intro hdec_len
    wp_steps
    wp_call hct1_raw ⟨a + 400#64, st.uc⟩
    wp_steps
    wp_call henc_raw ⟨a, st.sending_ct1⟩
    wp_steps
    have hsp_eq : stackAt sf.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by
      rw [hsp_sf, hsp_1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hdec_raw ⟨a + 528#64, dec_vecs⟩
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
    wp_done))

/-- Variant `ct1Sampled` (`tag = 0#64` or `1#64`, jump index `7` -> `+396`). -/
theorem drop_chunked_states_local1_ct1Sampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.ct1Sampled st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hct1_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"))
      (dropUnchunkedCt1SentSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]") (by decide))
    (drop_unchunked_ct1_sent_local1_ok_ext hdealloc)
  have henc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGluePolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_encoder_local1_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hdec_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyDecoderName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_decoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropUnchunkedCt1SentSpec,
    dropGluePolyEncoderSpec, dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedCt1SampledAt,
    chunkedStatesLocal1JumpTableAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, unchunkedCt1SentSize, polyEncoderSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hct1_raw henc_raw hdec_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_ct1Sampled_steps entry (chunkedStatesLocal1JumpTableExpanded b)

/-! ## Relocatable `[LibsignalPlacement]` Variant Proofs (Block `140`) -/

section PlacedStates1a
variable [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}

theorem drop_chunked_states_local1_keysUnsampled_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.keysUnsampled st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedStatesAt, chunkedKeysUnsampledAt, chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize] at hdealloc_raw ⊢
  wp_init a s0; states1_keysUnsampled_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_noHeaderReceived_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.noHeaderReceived st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedNoHeaderReceivedAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw hdec_raw ⊢
  wp_init a s0; states1_noHeaderReceived_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_headerReceived_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.headerReceived st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedHeaderReceivedAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw hdec_raw ⊢
  wp_init a s0; states1_headerReceived_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_ekSentCt1Received_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.ekSentCt1Received st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedEkSentCt1ReceivedAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw hdec_raw ⊢
  wp_init a s0; states1_ekSentCt1Received_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_ct1Acknowledged_placed
    (hct1_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 141) (dropUnchunkedCt1SentSpec A F))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Acknowledged st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  dsimp only [dropUnchunkedCt1SentSpec, dropGlueSortedSetPt16Spec, chunkedStatesAt,
    chunkedCt1AcknowledgedAt, chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hct1_raw hdec_raw ⊢
  wp_init a s0; states1_ct1Acknowledged_steps

theorem drop_chunked_states_local1_ct1Sampled_placed
    (hct1_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 141) (dropUnchunkedCt1SentSpec A F))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Sampled st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  dsimp only [dropUnchunkedCt1SentSpec, dropGluePolyEncoderSpec, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedCt1SampledAt, chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, unchunkedCt1SentSize, polyEncoderSize,
    polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hct1_raw henc_raw hdec_raw ⊢
  wp_init a s0; states1_ct1Sampled_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

end PlacedStates1a

end CryptoVerification.SpqrV1.Drop
