/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.Drop.TopDecodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `spqr::v1::chunked::states::States [local#2]` (`0x4c5d8`)

**Checked by Lean.**

Proves fixed-image (`drop_chunked_states_local2_ok_ext`, `0x4c5d8`, 109 instructions) and
relocatable `[LibsignalPlacement]` (`drop_chunked_states_local2_placed_ok`, Block `273`)
contracts for `core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L28

open Lean Elab Tactic Meta ProofLib

elab "code_fetches_sym2 " codeId:ident decPrefix:ident b:term:max H:term:max
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

/-! ## `.rodata` Jump Table for `0x4c5d8` (`States [local#2]`) at `0x82402` -/

/-- The 10-byte jump table at `0x82402` for `drop_glue::<States> [local#2]` (`0x4c5d8`,
    base `entry + 68`, scaled by `<< 2`). -/
def chunkedStatesLocal2JumpTableBytes : List (BitVec 8) :=
  [14#8, 0#8, 26#8, 0#8, 4#8, 38#8, 52#8, 30#8, 85#8, 8#8]

/-- Read-only separation-logic assertion for the 10-byte jump table at `b + 0xa1402`. -/
def chunkedStatesLocal2JumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_bytes% "0e001a000426341e5508")) ↦ᵣ chunkedStatesLocal2JumpTableBytes

def chunkedStatesLocal2JumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_bytes% "0e001a000426341e5508")) ↦₈ᵣ 14#8) ∗ ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 1)) ↦₈ᵣ 0#8) ∗
  ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 2)) ↦₈ᵣ 26#8) ∗ ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 3)) ↦₈ᵣ 0#8) ∗
  ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 4)) ↦₈ᵣ 4#8) ∗ ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 5)) ↦₈ᵣ 38#8) ∗
  ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 6)) ↦₈ᵣ 52#8) ∗ ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 7)) ↦₈ᵣ 30#8) ∗
  ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 8)) ↦₈ᵣ 85#8) ∗ ((b + bv% ((ls_bytes% "0e001a000426341e5508") + 9)) ↦₈ᵣ 8#8)

abbrev chunkedStatesLocal2JumpTableSym : String :=
  "spqr:.rodata.core::ptr::drop_glue::<spqr::v1::chunked::states::States>"

def chunkedStatesLocal2JumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsmpl.ρ chunkedStatesLocal2JumpTableSym) ↦ᵣ chunkedStatesLocal2JumpTableBytes

def chunkedStatesLocal2JumpTablePlacedExpanded [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ chunkedStatesLocal2JumpTableSym) ↦₈ᵣ 14#8) ∗ (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 1#64) ↦₈ᵣ 0#8) ∗
  (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 2#64) ↦₈ᵣ 26#8) ∗ (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 3#64) ↦₈ᵣ 0#8) ∗
  (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 4#64) ↦₈ᵣ 4#8) ∗ (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 5#64) ↦₈ᵣ 38#8) ∗
  (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 6#64) ↦₈ᵣ 52#8) ∗ (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 7#64) ↦₈ᵣ 30#8) ∗
  (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 8#64) ↦₈ᵣ 85#8) ∗ (((lsmpl.ρ chunkedStatesLocal2JumpTableSym) + 9#64) ↦₈ᵣ 8#8)

theorem fnAddr_adrp_4c604 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := by
  rw [Program.fnAddr_rebase, dropChunkedStatesLocal2_fnOff]
  revert hb; bv_bits

/-! ## Specifications for `0x4c5d8` (`States [local#2]`) -/

def dropChunkedStatesLocal2Spec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec (DropChunkedStatesGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      chunkedStatesAt A x.a x.st ∗
      chunkedStatesLocal2JumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      chunkedStatesLocal2JumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def dropChunkedStatesLocal2VariantSpec (A : RustAlloc) {F : ShaCompress} (b : BitVec 64)
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      chunkedStatesAt A a st ∗
      chunkedStatesLocal2JumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion a chunkedStatesSize ∗
      chunkedStatesLocal2JumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def dropChunkedStatesLocal2PlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (DropChunkedStatesGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedStatesAt A x.a x.st ∗
      chunkedStatesLocal2JumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      chunkedStatesLocal2JumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

def dropChunkedStatesLocal2PlacedVariantSpec [LibsignalPlacement] (A : RustAlloc) {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a⌝ ∗
      chunkedStatesAt A a st ∗
      chunkedStatesLocal2JumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion a chunkedStatesSize ∗
      chunkedStatesLocal2JumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

/-! ## Per-Variant Proofs for `0x4c5d8` (`States [local#2]`) -/

set_option hygiene false

local macro "states2_keysUnsampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 144#64)
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
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have hjoin928 : (a ↦₆₄ 2#64) ∗ twoVec8HeadersAt a g ∗ memRegion (a + 64#64) 864 ⊢ memRegion a 928 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (twoVec8HeadersAt_entails_memRegion_56 a g))) ?_
      exact tag_and_two_regions_entails_928 a 2#64 56 864 64#64 (BitVec.add_assoc a 8#64 56#64).symm rfl
    dsimp only [twoVec8HeadersAt, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded] at hjoin928 ⊢
    by_cases hc2 : (g.v2.cap == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done
    · wp_steps
      refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      have hsplit_top : stackAt s0.sp dropStackPoly64 =
          memRegion (s0.sp - 4160#64) 64 ∗ stackAt s0.sp allocHookStack :=
        stackAt_split_bottom s0.sp allocHookStack 64 (by decide)
      refine SepWP.focus_weaken (Entails.of_eq hsplit_top) (by sep_focus) ?_
      wp_apply
      refine SepWP.focus_weaken (Entails.of_eq hsplit_top.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_keysUnsampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.keysUnsampled st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, chunkedStatesAt,
    chunkedKeysUnsampledAt, chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_keysUnsampled_steps entry (chunkedStatesLocal2JumpTableExpanded b)

local macro "states2_ct1Received_steps" : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a 5#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_ct1Received {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.ct1Received st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hsub_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"))
      (dropChunkedCt1ReceivedSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>") (by decide))
    (drop_chunked_ct1_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropChunkedCt1ReceivedSpec,
    chunkedStatesAt, chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, chunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hsub_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_ct1Received_steps

local macro "states2_keysSampled_steps" : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, chunkedKeysSampledToCt1Received st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a 3#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_keysSampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.keysSampled st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hsub_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"))
      (dropChunkedCt1ReceivedSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::Ct1Received>") (by decide))
    (drop_chunked_ct1_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropChunkedCt1ReceivedSpec,
    chunkedStatesAt, chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, chunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hsub_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_keysSampled_steps

local macro "states2_headerSent_steps" : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  have hjoin928 := tag_and_two_regions_entails_928 a 4#64 880 40 888#64
    (BitVec.add_assoc a 8#64 880#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_headerSent {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.headerSent st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hsub_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"))
      (dropChunkedHeaderSentSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::HeaderSent>") (by decide))
    (drop_chunked_header_sent_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropChunkedHeaderSentSpec,
    chunkedStatesAt, chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hsub_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_headerSent_steps

local macro "states2_ekSentCt1Received_steps" : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a 6#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_ekSentCt1Received {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.ekSentCt1Received st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hsub_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>"))
      (dropChunkedEkSentCt1ReceivedSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ek::EkSentCt1Received>") (by decide))
    (drop_chunked_ek_sent_ct1_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropChunkedEkSentCt1ReceivedSpec,
    chunkedStatesAt, chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hsub_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_ekSentCt1Received_steps

local macro "states2_noHeaderReceived_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 240#64)
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
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 260#64)
      (P_mid := ((a ↦₆₄ 7#64) ∗ memRegion (a + 8#64) 56 ∗
        vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
        memRegion (a + 464#64) 464) ∗
        $jtExp ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hhdr56 := twoVec8HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec8HeadersAt] at hhdr56
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hpt16_raw ⟨a + 64#64, vecs⟩
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
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_noHeaderReceived {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.noHeaderReceived st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpt16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name =
        (dropProgAtExt b ext).fnAddr dropSortedSetPt16Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"))
        (b := b) (X := Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
        dropChunkedStatesLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedNoHeaderReceivedAt, chunkedStatesLocal2JumpTableAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpt16_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_noHeaderReceived_steps entry (chunkedStatesLocal2JumpTableExpanded b)

local macro "states2_headerReceived_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 296#64)
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
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 316#64)
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
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 336#64)
        (P_mid := ((a ↦₆₄ 8#64) ∗ memRegion (a + 8#64) 80 ∗
          vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
          memRegion (a + 488#64) 440) ∗
          $jtExp ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · have hhdr80 := threeVec8HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec8HeadersAt] at hhdr80
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          have hsp_eq : stackAt s2.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]
        wp_steps
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hpt16_raw ⟨a + 88#64, vecs⟩
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
        refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_headerReceived {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.headerReceived st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpt16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name =
        (dropProgAtExt b ext).fnAddr dropSortedSetPt16Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"))
        (b := b) (X := Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
        dropChunkedStatesLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedHeaderReceivedAt, chunkedStatesLocal2JumpTableAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpt16_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_headerReceived_steps entry (chunkedStatesLocal2JumpTableExpanded b)

local macro "states2_ekReceivedCt1Sampled_steps" : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  wp_steps
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  have hjoin928 := tag_and_two_regions_entails_928 a 10#64 528 392 536#64
    (BitVec.add_assoc a 8#64 528#64).symm rfl
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_ekReceivedCt1Sampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.ekReceivedCt1Sampled st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hsub_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>"))
      (dropChunkedEkReceivedCt1SampledSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>") (by decide))
    (drop_chunked_ek_received_ct1_sampled_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropChunkedEkReceivedCt1SampledSpec,
    chunkedStatesAt, chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, chunkedEkReceivedCt1SampledSize, BitVec.ofNat_eq_ofNat] at hsub_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_ekReceivedCt1Sampled_steps

local macro "states2_ct1Acknowledged_steps" : tactic => `(tactic| (
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
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hpt16_raw ⟨a + 136#64, vecs⟩
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
  refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_ct1Acknowledged {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.ct1Acknowledged st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hct1_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"))
      (dropUnchunkedCt1SentSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]") (by decide))
    (drop_unchunked_ct1_sent_local2_ok_ext hdealloc)
  have hpt16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name =
        (dropProgAtExt b ext).fnAddr dropSortedSetPt16Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"))
        (b := b) (X := Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
        dropChunkedStatesLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropUnchunkedCt1SentSpec,
    dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedCt1AcknowledgedAt,
    chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hct1_raw hpt16_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_ct1Acknowledged_steps

local macro "states2_ct1Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyEncoderAt_expose_tag A a st.sending_ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i w; wp_focus_pure; intro hw
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  refine seq_clean (mid := $entry + 188#64)
    (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
      unchunkedCt1SentAt A (a + 400#64) st.uc ∗
      polyDecoderAt A (a + 528#64) st.receiving_ek) ∗
      $jtExp ∗
      A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · rcases hw with rfl | rfl
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 0#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 1#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    dsimp only [chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]
    refine SepWP.focus_weaken (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ct1) (by sep_focus) ?_
    wp_pull_exists; rename_i tag enc_vecs; wp_focus_pure; intro henc_len
    refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 528#64) st.receiving_ek) (by sep_focus) ?_
    wp_pull_exists; rename_i dec_vecs; wp_focus_pure; intro hdec_len
    wp_steps
    wp_call hct1_raw ⟨a + 400#64, st.uc⟩
    wp_steps
    wp_call hpoly16_raw ⟨a + 8#64, enc_vecs⟩
    wp_steps
    have hsp_eq : stackAt sf.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by rw [hsp_sf, hsp_1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hpt16_raw ⟨a + 528#64, dec_vecs⟩
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
    refine SepWP.focus_weaken (polyDecoder_post_join (a + 528#64)) (by sep_focus) ?_
    refine SepWP.focus_weaken (chunked_400_join a tag 128 528 rfl (by decide)) (by sep_focus) ?_
    have hjoin928 : memRegion a 528 ∗ memRegion (a + 528#64) polyDecoderSize ⊢ memRegion a 928 := by
      rw [show (928 : Nat) = 528 + polyDecoderSize from rfl,
          ProofLib.memRegion_split a 528 polyDecoderSize (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_ct1Sampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.ct1Sampled st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hct1_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"))
      (dropUnchunkedCt1SentSpec A F) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]") (by decide))
    (drop_unchunked_ct1_sent_local2_ok_ext hdealloc)
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name =
        (dropProgAtExt b ext).fnAddr dropPoly16Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"))
        (b := b) (X := Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>")
        dropChunkedStatesLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hpt16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name =
        (dropProgAtExt b ext).fnAddr dropSortedSetPt16Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"))
        (b := b) (X := Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
        dropChunkedStatesLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal2Name + 44#64) &&&
        0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]") + 44)) := fnAddr_adrp_4c604
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropUnchunkedCt1SentSpec,
    dropGluePoly16Spec, dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedCt1SampledAt,
    chunkedStatesLocal2JumpTableAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hct1_raw hpoly16_raw hpt16_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states2_ct1Sampled_steps entry (chunkedStatesLocal2JumpTableExpanded b)

local macro "states2_ct2Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedCt2Sent408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyEncoder8_entails_tag_vecs_tail A a st.sending_ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i tag vecs; wp_focus_pure; intro hvecs_len
  dsimp only [twoVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean (mid := $entry + 372#64)
    (P_mid := ((a ↦₆₄ 12#64) ∗
      ((a + 8#64) ↦₆₄ tag) ∗ vecGF16ListOf A (a + 16#64) vecs ∗ memRegion (a + 400#64) 8 ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      memRegion (a + 464#64) 464) ∗
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 392#64)
      (P_mid := ((a ↦₆₄ 12#64) ∗
        ((a + 8#64) ↦₆₄ tag) ∗ vecGF16ListOf A (a + 16#64) vecs ∗ memRegion (a + 400#64) 8 ∗
        memRegion (a + 408#64) 56 ∗
        memRegion (a + 464#64) 464) ∗
        $jtExp ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hhdr56 := twoVec408HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec408HeadersAt] at hhdr56
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [chunkedStatesLocal2JumpTableExpanded, chunkedStatesLocal2JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hpoly16_raw ⟨a + 16#64, vecs⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken (polyEncoder_local2_8_post_join a tag) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 56 ⊢
          memRegion (a + 8#64) 456 := by
        have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
        rw [← h408, show (456 : Nat) = 400 + 56 from rfl,
            ProofLib.memRegion_split (a + 8#64) 400 56 (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      have hjoin928 := tag_and_two_regions_entails_928 a 12#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done))

theorem drop_chunked_states_local2_ct2Sampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2VariantSpec A b (.ct2Sampled st)) := by
  simp only [dropChunkedStatesLocal2VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext) dropChunkedStatesLocal2_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name =
        (dropProgAtExt b ext).fnAddr dropPoly16Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]"))
        (b := b) (X := Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>")
        dropChunkedStatesLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym2 libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" 436
  dsimp only [dropProgAtExt, dropChunkedStatesLocal2Name, dropGluePoly16Spec,
    chunkedStatesAt, chunkedCt2SampledAt, chunkedStatesLocal2JumpTableAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]" = entry
  examples_hide_fetches; wp_init a s0
  states2_ct2Sampled_steps entry (chunkedStatesLocal2JumpTableExpanded b)

/-! ## Top-Level Proof of `0x4c5d8` (`drop_chunked_states_local2_ok_ext`) -/

theorem drop_chunked_states_local2_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal2Name)
      (dropChunkedStatesLocal2Spec A F b) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | keysUnsampled s => exact (drop_chunked_states_local2_keysUnsampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | keysSampled s => exact (drop_chunked_states_local2_keysSampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | headerSent s => exact (drop_chunked_states_local2_headerSent hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Received s => exact (drop_chunked_states_local2_ct1Received hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ekSentCt1Received s => exact (drop_chunked_states_local2_ekSentCt1Received hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | noHeaderReceived s => exact (drop_chunked_states_local2_noHeaderReceived hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | headerReceived s => exact (drop_chunked_states_local2_headerReceived hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Sampled s => exact (drop_chunked_states_local2_ct1Sampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ekReceivedCt1Sampled s => exact (drop_chunked_states_local2_ekReceivedCt1Sampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Acknowledged s => exact (drop_chunked_states_local2_ct1Acknowledged hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct2Sampled s => exact (drop_chunked_states_local2_ct2Sampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)

/-! ## Relocatable `[LibsignalPlacement]` Proof of Block `273` -/

section PlacedStates2
variable [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}

theorem drop_chunked_states_local2_keysUnsampled_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.keysUnsampled st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [chunkedStatesAt, chunkedKeysUnsampledAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize] at hdealloc_raw ⊢
  wp_init a s0; states2_keysUnsampled_steps (blkPl_273).base chunkedStatesLocal2JumpTablePlacedExpanded

theorem drop_chunked_states_local2_ct1Received_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 277) (dropChunkedCt1ReceivedSpec A F))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.ct1Received st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropChunkedCt1ReceivedSpec, chunkedStatesAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, chunkedCt1ReceivedSize] at hsub_raw ⊢
  wp_init a s0; states2_ct1Received_steps

theorem drop_chunked_states_local2_keysSampled_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 277) (dropChunkedCt1ReceivedSpec A F))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.keysSampled st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropChunkedCt1ReceivedSpec, chunkedStatesAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, chunkedCt1ReceivedSize] at hsub_raw ⊢
  wp_init a s0; states2_keysSampled_steps

theorem drop_chunked_states_local2_headerSent_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 276) (dropChunkedHeaderSentSpec A F))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.headerSent st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropChunkedHeaderSentSpec, chunkedStatesAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, chunkedHeaderSentSize] at hsub_raw ⊢
  wp_init a s0; states2_headerSent_steps

theorem drop_chunked_states_local2_ekSentCt1Received_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 278) (dropChunkedEkSentCt1ReceivedSpec A F))
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.ekSentCt1Received st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropChunkedEkSentCt1ReceivedSpec, chunkedStatesAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, chunkedEkSentCt1ReceivedSize] at hsub_raw ⊢
  wp_init a s0; states2_ekSentCt1Received_steps

theorem drop_chunked_states_local2_noHeaderReceived_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.noHeaderReceived st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedNoHeaderReceivedAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw hpt16_raw ⊢
  wp_init a s0; states2_noHeaderReceived_steps (blkPl_273).base chunkedStatesLocal2JumpTablePlacedExpanded

theorem drop_chunked_states_local2_headerReceived_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.headerReceived st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedHeaderReceivedAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw hpt16_raw ⊢
  wp_init a s0; states2_headerReceived_steps (blkPl_273).base chunkedStatesLocal2JumpTablePlacedExpanded

theorem drop_chunked_states_local2_ekReceivedCt1Sampled_placed
    (hsub_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 275) (dropChunkedEkReceivedCt1SampledSpec A F))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.ekReceivedCt1Sampled st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropChunkedEkReceivedCt1SampledSpec, chunkedStatesAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, chunkedEkReceivedCt1SampledSize] at hsub_raw ⊢
  wp_init a s0; states2_ekReceivedCt1Sampled_steps

theorem drop_chunked_states_local2_ct1Acknowledged_placed
    (hct1_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 279) (dropUnchunkedCt1SentSpec A F))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.ct1Acknowledged st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropUnchunkedCt1SentSpec, dropGlueSortedSetPt16Spec, chunkedStatesAt,
    chunkedCt1AcknowledgedAt, chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hct1_raw hpt16_raw ⊢
  wp_init a s0; states2_ct1Acknowledged_steps

theorem drop_chunked_states_local2_ct1Sampled_placed
    (hct1_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 279) (dropUnchunkedCt1SentSpec A F))
    (hpoly16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 265) (dropGluePoly16Spec A))
    (hpt16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.ct1Sampled st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  dsimp only [dropUnchunkedCt1SentSpec, dropGluePoly16Spec, dropGlueSortedSetPt16Spec,
    chunkedStatesAt, chunkedCt1SampledAt, chunkedStatesLocal2JumpTablePlacedAt,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes,
    dropGluePoly16Stack, spqrPolyApi] at hct1_raw hpoly16_raw hpt16_raw ⊢
  wp_init a s0; states2_ct1Sampled_steps (blkPl_273).base chunkedStatesLocal2JumpTablePlacedExpanded

theorem drop_chunked_states_local2_ct2Sampled_placed
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 265) (dropGluePoly16Spec A))
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedVariantSpec A (.ct2Sampled st)) := by
  simp only [dropChunkedStatesLocal2PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGluePoly16Spec, chunkedStatesAt, chunkedCt2SampledAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableBytes,
    chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw hpoly16_raw ⊢
  wp_init a s0; states2_ct2Sampled_steps (blkPl_273).base chunkedStatesLocal2JumpTablePlacedExpanded

theorem drop_chunked_states_local2_placed_ok
    (hdealloc : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpt16 : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (hpoly16 : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 265) (dropGluePoly16Spec A))
    (hek_ct1 : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 275) (dropChunkedEkReceivedCt1SampledSpec A F))
    (hhdr : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 276) (dropChunkedHeaderSentSpec A F))
    (hct1_recv : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 277) (dropChunkedCt1ReceivedSpec A F))
    (hek_sent : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 278) (dropChunkedEkSentCt1ReceivedSpec A F))
    (hct1_sent : subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (lsmpl.base 279) (dropUnchunkedCt1SentSpec A F)) :
    subroutine_ok ((blkPC_273).rebase (blkPl_273).base H) (blkPl_273).base
      (dropChunkedStatesLocal2PlacedSpec A F) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | keysUnsampled s => exact (drop_chunked_states_local2_keysUnsampled_placed hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | keysSampled s => exact (drop_chunked_states_local2_keysSampled_placed hct1_recv s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | headerSent s => exact (drop_chunked_states_local2_headerSent_placed hhdr s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Received s => exact (drop_chunked_states_local2_ct1Received_placed hct1_recv s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ekSentCt1Received s => exact (drop_chunked_states_local2_ekSentCt1Received_placed hek_sent s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | noHeaderReceived s => exact (drop_chunked_states_local2_noHeaderReceived_placed hdealloc hpt16 s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | headerReceived s => exact (drop_chunked_states_local2_headerReceived_placed hdealloc hpt16 s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Sampled s => exact (drop_chunked_states_local2_ct1Sampled_placed hct1_sent hpoly16 hpt16 s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ekReceivedCt1Sampled s => exact (drop_chunked_states_local2_ekReceivedCt1Sampled_placed hek_ct1 s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct1Acknowledged s => exact (drop_chunked_states_local2_ct1Acknowledged_placed hct1_sent hpt16 s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)
  | ct2Sampled s => exact (drop_chunked_states_local2_ct2Sampled_placed hdealloc hpoly16 s).mono_outcome a R s0 hpc hrun hpre hsp (fun _ hout => hout)

end PlacedStates2

end CryptoVerification.SpqrV1.Drop
