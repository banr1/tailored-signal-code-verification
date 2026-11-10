/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::skip_field::<&mut &[u8]> [local#3]`

Verifies the 105-instruction field-skipping routine (`0x4bb74`) against
`LibsignalProtoCodec.skipField` (`skipField3Spec`) by induction on recursion depth.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

abbrev skipField3Name : String :=
  "prost::encoding::skip_field::<&mut &[u8]> [local#3]"

theorem skipField3_fnOff :
    libsignalSessionCode.fnOff skipField3Name = 0x4677c :=
  libsignalSessionCode_fnOff_0x4677c

/-- Stack budget for `prost::encoding::skip_field::<&mut &[u8]> [local#3]` (`0x4bb74`)
at recursion budget `depth`: each recursive frame uses `0x60` bytes (`sub sp, sp, #96`),
and leaf calls invoke `decode_varint [local#2]` (`decodeVarint2Stack`) or
`DecodeError::from` (`decodeErrorHookStack ≤ decodeVarint2Stack`). -/
abbrev skipField3Stack (depth : Nat) : Nat :=
  (depth + 1) * 0x60 + decodeVarint2Stack

/-- Contract of `prost::encoding::skip_field::<&mut &[u8]> [local#3]` (`0x4bb74`)
in terms of `LibsignalProtoCodec.skipField`. -/
def skipField3Spec (A : RustAlloc) : Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipField3Stack x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipField3Stack x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Case-restricted specification for `skip_field [local#3]` at fixed recursion budget `depth`. -/
def skipField3SpecAt (A : RustAlloc) (depth : Nat) (P : SkipFieldGhost → Prop) :
    Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜P x ∧ x.depth = depth ∧
      (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth ∧ depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipField3Stack depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipField3Stack depth) ∗
      match skipField (2 * x.bs.length + 2) depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Stack decomposition helpers -/

/-- Stack region below the 96-byte frame of `skip_field [local#3]` at recursion budget `depth`. -/
abbrev skipBelow3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  stackAt (sp - 96#64) (depth * 0x60 + decodeVarint2Stack)

private theorem bv_sub_add_96 (sp v : BitVec 64) :
    sp - 96#64 = sp - (v + 96#64) + v := by bv_lin

private theorem bv_sub_96_sub (sp v : BitVec 64) :
    sp - 96#64 - v = sp - (v + 96#64) := by bv_lin

private theorem bv_sub_96_add_cancel (sp u w : BitVec 64) :
    sp - 96#64 - w = sp - 96#64 - (u + w) + u := by bv_lin

theorem stackAt_skipField3 (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    stackAt sp (skipField3Stack depth) =
      (∃∗ v19 : BitVec 64, ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
        ∃∗ v22 : BitVec 64, ∃∗ v_lr : BitVec 64, ∃∗ v_fp : BitVec 64,
        skipBelow3 sp depth ∗
          memRegion (sp - 96#64) 48 ∗
          ((sp - 48#64) ↦₆₄ v_fp) ∗ ((sp - 40#64) ↦₆₄ v_lr) ∗
          ((sp - 32#64) ↦₆₄ v22) ∗ ((sp - 24#64) ↦₆₄ v21) ∗
          ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
  simp only [stackAt, skipBelow3]
  have hlen : skipField3Stack depth = (depth * 0x60 + decodeVarint2Stack) + 96 := by
    simp only [skipField3Stack]; omega
  have hbound : skipField3Stack depth ≤ 2 ^ 64 := by
    simp only [skipField3Stack, decodeVarint2Stack, decodeVarintSlowStack,
      decodeErrorHookStack, allocHookStack]
    omega
  have hbit : BitVec.ofNat 64 (skipField3Stack depth) =
      BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack) + 96#64 := by
    rw [hlen, BitVec.ofNat_add]
  have h1 := memRegion_split'
    (b := sp - BitVec.ofNat 64 (skipField3Stack depth))
    (b' := sp - 96#64)
    (n := depth * 0x60 + decodeVarint2Stack) (k := 96)
    (N := skipField3Stack depth) hlen
    (by rw [hbit]; exact bv_sub_add_96 sp _)
    hbound
  have hsp_sub :
      sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack) =
        sp - BitVec.ofNat 64 (skipField3Stack depth) := by
    rw [hbit]; exact bv_sub_96_sub sp _
  have h2 := memRegion_split' (b := sp - 96#64) (b' := sp - 48#64)
    (n := 48) (k := 48) (N := 96) rfl (by bv_lin) (by decide)
  have h3 := memRegion_split' (b := sp - 48#64) (b' := sp - 40#64)
    (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have h4 := memRegion_split' (b := sp - 40#64) (b' := sp - 32#64)
    (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have h5 := memRegion_split' (b := sp - 32#64) (b' := sp - 24#64)
    (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have h6 := memRegion_split' (b := sp - 24#64) (b' := sp - 16#64)
    (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have h7 := memRegion_split' (b := sp - 16#64) (b' := sp - 8#64)
    (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [hsp_sub, h1, h2, h3, h4, h5, h6, h7,
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

abbrev skipLeafRest3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack)) (depth * 0x60)

theorem skipBelow3_leaf (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelow3 sp depth =
      skipLeafRest3 sp depth ∗ stackAt (sp - 96#64) decodeVarint2Stack := by
  simp only [skipBelow3, skipLeafRest3, stackAt]
  have hbound : depth * 0x60 + decodeVarint2Stack ≤ 2 ^ 64 := by
    simp only [decodeVarint2Stack, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
    omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack) =
      BitVec.ofNat 64 (depth * 0x60) + BitVec.ofNat 64 decodeVarint2Stack :=
    BitVec.ofNat_add _ _
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeVarint2Stack)
    (n := depth * 0x60) (k := decodeVarint2Stack)
    (N := depth * 0x60 + decodeVarint2Stack) rfl
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelow3_leaf_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipLeafRest3 sp depth ∗ stackAt (sp - 96#64) decodeVarint2Stack ⊢
      skipBelow3 sp depth :=
  Entails.of_eq (skipBelow3_leaf sp depth hdepth).symm

abbrev skipErrRest3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack))
    (depth * 0x60 + 0x80)

theorem skipBelow3_err (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelow3 sp depth =
      skipErrRest3 sp depth ∗ stackAt (sp - 96#64) decodeErrorHookStack := by
  simp only [skipBelow3, skipErrRest3, stackAt]
  have hlen : depth * 0x60 + decodeVarint2Stack =
      (depth * 0x60 + 0x80) + decodeErrorHookStack := by
    simp only [decodeVarint2Stack, decodeVarintSlowStack]; omega
  have hbound : depth * 0x60 + decodeVarint2Stack ≤ 2 ^ 64 := by
    simp only [decodeVarint2Stack, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
    omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack) =
      BitVec.ofNat 64 (depth * 0x60 + 0x80) + BitVec.ofNat 64 decodeErrorHookStack := by
    rw [hlen, BitVec.ofNat_add]
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeErrorHookStack)
    (n := depth * 0x60 + 0x80) (k := decodeErrorHookStack)
    (N := depth * 0x60 + decodeVarint2Stack) hlen
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelow3_err_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipErrRest3 sp depth ∗ stackAt (sp - 96#64) decodeErrorHookStack ⊢
      skipBelow3 sp depth :=
  Entails.of_eq (skipBelow3_err sp depth hdepth).symm

theorem subroutine_ok_skipField3_or {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (skipField3SpecAt A depth P))
    (h2 : subroutine_ok prog entry (skipField3SpecAt A depth Q)) :
    subroutine_ok prog entry (skipField3SpecAt A depth (fun x => P x ∨ Q x)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipField3_imp {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (skipField3SpecAt A depth Q)) :
    subroutine_ok prog entry (skipField3SpecAt A depth P) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

/-! ## Decode tree for `0x4bb74..0x4bd18` (105 instructions) -/

gen_decodes libsignalSessionCode_tree skipField3 [0x4677c → 0x46920]

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

set_option hygiene false in
local macro "skipField3_top_err_call" entry:term:max fromTarget:term:max depthTerm:term:max hdepthTerm:term:max kind:term:max : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $fromTarget)
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp $depthTerm $hdepthTerm]
  wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, $kind))
    (ret_pc := $entry + 204#64) hFromCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap $kind)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp $depthTerm $hdepthTerm) (by sep_focus)
  wp_steps
  wp_done))

set_option hygiene false in
local macro "skipField3_depth_zero_body" entry:term:max fromTarget:term:max : tactic => `(tactic| (
  have hcbz := cbz_depth_zero h_6
  rw [skipField_depth_zero]
  skipField3_top_err_call $entry $fromTarget 0 (by decide) 0x8000000000000002#64))

theorem skipField3_depth_zero_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A 0 (fun _ => True)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_depth_zero_body entry (entry + 0xfffffffffffff22c#64)

theorem skipField3_depth_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A)) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A 0 (fun _ => True)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  skipField3_depth_zero_body (blkPl_263).base (lsmpl.base 261)

/-! ## Case 2: `depth = d + 1`, `wt = .endGroup` (`UnexpectedEndGroupTag`) -/

set_option hygiene false in
local macro "skipField3_endGroup_body" entry:term:max fromTarget:term:max : tactic => `(tactic| (
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_endGroup]
  skipField3_top_err_call $entry $fromTarget (d + 1) hdepth 0x8000000000000009#64))

theorem skipField3_endGroup_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .endGroup)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_endGroup_body entry (entry + 0xfffffffffffff22c#64)

theorem skipField3_endGroup_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .endGroup)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  skipField3_endGroup_body (blkPl_263).base (lsmpl.base 261)

/-! ## Cases 3 & 4: `depth = d + 1`, `wt = .sixtyFourBit` (`skipBytes 8`) / `.thirtyTwoBit` (`skipBytes 4`) -/

set_option hygiene false in
local macro "skipField3_fixedWidth_body" entry:term:max fromTarget:term:max nNat:term:max nBv:term:max skipLem:ident : tactic => `(tactic| (
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [$skipLem:ident]
  by_cases hlt : bs.length < $nNat
  · have hule := ule_len_of_lt (n := $nBv) hlt h
    simp only [skipBytes, hlt, ↓reduceIte]
    skipField3_top_err_call $entry $fromTarget (d + 1) hdepth 0x8000000000000007#64
  · have hule := ule_len_of_ge (n := $nBv) hlt h
    have hsub := bv_len_sub_skip (n := $nBv) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := $nBv) hlt
    simp only [skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done))

theorem skipField3_sixtyFourBit_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .sixtyFourBit)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_fixedWidth_body entry (entry + 0xfffffffffffff22c#64) 8 8#64 skipField_succ_sixtyFourBit

theorem skipField3_sixtyFourBit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .sixtyFourBit)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  skipField3_fixedWidth_body (blkPl_263).base (lsmpl.base 261) 8 8#64 skipField_succ_sixtyFourBit

theorem skipField3_thirtyTwoBit_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .thirtyTwoBit)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_fixedWidth_body entry (entry + 0xfffffffffffff22c#64) 4 4#64 skipField_succ_thirtyTwoBit

theorem skipField3_thirtyTwoBit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .thirtyTwoBit)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  skipField3_fixedWidth_body (blkPl_263).base (lsmpl.base 261) 4 4#64 skipField_succ_thirtyTwoBit

/-! ## Case 5: `depth = d + 1`, `wt = .varint` -/

set_option hygiene false in
local macro "skipField3_varint_body" entry:term:max varintTarget:term:max : tactic => `(tactic| (
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_varint]
  apply SepWPp.of_sepWP (mid := $varintTarget)
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  refine SepWPp.call_frame (x := ⟨bufRef, slot, ptr, bs⟩)
    (ret_pc := $entry + 112#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, h⟩ : bufRef = bufRef ∧ bs.length < 2 ^ 63)
    (by simp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  cases hd : decodeVarint bs with
  | none =>
    simp only [hd, Option.map, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    rcases p with ⟨v, rest⟩
    simp only [hd, Option.map, sliceCursorAfter, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done))

theorem skipField3_varint_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 6488#64)
      (decodeVarint2Spec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .varint)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_varint_body entry (entry + 6488#64)

theorem skipField3_varint_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .varint)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  skipField3_varint_body (blkPl_263).base (lsmpl.base 291)

/-! ## Case 6: `depth = d + 1`, `wt = .lengthDelimited` -/

set_option hygiene false in
local macro "skipField3_lengthDelimited_body" entry:term:max fromTarget:term:max varintTarget:term:max : tactic => `(tactic| (
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  rw [skipField_succ_lengthDelimited]
  apply SepWPp.of_sepWP (mid := $varintTarget)
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  refine SepWPp.call_frame (x := ⟨bufRef, slot, ptr, bs⟩)
    (ret_pc := $entry + 160#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, h⟩ : bufRef = bufRef ∧ bs.length < 2 ^ 63)
    (by simp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  cases hd : decodeVarint bs with
  | none =>
    apply SepWPp.of_sepWP_ret
    simp only [hd, sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; intro hsm0
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps
    wp_done
  | some p =>
    rcases p with ⟨len, rest⟩
    have hrest_le : rest.length ≤ bs.length := Nat.le_of_lt (decodeVarint_length hd)
    have hrest_lt : rest.length < 2 ^ 63 := by omega
    by_cases hlt : rest.length < len.toNat
    · have hule := ule_len_of_lt hlt hrest_lt
      simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
      apply SepWPp.of_sepWP (mid := $fromTarget)
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
      conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
      wp_reach
      refine SepWPp.call_frame (x := (s0.sp - 96#64, 0x8000000000000007#64))
        (ret_pc := $entry + 204#64) hFromCall
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [arm64_norm]; rfl)
        (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64)
        (by sep_focus)
        (fun _ _ _ _ hex => allowPanic_not_exited hex)
        (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm]) hpan) ?_
      intro sm2 hpcm2 hrunm2 hspm2 hcsm2
      simp only [CalleeSavedPreserved] at hcsm2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
      simp (config := { decide := true }) only [arm64_norm, hspm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply SepWPp.of_sepWP_ret
      simp only [arm64_norm, htrm, hspm]
      apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done
    · have hule := ule_len_of_ge hlt hrest_lt
      have hsub := bv_len_sub_skip hlt
      have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
      simp only [hd, skipBytes, hlt, ↓reduceIte, sliceCursorAfter, sepConj_assoc, arm64_norm]
      apply SepWPp.of_sepWP_ret
      apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps
      wp_done))

theorem skipField3_lengthDelimited_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 6488#64)
      (decodeVarint2Spec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .lengthDelimited)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_lengthDelimited_body entry (entry + 0xfffffffffffff22c#64) (entry + 6488#64)

theorem skipField3_lengthDelimited_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .lengthDelimited)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  skipField3_lengthDelimited_body (blkPl_263).base (lsmpl.base 261) (lsmpl.base 291)

/-! ## Case 7: `depth = d + 1`, `wt = .startGroup` -/

abbrev HighCalleeSaved3 (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

abbrev skipGroupLoopPre3 (A : RustAlloc) (s0 : State) (d : Nat)
    (bufRef slot ptr v_pad : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ v_pad) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelow3 s0.sp (d + 1)

set_option hygiene false in
local macro "skipField3_startGroup_err_call" entry:term:max kind:term:max : tactic => `(tactic| (
  conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
  wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, $kind))
    (ret_pc := $entry + 204#64) hFromCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
    (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (⟨rfl, by decide⟩ : s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap $kind)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
  intro sm2 hpcm2 hrunm2 hspm2 hcsm2
  simp only [CalleeSavedPreserved] at hcsm2
  obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
  simp (config := { decide := true }) only [arm64_norm, hspm, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  apply SepWPp.of_sepWP_ret
  simp only [arm64_norm, htrm, htr_s, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps
  wp_done))

set_option hygiene false in
local macro "skipField3_startGroup_varint_call" entry:term:max varintTarget:term:max : tactic => `(tactic| (
  obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
  have hcur_lt : cur.length < 2 ^ 63 := by omega
  let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
  apply SepWPp.of_sepWP (mid := $varintTarget)
  conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
    skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps
  wp_reach
  refine SepWPp.call_frame (x := ⟨bufRef, slot, curPtr, cur⟩)
    (ret_pc := $entry + 240#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
    (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hsp_s]; rfl)
    (⟨rfl, hcur_lt⟩ : bufRef = bufRef ∧ cur.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr_s]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs))

set_option hygiene false in
local macro "skipField3_startGroup_varint_none" : tactic => `(tactic| (
  have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
  rw [hnone] at hres_cur
  subst hres_cur
  apply SepWPp.of_sepWP_ret
  simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
  apply SepWP.pure_elim; intro hsm0
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
  wp_steps
  wp_done))

set_option hygiene false in
local macro "skipField3_startGroup_body" prog:term:max entry:term:max fromTarget:term:max varintTarget:term:max : tactic => `(tactic| (
  have hcbz := cbz_depth_succ h_7 hdepth
  have hw0 := w0_and_255_eq h_3
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat h_5
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.of_sepWP (mid := $entry + 232#64)
  wp_steps
  wp_reach
  apply SepWPp.weaken_pre (P' := skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs bs)
    (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; simp only [sliceCursorAfter, Nat.sub_self,
      BitVec.add_zero]; ac_rfl))
  refine (fun (Q_f Qp_f : State → SepProp → Prop)
      (hloop : ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n →
        cur.length ≤ bs.length →
        IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = $entry + 232#64 →
        s.status = .Running →
        s.sp = s0.sp - 96#64 →
        s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef →
        s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
        HighCalleeSaved3 s0 s →
        SepWPp $prog (s0.readReg64 Reg.lr) s
          (skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs cur) Q_f Qp_f) =>
      hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    _ _ ?_
  intro n
  induction n with
  | zero =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s
    skipField3_startGroup_varint_call $entry $varintTarget
    cases hd : decodeVarint cur with
    | none => skipField3_startGroup_varint_none
    | some p =>
      have hlt_cur := decodeVarint_length hd
      omega
  | succ n ih =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s
    skipField3_startGroup_varint_call $entry $varintTarget
    cases hd : decodeVarint cur with
    | none => skipField3_startGroup_varint_none
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ bs.length := by omega
      have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone := skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge
        rw [hnone] at hres_cur
        subst hres_cur
        have hshr := key_shr32_of_ge hk_ge
        apply SepWPp.of_sepWP (mid := $fromTarget)
        conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
          sliceCursorAt, memRegion_48_split2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        skipField3_startGroup_err_call $entry 0x8000000000000004#64
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone := skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt
          rw [hnone] at hres_cur
          subst hres_cur
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply SepWPp.of_sepWP (mid := $fromTarget)
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
          apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
            sliceCursorAt, memRegion_48_split2 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
          rw [← bv_sub_add_lit s0.sp 96 8] at h40
          apply SepWP.fold h40 (by sep_focus)
          skipField3_startGroup_err_call $entry 0x8000000000000003#64
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone := skipGroup_of_tag_zero (d := d) (tag := tag) hd hk_ge hwt hitag0
            rw [hnone] at hres_cur
            subst hres_cur
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply SepWPp.of_sepWP (mid := $fromTarget)
            conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
            apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
            apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
              sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_err0
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            skipField3_startGroup_err_call $entry 0x8000000000000005#64
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            by_cases hiwt_eg : iwt = .endGroup
            · subst hiwt_eg
              dsimp [WireType.toNat] at hand_wt hcc1_wt hcc2_wt
              have heg := skipGroup_of_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0
              rw [heg] at hres_cur
              by_cases hitag_eq : key.toNat / 8 = tag
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                subst hres_cur
                rw [hitag_eq] at hw1 hw1_2 hw1_zext1 hw1_zext2 hcbz_tag1 hcbz_tag2
                apply SepWPp.of_sepWP_ret
                simp only [hd, sepConj_assoc, arm64_norm, htr_s, hsp_s]
                apply SepWP.pure_elim; rintro ⟨hsm0, hsm1⟩
                apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
                simp only [sliceCursorAfter]
                wp_steps
                wp_done
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                subst hres_cur
                obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt h_5
                apply SepWPp.of_sepWP (mid := $fromTarget)
                conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
                apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
                conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                  sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                apply SepWP.exists_elim; intro v_err0
                wp_steps
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                skipField3_startGroup_err_call $entry 0x8000000000000009#64
            · have hne_eg := skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg
              rw [hne_eg] at hres_cur
              have hiwt_ne4 := iwt_beq_4_false hiwt_eg
              obtain ⟨hiwt_w0_1, hiwt_w0_2⟩ := iwt_w0_setWidth8 iwt
              have hd_lt : d < 2 ^ 32 := by omega
              apply SepWPp.of_sepWP (mid := $entry)
              conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm, hsp_s]
              apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
              apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                show skipBelow3 s0.sp (d + 1) = stackAt sm.sp (skipField3Stack d) from by
                  rw [hspm]]
              simp only [sepConj_assoc]
              wp_steps
              wp_reach
              refine SepWPp.call_frame
                (x := ⟨iwt, key.toNat / 8, d, bufRef, slot,
                  ptr + BitVec.ofNat 64 (bs.length - rest.length), rest⟩)
                (ret_pc := $entry + 304#64) hrec
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [arm64_norm]; rfl)
                ?_
                (by sep_focus)
                (fun _ _ _ _ hex => allowPanic_not_exited hex)
                (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr_s]) hpan) ?_
              · simp only [arm64_norm, hiwt_w0_2, sf_truncate32_ofNat64]
                exact ⟨hitag_lt, hd_lt, hrest_lt⟩
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2
              simp only [CalleeSavedPreserved] at hcsm2
              obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
              simp (config := { decide := true }) only [arm64_norm, hspm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
              cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
              | none =>
                rw [hs] at hres_cur
                dsimp only at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [hs, sepConj_assoc, arm64_norm, htrm, htr_s, hspm]
                apply SepWP.pure_elim; rintro ⟨htrm2, hsm2_0⟩
                have hcbz_sm0 : (sm2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm2_0
                conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl]
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                wp_steps
                wp_done
              | some rest' =>
                rw [hs] at hres_cur
                dsimp only at hres_cur
                have hrest'_le_rest : rest'.length ≤ rest.length :=
                  (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
                have hrest'_le_n : rest'.length ≤ n := by omega
                have hrest'_le_bs : rest'.length ≤ bs.length := by omega
                have hrest'_suf : IsDropSuffix bs rest' :=
                  suffix_trans hrest_le hrest_suf hrest'_le_rest
                    ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs)
                apply SepWPp.of_sepWP (mid := $entry + 232#64)
                conv => arg 4; simp only [hs, sepConj_assoc, arm64_norm, hspm]
                apply SepWP.pure_elim; rintro ⟨htrm2, hsm2_0⟩
                conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl]
                apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
                wp_steps
                wp_reach
                apply SepWPp.weaken_pre (P' := skipGroupLoopPre3 A s0 d bufRef slot ptr v_stk_2 bs rest')
                  (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; ac_rfl))
                refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm2])
                  (by simp only [arm64_norm, hspm2]) (by simp only [arm64_norm, htrm2, htrm, htr_s])
                  (by simp only [arm64_norm, hx19_2]) (by simp only [arm64_norm, hx20_2])
                  (by simp only [arm64_norm, hx21_2])
                  ⟨by simp only [arm64_norm, hx22_2], by simp only [arm64_norm, hx23_2],
                    by simp only [arm64_norm, hx24_2], by simp only [arm64_norm, hx25_2],
                    by simp only [arm64_norm, hx26_2], by simp only [arm64_norm, hx27_2],
                    by simp only [arm64_norm, hx28_2], by simp only [arm64_norm, hvregs_2]⟩))

set_option maxHeartbeats 2000000 in
theorem skipField3_startGroup_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 6488#64)
      (decodeVarint2Spec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A d (fun _ => True))) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .startGroup)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  have hfn := libsignalSessionCode_fnOff_0x4677c
  code_fetches CryptoVerification.libsignalSessionCode skipField3 b H hfn 0x4677c 420
  examples_generalize_entry
  examples_hide_fetches
  skipField3_startGroup_body (libsignalSessionCode.rebase b H) entry (entry + 0xfffffffffffff22c#64) (entry + 6488#64)

set_option maxHeartbeats 2000000 in
theorem skipField3_startGroup_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A d (fun _ => True))) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A (d + 1) (fun x => x.wt = .startGroup)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  dsimp only at *
  subst h_1
  skipField3_startGroup_body ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base (lsmpl.base 261) (lsmpl.base 291)

/-! ## Induction on Recursion Depth -/

theorem skipField3_at_depth_ok {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 6488#64)
      (decodeVarint2Spec A))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3SpecAt A depth (fun _ => True)) := by
  induction depth with
  | zero => exact skipField3_depth_zero_ok hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipField3_or (skipField3_varint_ok hVarintCall d hdepth)
        (subroutine_ok_skipField3_or (skipField3_sixtyFourBit_ok hFromCall d hdepth)
          (subroutine_ok_skipField3_or (skipField3_lengthDelimited_ok hFromCall hVarintCall d hdepth)
            (subroutine_ok_skipField3_or (skipField3_startGroup_ok hFromCall hVarintCall d hdepth hrec)
              (subroutine_ok_skipField3_or (skipField3_endGroup_ok hFromCall d hdepth)
                (skipField3_thirtyTwoBit_ok hFromCall d hdepth)))))
    refine subroutine_ok_skipField3_imp (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem skipField3_at_depth_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A depth (fun _ => True)) := by
  induction depth with
  | zero => exact skipField3_depth_zero_placed_ok hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipField3_or (skipField3_varint_placed_ok hVarintCall d hdepth)
        (subroutine_ok_skipField3_or (skipField3_sixtyFourBit_placed_ok hFromCall d hdepth)
          (subroutine_ok_skipField3_or (skipField3_lengthDelimited_placed_ok hFromCall hVarintCall d hdepth)
            (subroutine_ok_skipField3_or (skipField3_startGroup_placed_ok hFromCall hVarintCall d hdepth hrec)
              (subroutine_ok_skipField3_or (skipField3_endGroup_placed_ok hFromCall d hdepth)
                (skipField3_thirtyTwoBit_placed_ok hFromCall d hdepth)))))
    refine subroutine_ok_skipField3_imp (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem skipField3SpecAt_reaches_outcome_eq (prog : Program) (A : RustAlloc)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (R : SepProp) (s0 : State) :
    reaches_outcome prog (skipField3SpecAt A x.depth P) x R s0 s0 =
      reaches_outcome prog (skipField3Spec A) x R s0 s0 :=
  reaches_outcome_eq_of_parts_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

theorem subroutine_ok_skipField3Spec_of_at_depth {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : ∀ depth, depth < 2 ^ 32 → subroutine_ok prog entry (skipField3SpecAt A depth (fun _ => True))) :
    subroutine_ok prog entry (skipField3Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

theorem skipField3_add_from_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64 =
      (libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName := by
  have h1 := libsignalSessionCode_fnOff_0x4677c
  have h2 : libsignalSessionCode.fnOff decodeErrorFromName = 0x459a8 := libsignalSessionCode_fnOff_0x459a8
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff skipField3Name)) + 0xfffffffffffff22c#64 =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff decodeErrorFromName)
  rw [h1, h2]
  bv_omega

theorem skipField3_ok_of_contracts {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 0xfffffffffffff22c#64)
      (decodeErrorFromSpec A))
    (hVarint : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarint2Name)
      (decodeVarint2Spec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3Spec A) := by
  have hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name + 6488#64)
      (decodeVarint2Spec A) := by
    rw [fnAddr_rebase_offset libsignalSessionCode_fnOff_0x4677c libsignalSessionCode_fnOff_0x480d4 (by decide)]
    exact hVarint
  exact subroutine_ok_skipField3Spec_of_at_depth
    (skipField3_at_depth_ok hFromCall hVarintCall)

theorem skipField3_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A)) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (blkPl_263).base (skipField3Spec A) :=
  subroutine_ok_skipField3Spec_of_at_depth
    (skipField3_at_depth_placed_ok hFromCall hVarintCall)

theorem skipField3_ok_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr skipField3Name)
      (skipField3Spec A) := by
  refine skipField3_ok_of_contracts ?_ (decodeVarint2_ok_ext hC)
  rw [skipField3_add_from_eq_fnAddr]
  exact hC.decode_error_from

theorem skipField3_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hFrom : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr skipField3Name)
      (skipField3Spec A) := by
  refine skipField3_ok_of_contracts ?_ (decodeVarint2_ok hFrom)
  rw [skipField3_add_from_eq_fnAddr]
  exact LibsignalTripleRatchet.decodeErrorFrom_ok b C A ctl abs hFrom

end CryptoVerification.SpqrV1.Varint
