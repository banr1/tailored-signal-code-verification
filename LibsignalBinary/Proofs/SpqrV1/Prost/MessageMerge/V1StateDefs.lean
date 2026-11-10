/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateFetch
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefs
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommon
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
import ProofLib.SepLogic.WPp

/-!
# Definitions, Stack Splits, and Capacity Invariants for `V1State::merge` (`0x4e7e8`)

Defines the `.rodata` jump table (`0x8240c`), stack frame layout (`14,640` bytes),
capacity-bounded `Option<V1State.InnerState>` separation-logic representation, pure
`InnerStatePolyBound` preservation lemmas, and Hoare specifications for `V1State::merge`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

macro "v1StateMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateMergeBin $b $H
    CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateMerge_fnOff 0x493f0 $k0 $len)

/-! ## 1. `.rodata` Jump Table for `V1State::merge` (`0x4e7e8`) at `0x8240c` -/

def v1StateMergeJumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_bytes% "0042202c094c5836701464")) ↦₈ᵣ 0#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 1)) ↦₈ᵣ 66#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 2)) ↦₈ᵣ 32#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 3)) ↦₈ᵣ 44#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 4)) ↦₈ᵣ 9#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 5)) ↦₈ᵣ 76#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 6)) ↦₈ᵣ 88#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 7)) ↦₈ᵣ 54#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 8)) ↦₈ᵣ 112#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 9)) ↦₈ᵣ 20#8) ∗
    ((b + bv% (ls_bytes% "0042202c094c5836701464" + 10)) ↦₈ᵣ 100#8)

theorem v1StateMergeJumpTableAt_eq_expanded (b : BitVec 64) :
    v1StateMergeJumpTableAt b = v1StateMergeJumpTableExpanded b := by
  unfold v1StateMergeJumpTableAt v1StateMergeJumpTableBytes v1StateMergeJumpTableExpanded
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

def v1StateMergeJumpTablePlacedExpanded [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ v1StateMergeJumpTableSym) ↦₈ᵣ 0#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 1#64) ↦₈ᵣ 66#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 2#64) ↦₈ᵣ 32#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 3#64) ↦₈ᵣ 44#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 4#64) ↦₈ᵣ 9#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 5#64) ↦₈ᵣ 76#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 6#64) ↦₈ᵣ 88#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 7#64) ↦₈ᵣ 54#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 8#64) ↦₈ᵣ 112#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 9#64) ↦₈ᵣ 20#8) ∗
    ((lsmpl.ρ v1StateMergeJumpTableSym + 10#64) ↦₈ᵣ 100#8)

theorem v1StateMergeJumpTablePlacedAt_eq_expanded [LibsignalPlacement] :
    v1StateMergeJumpTablePlacedAt = v1StateMergeJumpTablePlacedExpanded := by
  unfold v1StateMergeJumpTablePlacedAt v1StateMergeJumpTableBytes v1StateMergeJumpTablePlacedExpanded
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem rodata_v1StateMergeJumpTablePlaced [LibsignalPlacement]
    {s : State} (hro : LibsignalRoLoaded lsmpl s.mem) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ v1StateMergeJumpTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

theorem rodata_v1StateMergeJumpTablePlacedExpanded [LibsignalPlacement]
    {s : State} (hro : LibsignalRoLoaded lsmpl s.mem) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ v1StateMergeJumpTablePlacedExpanded ∗ P := by
  rw [← v1StateMergeJumpTablePlacedAt_eq_expanded]
  exact rodata_v1StateMergeJumpTablePlaced hro hP

/-- `.rodata` slice at `0x8240c` (`11` bytes): `v1StateMergeJumpTableBytes`. -/
theorem rodata_v1StateMergeJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ v1StateMergeJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0042202c094c5836701464")) (n := 11) (bs := v1StateMergeJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_v1StateMergeJumpTableExpanded {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ v1StateMergeJumpTableExpanded img.base ∗ P := by
  rw [← v1StateMergeJumpTableAt_eq_expanded]
  exact rodata_v1StateMergeJumpTable himg hF hP

/-! ## 2. Stack Frame Sizes (`v1StateMergeStack = 816 + chunkedInlStack`) -/

/-- Own stack frame of `V1State::merge` (`0x4e7e8`): `816` bytes (`0x330`),
    plus `chunkedInlStack` (`13,824` bytes) for callees (`14,640` bytes total). -/
abbrev v1StateMergeStack : Nat := 816 + chunkedInlStack

/-- Saved callee-saved registers at `[s0.sp - 96, s0.sp)` (`x29 = s0.sp - 96 = sp + 720`). -/
def v1StateSavedRegsAt (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_v1StateMerge_prologue (sp : BitVec 64) :
    stackAt sp v1StateMergeStack =
      stackAt (sp - 816#64) chunkedInlStack ∗ memRegion (sp - 816#64) 720 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
        ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp (720 + chunkedInlStack) 12 (by decide)
  change stackAt sp v1StateMergeStack = stackAt (sp - 96#64) (720 + chunkedInlStack) ∗ cells (sp - 96#64) 12 at h1
  have h2 := memRegion_split' (b := sp - 96#64 - BitVec.ofNat 64 (720 + chunkedInlStack))
    (b' := sp - 816#64) (n := chunkedInlStack) (k := 720) (N := 720 + chunkedInlStack) (by decide) (by bv_omega) (by decide)
  have h2_addr : sp - 96#64 - BitVec.ofNat 64 (720 + chunkedInlStack) = sp - 816#64 - BitVec.ofNat 64 chunkedInlStack := by bv_omega
  change stackAt (sp - 96#64) (720 + chunkedInlStack) = _ at h2; rw [h2_addr] at h2
  change stackAt (sp - 96#64) (720 + chunkedInlStack) = stackAt (sp - 816#64) chunkedInlStack ∗ memRegion (sp - 816#64) 720 at h2
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
        ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by cells_unfold
  rw [h1, h2, hc12]; ac_rfl

theorem stackAt_v1StateMerge_epilogue (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 816#64) chunkedInlStack ∗
      memRegion (sp - 816#64) 720 ∗ v1StateSavedRegsAt sp s0 ⊢
    stackAt sp v1StateMergeStack := by
  rw [stackAt_v1StateMerge_prologue]
  refine sepConj_mono_right (sepConj_mono_right ?_); unfold v1StateSavedRegsAt
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x29))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x30))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x28))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x27))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x26))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x25))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x24))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x23))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x22))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x21))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x20))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x19))
  exact Entails.refl _

theorem memRegion_720_split (sp : BitVec 64) :
    memRegion sp 720 =
      (∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64,
        (sp ↦₆₄ v0) ∗ ((sp + 8#64) ↦₆₄ v8) ∗
        memRegion (sp + 16#64) 224 ∗
        memRegion (sp + 240#64) 224 ∗
        memRegion (sp + 464#64) 16 ∗
        memRegion (sp + 480#64) 224 ∗
        memRegion (sp + 704#64) 16) := by
  have h1 := memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := 712) (N := 720) rfl rfl (by decide)
  have h2 := memRegion_split' (b := sp + 8#64) (b' := sp + 16#64) (n := 8) (k := 704) (N := 712) rfl (by bv_omega) (by decide)
  have h3 := memRegion_split' (b := sp + 16#64) (b' := sp + 240#64) (n := 224) (k := 480) (N := 704) rfl (by bv_omega) (by decide)
  have h4 := memRegion_split' (b := sp + 240#64) (b' := sp + 464#64) (n := 224) (k := 256) (N := 480) rfl (by bv_omega) (by decide)
  have h5 := memRegion_split' (b := sp + 464#64) (b' := sp + 480#64) (n := 16) (k := 240) (N := 256) rfl (by bv_omega) (by decide)
  have h6 := memRegion_split' (b := sp + 480#64) (b' := sp + 704#64) (n := 224) (k := 16) (N := 240) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3, h4, h5, h6, Prost.memRegion_eight sp, sepExists_sepConj_left]
  congr 1; funext v0
  rw [Prost.memRegion_eight (sp + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_720_join (sp : BitVec 64) (v0 v8 : BitVec 64) :
    (sp ↦₆₄ v0) ∗ ((sp + 8#64) ↦₆₄ v8) ∗
      memRegion (sp + 16#64) 224 ∗
      memRegion (sp + 240#64) 224 ∗
      memRegion (sp + 464#64) 16 ∗
      memRegion (sp + 480#64) 224 ∗
      memRegion (sp + 704#64) 16 ⊢
    memRegion sp 720 := by
  rw [memRegion_720_split sp]
  refine Entails.trans ?_ (Entails.sepExists_intro v0)
  refine Entails.trans ?_ (Entails.sepExists_intro v8)
  exact Entails.refl _

/-! ## 3. Callee Stack Splits from `stackAt sp chunkedInlStack` (`13,824` bytes) -/

abbrev v1StateBelowRest (sp : BitVec 64) (subStack : Nat) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 chunkedInlStack) (chunkedInlStack - subStack)

private theorem bv_sub_add_cancel_v1 (sp u w : BitVec 64) :
    sp - w = sp - (u + w) + u := by bv_omega

theorem v1StateBelow_split (sp : BitVec 64) (subStack : Nat) (hle : subStack ≤ chunkedInlStack) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp subStack ∗ stackAt sp subStack := by
  simp only [v1StateBelowRest, stackAt]
  have hlen : chunkedInlStack = (chunkedInlStack - subStack) + subStack := by omega
  have hbound : chunkedInlStack ≤ 2 ^ 64 := by
    simp only [chunkedInlStack, chunkedInlBelowStack, skipField3Stack, decodeVarint2Stack,
      decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]; omega
  have hbit : BitVec.ofNat 64 chunkedInlStack =
      BitVec.ofNat 64 (chunkedInlStack - subStack) + BitVec.ofNat 64 subStack := by
    rw [← BitVec.ofNat_add, ← hlen]
  exact memRegion_split' (b := sp - BitVec.ofNat 64 chunkedInlStack)
    (b' := sp - BitVec.ofNat 64 subStack) (n := chunkedInlStack - subStack) (k := subStack)
    (N := chunkedInlStack) hlen (by rw [hbit]; exact bv_sub_add_cancel_v1 sp _ _) hbound

theorem v1StateBelow_entails (sp : BitVec 64) (subStack : Nat) (hle : subStack ≤ chunkedInlStack) :
    v1StateBelowRest sp subStack ∗ stackAt sp subStack ⊢
      stackAt sp chunkedInlStack :=
  Entails.of_eq (v1StateBelow_split sp subStack hle).symm

theorem stackAt_chunkedInl_eq_chunkedMerge (sp : BitVec 64) :
    stackAt sp chunkedInlStack = stackAt sp chunkedMergeStack := rfl

theorem v1StateBelow_skipField99 (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp (skipField3Stack 99) ∗ stackAt sp (skipField3Stack 99) :=
  v1StateBelow_split sp (skipField3Stack 99) (by decide)

theorem v1StateBelow_skipField99_entails (sp : BitVec 64) :
    v1StateBelowRest sp (skipField3Stack 99) ∗ stackAt sp (skipField3Stack 99) ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp (skipField3Stack 99) (by decide)

theorem v1StateBelow_dropStack96 (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp dropStack96 ∗ stackAt sp dropStack96 :=
  v1StateBelow_split sp dropStack96 (by decide)

theorem v1StateBelow_dropStack96_entails (sp : BitVec 64) :
    v1StateBelowRest sp dropStack96 ∗ stackAt sp dropStack96 ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp dropStack96 (by decide)

theorem v1StateBelow_dropStack80 (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp dropStack80 ∗ stackAt sp dropStack80 :=
  v1StateBelow_split sp dropStack80 (by decide)

theorem v1StateBelow_dropStack80_entails (sp : BitVec 64) :
    v1StateBelowRest sp dropStack80 ∗ stackAt sp dropStack80 ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp dropStack80 (by decide)

theorem v1StateBelow_dropStack48 (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp dropStack48 ∗ stackAt sp dropStack48 :=
  v1StateBelow_split sp dropStack48 (by decide)

theorem v1StateBelow_dropStack48_entails (sp : BitVec 64) :
    v1StateBelowRest sp dropStack48 ∗ stackAt sp dropStack48 ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp dropStack48 (by decide)

theorem v1StateBelow_dropStack32 (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp dropStack32 ∗ stackAt sp dropStack32 :=
  v1StateBelow_split sp dropStack32 (by decide)

theorem v1StateBelow_dropStack32_entails (sp : BitVec 64) :
    v1StateBelowRest sp dropStack32 ∗ stackAt sp dropStack32 ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp dropStack32 (by decide)

theorem v1StateBelow_decodeVarint2 (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp decodeVarint2Stack ∗ stackAt sp decodeVarint2Stack :=
  v1StateBelow_split sp decodeVarint2Stack (by decide)

theorem v1StateBelow_decodeVarint2_entails (sp : BitVec 64) :
    v1StateBelowRest sp decodeVarint2Stack ∗ stackAt sp decodeVarint2Stack ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp decodeVarint2Stack (by decide)

theorem v1StateBelow_decodeError (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp decodeErrorHookStack ∗ stackAt sp decodeErrorHookStack :=
  v1StateBelow_split sp decodeErrorHookStack (by decide)

theorem v1StateBelow_decodeError_entails (sp : BitVec 64) :
    v1StateBelowRest sp decodeErrorHookStack ∗ stackAt sp decodeErrorHookStack ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp decodeErrorHookStack (by decide)

theorem v1StateBelow_allocHook (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      v1StateBelowRest sp allocHookStack ∗ stackAt sp allocHookStack :=
  v1StateBelow_split sp allocHookStack (by decide)

theorem v1StateBelow_allocHook_entails (sp : BitVec 64) :
    v1StateBelowRest sp allocHookStack ∗ stackAt sp allocHookStack ⊢
      stackAt sp chunkedInlStack :=
  v1StateBelow_entails sp allocHookStack (by decide)

/-! ## 4. Capacity-Bounded `V1State` Representation (`protoInnerStateCapAt` & `optProtoInnerStateCapAt`) -/

/-- Pure `OptPolyEncoderBound` / `OptPolyDecoderBound` invariant for `V1State.InnerState` at remaining input length `bsLen`. -/
def InnerStatePolyBound (bsLen : Nat) : V1State.InnerState → Prop
  | .keysUnsampled _ => bsLen < 2 ^ 56
  | .keysSampled s => OptPolyEncoderBound s.sendingHdr bsLen
  | .headerSent s => OptPolyEncoderBound s.sendingEk bsLen ∧ OptPolyDecoderBound s.receivingCt1 bsLen
  | .ct1Received s => OptPolyEncoderBound s.sendingEk bsLen
  | .ekSentCt1Received s => OptPolyDecoderBound s.receivingCt2 bsLen
  | .noHeaderReceived s => OptPolyDecoderBound s.receivingHdr bsLen
  | .headerReceived s => OptPolyDecoderBound s.receivingEk bsLen
  | .ct1Sampled s => OptPolyEncoderBound s.sendingCt1 bsLen ∧ OptPolyDecoderBound s.receivingEk bsLen
  | .ekReceivedCt1Sampled s => OptPolyEncoderBound s.sendingCt1 bsLen
  | .ct1Acknowledged s => OptPolyDecoderBound s.receivingEk bsLen
  | .ct2Sampled s => OptPolyEncoderBound s.sendingCt2 bsLen

def OptInnerStatePolyBound (bsLen : Nat) : Option V1State.InnerState → Prop
  | none => bsLen < 2 ^ 56
  | some st => InnerStatePolyBound bsLen st

theorem optInnerStatePolyBound_lt_2_56 {n : Nat} {opt : Option V1State.InnerState}
    (h : OptInnerStatePolyBound n opt) : n < 2 ^ 56 := by
  rcases opt with _ | st
  · exact h
  · cases st <;> (unfold OptInnerStatePolyBound InnerStatePolyBound OptPolyEncoderBound OptPolyDecoderBound at h; omega)

theorem innerStatePolyBound_mono {st : V1State.InnerState} {m n : Nat}
    (h : InnerStatePolyBound n st) (hle : m ≤ n) :
    InnerStatePolyBound m st := by
  cases st with
  | keysUnsampled _ => unfold InnerStatePolyBound at h ⊢; omega
  | keysSampled s => exact optPolyEncoderBound_mono h hle
  | headerSent s => exact ⟨optPolyEncoderBound_mono h.1 hle, optPolyDecoderBound_mono h.2 hle⟩
  | ct1Received s => exact optPolyEncoderBound_mono h hle
  | ekSentCt1Received s => exact optPolyDecoderBound_mono h hle
  | noHeaderReceived s => exact optPolyDecoderBound_mono h hle
  | headerReceived s => exact optPolyDecoderBound_mono h hle
  | ct1Sampled s => exact ⟨optPolyEncoderBound_mono h.1 hle, optPolyDecoderBound_mono h.2 hle⟩
  | ekReceivedCt1Sampled s => exact optPolyEncoderBound_mono h hle
  | ct1Acknowledged s => exact optPolyDecoderBound_mono h hle
  | ct2Sampled s => exact optPolyEncoderBound_mono h hle

theorem optInnerStatePolyBound_mono {opt : Option V1State.InnerState} {m n : Nat}
    (h : OptInnerStatePolyBound n opt) (hle : m ≤ n) :
    OptInnerStatePolyBound m opt := by
  cases opt with
  | none => unfold OptInnerStatePolyBound at h ⊢; omega
  | some st => exact innerStatePolyBound_mono h hle

/-- Capacity-bounded representation predicate for `spqr::proto::pq_ratchet::v1_state::InnerState` (`224`B). -/
def protoInnerStateCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) : V1State.InnerState → SepProp
  | .keysUnsampled s =>
      (a ↦₆₄ 0x8000000000000000#64) ∗
      chunkedKeysUnsampledPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 64#64) 160
  | .keysSampled s =>
      (a ↦₆₄ 0x8000000000000001#64) ∗
      chunkedKeysSampledPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 168#64) 56
  | .headerSent s =>
      (a ↦₆₄ 0x8000000000000002#64) ∗
      chunkedHeaderSentPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 184#64) 40
  | .ct1Received s =>
      (a ↦₆₄ 0x8000000000000003#64) ∗
      chunkedCt1ReceivedPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 168#64) 56
  | .ekSentCt1Received s =>
      (a ↦₆₄ 0x8000000000000004#64) ∗
      chunkedEkSentCt1ReceivedPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 152#64) 72
  | .noHeaderReceived s =>
      (a ↦₆₄ 0x8000000000000005#64) ∗
      chunkedNoHeaderReceivedPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 104#64) 120
  | .headerReceived s =>
      (a ↦₆₄ 0x8000000000000006#64) ∗
      chunkedHeaderReceivedPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 128#64) 96
  | .ct1Sampled s =>
      chunkedCt1SampledPBCapAt A a bsLen s
  | .ekReceivedCt1Sampled s =>
      (a ↦₆₄ 0x8000000000000008#64) ∗
      chunkedEkReceivedCt1SampledPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 192#64) 32
  | .ct1Acknowledged s =>
      (a ↦₆₄ 0x8000000000000009#64) ∗
      chunkedCt1AcknowledgedPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 176#64) 48
  | .ct2Sampled s =>
      (a ↦₆₄ 0x800000000000000a#64) ∗
      chunkedCt2SampledPBCapAt A (a + 8#64) bsLen s ∗
      memRegion (a + 120#64) 104

/-- Capacity-bounded representation predicate for `Option<V1State.InnerState>` (`224`B). -/
def optProtoInnerStateCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.InnerState → SepProp
  | none => (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216
  | some st => protoInnerStateCapAt A a bsLen st

theorem protoInnerStateCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (st : V1State.InnerState) {m n : Nat} (hle : m ≤ n) :
    protoInnerStateCapAt A a n st ⊢ protoInnerStateCapAt A a m st := by
  cases st with
  | keysUnsampled s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedKeysUnsampledPBCapAt_mono A (a + 8#64) s hle))
  | keysSampled s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedKeysSampledPBCapAt_mono A (a + 8#64) s hle))
  | headerSent s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedHeaderSentPBCapAt_mono A (a + 8#64) s hle))
  | ct1Received s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedCt1ReceivedPBCapAt_mono A (a + 8#64) s hle))
  | ekSentCt1Received s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedEkSentCt1ReceivedPBCapAt_mono A (a + 8#64) s hle))
  | noHeaderReceived s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedNoHeaderReceivedPBCapAt_mono A (a + 8#64) s hle))
  | headerReceived s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedHeaderReceivedPBCapAt_mono A (a + 8#64) s hle))
  | ct1Sampled s =>
    exact chunkedCt1SampledPBCapAt_mono A a s hle
  | ekReceivedCt1Sampled s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedEkReceivedCt1SampledPBCapAt_mono A (a + 8#64) s hle))
  | ct1Acknowledged s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedCt1AcknowledgedPBCapAt_mono A (a + 8#64) s hle))
  | ct2Sampled s =>
    exact sepConj_mono_right (sepConj_mono_left (chunkedCt2SampledPBCapAt_mono A (a + 8#64) s hle))

theorem optProtoInnerStateCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) {m n : Nat} (hle : m ≤ n) :
    optProtoInnerStateCapAt A a n opt ⊢ optProtoInnerStateCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some st => exact protoInnerStateCapAt_mono A a st hle

theorem optPolynomialEncoderPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBAt A a opt =
      optProtoPolynomialEncoderAt A a (opt.map pbToProtoPolyEncoder) := by
  cases opt <;> rfl

theorem optPolynomialDecoderPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBAt A a opt =
      optProtoPolynomialDecoderAt A a (opt.map pbToProtoPolyDecoder) := by
  cases opt <;> rfl

theorem chunkedKeysUnsampledPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.KeysUnsampled) :
    chunkedKeysUnsampledPBAt A a s = protoChunkedKeysUnsampledAt A a s := by
  cases s.uc <;> rfl

theorem chunkedKeysSampledPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.KeysSampled) :
    chunkedKeysSampledPBAt A a s = protoChunkedKeysSampledAt A a s := by
  unfold chunkedKeysSampledPBAt protoChunkedKeysSampledAt
  rw [optPolynomialEncoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedHeaderSentPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBAt A a s = protoChunkedHeaderSentAt A a s := by
  unfold chunkedHeaderSentPBAt protoChunkedHeaderSentAt
  rw [optPolynomialEncoderPBAt_eq_proto, optPolynomialDecoderPBAt_eq_proto]
  cases s.uc <;> rfl

theorem chunkedCt1ReceivedPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.Ct1Received) :
    chunkedCt1ReceivedPBAt A a s = protoChunkedCt1ReceivedAt A a s := by
  unfold chunkedCt1ReceivedPBAt protoChunkedCt1ReceivedAt
  rw [optPolynomialEncoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedEkSentCt1ReceivedPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.EkSentCt1Received) :
    chunkedEkSentCt1ReceivedPBAt A a s = protoChunkedEkSentCt1ReceivedAt A a s := by
  unfold chunkedEkSentCt1ReceivedPBAt protoChunkedEkSentCt1ReceivedAt
  rw [optPolynomialDecoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedNoHeaderReceivedPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.NoHeaderReceived) :
    chunkedNoHeaderReceivedPBAt A a s = protoChunkedNoHeaderReceivedAt A a s := by
  unfold chunkedNoHeaderReceivedPBAt protoChunkedNoHeaderReceivedAt
  rw [optPolynomialDecoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedHeaderReceivedPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.HeaderReceived) :
    chunkedHeaderReceivedPBAt A a s = protoChunkedHeaderReceivedAt A a s := by
  unfold chunkedHeaderReceivedPBAt protoChunkedHeaderReceivedAt
  rw [optPolynomialDecoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedCt1SampledPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) :
    chunkedCt1SampledPBAt A a s = protoChunkedCt1SampledAt A a s := by
  unfold chunkedCt1SampledPBAt protoChunkedCt1SampledAt
  rw [optPolynomialEncoderPBAt_eq_proto, optPolynomialDecoderPBAt_eq_proto]
  cases s.uc <;> rfl

theorem chunkedEkReceivedCt1SampledPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.EkReceivedCt1Sampled) :
    chunkedEkReceivedCt1SampledPBAt A a s = protoChunkedEkReceivedCt1SampledAt A a s := by
  unfold chunkedEkReceivedCt1SampledPBAt protoChunkedEkReceivedCt1SampledAt
  rw [optPolynomialEncoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedCt1AcknowledgedPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.Ct1Acknowledged) :
    chunkedCt1AcknowledgedPBAt A a s = protoChunkedCt1AcknowledgedAt A a s := by
  unfold chunkedCt1AcknowledgedPBAt protoChunkedCt1AcknowledgedAt
  rw [optPolynomialDecoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem chunkedCt2SampledPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.Ct2Sampled) :
    chunkedCt2SampledPBAt A a s = protoChunkedCt2SampledAt A a s := by
  unfold chunkedCt2SampledPBAt protoChunkedCt2SampledAt
  rw [optPolynomialEncoderPBAt_eq_proto]; cases s.uc <;> rfl

theorem protoInnerStateCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (st : V1State.InnerState) :
    protoInnerStateCapAt A a n st ⊢ protoInnerStateAt A a st := by
  cases st with
  | keysUnsampled s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedKeysUnsampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedKeysUnsampledPBCapAt_entails_pb A (a + 8#64) n s))
  | keysSampled s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedKeysSampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedKeysSampledPBCapAt_entails_pb A (a + 8#64) n s))
  | headerSent s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedHeaderSentPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedHeaderSentPBCapAt_entails_pb A (a + 8#64) n s))
  | ct1Received s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedCt1ReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedCt1ReceivedPBCapAt_entails_pb A (a + 8#64) n s))
  | ekSentCt1Received s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedEkSentCt1ReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedEkSentCt1ReceivedPBCapAt_entails_pb A (a + 8#64) n s))
  | noHeaderReceived s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedNoHeaderReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedNoHeaderReceivedPBCapAt_entails_pb A (a + 8#64) n s))
  | headerReceived s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedHeaderReceivedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedHeaderReceivedPBCapAt_entails_pb A (a + 8#64) n s))
  | ct1Sampled s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedCt1SampledPBAt_eq_proto]
    exact chunkedCt1SampledPBCapAt_entails_pb A a n s
  | ekReceivedCt1Sampled s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedEkReceivedCt1SampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A (a + 8#64) n s))
  | ct1Acknowledged s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedCt1AcknowledgedPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedCt1AcknowledgedPBCapAt_entails_pb A (a + 8#64) n s))
  | ct2Sampled s =>
    unfold protoInnerStateCapAt protoInnerStateAt; dsimp only; rw [← chunkedCt2SampledPBAt_eq_proto]
    exact sepConj_mono_right (sepConj_mono_left (chunkedCt2SampledPBCapAt_entails_pb A (a + 8#64) n s))

theorem optProtoInnerStateCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapAt A a n opt ⊢ optProtoInnerStateAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some st => exact protoInnerStateCapAt_entails_pb A a n st

theorem optProtoInnerStateAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) :
    optProtoInnerStateAt A a opt ⊢ ∃∗ opt' : Option V1State.InnerState, optProtoInnerStateAt A a opt' :=
  Entails.sepExists_intro opt

/-! ## 5. Preservation of `InnerStatePolyBound` Across `Proto.mergeMessage` -/

theorem mergeFieldsLoop_measure_le {M : Type}
    (mf : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (f : M → Nat)
    (hstep : ∀ {m m' : M} {tag : BitVec 32} {wt : Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat},
      mf m tag wt r1 depth = .ok (m', r2) → f m' + r2.length ≤ f m + r1.length)
    (fuel : Nat) :
    ∀ {m m' : M} {s : List (BitVec 8)} {depth : Nat},
      Proto.mergeFieldsLoop mf fuel m s depth = .ok m' →
      f m' ≤ f m + s.length := by
  induction fuel with
  | zero =>
    intro m m' s depth h
    cases s with
    | nil => cases h; omega
    | cons _ _ => nomatch h
  | succ fuel ih =>
    intro m m' s depth h
    cases s with
    | nil => cases h; omega
    | cons b tl =>
      simp only [Proto.mergeFieldsLoop, Bind.bind, Except.bind] at h
      rcases hdk : Proto.decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, r1⟩
      · rw [hdk] at h; nomatch h
      · rw [hdk] at h; dsimp only at h
        have hlt1 : r1.length < (b :: tl).length :=
          (proto_decodeKey_suffix (by rw [hdk]; rfl)).1
        rcases hmf : mf m tag wt r1 depth with _ | ⟨m1, r2⟩
        · rw [hmf] at h; nomatch h
        · rw [hmf] at h; dsimp only at h
          have hs := hstep hmf
          have hih := ih h
          omega

theorem mergeMessage_measure_lt {M : Type}
    (mf : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (f : M → Nat)
    (hstep : ∀ {m m' : M} {tag : BitVec 32} {wt : Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat},
      mf m tag wt r1 depth = .ok (m', r2) → f m' + r2.length ≤ f m + r1.length)
    {wt : Proto.WireType} {m m' : M} {bs after : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeMessage mf wt m bs depth).toOption = some (m', after)) :
    f m' + after.length < f m + bs.length := by
  cases depth with
  | zero =>
    rcases hcw : Proto.checkWireType .lengthDelimited wt with _ | ⟨⟩ <;>
      simp [Proto.mergeMessage, hcw, Bind.bind, Except.bind, Except.toOption] at h
  | succ depth' =>
    simp only [Proto.mergeMessage, Bind.bind, Except.bind] at h
    rcases hcw : Proto.checkWireType .lengthDelimited wt with _ | ⟨⟩
    · simp [hcw, Except.toOption] at h
    · simp only [hcw] at h
      rcases hdv : Proto.decodeVarint bs with _ | ⟨len, r0⟩
      · simp [hdv, Except.toOption] at h
      · simp only [hdv] at h
        have hlt0 : r0.length < bs.length := (proto_decodeVarint_suffix (by rw [hdv]; rfl)).1
        rcases hte : Proto.takeExact len.toNat r0 with _ | ⟨sub, after'⟩
        · simp [hte, Except.toOption] at h
        · simp only [hte] at h
          rcases hloop : Proto.mergeFieldsLoop mf sub.length m sub depth' with _ | m2
          · simp [hloop, Except.toOption] at h
          · simp only [hloop, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hfl := mergeFieldsLoop_measure_le mf f hstep _ hloop
            rw [takeExact_eq_take_drop] at hte
            split at hte
            · rename_i hlen_le
              injection hte with hpair; injection hpair with hsub hafter; subst hsub hafter
              rw [List.length_take_of_le hlen_le] at hfl
              rw [List.length_drop]
              omega
            · nomatch hte

private theorem mergeOptPolyDecoder_pts_le {opt v : Option PolynomialDecoder}
    {wt : Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat}
    (h : Proto.mergeOptMessage PolynomialDecoder.mergeField wt opt r1 depth = .ok (v, r2)) :
    optPolyDecoderPtsLen v + r2.length ≤ optPolyDecoderPtsLen opt + r1.length := by
  unfold Proto.mergeOptMessage at h
  rcases hm : Proto.mergeMessage PolynomialDecoder.mergeField wt (opt.getD default) r1 depth with _ | ⟨d, r2'⟩
  · simp [hm, Bind.bind, Except.bind] at h
  · simp only [hm, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hlt := polyDecoder_mergeMessage_pts_len (show (Proto.mergeMessage PolynomialDecoder.mergeField wt (opt.getD default) r1 depth).toOption = some (d, r2') by rw [hm]; rfl)
    rw [optPolyDecoder_getD_default_pts_len] at hlt
    change d.pts.length + r2'.length ≤ optPolyDecoderPtsLen opt + r1.length
    omega

private theorem mergeOptPolyEncoder_pts_polys_le {opt v : Option PolynomialEncoder}
    {wt : Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat}
    (h : Proto.mergeOptMessage PolynomialEncoder.mergeField wt opt r1 depth = .ok (v, r2)) :
    optPolyEncoderPtsLen v + r2.length ≤ optPolyEncoderPtsLen opt + r1.length ∧
      optPolyEncoderPolysLen v + r2.length ≤ optPolyEncoderPolysLen opt + r1.length := by
  unfold Proto.mergeOptMessage at h
  rcases hm : Proto.mergeMessage PolynomialEncoder.mergeField wt (opt.getD default) r1 depth with _ | ⟨e, r2'⟩
  · simp [hm, Bind.bind, Except.bind] at h
  · simp only [hm, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨hlt1, hlt2⟩ := polyEncoder_mergeMessage_pts_polys_len (show (Proto.mergeMessage PolynomialEncoder.mergeField wt (opt.getD default) r1 depth).toOption = some (e, r2') by rw [hm]; rfl)
    rw [optPolyEncoder_getD_default_pts_len] at hlt1
    rw [optPolyEncoder_getD_default_polys_len] at hlt2
    change e.pts.length + r2'.length ≤ optPolyEncoderPtsLen opt + r1.length ∧
      e.polys.length + r2'.length ≤ optPolyEncoderPolysLen opt + r1.length
    exact ⟨by omega, by omega⟩

theorem optPolyDecoderBound_iff (opt : Option PolynomialDecoder) (n : Nat) :
    OptPolyDecoderBound opt n ↔ optPolyDecoderPtsLen opt + n < 2 ^ 56 := by
  unfold OptPolyDecoderBound; rw [optPolyDecoder_getD_default_pts_len]

theorem optPolyEncoderBound_iff (opt : Option PolynomialEncoder) (n : Nat) :
    OptPolyEncoderBound opt n ↔ optPolyEncoderPtsLen opt + n < 2 ^ 56 ∧ optPolyEncoderPolysLen opt + n < 2 ^ 56 := by
  unfold OptPolyEncoderBound; rw [optPolyEncoder_getD_default_pts_len, optPolyEncoder_getD_default_polys_len]

theorem optPolyDecoderBound_of_chunked_merge {M : Type}
    (mf : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (getDec : M → Option PolynomialDecoder)
    (hstep : ∀ {m m' : M} {tag : BitVec 32} {wt : Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat},
      mf m tag wt r1 depth = .ok (m', r2) →
      (getDec m' = getDec m ∧ r2.length ≤ r1.length) ∨
      Proto.mergeOptMessage PolynomialDecoder.mergeField wt (getDec m) r1 depth = .ok (getDec m', r2))
    {wt : Proto.WireType} {m m' : M} {bs after : List (BitVec 8)} {depth : Nat}
    (hb : OptPolyDecoderBound (getDec m) bs.length)
    (hm : (Proto.mergeMessage mf wt m bs depth).toOption = some (m', after)) :
    OptPolyDecoderBound (getDec m') after.length := by
  rw [optPolyDecoderBound_iff] at hb ⊢
  have hlt := mergeMessage_measure_lt mf (fun x => optPolyDecoderPtsLen (getDec x))
    (fun h => by
      rcases hstep h with ⟨heq, hle⟩ | hopt
      · rw [heq]; omega
      · exact mergeOptPolyDecoder_pts_le hopt) hm
  omega

theorem optPolyEncoderBound_of_chunked_merge {M : Type}
    (mf : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (getEnc : M → Option PolynomialEncoder)
    (hstep : ∀ {m m' : M} {tag : BitVec 32} {wt : Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat},
      mf m tag wt r1 depth = .ok (m', r2) →
      (getEnc m' = getEnc m ∧ r2.length ≤ r1.length) ∨
      Proto.mergeOptMessage PolynomialEncoder.mergeField wt (getEnc m) r1 depth = .ok (getEnc m', r2))
    {wt : Proto.WireType} {m m' : M} {bs after : List (BitVec 8)} {depth : Nat}
    (hb : OptPolyEncoderBound (getEnc m) bs.length)
    (hm : (Proto.mergeMessage mf wt m bs depth).toOption = some (m', after)) :
    OptPolyEncoderBound (getEnc m') after.length := by
  rw [optPolyEncoderBound_iff] at hb ⊢
  have hlt1 := mergeMessage_measure_lt mf (fun x => optPolyEncoderPtsLen (getEnc x))
    (fun h => by
      rcases hstep h with ⟨heq, hle⟩ | hopt
      · rw [heq]; omega
      · exact (mergeOptPolyEncoder_pts_polys_le hopt).1) hm
  have hlt2 := mergeMessage_measure_lt mf (fun x => optPolyEncoderPolysLen (getEnc x))
    (fun h => by
      rcases hstep h with ⟨heq, hle⟩ | hopt
      · rw [heq]; omega
      · exact (mergeOptPolyEncoder_pts_polys_le hopt).2) hm
  exact ⟨by omega, by omega⟩

theorem optPolyDecoderBound_none {n : Nat} (hn : n < 2 ^ 56) :
    OptPolyDecoderBound none n := by
  rw [optPolyDecoderBound_iff]; dsimp [optPolyDecoderPtsLen]; omega

theorem optPolyEncoderBound_none {n : Nat} (hn : n < 2 ^ 56) :
    OptPolyEncoderBound none n := by
  rw [optPolyEncoderBound_iff]; dsimp [optPolyEncoderPtsLen, optPolyEncoderPolysLen]; exact ⟨by omega, by omega⟩

private theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem innerStatePolyBound_of_keysUnsampled {wt : Proto.WireType}
    {m m' : V1State.Chunked.KeysUnsampled} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.keysUnsampled m))
    (hm : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.keysUnsampled m') := by
  have hlt := mergeMessage_measure_lt V1State.Chunked.KeysUnsampled.mergeField (fun _ => 0)
    (fun h => by
      have hle := (protoPrefixStep_chunked_keysUnsampled_mergeField _ _ _ _).length_le h
      omega) hm
  unfold InnerStatePolyBound at hb ⊢; omega

theorem innerStatePolyBound_of_keysSampled {wt : Proto.WireType}
    {m m' : V1State.Chunked.KeysSampled} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.keysSampled m))
    (hm : (Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.keysSampled m') := by
  refine optPolyEncoderBound_of_chunked_merge V1State.Chunked.KeysSampled.mergeField (·.sendingHdr) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_keysSampled_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.KeysSampled.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_headerSent {wt : Proto.WireType}
    {m m' : V1State.Chunked.HeaderSent} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.headerSent m))
    (hm : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.headerSent m') := by
  refine ⟨optPolyEncoderBound_of_chunked_merge V1State.Chunked.HeaderSent.mergeField (·.sendingEk) (fun h => ?_) hb.1 hm,
    optPolyDecoderBound_of_chunked_merge V1State.Chunked.HeaderSent.mergeField (·.receivingCt1) (fun h => ?_) hb.2 hm⟩
  · have hle := (protoPrefixStep_chunked_headerSent_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.HeaderSent.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
      · split at h
        · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · have hle := (protoPrefixStep_chunked_headerSent_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.HeaderSent.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
      · split at h
        · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_ct1Received {wt : Proto.WireType}
    {m m' : V1State.Chunked.Ct1Received} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.ct1Received m))
    (hm : (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.ct1Received m') := by
  refine optPolyEncoderBound_of_chunked_merge V1State.Chunked.Ct1Received.mergeField (·.sendingEk) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_ct1Received_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.Ct1Received.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_ekSentCt1Received {wt : Proto.WireType}
    {m m' : V1State.Chunked.EkSentCt1Received} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.ekSentCt1Received m))
    (hm : (Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.ekSentCt1Received m') := by
  refine optPolyDecoderBound_of_chunked_merge V1State.Chunked.EkSentCt1Received.mergeField (·.receivingCt2) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_ekSentCt1Received_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.EkSentCt1Received.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_noHeaderReceived {wt : Proto.WireType}
    {m m' : V1State.Chunked.NoHeaderReceived} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.noHeaderReceived m))
    (hm : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.noHeaderReceived m') := by
  refine optPolyDecoderBound_of_chunked_merge V1State.Chunked.NoHeaderReceived.mergeField (·.receivingHdr) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_noHeaderReceived_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.NoHeaderReceived.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_headerReceived {wt : Proto.WireType}
    {m m' : V1State.Chunked.HeaderReceived} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.headerReceived m))
    (hm : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.headerReceived m') := by
  refine optPolyDecoderBound_of_chunked_merge V1State.Chunked.HeaderReceived.mergeField (·.receivingEk) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_headerReceived_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.HeaderReceived.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_ct1Sampled {wt : Proto.WireType}
    {m m' : V1State.Chunked.Ct1Sampled} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.ct1Sampled m))
    (hm : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.ct1Sampled m') := by
  refine ⟨optPolyEncoderBound_of_chunked_merge V1State.Chunked.Ct1Sampled.mergeField (·.sendingCt1) (fun h => ?_) hb.1 hm,
    optPolyDecoderBound_of_chunked_merge V1State.Chunked.Ct1Sampled.mergeField (·.receivingEk) (fun h => ?_) hb.2 hm⟩
  · have hle := (protoPrefixStep_chunked_ct1Sampled_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.Ct1Sampled.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
      · split at h
        · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · have hle := (protoPrefixStep_chunked_ct1Sampled_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.Ct1Sampled.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
      · split at h
        · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_ekReceivedCt1Sampled {wt : Proto.WireType}
    {m m' : V1State.Chunked.EkReceivedCt1Sampled} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.ekReceivedCt1Sampled m))
    (hm : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.ekReceivedCt1Sampled m') := by
  refine optPolyEncoderBound_of_chunked_merge V1State.Chunked.EkReceivedCt1Sampled.mergeField (·.sendingCt1) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_ct1Acknowledged {wt : Proto.WireType}
    {m m' : V1State.Chunked.Ct1Acknowledged} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.ct1Acknowledged m))
    (hm : (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.ct1Acknowledged m') := by
  refine optPolyDecoderBound_of_chunked_merge V1State.Chunked.Ct1Acknowledged.mergeField (·.receivingEk) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_ct1Acknowledged_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.Ct1Acknowledged.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem innerStatePolyBound_of_ct2Sampled {wt : Proto.WireType}
    {m m' : V1State.Chunked.Ct2Sampled} {bs after : List (BitVec 8)}
    (hb : InnerStatePolyBound bs.length (.ct2Sampled m))
    (hm : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField wt m bs 99).toOption = some (m', after)) :
    InnerStatePolyBound after.length (.ct2Sampled m') := by
  refine optPolyEncoderBound_of_chunked_merge V1State.Chunked.Ct2Sampled.mergeField (·.sendingCt2) (fun h => ?_) hb hm
  have hle := (protoPrefixStep_chunked_ct2Sampled_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.Ct2Sampled.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

/-! ## 6. Pure `V1State.mergeField` Step Lemmas -/

theorem v1State_mergeField_tag1 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.keysUnsampled x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.keysUnsampled v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag2 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.keysSampled x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.keysSampled v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag3 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.headerSent x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.headerSent v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag4 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 4) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.ct1Received x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Received v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag5 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 5) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.ekSentCt1Received x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ekSentCt1Received v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag6 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 6) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.noHeaderReceived x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.noHeaderReceived v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag7 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 7) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.headerReceived x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.headerReceived v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag8 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 8) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.ct1Sampled x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Sampled v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag9 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 9) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.ekReceivedCt1Sampled x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ekReceivedCt1Sampled v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag10 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 10) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.ct1Acknowledged x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Acknowledged v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_tag11 (m : V1State) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.mergeField m (BitVec.ofNat 32 11) (codecWireTypeToProto iwt) rest depth').toOption =
      let v := match m.innerState with
        | some (.ct2Sampled x) => x
        | _ => default
      (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) v rest depth').toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct2Sampled v') }, rest')) := by
  dsimp only [V1State.mergeField, V1State.InnerState.merge]
  rcases Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) _ rest depth' with _ | ⟨v', r⟩ <;> rfl

theorem v1State_mergeField_other (m : V1State) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (h : tag = 0 ∨ 11 < tag) :
    (V1State.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  have hcond : (decide (BitVec.ofNat 32 tag ≥ 1#32) && decide (BitVec.ofNat 32 tag ≤ 11#32)) = false := by
    rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    simp only [ge_iff_le, BitVec.le_def, htag_toNat]
    change ¬ 1 ≤ tag ∨ ¬ tag ≤ 11
    omega
  unfold V1State.mergeField
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem keysSampled_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyEncoderBound (match is with | some (.keysSampled x) => x | _ => default).sendingHdr n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyEncoderBound_none hn; (cases x <;> first | exact hb | exact optPolyEncoderBound_none hn)]

theorem headerSent_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyEncoderBound (match is with | some (.headerSent x) => x | _ => default).sendingEk n ∧
      OptPolyDecoderBound (match is with | some (.headerSent x) => x | _ => default).receivingCt1 n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;>
    [exact ⟨optPolyEncoderBound_none hn, optPolyDecoderBound_none hn⟩;
     (cases x <;> first | exact hb | exact ⟨optPolyEncoderBound_none hn, optPolyDecoderBound_none hn⟩)]

theorem ct1Received_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyEncoderBound (match is with | some (.ct1Received x) => x | _ => default).sendingEk n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyEncoderBound_none hn; (cases x <;> first | exact hb | exact optPolyEncoderBound_none hn)]

theorem ekSentCt1Received_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyDecoderBound (match is with | some (.ekSentCt1Received x) => x | _ => default).receivingCt2 n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyDecoderBound_none hn; (cases x <;> first | exact hb | exact optPolyDecoderBound_none hn)]

theorem noHeaderReceived_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyDecoderBound (match is with | some (.noHeaderReceived x) => x | _ => default).receivingHdr n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyDecoderBound_none hn; (cases x <;> first | exact hb | exact optPolyDecoderBound_none hn)]

theorem headerReceived_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyDecoderBound (match is with | some (.headerReceived x) => x | _ => default).receivingEk n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyDecoderBound_none hn; (cases x <;> first | exact hb | exact optPolyDecoderBound_none hn)]

theorem ct1Sampled_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyEncoderBound (match is with | some (.ct1Sampled x) => x | _ => default).sendingCt1 n ∧
      OptPolyDecoderBound (match is with | some (.ct1Sampled x) => x | _ => default).receivingEk n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;>
    [exact ⟨optPolyEncoderBound_none hn, optPolyDecoderBound_none hn⟩;
     (cases x <;> first | exact hb | exact ⟨optPolyEncoderBound_none hn, optPolyDecoderBound_none hn⟩)]

theorem ekReceivedCt1Sampled_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyEncoderBound (match is with | some (.ekReceivedCt1Sampled x) => x | _ => default).sendingCt1 n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyEncoderBound_none hn; (cases x <;> first | exact hb | exact optPolyEncoderBound_none hn)]

theorem ct1Acknowledged_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyDecoderBound (match is with | some (.ct1Acknowledged x) => x | _ => default).receivingEk n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyDecoderBound_none hn; (cases x <;> first | exact hb | exact optPolyDecoderBound_none hn)]

theorem ct2Sampled_polyBound_extract {n : Nat} {is : Option V1State.InnerState}
    (hb : OptInnerStatePolyBound n is) :
    OptPolyEncoderBound (match is with | some (.ct2Sampled x) => x | _ => default).sendingCt2 n := by
  have hn := optInnerStatePolyBound_lt_2_56 hb
  rcases is with _ | ⟨x⟩ <;> [exact optPolyEncoderBound_none hn; (cases x <;> first | exact hb | exact optPolyEncoderBound_none hn)]

/-! ## 7. Hoare Specification `v1StateMergeSpec` and Loop Invariant Bundles -/

def v1StateJumpTablesAt (b : BitVec 64) : SepProp :=
  v1StateMergeJumpTableExpanded b ∗ optProtoInnerStateJumpTableAt b

theorem decodeErrorWith_zero_entails_le4 (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 0 ⊢ ∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  simp only [Nat.zero_le, pure_true, emp_sepConj]; exact Entails.refl _

theorem decodeErrorWith_succ_entails_le4 (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 3) :
    decodeErrorAtStackLen A e (n + 1) ⊢ ∃∗ k : Nat, ⌜k ≤ 4⌝ ∗ decodeErrorAtStackLen A e k :=
  Entails.trans (Entails.pure_right (by omega : n + 1 ≤ 4) (Entails.refl _))
    (Entails.sepExists_right (n + 1) (Entails.refl _))

structure V1StateMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def v1StateMergeSpec (A : RustAlloc) (b : BitVec 64) : Spec V1StateMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧ b &&& 0xfff#64 = 0#64 ∧
      OptInnerStatePolyBound x.bs.length x.msg.innerState⌝ ∗
      optProtoInnerStateCapAt A x.msgPtr x.bs.length x.msg.innerState ∗
      v1StateJumpTablesAt b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp v1StateMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ v1StateJumpTablesAt b ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp v1StateMergeStack ∗
      match (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
          optProtoInnerStateCapAt A x.msgPtr rest.length m'.innerState ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def v1StateErrFrame (A : RustAlloc) (b : BitVec 64) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A msgPtr is') ∗
    v1StateJumpTablesAt b ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
    A.pool ∗ v1StateSavedRegsAt s0.sp s0

def v1StateLoopPre (A : RustAlloc) (b : BitVec 64) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State) (bs cur : List (BitVec 8)) : SepProp :=
  optProtoInnerStateCapAt A msgPtr cur.length m.innerState ∗
    v1StateJumpTablesAt b ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool ∗
    stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗ v1StateSavedRegsAt s0.sp s0

def V1StateLoopRegs (b : BitVec 64) (s0 : State) (x : V1StateMergeGhost) (limit : Nat) (s : State) : Prop :=
  s.readReg64 (Reg.gpr 19#5) = x.bufRef ∧
    s.readReg64 (Reg.gpr 20#5) = x.msgPtr ∧
    s.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧
    s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
    s.readReg64 (Reg.gpr 24#5) = b + bv% (ls_bytes% "0042202c094c5836701464") ∧
    s.readReg64 (Reg.gpr 25#5) = s0.sp - 576#64 ∧
    s.readReg64 (Reg.gpr 26#5) = x.slot ∧
    s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
    s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 limit ∧
    s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64

def v1StateJumpTablesPlacedAt [LibsignalPlacement] : SepProp :=
  v1StateMergeJumpTablePlacedExpanded ∗ optProtoInnerStateJumpTablePlacedAt

def v1StateMergePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec V1StateMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      OptInnerStatePolyBound x.bs.length x.msg.innerState⌝ ∗
      optProtoInnerStateCapAt A x.msgPtr x.bs.length x.msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp v1StateMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp v1StateMergeStack ∗
      match (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
          optProtoInnerStateCapAt A x.msgPtr rest.length m'.innerState ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def v1StateErrFramePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A msgPtr is') ∗
    v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
    A.pool ∗ v1StateSavedRegsAt s0.sp s0

def v1StateLoopPrePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State) (bs cur : List (BitVec 8)) : SepProp :=
  optProtoInnerStateCapAt A msgPtr cur.length m.innerState ∗
    v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool ∗
    stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗ v1StateSavedRegsAt s0.sp s0

def V1StateLoopRegsPlaced [LibsignalPlacement] (s0 : State) (x : V1StateMergeGhost) (limit : Nat) (s : State) : Prop :=
  s.readReg64 (Reg.gpr 19#5) = x.bufRef ∧
    s.readReg64 (Reg.gpr 20#5) = x.msgPtr ∧
    s.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧
    s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
    s.readReg64 (Reg.gpr 24#5) = lsmpl.ρ v1StateMergeJumpTableSym ∧
    s.readReg64 (Reg.gpr 25#5) = s0.sp - 576#64 ∧
    s.readReg64 (Reg.gpr 26#5) = x.slot ∧
    s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
    s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 limit ∧
    s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64

@[simp, arm64_norm] abbrev _root_.Arm64.State.v1TraceEq (s1 s2 : State) : Prop :=
  s1.trace = s2.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s2

theorem _root_.Arm64.State.v1TraceEq.trans {s1 s2 s3 : State}
    (h1 : s1.v1TraceEq s2) (h2 : s2.v1TraceEq s3) : s1.v1TraceEq s3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem _root_.And.trans {α β : Type _} {a1 a2 a3 : α} {b1 b2 b3 : β}
    (h1 : a1 = a2 ∧ b1 = b2) (h2 : a2 = a3 ∧ b2 = b3) : a1 = a3 ∧ b1 = b3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem allowPanic_frame' {s0 s sf : State} {F R : SepProp}
    (htr : s.v1TraceEq s0)
    (hpan : sf.mem ⊨ ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R :=
  CryptoVerification.LibsignalTripleRatchet.Prost.allowPanic_frame' htr.1 hpan

end CryptoVerification.SpqrV1.Prost.MessageMerge

