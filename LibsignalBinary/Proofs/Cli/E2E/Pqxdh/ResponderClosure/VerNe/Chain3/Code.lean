/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs

/-!
# `message::merge<Chain> [local#5]` Fetch Tactic and Frame Split

Provides the layout-independent `chain3_fetches_range` instruction-fetch tactic and stack-frame
decomposition lemmas (`stackAt_chainMerge3StackX_split`, `chain3SavedRegs_restore`,
`chain3_stack_restore`) for the `0xf0`-byte frame of `message::merge<Chain> [local#5]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoVerification CryptoVerification.CodeLayout

/-! ## 1. Layout-independent fetch tactic -/

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

/-- Fetch facts for byte offsets `kStart, kStart + 4, …, kEnd` (inclusive) of
`message::merge<Chain> [local#5]` in `libsignalSessionCode.rebase b H`. -/
elab "chain3_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := Lean.Syntax.mkNumLit (toString (num% (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")))
  let len := Lean.Syntax.mkNumLit (toString (kEnd.getNat - kStart.getNat + 4))
  evalTactic (← `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.Cli.ShardFill.ChainMerge5Decode.chainMerge5Bin
      $b $H
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")
      $off $kStart $len))

end Fetch

/-! ## 2. Frame split -/

/-- The 10 words `[sp0 - 0x50, sp0)` of the `0xf0` frame, contents existential. -/
def chain3Cells (sp0 : BitVec 64) : SepProp :=
  ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
  ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
  ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
    ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
    ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
    ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
    ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
    ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)

/-- `stackAt sp0 chainMerge3StackX` = the callee sub-stack below `sp0 - 0xf0`, the 160-byte local
frame `[sp0 - 0xf0, sp0 - 0x50)` and the 10 top words. -/
theorem stackAt_chainMerge3StackX_split (sp0 : BitVec 64) :
    stackAt sp0 chainMerge3StackX =
      stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ memRegion (sp0 - 0xf0#64) 160 ∗
        chain3Cells sp0 := by
  have h1 : stackAt sp0 chainMerge3StackX =
      stackAt (sp0 - 80#64) (chainMerge3SubStackX + 160) ∗ cells (sp0 - 80#64) 10 :=
    ProofLib.stackAt_split_cells sp0 (chainMerge3SubStackX + 160) 10 (by decide)
  have h2 : stackAt (sp0 - 80#64) (chainMerge3SubStackX + 160) =
      stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ memRegion (sp0 - 0xf0#64) 160 := by
    unfold stackAt
    have hb : sp0 - 80#64 - BitVec.ofNat 64 (chainMerge3SubStackX + 160) =
        sp0 - 0xf0#64 - BitVec.ofNat 64 chainMerge3SubStackX := by
      simp only [chainMerge3SubStackX_eq, Nat.reduceAdd]
      bv_omega
    rw [hb]
    refine memRegion_split' (n := chainMerge3SubStackX) (k := 160) rfl ?_ (by decide)
    simp only [chainMerge3SubStackX_eq]
    bv_omega
  have h3 : cells (sp0 - 80#64) 10 = chain3Cells sp0 := by
    unfold chain3Cells
    cells_unfold
  rw [h1, h2, h3, sepConj_assoc]

/-- The prologue's frame (`chain3SavedRegs`) entails the local frame and the 10 top words. -/
theorem chain3SavedRegs_restore (sp0 : BitVec 64) (s0 : State) :
    chain3SavedRegs sp0 s0 ⊢ memRegion (sp0 - 0xf0#64) 160 ∗ chain3Cells sp0 := by
  unfold chain3SavedRegs
  refine sepConj_mono_right ?_
  rw [ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w56 => ?_
  unfold chain3Cells
  exact Entails.sepExists_right (s0.readReg64 .x29) <| Entails.sepExists_right (s0.readReg64 .x30) <|
    Entails.sepExists_right (s0.readReg64 .x25) <| Entails.sepExists_right w56 <|
    Entails.sepExists_right (s0.readReg64 .x24) <| Entails.sepExists_right (s0.readReg64 .x23) <|
    Entails.sepExists_right (s0.readReg64 .x22) <| Entails.sepExists_right (s0.readReg64 .x21) <|
    Entails.sepExists_right (s0.readReg64 .x20) <| Entails.sepExists_right (s0.readReg64 .x19) <|
    Entails.refl _

/-- Return-side fold: the sub-stack and the prologue's frame give `stackAt sp0 chainMerge3StackX`. -/
theorem chain3_stack_restore (sp0 : BitVec 64) (s0 : State) :
    stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs sp0 s0 ⊢
      stackAt sp0 chainMerge3StackX := by
  rw [stackAt_chainMerge3StackX_split]
  exact sepConj_mono_right (chain3SavedRegs_restore sp0 s0)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
