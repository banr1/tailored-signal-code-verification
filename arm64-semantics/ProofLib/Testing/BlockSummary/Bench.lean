/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.SepLogic.BlockSummary
public import ProofLib.SepLogic.SymBlock.Tactic

/-!
# `block_summary` Benchmarks

Compares straight-line instruction stepping (`wp_steps`, `wp_sym_steps`, and `sym_block`) against
prebuilt `block_summary` declarations applied via `wp_block` over synthetic position-independent
code segments of 8, 32, and 60 instructions, checking `#print axioms` on every theorem.
-/

@[expose] public section

namespace Testing.BlockSummary.Bench

open Arm64 ProofLib

arm64_proof_prelude

set_option maxHeartbeats 1000000

/-! ## Spec variants -/

def variantWords : List (BitVec 32) :=
  "f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405"

theorem variantA_hand {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base variantWords)
    {s : State} {p v q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
      w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23
      w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35
      w36 w37 w38 w39 : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F) ∧
        sf.readReg64 .x5 = v + 16#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem variantB_hand {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base variantWords)
    {s : State} {p v q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
      w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23
      w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35
      w36 w37 w38 w39 : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F)
      (fun sf Pf => (Pf ⊢ ((p + 8#64) ↦₆₄ (v + 16#64)) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F) ∧
        sf.readReg64 .x0 = p) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨Entails.refl _, by simp only [wp_norm, arm64_norm, hx0]⟩

block_summary variant_seg {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base variantWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 128#64)

theorem variantA_auto {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base variantWords)
    {s : State} {p v q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
      w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23
      w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35
      w36 w37 w38 w39 : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F) ∧
        sf.readReg64 .x5 = v + 16#64) := by
  wp_block variant_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem variantB_auto {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base variantWords)
    {s : State} {p v q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
      w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23
      w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35
      w36 w37 w38 w39 : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F)
      (fun sf Pf => (Pf ⊢ ((p + 8#64) ↦₆₄ (v + 16#64)) ∗ ((q + 0#64) ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ∗
        ((q + 32#64) ↦₆₄ w4) ∗ ((q + 40#64) ↦₆₄ w5) ∗ ((q + 48#64) ↦₆₄ w6) ∗ ((q + 56#64) ↦₆₄ w7) ∗
        ((q + 64#64) ↦₆₄ w8) ∗ ((q + 72#64) ↦₆₄ w9) ∗ ((q + 80#64) ↦₆₄ w10) ∗ ((q + 88#64) ↦₆₄ w11) ∗
        ((q + 96#64) ↦₆₄ w12) ∗ ((q + 104#64) ↦₆₄ w13) ∗ ((q + 112#64) ↦₆₄ w14) ∗ ((q + 120#64) ↦₆₄ w15) ∗
        ((q + 128#64) ↦₆₄ w16) ∗ ((q + 136#64) ↦₆₄ w17) ∗ ((q + 144#64) ↦₆₄ w18) ∗ ((q + 152#64) ↦₆₄ w19) ∗
        ((q + 160#64) ↦₆₄ w20) ∗ ((q + 168#64) ↦₆₄ w21) ∗ ((q + 176#64) ↦₆₄ w22) ∗ ((q + 184#64) ↦₆₄ w23) ∗
        ((q + 192#64) ↦₆₄ w24) ∗ ((q + 200#64) ↦₆₄ w25) ∗ ((q + 208#64) ↦₆₄ w26) ∗ ((q + 216#64) ↦₆₄ w27) ∗
        ((q + 224#64) ↦₆₄ w28) ∗ ((q + 232#64) ↦₆₄ w29) ∗ ((q + 240#64) ↦₆₄ w30) ∗ ((q + 248#64) ↦₆₄ w31) ∗
        ((q + 256#64) ↦₆₄ w32) ∗ ((q + 264#64) ↦₆₄ w33) ∗ ((q + 272#64) ↦₆₄ w34) ∗ ((q + 280#64) ↦₆₄ w35) ∗
        ((q + 288#64) ↦₆₄ w36) ∗ ((q + 296#64) ↦₆₄ w37) ∗ ((q + 304#64) ↦₆₄ w38) ∗ ((q + 312#64) ↦₆₄ w39) ∗ F) ∧
        sf.readReg64 .x0 = p) := by
  wp_block variant_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨Entails.refl _, by simp only [wp_norm, arm64_norm, hx0]⟩

/-- info: 'Testing.BlockSummary.Bench.variantA_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variantA_hand

/-- info: 'Testing.BlockSummary.Bench.variantB_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variantB_hand

/-- info: 'Testing.BlockSummary.Bench.variant_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variant_seg

/-- info: 'Testing.BlockSummary.Bench.variantA_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variantA_auto

/-- info: 'Testing.BlockSummary.Bench.variantB_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms variantB_auto

/-! ## Repeated chunks -/

def chunkWords : List (BitVec 32) :=
  "f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405"

theorem chunk0_hand {prog : Program} {b : BitVec 64} (h_code : prog.hasCode b chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = b) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (b + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem chunk1_hand {prog : Program} {b : BitVec 64} (h_code : prog.hasCode (b + 0x1000#64) chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = (b + 0x1000#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog ((b + 0x1000#64) + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem chunk2_hand {prog : Program} {b : BitVec 64} (h_code : prog.hasCode (b + 0x2000#64) chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = (b + 0x2000#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog ((b + 0x2000#64) + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem chunk3_hand {prog : Program} {b : BitVec 64} (h_code : prog.hasCode (b + 0x3000#64) chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = (b + 0x3000#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog ((b + 0x3000#64) + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

block_summary chunk_seg {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 128#64)

theorem chunk0_auto {prog : Program} {b : BitVec 64} (h_code : prog.hasCode b chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = b) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (b + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_block chunk_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem chunk1_auto {prog : Program} {b : BitVec 64} (h_code : prog.hasCode (b + 0x1000#64) chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = (b + 0x1000#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog ((b + 0x1000#64) + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_block chunk_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem chunk2_auto {prog : Program} {b : BitVec 64} (h_code : prog.hasCode (b + 0x2000#64) chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = (b + 0x2000#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog ((b + 0x2000#64) + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_block chunk_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem chunk3_auto {prog : Program} {b : BitVec 64} (h_code : prog.hasCode (b + 0x3000#64) chunkWords)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = (b + 0x3000#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog ((b + 0x3000#64) + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_block chunk_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

/-- info: 'Testing.BlockSummary.Bench.chunk0_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk0_hand

/-- info: 'Testing.BlockSummary.Bench.chunk1_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk1_hand

/-- info: 'Testing.BlockSummary.Bench.chunk2_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk2_hand

/-- info: 'Testing.BlockSummary.Bench.chunk3_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk3_hand

/-- info: 'Testing.BlockSummary.Bench.chunk_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk_seg

/-- info: 'Testing.BlockSummary.Bench.chunk0_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk0_auto

/-- info: 'Testing.BlockSummary.Bench.chunk1_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk1_auto

/-- info: 'Testing.BlockSummary.Bench.chunk2_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk2_auto

/-- info: 'Testing.BlockSummary.Bench.chunk3_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chunk3_auto

/-! ## Stepper micro-benchmarks -/

def step8Words : List (BitVec 32) :=
  "f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405"

theorem step8_wp_steps {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step8Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 32#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 4#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 4#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem step8_wp_sym_steps {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step8Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 32#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 4#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 4#64) := by
  wp_sym_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem step8_sym_block {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step8Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 32#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 4#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 4#64) := by
  sym_block 8
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

block_summary step8_seg {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step8Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 32#64)

theorem step8_summary {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step8Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 32#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 4#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 4#64) := by
  wp_block step8_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

/-- info: 'Testing.BlockSummary.Bench.step8_wp_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step8_wp_steps

/-- info: 'Testing.BlockSummary.Bench.step8_wp_sym_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step8_wp_sym_steps

/-- info: 'Testing.BlockSummary.Bench.step8_sym_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step8_sym_block

/-- info: 'Testing.BlockSummary.Bench.step8_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step8_seg

/-- info: 'Testing.BlockSummary.Bench.step8_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step8_summary

def step32Words : List (BitVec 32) :=
  "f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405"

theorem step32_wp_steps {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step32Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem step32_wp_sym_steps {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step32Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_sym_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem step32_sym_block {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step32Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  sym_block 32
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

block_summary step32_seg {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step32Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 128#64)

theorem step32_summary {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step32Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 128#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 16#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 16#64) := by
  wp_block step32_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

/-- info: 'Testing.BlockSummary.Bench.step32_wp_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step32_wp_steps

/-- info: 'Testing.BlockSummary.Bench.step32_wp_sym_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step32_wp_sym_steps

/-- info: 'Testing.BlockSummary.Bench.step32_sym_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step32_sym_block

/-- info: 'Testing.BlockSummary.Bench.step32_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step32_seg

/-- info: 'Testing.BlockSummary.Bench.step32_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step32_summary

def step60Words : List (BitVec 32) :=
  "f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405 f9400405 910004a5 910004a5 f9000405"

theorem step60_wp_steps {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step60Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 240#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 30#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 30#64) := by
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem step60_wp_sym_steps {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step60Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 240#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 30#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 30#64) := by
  wp_sym_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

theorem step60_sym_block {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step60Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 240#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 30#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 30#64) := by
  sym_block 60
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

block_summary step60_seg {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step60Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    BlockSegment prog s (((p + 8#64) ↦₆₄ v) ∗ F) (base + 240#64)

theorem step60_summary {prog : Program} {base : BitVec 64} (h_code : prog.hasCode base step60Words)
    {s : State} {p v : BitVec 64} {F : SepProp}
    (hpc : s.pc = base) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = p) :
    SepWP prog (base + 240#64) s (((p + 8#64) ↦₆₄ v) ∗ F)
      (fun sf Pf => Pf = (((p + 8#64) ↦₆₄ (v + 30#64)) ∗ F) ∧ sf.readReg64 .x5 = v + 30#64) := by
  wp_block step60_seg
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  exact ⟨rfl, by simp only [wp_norm, arm64_norm]⟩

/-- info: 'Testing.BlockSummary.Bench.step60_wp_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step60_wp_steps

/-- info: 'Testing.BlockSummary.Bench.step60_wp_sym_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step60_wp_sym_steps

/-- info: 'Testing.BlockSummary.Bench.step60_sym_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step60_sym_block

/-- info: 'Testing.BlockSummary.Bench.step60_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step60_seg

/-- info: 'Testing.BlockSummary.Bench.step60_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step60_summary

end Testing.BlockSummary.Bench
