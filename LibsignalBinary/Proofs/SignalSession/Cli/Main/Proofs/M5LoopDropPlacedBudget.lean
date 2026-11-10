/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlacedBudget

/-!
# Budget-Threaded M5 Post-Commit Entry Drop Loop (`M+0xa90 .. M+0xabc`, Block `617`)

Defines `m5ErrEntryDropEvents` and verifies budget-threaded `m5_entry_drop_loop_placed`
(`M+0xa90 .. M+0xabc`) on Block `617`, advancing `A.pool` by `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli (dirEntryAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (InMainPlaced LsCodeInv M5ErrEntryPlaced mainFrameSize)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropLoopCorePlacedBudget
  (m5_drop_loop_body_0xa84_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

/-- Exact allocator events emitted by the initial temporary-path `String` drop at `M5ErrEntryPlaced`
(`0xbcc` / `0xbdc` / `0xbf4`) before `0xbf4 → 0xc5c` drops `curEntries` and remaining `Dir`s. -/
def m5ErrEntryDropEvents : M5ErrEntryPlaced → List AllocEvent
  | .bcc cap _ _ => if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1
  | .bdc cap _ _ => rustDeallocEvents cap.toNat 1
  | .bf4 => []

/-- Allocator event envelope of `m5_entry_drop_loop_placed` (`M+0xa90 .. M+0xabc`): pure
`__rust_dealloc` calls over the `(String, Vec<u8>)` entries of `es`. -/
def M5EntryDropLoopEnv (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs

example : ∃ evs, M5EntryDropLoopEnv evs :=
  ⟨[], by rintro _ ⟨⟩⟩

theorem m5ErrEntryDropEvents_freeOnly (errE : M5ErrEntryPlaced) :
    FreeOnlyEvs (m5ErrEntryDropEvents errE) := by
  cases errE with
  | bcc cap _ _ =>
    by_cases h : cap = 0#64
    · simp only [m5ErrEntryDropEvents, h, ↓reduceIte]
      exact FreeOnlyEvs.nil
    · simp only [m5ErrEntryDropEvents, h, ↓reduceIte]
      exact FreeOnlyEvs.singleton 1 cap.toNat
  | bdc cap _ _ =>
    exact FreeOnlyEvs.singleton 1 cap.toNat
  | bf4 =>
    exact FreeOnlyEvs.nil

/-- Budget-threaded drop of a non-empty array of `(String, Vec<u8>)` entries starting at `M+0xa90`
(`x21 = base + 32`, `x20 = es.length`), looping via `M+0xa84 .. M+0xa8c` until `x20 = 0` branches
to `M+0xabc`. -/
theorem m5_entry_drop_loop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {base : BitVec 64}
    (es : List (List (BitVec 8) × List (BitVec 8)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A lim H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hne : es ≠ [])
    (hlen : es.length * 48 < 2 ^ 63)
    (hs : InMainPlaced CodeOk s0 s 0xa90)
    (hx21 : s.readReg64 (.gpr 21#5) = base + 32#64)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 es.length)
    (hP : P ⊢ arrayAt (dirEntryAt A.repAlloc) 48 base es ∗ A.pool lim st s ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      M5EntryDropLoopEnv evs →
      InMainPlaced CodeOk s0 sm 0xabc →
      sm.fs = s.fs →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (memRegion base (es.length * 48) ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  refine SepWPp.weaken_pre (Entails.trans hP (Entails.of_eq (by rw [← hs.sp]))) ?_
  refine m5_drop_loop_body_0xa84_placed (st := st) hA hstk (by omega) hne hlen hs hx20 hx21 ?_
  intro sm evs hf hsm hkeeps hfs htr
  rw [hs.sp]
  exact hnext sm evs hf hsm hfs htr
    (hkeeps 19#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 22#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 23#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 24#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 25#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 26#5 (by decide) (by decide) (by decide) (by decide))
    (hkeeps 27#5 (by decide) (by decide) (by decide) (by decide))

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopDropPlacedBudget
