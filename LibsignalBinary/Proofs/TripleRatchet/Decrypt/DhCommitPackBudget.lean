/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget

/-!
# Budget-Threaded DH Commit Packing & `ReachesOrPanicOom` Combinators

Provides `RustCliAllocBudget M` layout-packing lemmas (`vecU8Buf_33_of_live`,
`chainAt_newChain_of_cells`) and relocatable `[LibsignalPlacement]` `ReachesOrPanicOom` stepping
and call combinators threading `VmPreserved` and `OomPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPackBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoGames.LibsignalSession (PublicKey ChainKey)
open CryptoVerification.RustHeap (vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  optChainKeyTailBytes optChainKeyHeap pack64 newChainGhost newReceiverChain
)
open LibsignalBinary.Heap (
  AllocCostModel RustCliAllocBudget VmPreserved OomPreserved
)
open LibsignalBinary.Heap.IfaceSimp (ReachesOrPanicOom)

/-! ## 1. Budget-Form Layout Packing Helpers -/

/-- Budget-form counterpart of `DhCommit.vecU8Buf_33_of_live` for `(A : RustCliAllocBudget M)`. -/
theorem vecU8Buf_33_of_live {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ptr : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr ≠ 0) (hlen : bs.length = 33) :
    (A.live ptr 33 1 ∗ (ptr ↦ₛ bs)) ⊢ vecU8Buf A.repAlloc 33#64 ptr bs := by
  rw [← A.repAlloc_live_norm]
  exact CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.vecU8Buf_33_of_live
    A.repAlloc ptr bs hptr hlen

/-- Budget-form counterpart of `DhCommit.chainAt_newChain_of_cells` for `(A : RustCliAllocBudget M)`. -/
theorem chainAt_newChain_of_cells {M : AllocCostModel} (A : RustCliAllocBudget M)
    (slot srkPtr ckPtr : BitVec 64) (srk : PublicKey) (rck : ChainKey)
    {pad : List (BitVec 8)} (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0) :
    let tail := optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad
    ((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
     ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
     ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
     ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗ ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
     ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗ ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24)) ∗
     (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
     optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck)) ⊢
      chainAt A.repAlloc (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck) slot := by
  intro tail
  rw [← A.repAlloc_live_norm]
  exact CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.chainAt_newChain_of_cells
    A.repAlloc slot srkPtr ckPtr srk rck hpad hsrk_ne

/-! ## 2. `OomPreserved` Step Composition -/

/-- Transitivity of `OomPreserved` (`fs`, `trace`, and `sigActions` preserved). -/
theorem oomPreserved_step_trans {s0 s s1 : State}
    (hoom0 : OomPreserved s0 s) (hoom1 : OomPreserved s s1) :
    OomPreserved s0 s1 :=
  ⟨hoom1.1.trans hoom0.1, hoom1.2.1.trans hoom0.2.1, hoom1.2.2.trans hoom0.2.2⟩

/-! ## 3. Placed `[LibsignalPlacement]` `ReachesOrPanicOom` Combinators -/

/-- Placed counterpart of `DhCommit.ReachesOrPanic.seq_placed` on `ReachesOrPanicOom`. -/
theorem reachesOrPanicOom_seq_placed [LibsignalPlacement] {prog : Program}
    {Pan : State → State → SepProp} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : ReachesOrPanicOom prog Pan R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → P s1 →
      ReachesOrPanicOom prog Pan R s0 s1 Q) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.seq h1 fun s1 hkf _ hP => h2 s1 hkf hP

/-- Placed counterpart of `DhCommit.ReachesOrPanic.of_sepWP_placed` on `ReachesOrPanicOom`. -/
theorem reachesOrPanicOom_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {Pan : State → State → SepProp} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {Pre Frame : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ (Frame ∗ R)) →
      PostWP s1 P_out →
      ReachesOrPanicOom prog Pan R s0 s1 Q) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.of_sepWP hwp hmem hL
    fun s1 P_out hpc1 hrun1 hkf1 _ hL1 hm1 hpost1 =>
      hcont s1 P_out hpc1 hrun1 hkf1 hL1 hm1 hpost1

/-- Run a VM- and OOM-preserving `SepWP` segment (`VmPreserved s s1 ∧ OomPreserved s s1 ∧ PostWP s1 P_out`,
e.g. produced by `wp_steps_sync_pool`) and continue in `ReachesOrPanicOom` with both
`VmPreserved s s1` and `OomPreserved s0 s1` in scope. -/
theorem reachesOrPanicOom_of_sepWP_vm_placed [LibsignalPlacement] {prog : Program}
    {Pan : State → State → SepProp} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {Pre Frame : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre
      (fun s1 P_out => VmPreserved s s1 ∧ OomPreserved s s1 ∧ PostWP s1 P_out))
    (hoom0 : OomPreserved s0 s)
    (hmem : s.mem ⊨ Pre ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      VmPreserved s s1 → OomPreserved s0 s1 →
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ (Frame ∗ R)) →
      PostWP s1 P_out →
      ReachesOrPanicOom prog Pan R s0 s1 Q) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.of_sepWP hwp hmem hL
    fun s1 P_out hpc1 hrun1 hkf1 _ hL1 hm1 ⟨hvm1, hoom1, hpost1⟩ =>
      hcont s1 P_out hpc1 hrun1 hvm1 (oomPreserved_step_trans hoom0 hoom1) hkf1 hL1 hm1 hpost1

/-- Placed counterpart of `DhCommit.ReachesOrPanic.of_call_no_panic_placed` on `ReachesOrPanicOom`. -/
theorem reachesOrPanicOom_of_call_no_panic_placed [LibsignalPlacement] {α : Type}
    {prog : Program} {Pan : State → State → SepProp} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanicOom prog Pan R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.of_call_no_panic hcall hpc hrun hsp hlr hpre hL hpan_false hexit_false
    (fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 _ hL1 hm1 =>
      hcont s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 hL1 hm1)
    hoom_false

/-- Call a non-panicking subroutine with `onOom = ⌜OomPreserved s sf⌝` (e.g. `rustCliAllocSpec` or
an OOM-propagating helper) and continue in `ReachesOrPanicOom`. -/
theorem reachesOrPanicOom_of_call_oom_placed [LibsignalPlacement] {α : Type}
    {prog : Program} {Pan : State → State → SepProp} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hoom0 : OomPreserved s0 s)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom arg s sf = ⌜OomPreserved s sf⌝ := by intro _; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanicOom prog Pan R s0 s1 Q) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.of_call_oom hcall hpc hrun hsp hlr hoom0 hpre hL hpan_false hexit_false hoom_eq
    fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 _ hL1 hm1 =>
      hcont s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 hL1 hm1

/-- Placed counterpart of `DhCommit.ReachesOrPanic.of_call_alloc_panic_placed` on `ReachesOrPanicOom`
for callees that may both panic and stop in `.OutOfMemory` (such as budget-form `grow_one`). -/
theorem reachesOrPanicOom_of_call_alloc_panic_placed [LibsignalPlacement] {α : Type}
    {prog : Program} {Pan : State → State → SepProp} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hoom0 : OomPreserved s0 s)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan : ∀ s1, s1.status = .Panicked →
      (s1.mem ⊨ spec.onPanic arg s s1 ∗ (Frame ∗ R)) → (s1.mem ⊨ Pan s0 s1 ∗ R))
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      ReachesOrPanicOom prog Pan R s0 s1 Q)
    (hoom_eq : ∀ sf, spec.onOom arg s sf = ⌜OomPreserved s sf⌝ := by intro _; rfl) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.of_call_alloc_panic hcall hpc hrun hsp hlr hoom0 hpre hL hpan hexit_false
    (fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 _ hL1 hm1 =>
      hcont s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hkf1 hL1 hm1)
    hoom_eq

/-- Placed wrapper for `ReachesOrPanicOom.of_panic_extern`. -/
theorem reachesOrPanicOom_of_panic_extern_placed [LibsignalPlacement] {prog : Program}
    {Pan : State → State → SepProp} {R : SepProp} {s0 s : State} {Q : State → Prop}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hpan : (Rust.panicked s).mem ⊨ Pan s0 (Rust.panicked s) ∗ R) :
    ReachesOrPanicOom prog Pan R s0 s Q :=
  ReachesOrPanicOom.of_panic_extern hrun hext hpan

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPackBudget
