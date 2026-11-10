/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Field Error Push Paths (Block `325`)

Proves the budget-threaded relocatable `DecodeError::push` and wire-type mismatch blocks
(`+2156..+2348`) for `VersionNegotiationPB` fields (`public`, `version`, `max_version`, `params`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap decodeErrorAtStackLen)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateSavedAt protoPqRatchetStateAt sp_sub_1392_aligned)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
  (bv_sub_688_add_8 decodeStateErrFramePlaced scratch_680_fold_1_1 scratch_680_fold_8
   scratch_680_split_1_1 scratch_680_split_8)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (SepWPp.call_decodeErrorFrom_placed_ofEnv SepWPp.call_decodeErrorPush_placed_ofEnv
   decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv decodeState_err_push_53dcc_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_fold {prog : Program} {ret : BitVec 64} {s : State} {P T T' F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp oom) : SepWPp prog ret s P Q Qp oom := fun R hm hL => by
  rw [hf] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a : α, P a) Q Qp oom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

/-- Envelope-parameterized shared `VersionNegotiationPB` error push at `0x53dc4..0x53dc8`
(`+2344..+2348`, 2 instructions): calls `DecodeError::push`, reloads `x1` from `[sp + 0x2c0]`
(`s0.sp - 688#64`), and falls through to `0x53dcc` (`decodeState_err_push_53dcc_placed_ofEnv`). -/
theorem decodeState_err_push_53dc4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ errBox) ∗ decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hpush ⊢
  wp_steps_sync_pool (lsmpl.base 257)
  try simp only [State.setMem_setMem]
  refine SepWPp.call_decodeErrorPush_placed_ofEnv hpush (s0.sp - 688#64) errBox n st
    (ret_pc := (blkPl_325).base + 2348#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0])
    (hn := by omega)
    (hfits := hfits1)
    (hP := by sep_focus) ?_
  intro s1 evs_p1 hevs_p1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  wp_steps_sync_pool ((blkPl_325).base + 2352#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53dcc_placed_ofEnv hc x st0 (M.stepEvents evs_p1 st) curSt errBox
    (n + 1) s0 _ _ R post hpost herr (by omega)
    (hfits2 evs_p1 hevs_p1)
    (fun evs_p2 evs_f hp2 hfree => henv evs_p1 evs_p2 evs_f hevs_p1 hp2 hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
        Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_push_53dc4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ errBox) ∗ decodeErrorAtStackLen A.repAlloc errBox n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53dc4_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt errBox n s0 s P R post hpost herr hn hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx0 hx19 hP

/-- Envelope-parameterized error push at `0x53da4..0x53dc0` (`+2312..+2340`, 8 instructions) for
`VersionNegotiation::params`: stores `x0` (`errBox`) at `[sp + 0x2c0]` and falls through to
`0x53dc4`. -/
theorem decodeState_err_push_53da4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2312#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 2344#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53dc4_placed_ofEnv hc x st0 st curSt (s.readReg64 .x0) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53da4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2312#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53da4_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized error push at `0x53d80..0x53da0` (`+2276..+2308`, 9 instructions) for
`VersionNegotiation::max_version`: stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to
`0x53dc4`. -/
theorem decodeState_err_push_53d80_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2276#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 2344#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53dc4_placed_ofEnv hc x st0 st curSt (s.readReg64 .x8) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53d80_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2276#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53d80_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized wire-type mismatch error on `VersionNegotiation::max_version` at
`0x53d68..0x53d7c` (`+2252..+2272`, 6 instructions). -/
theorem decodeState_err_53d68_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  refine sepWPp_fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepWPp_exists_left; intro b1
  apply sepWPp_exists_left; intro b0
  wp_steps_sync_pool (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine sepWPp_fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 688#64) 0x8000000000000006#64 st
    (ret_pc := (blkPl_325).base + 2272#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hsp])
    (hw := by decide)
    (hfits := hfits1)
    (hP := by simp only [bv_sub_688_add_8, hx21]; sep_focus) ?_
  intro s1 v_k evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  rw [bv_sub_688_add_8 s0.sp]
  wp_steps_sync_pool ((blkPl_325).base + 2276#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53d80_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt v_k 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p1 hp1 => hfits3 evs_fr evs_p1 hevs_fr hp1)
    (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv evs_fr evs_p1 evs_p2 evs_f hevs_fr hp1 hp2 hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_53d68_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53d68_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 hfits3 henv
    hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized error push at `0x53d44..0x53d64` (`+2216..+2248`, 9 instructions) for
`VersionNegotiation::version`: stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to
`0x53dc4`. -/
theorem decodeState_err_push_53d44_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 2344#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53dc4_placed_ofEnv hc x st0 st curSt (s.readReg64 .x8) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53d44_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53d44_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized wire-type mismatch error on `VersionNegotiation::version` at
`0x53d2c..0x53d40` (`+2192..+2212`, 6 instructions). -/
theorem decodeState_err_53d2c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  refine sepWPp_fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepWPp_exists_left; intro b1
  apply sepWPp_exists_left; intro b0
  wp_steps_sync_pool (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine sepWPp_fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 688#64) 0x8000000000000006#64 st
    (ret_pc := (blkPl_325).base + 2212#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hsp])
    (hw := by decide)
    (hfits := hfits1)
    (hP := by simp only [bv_sub_688_add_8, hx21]; sep_focus) ?_
  intro s1 v_k evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  rw [bv_sub_688_add_8 s0.sp]
  wp_steps_sync_pool ((blkPl_325).base + 2216#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53d44_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt v_k 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p1 hp1 => hfits3 evs_fr evs_p1 hevs_fr hp1)
    (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree => henv evs_fr evs_p1 evs_p2 evs_f hevs_fr hp1 hp2 hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_53d2c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits3 : ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv : ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hpc : s.pc = decodeStatePlacedEntry + 2192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53d2c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 hfits3 henv
    hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized error push at `0x53d08..0x53d28` (`+2156..+2188`, 9 instructions) for
`VersionNegotiation::public`: stores `x0` (`errBox`) at `[sp + 0x2c0]` and branches to
`0x53dc4`. -/
theorem decodeState_err_push_53d08_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 2344#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53dc4_placed_ofEnv hc x st0 st curSt (s.readReg64 .x0) n
    s0 _ _ R post hpost herr hn hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_push_53d08_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hfits1 : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hfits2 : ∀ evs_p1, DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 st) (DecodeErrorPushEnv (n + 1)))
    (henv : ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_push_53d08_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 n s0 s P R post hpost herr hn hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux
