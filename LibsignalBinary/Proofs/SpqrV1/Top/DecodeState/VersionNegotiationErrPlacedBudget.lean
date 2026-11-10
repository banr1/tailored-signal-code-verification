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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Error Exit Paths (Block `325`)

Re-exports `VersionNegotiationErrPlacedBudgetAux` and proves the remaining budget-threaded
relocatable `VersionNegotiationPB` error-exit blocks (`+1728..+1772`, `+1852..+1868`,
`+2148..+2152`, `+2964..+2968`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudget

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

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux
  (decodeState_err_push_53dc4_placed_ofEnv decodeState_err_push_53dc4_placed
   decodeState_err_push_53da4_placed_ofEnv decodeState_err_push_53da4_placed
   decodeState_err_push_53d80_placed_ofEnv)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux
  (decodeState_err_push_53d80_placed decodeState_err_53d68_placed_ofEnv
   decodeState_err_53d68_placed decodeState_err_push_53d44_placed_ofEnv
   decodeState_err_push_53d44_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux
  (decodeState_err_53d2c_placed_ofEnv decodeState_err_53d2c_placed
   decodeState_err_push_53d08_placed_ofEnv decodeState_err_push_53d08_placed)

/-- Envelope-parameterized error conversion at `0x53b7c..0x53b88` (`+1760..+1772`, 4 instructions)
for `VersionNegotiation`: sets `x0 = sp + 0x2c0`, calls `DecodeError::from`, moves `x0` into `x1`,
and branches to `0x53dcc` (`decodeState_err_push_53dcc_placed_ofEnv`). -/
theorem decodeState_err_from_53b7c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1760#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfrom := hc.decodeErrorFrom
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  wp_steps_sync_pool (lsmpl.base 261)
  try simp only [State.setMem_setMem]
  refine SepWPp.call_decodeErrorFrom_placed_ofEnv hfrom (s0.sp - 688#64) w0 st
    (ret_pc := (blkPl_325).base + 1768#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hsp])
    (hw := hw)
    (hfits := hfits1)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k evs_fr hevs_fr hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  try simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
  try simp only [arm64_norm, wp_norm] at hx27_1 hx28_1 hx29_1 hvregs_1
  rw [bv_sub_688_add_8 s0.sp]
  wp_steps_sync_pool ((blkPl_325).base + 2352#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_push_53dcc_placed_ofEnv hc x st0 (M.stepEvents evs_fr st) curSt v_k 0
    s0 _ _ R post hpost herr (by decide)
    (hfits2 evs_fr hevs_fr)
    (fun evs_p evs_f hp hfree => henv evs_fr evs_p evs_f hevs_fr hp hfree)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *])
    (by
      dsimp only [Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
        Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, *]
      sep_ac_rfl)

theorem decodeState_err_from_53b7c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1760#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_from_53b7c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hw hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized error conversion at `0x53b78` (`+1756`, 1 instruction):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`) and falls through to `0x53b7c`. -/
theorem decodeState_err_from_53b78_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1756#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 1760#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53b7c_placed_ofEnv hc x st0 st curSt (s.readReg64 .x8)
    s0 _ _ R post hpost herr hw hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_from_53b78_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hfits1 : FitsEnv M lim st DecodeErrorFromEnv)
    (hfits2 : ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1756#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_from_53b78_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hw hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized `InvalidKeyValue` (`key >= 2^32`) in `VersionNegotiation` `decode_key` at
`0x53b5c..0x53b64` (`+1728..+1736`, 3 instructions). -/
theorem decodeState_err_53b5c_placed_ofEnv [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1728#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  refine sepWPp_fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepWPp_exists_left; intro v_sc
  wp_steps_sync_pool ((blkPl_325).base + 1756#64)
  try simp only [State.setMem_setMem]
  refine sepWPp_fold (scratch_680_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  exact decodeState_err_from_53b78_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x1, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53b5c_placed [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1728#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53b5c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized `InvalidWireType` (`(key & 7) >= 6`) in `VersionNegotiation` `decode_key`
at `0x53b68..0x53b70` (`+1740..+1748`, 3 instructions). -/
theorem decodeState_err_53b68_placed_ofEnv [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  refine sepWPp_fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepWPp_exists_left; intro v_sc
  wp_steps_sync_pool ((blkPl_325).base + 1756#64)
  try simp only [State.setMem_setMem]
  refine sepWPp_fold (scratch_680_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  exact decodeState_err_from_53b78_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53b68_placed [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53b68_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized `InvalidTag` (`tag == 0`) in `VersionNegotiation` `decode_key` at
`0x53b74` (`+1752`, 1 instruction). -/
theorem decodeState_err_53b74_placed_ofEnv [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1752#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 1756#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53b78_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53b74_placed [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1752#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53b74_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized wire-type mismatch error (`wt != LengthDelimited`) on
`PqRatchetState::version_negotiation` at `0x53bd8..0x53be8` (`+1852..+1868`, 5 instructions). -/
theorem decodeState_err_53bd8_placed_ofEnv [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1852#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  refine sepWPp_fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepWPp_exists_left; intro b1
  apply sepWPp_exists_left; intro b0
  wp_steps_sync_pool ((blkPl_325).base + 1760#64)
  try simp only [State.setMem_setMem]
  refine sepWPp_fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  exact decodeState_err_from_53b7c_placed_ofEnv hc x st0 st curSt 0x8000000000000006#64
    s0 _ _ R post hpost herr (by decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm, hx21]
      sep_ac_rfl)

theorem decodeState_err_53bd8_placed [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 1852#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53bd8_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hx21 hP

/-- Envelope-parameterized `BufferUnderflow` (`len > rem`) on `VersionNegotiation` at
`0x53d00..0x53d04` (`+2148..+2152`, 2 instructions). -/
theorem decodeState_err_53d00_placed_ofEnv [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2148#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 1756#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53b78_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_53d00_placed [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2148#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_53d00_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hP

/-- Envelope-parameterized `BufferUnderflow` (`rem < limit`) on `VersionNegotiation` at
`0x54030..0x54034` (`+2964..+2968`, 2 instructions). -/
theorem decodeState_err_54030_placed_ofEnv [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2964#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  wp_steps_sync_pool ((blkPl_325).base + 1756#64)
  try simp only [State.setMem_setMem]
  exact decodeState_err_from_53b78_placed_ofEnv hc x st0 st curSt w0
    s0 _ _ R post hpost herr
    (by simp only [wp_norm, arm64_norm, hx21]; decide)
    hfits1 hfits2 henv
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    hs0A
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by
      dsimp only [decodeStateErrFramePlaced, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

theorem decodeState_err_54030_placed [LibsignalPlacement]
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
    (henv : ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)))
    (hpc : s.pc = decodeStatePlacedEntry + 2964#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_err_54030_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt w0 s0 s P R post hpost herr hfits1 hfits2 henv
    hpc hrun hsp hs0A htr hx19 hx21 hP

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudget
