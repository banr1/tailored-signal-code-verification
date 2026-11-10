/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Step Lemmas for `PolynomialDecoder::encode` (`Blocks 152 & 315`)

Defines placed contract propositions and pinned-to-unpinned bridges for `PolynomialDecoder::encode [local#1, 2]`,
and proves `VmPreserved`-threaded basic-block steppers for Blocks `152` and `315`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
  (EncodePolyDecoderEnv EncodePolyDecoderPinnedEnv
   encodePolyDecoderPinnedExactVmSpecOf
   encodePolyDecoderPinnedSpec encodePolyDecoderPinnedSpecOf
   encodePolyDecoderPinnedSpecOfEnv encodePolyDecoderPinnedSpecX
   encodePolyDecoderSpec encodePolyDecoderSpecOf
   encodePolyDecoderSpecOfEnv encodePolyDecoderSpecX
   polyDecoder_post_unpinned_of_pinned_env
   step_msg48rep_polyDecLen_call_prog)
open CryptoVerification
  (LibsignalPlacement blkPC_152 blkPC_315 blkPl_152 blkPl_315 lsProg_152 lsProg_315
   lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (StepInvPlaced sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Auth (vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Poly (ProtoPolynomialDecoderGhost boolByte)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyDecoderGhost EncodePolyDecoderPinnedGhost
   MsgEnc48CalleeSavedPlaced msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyDecoderElemsAt polyDecoder_tag_orr_eq
   protoPolynomialDecoderAt_eq_exists_pinned
   stackAt_msgEnc48_repeated stackAt_msgEnc48_repeated_recombine
   subroutine_ok_withLsCodeLoaded)

abbrev subroutine_ok_withLsCodeLoaded_dec := @subroutine_ok_withLsCodeLoaded

private theorem bv_sub_add_lit (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by
  bv_omega

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

private theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hpost⟩

private theorem sepWP_done_vm_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hvm : VmPreserved s0 s)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => VmPreserved s0 sm ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨hvm, hpost⟩

/-! ## 1. Call Wrapper, Pinned-to-Unpinned Bridges & Placed Contracts (Blocks `152` & `315`) -/

abbrev step_msg48rep_polyDecLen_call_placed := @step_msg48rep_polyDecLen_call_prog

theorem polyDecoder_unpinned_of_pinned_placed_env [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreP : EncodePolyDecoderPinnedGhost → (List AllocEvent → Prop) → Prop}
    {PreU : EncodePolyDecoderGhost → (List AllocEvent → Prop) → Prop}
    {PostP : EncodePolyDecoderPinnedGhost → List AllocEvent → Prop}
    {PostU : EncodePolyDecoderGhost → List AllocEvent → Prop}
    (hpre_env : ∀ (x : EncodePolyDecoderGhost) (g : ProtoPolynomialDecoderGhost) (st : M.σ),
      (∀ Env, PreU x Env → FitsEnv M lim st Env) →
      ∀ Env, PreP ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ Env → FitsEnv M lim st Env)
    (hpost_env : ∀ (x : EncodePolyDecoderGhost) (g : ProtoPolynomialDecoderGhost) evs,
      PostP ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ evs → PostU x evs)
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOfEnv resStack A lim PreP PostP))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpecOfEnv resStack A lim PreU PostU)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyDecoderSpecOfEnv] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hpts, hfit, hEnvU⟩, hrest⟩
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hrest
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hrest
  rcases hrest with ⟨g, hrest⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOfEnv resStack A lim PreP PostP)).pre
        (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv0, ?_⟩
    dsimp only [encodePolyDecoderPinnedSpecOfEnv]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hx1, hx2, hpts, hfit, hpre_env x g st hEnvU⟩, hrest⟩
  refine hpinned.mono_outcome (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest_out
  · exact Or.inl ⟨hret, hcc, polyDecoder_post_unpinned_of_pinned_env
      (PreP := PreP) (PreU := PreU) (hpost_env x g) hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest_out)

theorem polyDecoder_unpinned_of_pinned_placed_x [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecOf resStack A lim)).pre
        (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest_out
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact polyDecoder_post_unpinned_of_pinned_env
      (PreP := fun y Env => Env = EncodePolyDecoderPinnedEnv y)
      (PreU := fun y Env => Env = EncodePolyDecoderEnv y)
      (fun _ h => h)
      (by
        dsimp only [withLsCodeLoaded, encodePolyDecoderPinnedSpecOf] at hq
        dsimp only [encodePolyDecoderPinnedSpecOfEnv]
        exact hq)
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest_out)

/-- Relocatable base program for `PolynomialDecoder::encode [local#1, 2]` (Blocks `152` & `315`). -/
def IsPolyDecoderEncodePlacedBase (P_blk : Program) (pl : Placement) : Prop :=
  (∃ (inst : LibsignalPlacement), P_blk = @blkPC_152 inst ∧ pl = @blkPl_152 inst) ∨
  (∃ (inst : LibsignalPlacement), P_blk = @blkPC_315 inst ∧ pl = @blkPl_315 inst)

/-- Relocatable rebased program for `PolynomialDecoder::encode [local#1, 2]` (`lsProg_152 H` or `lsProg_315 H`). -/
def IsPolyDecoderEncodePlacedProg (prog : Program) (pl : Placement) : Prop :=
  ∃ P_blk H, prog = P_blk.rebase pl.base H ∧ IsPolyDecoderEncodePlacedBase P_blk pl

theorem isPolyDecoderEncodePlacedProg_152 [LibsignalPlacement]
    (H : String → Option (State → State)) :
    IsPolyDecoderEncodePlacedProg (lsProg_152 H) blkPl_152 :=
  ⟨blkPC_152, H, rfl, Or.inl ⟨‹_›, rfl, rfl⟩⟩

theorem isPolyDecoderEncodePlacedProg_315 [LibsignalPlacement]
    (H : String → Option (State → State)) :
    IsPolyDecoderEncodePlacedProg (lsProg_315 H) blkPl_315 :=
  ⟨blkPC_315, H, rfl, Or.inr ⟨‹_›, rfl, rfl⟩⟩

def EncodePolyDecoder152PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_152 H) (blkPl_152).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A lim))

def EncodePolyDecoder152PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_152 H) (blkPl_152).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A lim))

def EncodePolyDecoder152PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_152 H) (blkPl_152).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecX A lim))

def EncodePolyDecoder152PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_152 H) (blkPl_152).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpecX A lim))

def EncodePolyDecoder152PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder152PinnedPlacedOk A lim (Rust.withPanics ext)

def EncodePolyDecoder152PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder152PlacedOk A lim (Rust.withPanics ext)

def EncodePolyDecoder152PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder152PinnedPlacedOkX A lim (Rust.withPanics ext)

def EncodePolyDecoder152PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder152PlacedOkX A lim (Rust.withPanics ext)

def EncodePolyDecoder152PinnedExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_152 H) (blkPl_152).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedExactVmSpecOf resStack A))

def EncodePolyDecoder315PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_315 H) (blkPl_315).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A lim))

def EncodePolyDecoder315PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_315 H) (blkPl_315).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A lim))

def EncodePolyDecoder315PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_315 H) (blkPl_315).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecX A lim))

def EncodePolyDecoder315PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_315 H) (blkPl_315).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpecX A lim))

def EncodePolyDecoder315PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder315PinnedPlacedOk A lim (Rust.withPanics ext)

def EncodePolyDecoder315PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder315PlacedOk A lim (Rust.withPanics ext)

def EncodePolyDecoder315PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder315PinnedPlacedOkX A lim (Rust.withPanics ext)

def EncodePolyDecoder315PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  EncodePolyDecoder315PlacedOkX A lim (Rust.withPanics ext)

def EncodePolyDecoder315PinnedExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_315 H) (blkPl_315).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedExactVmSpecOf resStack A))

/-! ## 2. Placed Fetch Dispatch (Blocks `152` & `315`) -/

theorem polyDecoderPlaced_fetch_entry {P_blk : Program} {pl : Placement}
    (hbase : IsPolyDecoderEncodePlacedBase P_blk pl)
    (H : String → Option (State → State)) {ins : Instr}
    (h_152 : ∀ [LibsignalPlacement],
      (lsProg_152 H).fetch ((blkPl_152).base + 0#64) = some ins)
    (h_315 : ∀ [LibsignalPlacement],
      (lsProg_315 H).fetch ((blkPl_315).base + 0#64) = some ins) :
    (P_blk.rebase pl.base H).fetch pl.base = some ins := by
  rcases hbase with ⟨inst, rfl, rfl⟩ | ⟨inst, rfl, rfl⟩
  · simpa using @h_152 inst
  · simpa using @h_315 inst

theorem polyDecoderPlaced_fetch_add {P_blk : Program} {pl : Placement}
    (hbase : IsPolyDecoderEncodePlacedBase P_blk pl)
    (H : String → Option (State → State)) {k : Nat} {ins : Instr}
    (h_152 : ∀ [LibsignalPlacement],
      (lsProg_152 H).fetch ((blkPl_152).base + BitVec.ofNat 64 k) = some ins)
    (h_315 : ∀ [LibsignalPlacement],
      (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) = some ins) :
    (P_blk.rebase pl.base H).fetch (pl.base + BitVec.ofNat 64 k) = some ins := by
  rcases hbase with ⟨inst, rfl, rfl⟩ | ⟨inst, rfl, rfl⟩
  · exact @h_152 inst
  · exact @h_315 inst

open Lean Elab Tactic in
elab "pd_fetches_placed_only " hbase:ident H:ident kStart:num kEnd:num : tactic => do
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let kHex := String.ofList (Nat.toDigits 16 k)
    let p152 := mkIdent (`CryptoVerification |>.str s!"blkPC_152_rebase_fetch_0x{kHex}")
    let p315 := mkIdent (`CryptoVerification |>.str s!"blkPC_315_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := polyDecoderPlaced_fetch_entry $hbase $H
          (fun [LibsignalPlacement] => $p152 _ $H)
          (fun [LibsignalPlacement] => $p315 _ $H)))
    else
      evalTactic (← `(tactic|
        have := polyDecoderPlaced_fetch_add $hbase $H (k := $kq)
          (fun [LibsignalPlacement] => $p152 _ $H)
          (fun [LibsignalPlacement] => $p315 _ $H)))

/-! ## 3. Relocatable `VmPreserved`-Threaded Step Lemmas (Blocks `152` & `315`) -/

/-- Step `+0..+36`: allocates 48B frame (`msgEnc48SavedFrame`), saves `fp, lr, x21, x20, x19`,
sets `x20 = decA`, `x1 = v`, `x19 = v`, and `x0 = ((tag <<< 3) ||| 2#32).zeroExtend 64`. -/
theorem step_polyDecoder_prologue_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {pl : Placement} {s0 s : State}
    (hfn : IsPolyDecoderEncodePlacedProg prog pl) (tag : BitVec 32) (decA v sp : BitVec 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = pl.base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (s1 : State) (sv3 : BitVec 64),
      s1.pc = pl.base + 36#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = ((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64 →
      s1.readReg64 .x1 = v → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 → VmPreserved s s1 →
      SepWPp prog ret s1
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  have hw0' : BitVec.truncate 32 (s.readReg64 .x0) = tag := hw0
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 36#64)
  by_vm_steps (
    pd_fetches_placed_only hbase trapHooks 0 36
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv1
    refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ sv3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by dsimp only [State.readReg32, Reg.x0] at hw0' ⊢; simp only [arm64_norm, *]
            exact polyDecoder_tag_orr_eq tag)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        hvmp))

theorem step_polyDecoder_mov_x0_x20_40_placed
    {prog : Program} {pl : Placement} {s0 s : State}
    (hfn : IsPolyDecoderEncodePlacedProg prog pl) (decA v sp : BitVec 64)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = pl.base + 44#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = decA → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 → VmPreserved s s1 →
      SepWPp prog ret s1 P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  pd_fetches_placed_only hbase H 40 44
  examples_hide_fetches
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 44#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    hvmp

theorem step_polyDecoder_mov_x1_x19_48_placed
    {prog : Program} {pl : Placement} {s0 s : State}
    (hfn : IsPolyDecoderEncodePlacedProg prog pl) (decA v x0v sp : BitVec 64)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 48#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = x0v) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = pl.base + 52#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = x0v → s1.readReg64 .x1 = v → s1.readReg64 .x19 = v →
      s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 → VmPreserved s s1 →
      SepWPp prog ret s1 P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  pd_fetches_placed_only hbase H 48 52
  examples_hide_fetches
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 52#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    hvmp

/-- Step `+56..+64`: loads `w0 = [x20, #0x18]` (`pb.ptsNeeded`) and branches to `pl.base + 108#64`
if `pb.ptsNeeded == 0#32`, else falls through to `pl.base + 64#64`. -/
theorem step_polyDecoder_check_ptsNeeded_placed {prog : Program}
    {pl : Placement} (hfn : IsPolyDecoderEncodePlacedProg prog pl)
    (decA v sp : BitVec 64) (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 56#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + (if pb.ptsNeeded == 0#32 then 108#64 else 64#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (polyDecoderElemsAt decA g pb ptsElems ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  pd_fetches_placed_only hbase H 56 64
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpn : (pb.ptsNeeded == 0#32)
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hpn]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 64#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp)
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hpn]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 108#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp)

/-- Step `+80..+104`: stores tag byte `0x08#8` (`field 1, wire type varint`) into `curBs`
and sets `x1 = v`. -/
theorem step_polyDecoder_push_ptsNeeded_tag_placed {prog : Program} (A : RustAlloc)
    {pl : Placement} (hfn : IsPolyDecoderEncodePlacedProg prog pl)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 80#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 104#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 104#64)
  by_vm_steps (
    pd_fetches_placed_only hbase trapHooks 80 104
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Step `+108..+116`: loads `w0 = [x20, #0x1c]` (`pb.polys`) and branches to `pl.base + 160#64`
if `pb.polys == 0#32`, else falls through to `pl.base + 116#64`. -/
theorem step_polyDecoder_check_polys_placed {prog : Program}
    {pl : Placement} (hfn : IsPolyDecoderEncodePlacedProg prog pl)
    (decA v sp : BitVec 64) (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 108#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + (if pb.polys == 0#32 then 160#64 else 116#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (polyDecoderElemsAt decA g pb ptsElems ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  pd_fetches_placed_only hbase H 108 116
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpl : (pb.polys == 0#32)
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hpl]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 116#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp)
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hpl]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 160#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp)

/-- Step `+132..+156`: stores tag byte `0x10#8` (`field 2, wire type varint`) into `curBs`
and sets `x1 = v`. -/
theorem step_polyDecoder_push_polys_tag_placed {prog : Program} (A : RustAlloc)
    {pl : Placement} (hfn : IsPolyDecoderEncodePlacedProg prog pl)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 132#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = pl.base + 156#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 156#64)
  by_vm_steps (
    pd_fetches_placed_only hbase trapHooks 132 156
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv)
        hvmp))

/-- Step `+160..+172`: loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`,
sets `w0 = 3#32`, `x3 = v`. -/
theorem step_polyDecoder_prep_pts_placed
    {prog : Program} {pl : Placement} {s0 s : State}
    (hfn : IsPolyDecoderEncodePlacedProg prog pl) (decA v sp : BitVec 64)
    (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 160#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = pl.base + 172#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg32 .x0 = 3#32 → s1.readReg64 .x1 = g.pts.ptr →
      s1.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → s1.readReg64 .x3 = v →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 → VmPreserved s s1 →
      SepWPp prog ret s1 (polyDecoderElemsAt decA g pb ptsElems ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  pd_fetches_placed_only hbase H 160 172; examples_hide_fetches; subst hP
  dsimp only [polyDecoderElemsAt]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 172#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      hvmp)

/-- Step `+176..+188` / `+248..+264`: loads `w8 = [decA + 0x20]` (`boolByte pb.isComplete`).
- If `pb.isComplete = false`, branches to `+248` and executes the epilogue.
- If `pb.isComplete = true`, falls through to `+188`. -/
theorem step_polyDecoder_check_isComplete_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {pl : Placement} {s0 s : State}
    (hfn : IsPolyDecoderEncodePlacedProg prog pl)
    (decA v sp sv3 : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hfalse : pb.isComplete = false → ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → VmPreserved s sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F))
    (htrue : pb.isComplete = true → ∀ s1 : State,
      s1.pc = pl.base + 188#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 → VmPreserved s s1 →
      SepWPp prog (s0.readReg64 .lr) s1
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  pd_fetches_placed_only hbase H 176 188
  pd_fetches_placed_only hbase H 248 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  cases hc : pb.isComplete
  · have hbyte : boolByte pb.isComplete = 0#8 := by rw [hc]; rfl
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
    apply sepWPp_of_sepWP_cs_placed_vm (mid := s0.readReg64 .lr)
    dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    rw [hbyte]; wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinvf
    refine SepWPp.weaken_pre
      (show _ ⊢ (polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
    · rw [← hbyte]
      have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
        (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
        (s0.readReg64 .x20) (s0.readReg64 .x19)
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
      dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    · apply (hfalse hc)
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · epochEncLen_cc_close
      · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩
      · exact hvmp
  · have hbyte : boolByte pb.isComplete = 1#8 := by rw [hc]; rfl
    apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 188#64)
    dsimp only [polyDecoderElemsAt]; rw [hbyte]; wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *]); intro hvmp hinv1
    refine SepWPp.weaken_pre (by rw [← hbyte]; dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (htrue hc _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        hvmp)

/-- Step `+204..+228`: stores tag byte `0x20#8` (`field 4, wire type varint`) into `curBs`,
sets `x9 = curPtr`, `x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length`, and compares `x8 = curCap`
with `x10` at `+228`. -/
theorem step_polyDecoder_push_isComplete_tag_placed {prog : Program} (A : RustAlloc)
    {pl : Placement} {s0 s : State}
    (hfn : IsPolyDecoderEncodePlacedProg prog pl) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 204#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx8 : s.readReg64 .x8 = curCap) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = pl.base + 228#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x8 = curCap → s1.readReg64 .x9 = curPtr →
      s1.readReg64 .x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      s1.pstate = subsPState64 curCap (BitVec.ofNat 64 (curBs ++ [0x20#8]).length) →
      MsgEnc48CalleeSavedPlaced s0 s1 → VmPreserved s s1 →
      SepWPp prog ret s1 (vecU8At A v curCap curPtr (curBs ++ [0x20#8]) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := pl.base + 228#64)
  by_vm_steps (
    pd_fetches_placed_only hbase trapHooks 204 228
    examples_hide_fetches
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv1
    have hlen1 : BitVec.ofNat 64 curBs.length + 1#64 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length := by
      rw [List.length_append, List.length_singleton]; exact (BitVec.ofNat_add curBs.length 1).symm
    refine SepWPp.weaken_pre
      (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x20#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        hvmp))

/-- Step `+232..+264`: stores value byte `0x01#8` into `curBs`, updates `[v + 16] = curBs.length + 1`,
and executes the epilogue (`ldp x20, x19; ldr x21; ldp x29, x30, [sp], #0x30; ret`). -/
theorem step_polyDecoder_push_isComplete_val_epilogue_placed {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} (A : RustAlloc)
    {pl : Placement} {s0 s : State} (hfn : IsPolyDecoderEncodePlacedProg prog pl)
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pl.base + 232#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length) (hx19 : s.readReg64 .x19 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → VmPreserved s sf →
      Q sf ((vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp oom := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := s0.readReg64 .lr)
  by_vm_steps (
    pd_fetches_placed_only hbase trapHooks 232 264
    examples_hide_fetches
    dsimp only [msgEnc48SavedFrame]
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinvf
    refine SepWPp.weaken_pre
      (show _ ⊢ (vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
    · rw [← vecU8At_close_one A v curCap curPtr curBs 0x01#8 hlt]
      have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
        (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
        (s0.readReg64 .x20) (s0.readReg64 .x19)
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
      dsimp only [msgEnc48SavedFrame]
    · apply hnext
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · epochEncLen_cc_close
      · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩
      · exact hvmp)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
