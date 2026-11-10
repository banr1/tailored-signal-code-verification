/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed `SessionRecord::serialize` (`Prev1`) Body Specs and Step Statements

Budget-threaded `[LibsignalPlacement]` body contracts, field-2 allocation envelope `SerField2Env`
and step statements (`+444 .. +692`), and lifted `serializeSubStackX` callee contracts for
`<SessionRecord>::serialize` (block 52).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded
  withLsCl
)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52 blkPl_117)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (serializeSubStackX)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (prevVecAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (serializeStackX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (SepWPpLsCl)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget (
  SerializePrev1PlacedOkWithEnvStmt SerializePrev1PlacedOkStmt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  VecVecClone1Ghost
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget (
  VecVecClone1PlacedOkStmt vecVecClone1_placed_ok_cl
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget (
  SerializePrev1BodyGhost SerField2Saved encodeRecordPrev1Mem serializePrev1BodySpecX
  vecVecClone1SubSpecX vecVecClone1_withLsCodeLoaded_sub_okX vecVecClone1_withLsCl_sub_okX
)

/-! ## Body and Bridge Statements -/

/-- Envelope-parameterized budget-threaded body contract for `SessionRecord::serialize` on a
record with current session `x.sess` (ghost `x.G`) and `previous_sessions = [x.enc]`. -/
def serializePrev1BodySpecWithEnvX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec (SerializePrev1BodyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      FitsEnv M lim st (Env x.G x.sess x.enc)⌝ ∗
      prevVecAt A.repAlloc x.self x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      memRegion x.out 32 ∗ A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.G x.sess x.enc evs⌝ ∗
        prevVecAt A.repAlloc x.self x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
        (x.out ↦₆₄ okTagVec) ∗
        vecU8 A.repAlloc (x.out + 8#64) (encodeRecordPrev1Mem x.G x.sess x.enc) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

theorem serializePrev1BodySpecWithEnvX_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    serializePrev1BodySpecWithEnvX M A lim SerializePrev1Env = serializePrev1BodySpecX M A lim :=
  rfl

def SerializePrev1BodyPlacedOkWithEnvStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) :
    Prop :=
  subroutine_ok (lsProg_52 H) (blkPl_52).base
    (withLsCodeLoaded lsmpl (serializePrev1BodySpecWithEnvX M A lim Env))

def SerializePrev1BodyPlacedOkStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_52 H) (blkPl_52).base
    (withLsCodeLoaded lsmpl (serializePrev1BodySpecX M A lim))

theorem serializePrev1BodyPlacedOkWithEnvStmt_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs)
    (h : SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env₁) :
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env₂ := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [withLsCodeLoaded, serializePrev1BodySpecWithEnvX] at hp ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨hcl, hp⟩
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.mono (himp x.G x.sess x.enc)⟩, hp.2⟩
  · dsimp only [withLsCodeLoaded, serializePrev1BodySpecWithEnvX] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, himp x.G x.sess x.enc evs hq.1.2⟩, hq.2⟩

def SerializePrev1PlacedBridgeWithEnvStmt [LibsignalPlacement] : Prop :=
  ∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop),
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env →
      SerializePrev1PlacedOkWithEnvStmt (lsProg_52 H) M A lim Env

def SerializePrev1PlacedBridgeStmt [LibsignalPlacement] : Prop :=
  ∀ (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks),
    SerializePrev1BodyPlacedOkStmt M A lim H →
      SerializePrev1PlacedOkStmt (lsProg_52 H) M A lim

/-! ## Field-2 Write Envelope and Step Statements (`+444 .. +692`) -/

/-- Allocation envelope for the field-2 write block (`+444 .. +692`) of
`SessionRecord::serialize`: empty when `bs.length + (lenField 2 enc).length ≤ cap.toNat`, and
`EncRawSegEnv bs.length (lenField 2 enc).length` when capacity grows. -/
def SerField2Env (cap : BitVec 64) (bs enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if bs.length + (lenField 2 enc).length ≤ cap.toNat then evs = []
  else EncRawSegEnv bs.length (lenField 2 enc).length evs

theorem serField2Env_of_spare {cap : BitVec 64} {bs enc : List (BitVec 8)} {evs : List AllocEvent}
    (hspare : bs.length + (lenField 2 enc).length ≤ cap.toNat) :
    SerField2Env cap bs enc evs ↔ evs = [] := by
  unfold SerField2Env
  split
  · exact Iff.rfl
  · contradiction

theorem serField2Env_of_not_spare {cap : BitVec 64} {bs enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (hnspare : ¬ bs.length + (lenField 2 enc).length ≤ cap.toNat) :
    SerField2Env cap bs enc evs ↔ EncRawSegEnv bs.length (lenField 2 enc).length evs := by
  unfold SerField2Env
  split
  · contradiction
  · exact Iff.rfl

theorem encRawSegEnv_of_serField2Env {cap : BitVec 64} {bs enc : List (BitVec 8)}
    {evs : List AllocEvent} (h : SerField2Env cap bs enc evs) :
    EncRawSegEnv bs.length (lenField 2 enc).length evs := by
  unfold SerField2Env at h
  split at h
  · subst h
    exact encRawSegEnv_nil bs.length (lenField 2 enc).length
  · exact h

theorem fitsEnv_serField2_of_spare {M : AllocCostModel} {lim : BudgetLimits} (st : M.σ)
    {cap : BitVec 64} {bs enc : List (BitVec 8)}
    (hspare : bs.length + (lenField 2 enc).length ≤ cap.toNat) :
    FitsEnv M lim st (SerField2Env cap bs enc) := by
  intro evs hevs
  rw [(serField2Env_of_spare hspare).mp hevs]
  trivial

theorem fitsEnv_serField2_of_encRawSeg {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {cap : BitVec 64} {bs enc : List (BitVec 8)}
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (lenField 2 enc).length)) :
    FitsEnv M lim st (SerField2Env cap bs enc) :=
  FitsEnv.mono (fun _ => encRawSegEnv_of_serField2Env) hfit

/-- Continuation-passing `SepWPpLsCl` contract for the budget-threaded field-2 write block
(`+444 .. +692`) on `lsProg_52 H`. -/
def SerField2PlacedStepStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (sp0 q' cap ptr capE ptrE : BitVec 64) (bs enc : List (BitVec 8)) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop},
    bs.length + (lenField 2 enc).length < 2 ^ 32 →
    FitsEnv M lim st (SerField2Env cap bs enc) →
    s.pc = (blkPl_52).base + bv% (444) →
    s.status = .Running →
    s.sp = sp0 - 800#64 →
    sp0 &&& 15#64 = 0#64 →
    s.trace = s0.trace →
    s.readReg64 .x22 = q' →
    s.readReg64 .x25 = 1#64 →
    P = (vecU8At A.repAlloc (sp0 - 432#64) cap ptr bs ∗
      vecU8At A.repAlloc q' capE ptrE enc ∗
      A.pool lim st s ∗
      stackAt (sp0 - 800#64) serializeSubStackX) ∗ F →
    (∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      SerField2Env cap bs enc evs →
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved s sm →
      SepWPpLsCl lsmpl (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc (sp0 - 432#64) cap' ptr' (bs ++ lenField 2 enc) ∗
          vecU8At A.repAlloc q' capE ptrE enc ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) →
    SepWPpLsCl lsmpl (lsProg_52 H) ret s P Q Qp

def SerField2PlacedStepSepWPStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (sp0 q' cap ptr capE ptrE : BitVec 64) (bs enc : List (BitVec 8)) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop},
    bs.length + (lenField 2 enc).length < 2 ^ 32 →
    FitsEnv M lim st (SerField2Env cap bs enc) →
    LibsignalCodeLoaded lsmpl s.mem →
    s.pc = (blkPl_52).base + bv% (444) →
    s.status = .Running →
    s.sp = sp0 - 800#64 →
    sp0 &&& 15#64 = 0#64 →
    s.trace = s0.trace →
    s.readReg64 .x22 = q' →
    s.readReg64 .x25 = 1#64 →
    P = (vecU8At A.repAlloc (sp0 - 432#64) cap ptr bs ∗
      vecU8At A.repAlloc q' capE ptrE enc ∗
      A.pool lim st s ∗
      stackAt (sp0 - 800#64) serializeSubStackX) ∗ F →
    (∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      SerField2Env cap bs enc evs →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved s sm →
      SepWP (lsProg_52 H) ret sm
        ((vecU8At A.repAlloc (sp0 - 432#64) cap' ptr' (bs ++ lenField 2 enc) ∗
          vecU8At A.repAlloc q' capE ptrE enc ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q) →
    SepWP (lsProg_52 H) ret s P Q

/-! ## Lifted Callee Contracts at `serializeSubStackX` -/

theorem vecVecClone1_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hK1 : VecVecClone1PlacedOkStmt M A lim H) :
    subroutine_ok callerProg (blkPl_117).base
      (withLsCodeLoaded lsmpl (vecVecClone1SubSpecX M A lim)) :=
  vecVecClone1_withLsCodeLoaded_sub_okX
    (vecVecClone1_placed_ok_cl (callerProg := callerProg) hK1)

theorem vecVecClone1_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hK1 : VecVecClone1PlacedOkStmt M A lim H) :
    subroutine_ok callerProg (blkPl_117).base
      (withLsCl lsmpl (vecVecClone1SubSpecX M A lim)) :=
  vecVecClone1_withLsCl_sub_okX
    (vecVecClone1_placed_ok_cl (callerProg := callerProg) hK1)

abbrev dealloc_placed_sub_okX :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget.dealloc_placed_sub_okX
abbrev dealloc_placed_sub_clX :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget.dealloc_placed_sub_clX

/-! ## Tail Step (`+692 .. ret`) Re-Exports -/

abbrev SerPrev1PlacedTailStmt :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.SerPrev1PlacedTailStmt
abbrev serPrev1Tail_placed_ok :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.serPrev1Tail_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
