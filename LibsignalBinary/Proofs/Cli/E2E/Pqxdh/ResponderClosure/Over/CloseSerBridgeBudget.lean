/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecCloneBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClonePlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `SessionRecord::serialize` (`Prev1`) Bridge and Callee Assembly

Lifts the budget-threaded body contract `serializePrev1BodySpecWithEnvX` for
`SessionRecord::serialize` with one previous session to the 48-byte `serializePrev1SpecWithEnv` and
canonical 32-byte `serializePrev1CanonSpecWithEnvX` contracts, and assembles all placed callee
obligations from `SerContractsXPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgeBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.E2E.Bin (recordSerializeStack)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (prevVecAt sessionRecordPrevAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCodeLoaded_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget (Stage2ContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (do_reserve_placed_ok_ext_x)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget (
  drop_session_structure_local1_placed_ok_ext
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX serializeStackX_le_recordSerializeStack
  SerContractsXPlaced serContractsXPlaced_of_stage2ContractsPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  DoReservePlacedOkX EncodeVarintPlacedOkX EncodeRawPlacedOkX
  SessionClonePlacedOkX DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerXBudget (
  encodeRaw_placed_ok_of_serContractsX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneXBudget (
  sessionClone_placed_ok_ext
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (
  encode_varint_placed_ok_of_doReserve_x
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Ghost encodeRecordPrev1 encodeRecordPrev1Mem_eq_of_canon
  SerializePrev1Env serializePrev1SpecWithEnv serializePrev1Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget (
  SerializePrev1PlacedOkWithEnvStmt SerializePrev1PlacedOkStmt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget (
  VecVecClone1PlacedOkStmt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClonePlacedBudget (
  vecVecClone1_placed_okX_of_ser
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget (
  SerializePrev1BodyGhost serializePrev1BodySpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget (
  serializePrev1BodySpecWithEnvX
  SerializePrev1BodyPlacedOkWithEnvStmt SerializePrev1BodyPlacedOkStmt
  SerializePrev1PlacedBridgeWithEnvStmt SerializePrev1PlacedBridgeStmt
  SerField2PlacedStepStmt SerPrev1PlacedTailStmt serPrev1Tail_placed_ok
)

/-! ## Representation and Stack-Split Helpers -/

abbrev sessionRecordPrevAt_some_eq :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.sessionRecordPrevAt_some_eq

private theorem stackAt_sub_split_k5b (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

theorem stackAt_recordSerialize_split_k5b (sp : BitVec 64) :
    stackAt sp recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - serializeStackX) ∗
      stackAt sp serializeStackX :=
  stackAt_sub_split_k5b sp serializeStackX recordSerializeStack
    serializeStackX_le_recordSerializeStack (by decide)

theorem memRegion_48_split_32_16_k5b (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

theorem sessionRecordPrevAt_atState_some_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (r cap ptr : BitVec 64) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    sessionRecordPrevAt (A.atState lim st s) r ⟨cap, ptr, some G⟩ [enc] ⟨some sess⟩ =
      prevVecAt A.repAlloc r cap ptr [enc] ∗ sessionStateReprAt A.repAlloc (r + 24#64) G sess :=
  sessionRecordPrevAt_some_eq (A.atState lim st s) r cap ptr G sess [enc]

theorem vecU8_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 (A.atState lim st s) addr bs = vecU8 A.repAlloc addr bs :=
  rfl

/-! ## Canonical 32-Byte-Output Contracts -/

/-- Envelope-parameterized canonical-ghost 32-byte-`out` contract for `SessionRecord::serialize`
at `serializeStackX`. -/
def serializePrev1CanonSpecWithEnvX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec (SerializePrev1BodyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      CanonSession x.G x.sess ∧
      (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32 ∧
      FitsEnv M lim st (Env x.G x.sess x.enc)⌝ ∗
      sessionRecordPrevAt A.repAlloc x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      memRegion x.out 32 ∗ A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.G x.sess x.enc evs⌝ ∗
        sessionRecordPrevAt A.repAlloc x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
        (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encodeRecordPrev1 x.sess x.enc) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-- Canonical-ghost 32-byte-`out` contract instantiated at `SerializePrev1Env`. -/
def serializePrev1CanonSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializePrev1BodyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      CanonSession x.G x.sess ∧
      (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializePrev1Env x.G x.sess x.enc)⌝ ∗
      sessionRecordPrevAt A.repAlloc x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      memRegion x.out 32 ∗ A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializePrev1Env x.G x.sess x.enc evs⌝ ∗
        sessionRecordPrevAt A.repAlloc x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
        (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encodeRecordPrev1 x.sess x.enc) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

theorem serializePrev1CanonSpecWithEnvX_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    serializePrev1CanonSpecWithEnvX M A lim SerializePrev1Env =
      serializePrev1CanonSpecX M A lim :=
  rfl

/-! ## Body-to-Top and Body-to-Canonical Bridges -/

/-- Lifts `serializePrev1BodySpecWithEnvX` to the 48-byte `serializePrev1SpecWithEnv` contract
under envelope inclusion `Env₁ ⊆ Env₂`. -/
theorem serializePrev1_bridge_withEnv {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : subroutine_ok prog entry (serializePrev1BodySpecWithEnvX M A lim Env₁))
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok prog entry (serializePrev1SpecWithEnv M A lim Env₂) := by
  refine subroutine_ok_map_oom' hBody
    (fun ⟨x, st⟩ R s0 hpre => ?_)
    (fun _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
  dsimp only [serializePrev1SpecWithEnv,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec] at hpre
  rw [RustCliAllocBudget.atState_pool,
      sessionRecordPrevAt_atState_some_eq A lim st s0 x.self x.prevCap x.prevPtr x.G x.sess x.enc,
      memRegion_48_split_32_16_k5b x.out,
      stackAt_recordSerialize_split_k5b s0.sp] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hFit₂, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon.toCanonSession
  have hFit₁ : FitsEnv M lim st (Env₁ x.G x.sess x.enc) :=
    hFit₂.mono (himp x.G x.sess x.enc)
  let x_body : SerializePrev1BodyGhost :=
    ⟨x.self, x.out, x.prevCap, x.prevPtr, x.G, x.sess, x.enc⟩
  let R_body : SepProp :=
    memRegion (x.out + 32#64) 16 ∗
      memRegion (s0.sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - serializeStackX) ∗ R
  refine ⟨(x_body, st), R_body, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem,
      x_body, R_body]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, henc.symm ▸ hlen, hFit₁⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · intro sf hq
    dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem,
      x_body, R_body] at hq
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq_mem⟩
    rw [henc] at hq_mem
    dsimp only [serializePrev1SpecWithEnv,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [RustCliAllocBudget.atState_pool,
        sessionRecordPrevAt_atState_some_eq A lim (M.stepEvents evs st) sf
          x.self x.prevCap x.prevPtr x.G x.sess x.enc,
        vecU8_atState_eq,
        stackAt_recordSerialize_split_k5b s0.sp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himp x.G x.sess x.enc evs hevs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem

theorem serializePrev1_bridge {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hBody : subroutine_ok prog entry (serializePrev1BodySpecX M A lim)) :
    subroutine_ok prog entry (serializePrev1Spec M A lim) :=
  serializePrev1_bridge_withEnv hBody (fun _ _ _ _ hev => hev)

theorem serializePrev1_withLsCodeLoaded_of_body_withEnv {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1BodySpecWithEnvX M A lim Env₁)))
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1SpecWithEnv M A lim Env₂)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' hBody fun ⟨x, st⟩ R s0 hpre => ?_
  dsimp only [serializePrev1SpecWithEnv,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec] at hpre
  rw [RustCliAllocBudget.atState_pool,
      sessionRecordPrevAt_atState_some_eq A lim st s0 x.self x.prevCap x.prevPtr x.G x.sess x.enc,
      memRegion_48_split_32_16_k5b x.out,
      stackAt_recordSerialize_split_k5b s0.sp] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hFit₂, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon.toCanonSession
  have hFit₁ : FitsEnv M lim st (Env₁ x.G x.sess x.enc) :=
    hFit₂.mono (himp x.G x.sess x.enc)
  let x_body : SerializePrev1BodyGhost :=
    ⟨x.self, x.out, x.prevCap, x.prevPtr, x.G, x.sess, x.enc⟩
  let R_body : SepProp :=
    memRegion (x.out + 32#64) 16 ∗
      memRegion (s0.sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - serializeStackX) ∗ R
  refine ⟨(x_body, st), R_body, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem,
      x_body, R_body]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, henc.symm ▸ hlen, hFit₁⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · intro sf hq
    dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem,
      x_body, R_body] at hq
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq_mem⟩
    rw [henc] at hq_mem
    dsimp only [serializePrev1SpecWithEnv,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serializePrev1Spec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [RustCliAllocBudget.atState_pool,
        sessionRecordPrevAt_atState_some_eq A lim (M.stepEvents evs st) sf
          x.self x.prevCap x.prevPtr x.G x.sess x.enc,
        vecU8_atState_eq,
        stackAt_recordSerialize_split_k5b s0.sp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himp x.G x.sess x.enc evs hevs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem

theorem serializePrev1_withLsCodeLoaded_of_body {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hBody : subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1BodySpecX M A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1Spec M A lim)) :=
  serializePrev1_withLsCodeLoaded_of_body_withEnv hBody (fun _ _ _ _ hev => hev)

theorem serializePrev1_placed_ok_codeLoaded_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env₁)
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1SpecWithEnv M A lim Env₂)) :=
  serializePrev1_withLsCodeLoaded_of_body_withEnv hBody himp

theorem serializePrev1_placed_ok_codeLoaded [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hBody : SerializePrev1BodyPlacedOkStmt M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1Spec M A lim)) :=
  serializePrev1_withLsCodeLoaded_of_body hBody

theorem serializePrev1_placed_bridge_withEnv [LibsignalPlacement] :
    SerializePrev1PlacedBridgeWithEnvStmt := by
  intro M A lim H Env hBody
  exact ls_subroutine_ok_cl_of_callee (callerProg := lsProg_52 H) (j := 52)
    (serializePrev1_placed_ok_codeLoaded_withEnv hBody (fun _ _ _ _ hev => hev))

theorem serializePrev1_placed_bridge [LibsignalPlacement] :
    SerializePrev1PlacedBridgeStmt := by
  intro M A lim H hBody
  exact ls_subroutine_ok_cl_of_callee (callerProg := lsProg_52 H) (j := 52)
    (serializePrev1_placed_ok_codeLoaded hBody)

/-- Lifts `serializePrev1BodySpecWithEnvX` to the canonical-ghost contract
`serializePrev1CanonSpecWithEnvX` under `Env₁ ⊆ Env₂`. -/
theorem serializePrev1CanonX_of_body_withEnv {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : subroutine_ok prog entry (serializePrev1BodySpecWithEnvX M A lim Env₁))
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok prog entry (serializePrev1CanonSpecWithEnvX M A lim Env₂) := by
  refine subroutine_ok_map_oom' hBody
    (fun ⟨x, st⟩ R s0 hpre => ?_)
    (fun _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
  dsimp only [serializePrev1CanonSpecWithEnvX, encodeRecordPrev1] at hpre
  rw [sessionRecordPrevAt_some_eq A.repAlloc x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hcanon, hlen, hFit₂⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  refine ⟨(x, st), R, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, henc.symm ▸ hlen, hFit₂.mono (himp x.G x.sess x.enc)⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · intro sf hq
    dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem] at hq
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq_mem⟩
    rw [henc] at hq_mem
    dsimp only [serializePrev1CanonSpecWithEnvX, encodeRecordPrev1]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sessionRecordPrevAt_some_eq A.repAlloc x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, himp x.G x.sess x.enc evs hevs⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem⟩

theorem serializePrev1CanonX_of_body {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hBody : subroutine_ok prog entry (serializePrev1BodySpecX M A lim)) :
    subroutine_ok prog entry (serializePrev1CanonSpecX M A lim) :=
  serializePrev1CanonX_of_body_withEnv hBody (fun _ _ _ _ hev => hev)

theorem serializePrev1CanonX_withLsCodeLoaded_of_body_withEnv {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1BodySpecWithEnvX M A lim Env₁)))
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1CanonSpecWithEnvX M A lim Env₂)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' hBody fun ⟨x, st⟩ R s0 hpre => ?_
  dsimp only [serializePrev1CanonSpecWithEnvX, encodeRecordPrev1] at hpre
  rw [sessionRecordPrevAt_some_eq A.repAlloc x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hcanon, hlen, hFit₂⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  refine ⟨(x, st), R, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, henc.symm ▸ hlen, hFit₂.mono (himp x.G x.sess x.enc)⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · intro sf hq
    dsimp only [serializePrev1BodySpecWithEnvX, CloseSerDefsBudget.encodeRecordPrev1Mem] at hq
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq_mem⟩
    rw [henc] at hq_mem
    dsimp only [serializePrev1CanonSpecWithEnvX, encodeRecordPrev1]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sessionRecordPrevAt_some_eq A.repAlloc x.self x.prevCap x.prevPtr x.G x.sess [x.enc],
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, himp x.G x.sess x.enc evs hevs⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem⟩

theorem serializePrev1CanonX_withLsCodeLoaded_of_body {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hBody : subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1BodySpecX M A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_withLsCodeLoaded_of_body_withEnv hBody (fun _ _ _ _ hev => hev)

theorem serializePrev1CanonX_of_body_placed_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env₁)
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env₂)) :=
  serializePrev1CanonX_withLsCodeLoaded_of_body_withEnv hBody himp

theorem serializePrev1CanonX_of_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hBody : SerializePrev1BodyPlacedOkStmt M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializePrev1CanonSpecX M A lim)) :=
  serializePrev1CanonX_withLsCodeLoaded_of_body hBody

theorem serializePrev1CanonX_placed_cl_of_body_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env₁)
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecWithEnvX M A lim Env₂)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1CanonX_of_body_placed_withEnv hBody himp)

theorem serializePrev1CanonX_placed_cl_of_body [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hBody : SerializePrev1BodyPlacedOkStmt M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializePrev1CanonSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1CanonX_of_body_placed hBody)

theorem serializePrev1_placed_cl_of_body_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hBody : SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env₁)
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs) :
    SerializePrev1PlacedOkWithEnvStmt callerProg M A lim Env₂ :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1_placed_ok_codeLoaded_withEnv hBody himp)

theorem serializePrev1_placed_cl_of_body [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hBody : SerializePrev1BodyPlacedOkStmt M A lim H) :
    SerializePrev1PlacedOkStmt callerProg M A lim :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 52)
    (serializePrev1_placed_ok_codeLoaded hBody)

/-! ## Placed Callee Contract Assembly -/

/-- Placed callee and tail-step contracts for `SessionRecord::serialize` (block 52) with one
previous session. -/
structure SerPrev1CalleeContractsPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  sessionClone : SessionClonePlacedOkX M A lim H
  doReserve : DoReservePlacedOkX M A lim H
  encodeVarint : EncodeVarintPlacedOkX M A lim H
  encodeRaw : EncodeRawPlacedOkX M A lim H
  vecVecClone1 : VecVecClone1PlacedOkStmt M A lim H
  dropLocal1 : DropSessionStructureLocal1PlacedOkX M A lim H
  tail : SerPrev1PlacedTailStmt M A lim H

theorem serPrev1Callees_placed_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SerPrev1CalleeContractsPlaced M A lim H := by
  have hDR : DoReservePlacedOkX M A lim H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX M A lim H :=
    encode_varint_placed_ok_of_doReserve_x A lim H hDR
  have hDrop : DropSessionStructureLocal1PlacedOkX M A lim H :=
    drop_session_structure_local1_placed_ok_ext hC.alloc
  exact
    { sessionClone := sessionClone_placed_ok_ext hC
      doReserve := hDR
      encodeVarint := hEV
      encodeRaw := encodeRaw_placed_ok_of_serContractsX hC
      vecVecClone1 := vecVecClone1_placed_okX_of_ser hC
      dropLocal1 := hDrop
      tail := serPrev1Tail_placed_ok hC hDrop }

theorem serPrev1Callees_placed_of_stage2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H) :
    SerPrev1CalleeContractsPlaced M A lim H :=
  serPrev1Callees_placed_of_serContractsX (serContractsXPlaced_of_stage2ContractsPlaced hC)

theorem serializePrev1Body_placed_ok_of_serContractsX_with [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hField2 : DoReservePlacedOkX M A lim H → EncodeVarintPlacedOkX M A lim H →
      SerField2PlacedStepStmt M A lim H)
    (hBodyComb : SessionClonePlacedOkX M A lim H → EncodeVarintPlacedOkX M A lim H →
      EncodeRawPlacedOkX M A lim H → VecVecClone1PlacedOkStmt M A lim H →
      SerField2PlacedStepStmt M A lim H → SerPrev1PlacedTailStmt M A lim H →
      SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env) :
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env := by
  have hCal := serPrev1Callees_placed_of_serContractsX hC
  exact hBodyComb hCal.sessionClone hCal.encodeVarint hCal.encodeRaw hCal.vecVecClone1
    (hField2 hCal.doReserve hCal.encodeVarint) hCal.tail

theorem serializePrev1_placed_ok_of_serContractsX_with [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hC : SerContractsXPlaced M A lim H)
    (hField2 : DoReservePlacedOkX M A lim H → EncodeVarintPlacedOkX M A lim H →
      SerField2PlacedStepStmt M A lim H)
    (hBodyComb : SessionClonePlacedOkX M A lim H → EncodeVarintPlacedOkX M A lim H →
      EncodeRawPlacedOkX M A lim H → VecVecClone1PlacedOkStmt M A lim H →
      SerField2PlacedStepStmt M A lim H → SerPrev1PlacedTailStmt M A lim H →
      SerializePrev1BodyPlacedOkWithEnvStmt M A lim H Env) :
    SerializePrev1PlacedOkWithEnvStmt (lsProg_52 H) M A lim Env :=
  serializePrev1_placed_bridge_withEnv M A lim H Env
    (serializePrev1Body_placed_ok_of_serContractsX_with hC hField2 hBodyComb)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgeBudget
