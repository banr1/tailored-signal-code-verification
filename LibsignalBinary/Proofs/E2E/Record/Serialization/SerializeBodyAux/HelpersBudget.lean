/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch

/-!
# Budget-threaded callee specifications for `SessionRecord::serialize`

Lifts the seven `SessionRecord::serialize` callee contracts (`vecVecCloneEmptySpec`,
`sessionCloneSpec`, `sessionLenSpec`, `encodeVarintSpec`, `encodeRawSpec`,
`dropSessionStructureLocal1Spec`, and `rustCliAlloc*`) to `serializeSubStack` on block `52`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.HelpersBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement lsmpl withLsCodeLoaded withLsCl ls_subroutine_ok_of_block
  subroutine_ok_withLsCodeLoaded_of_plain lsRustAllocSym
  lsρ ls_hook_ok_of_mem blkPC_6 blkPl_6 blkPC_10 blkPl_10
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At allocHookStack)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAt)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  encodeVarintStack EncodeVarintGhost
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal1Name dropSessionStructureLocal1Stack
)
open CryptoVerification.E2E.Record.Placed (
  blkPl_14 lsProg_14 lsProg_52 blkPl_80 lsProg_80 blkPl_86 lsProg_86 blkPl_117 lsProg_117
)
open CryptoVerification.E2E.Record.Serialization (
  OkAt vecVecCloneStack sessionCloneStack sessionLenStack encodeRawStack encSessionMem
  VecVecCloneGhost SessionCloneGhost SessionLenGhost EncodeRawGhost
  serializeName vecVecCloneName sessionCloneName sessionLenName encodeRawName
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  serializeSubStack stackAt_serializeSub_split
  subroutine_ok_frame_weaken subroutine_ok_withLsCodeLoaded_frame_weaken
  subroutine_ok_withLsCl_of_withLsCodeLoaded
  libsignalSessionCode_fnOff_serialize libsignalSessionCode_fnOff_vecVecClone
  libsignalSessionCode_fnOff_sessionClone libsignalSessionCode_fnOff_sessionLen
  libsignalSessionCode_fnOff_encodeVarint libsignalSessionCode_fnOff_encodeRaw
  libsignalSessionCode_fnOff_dropLocal1
)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv FreeOnlyEvs
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
  subroutine_ok_rustCliAllocBudget_withStack subroutine_ok_rustCliAllocNoOom_withStack
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  vecVecCloneEmptySpec sessionCloneSpec sessionLenSpec encodeRawSpec
  SessionCloneEnv EncodeRawEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpec EncodeVarintOk
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal1Spec
)

/-! ## Lifted callee specifications at `serializeSubStack` -/

def vecVecCloneSubSpec : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp serializeSubStack

theorem vecVecClone_sub_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVV : OkAt b C ctl abs vecVecCloneName vecVecCloneEmptySpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      vecVecCloneSubSpec := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr vecVecCloneName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_vecVecClone,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - vecVecCloneStack))
    hVV
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

def sessionCloneSubSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SessionCloneEnv x.G x.s)⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗ memRegion x.dst 344 ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SessionCloneEnv x.G x.s evs⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A.repAlloc x.dst G' x.s) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStack

theorem sessionClone_sub_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hClone : OkAt b C ctl abs sessionCloneName (sessionCloneSpec M A lim)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (sessionCloneSubSpec M A lim) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_sessionClone,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - sessionCloneStack))
    hClone
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpec, sessionCloneSpec,
      stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [sessionCloneSubSpec, sessionCloneSpec]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

def sessionLenSubSpec (A : RustAlloc) : Spec SessionLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encSessionMem x.G x.s).length ∧
      sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s0.sp serializeSubStack

theorem sessionLen_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hLen : OkAt b C ctl abs sessionLenName (sessionLenSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (sessionLenSubSpec A) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_sessionLen,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - sessionLenStack))
    hLen
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

def encodeVarintSubSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧ x.bs.length + 10 < 2 ^ 62 ∧
      FitsEnv M lim st (EncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp serializeSubStack

theorem encodeVarint_sub_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : EncodeVarintOk b C A lim ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      (encodeVarintSubSpec M A lim) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarintName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_encodeVarint,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - encodeVarintStack))
    hEV
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpec, encodeVarintSpec,
      stackAt_serializeSub_split s0.sp encodeVarintStack (by decide)]
    refine Entails.trans (sepConj_mono_left (Entails.pure_mono
      (ψ := s0.readReg64 .x0 = x.val ∧ s0.readReg64 .x1 = x.v ∧
        (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
        FitsEnv M lim st (EncodeVarintEnv x))
      fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, Or.inr h2, h3⟩)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [encodeVarintSubSpec, encodeVarintSpec,
      stackAt_serializeSub_split s0.sp encodeVarintStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

def encodeRawSubSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeRawGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32 ∧
      FitsEnv M lim st (EncodeRawEnv x)⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp serializeSubStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ EncodeRawEnv x evs⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStack

theorem encodeRaw_sub_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hRaw : OkAt b C ctl abs encodeRawName (encodeRawSpec M A lim)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      (encodeRawSubSpec M A lim) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_encodeRaw,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - encodeRawStack))
    hRaw
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpec, encodeRawSpec,
      stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [encodeRawSubSpec, encodeRawSpec]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

def dropLocal1SubSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStack

def dropLocal1SubSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStack

theorem dropLocal1_sub_ok [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDrop : OkAt b C ctl abs dropSessionStructureLocal1Name (dropSessionStructureLocal1Spec M A lim)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      (dropLocal1SubSpec M A lim) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructureLocal1Name =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_dropLocal1,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - dropSessionStructureLocal1Stack))
    hDrop
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpec, dropSessionStructureLocal1Spec,
      stackAt_serializeSub_split s0.sp dropSessionStructureLocal1Stack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [dropLocal1SubSpec, dropSessionStructureLocal1Spec, sepExists_sepConj_left,
      stackAt_serializeSub_split s0.sp dropSessionStructureLocal1Stack (by decide)]
    refine Entails.sepExists_mono fun evs => ?_
    exact Entails.of_eq (by sep_ac_rfl)

abbrev rustAllocSubSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocBudgetSpecWithStack M A lim false serializeSubStack

abbrev rustAllocNoOomSubSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocNoOomSpecWithStack M A lim false serializeSubStack

/-! ## Relocatable `[LibsignalPlacement]` lifted callee proofs (block `52`) -/

section Placed

theorem vecVecClone_caller_sub_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hVV : subroutine_ok (lsProg_52 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec)) :
    subroutine_ok (lsProg_52 H) (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpec) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - vecVecCloneStack))
      hVV
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem vecVecClone_placed_sub_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hVV : subroutine_ok (lsProg_117 H) (blkPl_117).base vecVecCloneEmptySpec) :
    subroutine_ok (lsProg_52 H) (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpec) :=
  vecVecClone_caller_sub_ok
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H)
      (subroutine_ok_withLsCodeLoaded_of_plain hVV))

theorem sessionClone_caller_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hClone : subroutine_ok (lsProg_52 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec M A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_80).base
      (withLsCl lsmpl (sessionCloneSubSpec M A lim)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - sessionCloneStack))
      hClone
      (fun ⟨x, st⟩ s0 => ?_)
      (fun ⟨x, st⟩ s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpec, sessionCloneSpec,
      stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [sessionCloneSubSpec, sessionCloneSpec]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem sessionClone_placed_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hClone : subroutine_ok (lsProg_80 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec M A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_80).base
      (withLsCl lsmpl (sessionCloneSubSpec M A lim)) :=
  sessionClone_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hClone)

theorem sessionLen_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hLen : subroutine_ok (lsProg_52 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_86).base (withLsCl lsmpl (sessionLenSubSpec A)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - sessionLenStack))
      hLen
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem sessionLen_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hLen : subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_86).base (withLsCl lsmpl (sessionLenSubSpec A)) :=
  sessionLen_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hLen)

theorem encodeVarint_caller_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_52 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_10).base
      (withLsCl lsmpl (encodeVarintSubSpec M A lim)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - encodeVarintStack))
      hEV
      (fun ⟨x, st⟩ s0 => ?_)
      (fun ⟨x, st⟩ s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpec, encodeVarintSpec,
      stackAt_serializeSub_split s0.sp encodeVarintStack (by decide)]
    refine Entails.trans (sepConj_mono_left (Entails.pure_mono
      (ψ := s0.readReg64 .x0 = x.val ∧ s0.readReg64 .x1 = x.v ∧
        (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
        FitsEnv M lim st (EncodeVarintEnv x))
      fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, Or.inr h2, h3⟩)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [encodeVarintSubSpec, encodeVarintSpec,
      stackAt_serializeSub_split s0.sp encodeVarintStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem encodeVarint_placed_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_10).base
      (withLsCl lsmpl (encodeVarintSubSpec M A lim)) :=
  encodeVarint_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hEV)

theorem encodeRaw_caller_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hRaw : subroutine_ok (lsProg_52 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec M A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_14).base
      (withLsCl lsmpl (encodeRawSubSpec M A lim)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - encodeRawStack))
      hRaw
      (fun ⟨x, st⟩ s0 => ?_)
      (fun ⟨x, st⟩ s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpec, encodeRawSpec,
      stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [encodeRawSubSpec, encodeRawSpec]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem encodeRaw_placed_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hRaw : subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec M A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_14).base
      (withLsCl lsmpl (encodeRawSubSpec M A lim)) :=
  encodeRaw_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hRaw)

theorem dropLocal1_caller_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDrop : subroutine_ok (lsProg_52 H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_6).base
      (withLsCl lsmpl (dropLocal1SubSpec M A lim)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - dropSessionStructureLocal1Stack))
      hDrop
      (fun ⟨x, st⟩ s0 => ?_)
      (fun ⟨x, st⟩ s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpec, dropSessionStructureLocal1Spec,
      stackAt_serializeSub_split s0.sp dropSessionStructureLocal1Stack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [dropLocal1SubSpec, dropSessionStructureLocal1Spec, sepExists_sepConj_left,
      stackAt_serializeSub_split s0.sp dropSessionStructureLocal1Stack (by decide)]
    refine Entails.sepExists_mono fun evs => ?_
    exact Entails.of_eq (by sep_ac_rfl)

theorem dropLocal1_placed_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDrop : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim))) :
    subroutine_ok (lsProg_52 H) (blkPl_6).base
      (withLsCl lsmpl (dropLocal1SubSpec M A lim)) :=
  dropLocal1_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hDrop)

theorem alloc_caller_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (halloc : subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSubSpec M A lim) :=
  subroutine_ok_rustCliAllocBudget_withStack (by decide) (by decide) halloc

theorem alloc_placed_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSubSpec M A lim) :=
  alloc_caller_sub_ok (ls_hook_ok_of_mem halloc)

theorem allocNoOom_caller_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (halloc : subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocNoOomSubSpec M A lim) :=
  subroutine_ok_rustCliAllocNoOom_withStack (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budget halloc)

theorem allocNoOom_placed_sub_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocNoOomSubSpec M A lim) :=
  allocNoOom_caller_sub_ok (ls_hook_ok_of_mem halloc)

end Placed

end LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.HelpersBudget
