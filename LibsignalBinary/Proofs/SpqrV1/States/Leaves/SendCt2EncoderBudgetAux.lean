/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `send_ct2_encoder`: Allocator Event Trace & Framed Call Helpers

Exact allocator-event trace (`sendCt2EncoderEvents`), envelope inclusion into `SendCt2EncoderEnv`,
`HookSat` / extended-stack adapters, and budget-threaded framed call rules for
`spqr::v1::chunked::send_ct::send_ct2_encoder`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkLib_eq_382 blkPC_382 blkPl_382
  libsignalSessionCode lsProg_382 lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Bytes PolyEncoder spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall doReserveStack reserveCap
  sessionMemcpyRegionSpec sessionMemcpySpec sessionShimSpec withStack
)
open CryptoVerification.RustHeap (LayoutOk RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt polyEncoderSize resultPolyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (
  EncodeBytesGhost bytesAt encodeBytesResult encodeBytesStack encodeBytesStackX
)
open CryptoVerification.SpqrV1.States.Leaves (
  Relocatable SendCt2EncoderGhost bv_sub_sub fold_sendCt2SavedCells of_sepWP_lscl
  polyEncoderAt_split_tag relocate_post_entails relocate_pre_entails relocatedHeap
  sendCt2EncoderStack sendCt2SavedCells sepWPp_call_frozen
  slice_and_tail_entails_vecCapPtrDealloc slice_and_vecU8Tail_eq_doReserveBuf
  sp_sub_496_add_8 sp_sub_504_add_16 sp_sub_504_add_8
  sp_sub_512_add_16 sp_sub_512_add_24 sp_sub_512_add_32 sp_sub_512_add_432 sp_sub_512_add_8
  sp_sub_80_add_16 sp_sub_80_add_24 sp_sub_80_add_32 sp_sub_80_add_40 sp_sub_80_add_48
  sp_sub_80_add_56 sp_sub_80_add_64 sp_sub_80_add_72 sp_sub_80_add_80 sp_sub_80_sub_432
  stackAt_512_recompose stackAt_encodeBytesX_from_allocHook stackAt_encodeBytesX_from_doReserve
  stackAt_encodeBytesX_to_allocHook stackAt_encodeBytesX_to_doReserve
  stackAt_sendCt2Encoder_from_allocHook stackAt_sendCt2Encoder_to_allocHook
  vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  FreeOnlyEvs RustCliAllocBudget RustLayoutOk SeqEnv
  VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec rustCliAllocNoOomSpecBase
  rustCliDeallocBudgetSpec rustCliDeallocBudgetSpecBase
  rustDeallocEvents rustReallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveRawSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (
  EncodeBytesEnv encodeBytesAllocEvents encodeBytesSpec encodeBytesSpecX
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget (SendCt2EncoderEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs nonFreeCount)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents noAllocShimSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  sp_sub_80_sub_432 sp_sub_512_add_432
  sp_sub_512_add_8 sp_sub_512_add_16 sp_sub_512_add_24 sp_sub_512_add_32
  sp_sub_504_add_8 sp_sub_504_add_16 sp_sub_496_add_8
  sp_sub_80_add_16 sp_sub_80_add_24 sp_sub_80_add_32
  sp_sub_80_add_40 sp_sub_80_add_48 sp_sub_80_add_56 sp_sub_80_add_64
  sp_sub_80_add_72 sp_sub_80_add_80

/-! ## 1. Exact Allocator Event Sequence & Inclusion into `SendCt2EncoderEnv` -/

/-- Initial `Vec::from(ct2)` allocation events (`[]` when `ct2 = []`). -/
def sendCt2InitEvs (ct2 : Bytes) : List AllocEvent :=
  if ct2 = [] then [] else rustAllocEvents ct2.length 1

/-- Capacity after `Vec::from(ct2)`. -/
def sendCt2Cap1 (ct2 : Bytes) : Nat :=
  if ct2 = [] then 0 else ct2.length

/-- `extend_from_slice(mac)` (`do_reserve_and_handle`) events (`[]` when `mac = []`). -/
def sendCt2MacEvs (ct2 mac : Bytes) : List AllocEvent :=
  if mac = [] then []
  else
    let newCap := reserveCap (sendCt2Cap1 ct2) ct2.length mac.length
    if ct2 = [] then rustAllocEvents newCap 1
    else rustReallocEvents ct2.length newCap 1

/-- Capacity before `encode_bytes` and `Vec::drop`. -/
def sendCt2Cap2 (ct2 mac : Bytes) : Nat :=
  if mac = [] then sendCt2Cap1 ct2
  else reserveCap (sendCt2Cap1 ct2) ct2.length mac.length

/-- Trailing `Vec::drop` deallocation events (`[]` when `cap = 0`). -/
def sendCt2FreeEvs (cap : Nat) : List AllocEvent :=
  if cap = 0 then [] else rustDeallocEvents cap 1

/-- Exact allocator event list emitted by `spqr::v1::chunked::send_ct::send_ct2_encoder`. -/
def sendCt2EncoderEvents (ct2 mac : Bytes) : List AllocEvent :=
  (sendCt2InitEvs ct2 ++ sendCt2MacEvs ct2 mac) ++
    (encodeBytesAllocEvents (ct2.length + mac.length) ++
      sendCt2FreeEvs (sendCt2Cap2 ct2 mac))

/-- Exact singleton event envelope for `spqr::v1::chunked::send_ct::send_ct2_encoder`. -/
def SendCt2EncoderExactEnv (x : SendCt2EncoderGhost) (evs : List AllocEvent) : Prop :=
  evs = sendCt2EncoderEvents x.ct2 x.mac

theorem sendCt2EncoderExactEnv_nonempty (x : SendCt2EncoderGhost) :
    ∃ evs, SendCt2EncoderExactEnv x evs :=
  ⟨sendCt2EncoderEvents x.ct2 x.mac, rfl⟩

private theorem spqrBoundedEvs_rustAlloc1 {n maxReq : Nat}
    (hpos : 0 < n) (hlt : n ≤ 2 ^ 62) (hle : n ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (rustAllocEvents n 1) := by
  have hcond : 1 ≤ 16 ∧ 1 ≤ n := ⟨by decide, hpos⟩
  unfold SpqrBoundedEvs rustAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  refine ⟨?_, ?_, by rintro _ _ ⟨⟩, by rintro _ _ _ ⟨⟩⟩
  · unfold AllocEvent.withinMaxAlloc VerifiedLibraries.Mallocng.MallocngMaxAllocSize
    omega
  · simp [AllocEvent.reqBytes, hle]

private theorem spqrBoundedEvs_rustRealloc1 {old new maxReq : Nat}
    (hnew_pos : 0 < new) (hnew_lt : new ≤ 2 ^ 62)
    (hnew_le : new ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (rustReallocEvents old new 1) := by
  have hcond : 1 ≤ 16 ∧ 1 ≤ new := ⟨by decide, hnew_pos⟩
  unfold SpqrBoundedEvs rustReallocEvents
  simp only [hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  refine ⟨?_, ?_, by rintro _ _ ⟨⟩, ?_⟩
  · unfold AllocEvent.withinMaxAlloc VerifiedLibraries.Mallocng.MallocngMaxAllocSize
    omega
  · simp [AllocEvent.reqBytes]; omega
  · intro al _ _ h; cases h; decide

theorem freeOnlyEvs_sendCt2FreeEvs (cap : Nat) :
    FreeOnlyEvs (sendCt2FreeEvs cap) := by
  unfold sendCt2FreeEvs
  by_cases h0 : cap = 0
  · simp only [h0, ↓reduceIte]; exact FreeOnlyEvs.nil
  · simp only [h0, ↓reduceIte]; exact FreeOnlyEvs.singleton 1 cap

/-- Whenever `(x.ct2 ++ x.mac).length ≤ 1048576`, the exact event trace `sendCt2EncoderEvents`
    inhabits `SendCt2EncoderEnv x`. -/
theorem sendCt2EncoderEvents_in_sendCt2EncoderEnv (x : SendCt2EncoderGhost)
    (hlen : (x.ct2 ++ x.mac).length ≤ 1048576) :
    SendCt2EncoderEnv x (sendCt2EncoderEvents x.ct2 x.mac) := by
  have htot : x.ct2.length + x.mac.length ≤ 1048576 := by
    rwa [List.length_append] at hlen
  let maxReq := 2 * (x.ct2.length + x.mac.length) + 64
  have h1 : SpqrBoundedEvs 1 maxReq (sendCt2InitEvs x.ct2) := by
    unfold sendCt2InitEvs
    by_cases hc : x.ct2 = []
    · simp only [hc, ↓reduceIte]; exact SpqrBoundedEvs.nil 1 maxReq
    · simp only [hc, ↓reduceIte]
      have hpos : 0 < x.ct2.length := List.length_pos_iff.mpr hc
      exact spqrBoundedEvs_rustAlloc1 hpos (by omega) (by dsimp [maxReq]; omega)
  have h2 : SpqrBoundedEvs 1 maxReq (sendCt2MacEvs x.ct2 x.mac) := by
    unfold sendCt2MacEvs
    by_cases hm : x.mac = []
    · simp only [hm, ↓reduceIte]; exact SpqrBoundedEvs.nil 1 maxReq
    · simp only [hm, ↓reduceIte]
      let cap1 := sendCt2Cap1 x.ct2
      have hcap1_le : cap1 ≤ x.ct2.length := by
        dsimp [cap1, sendCt2Cap1]; split <;> omega
      let newCap := reserveCap cap1 x.ct2.length x.mac.length
      have hnew_pos : 0 < newCap := by
        dsimp [newCap, reserveCap]; omega
      have hnew_le : newCap ≤ maxReq := by
        dsimp [newCap, reserveCap, maxReq]; omega
      have hnew_lt : newCap ≤ 2 ^ 62 := by
        dsimp [maxReq] at hnew_le; omega
      change SpqrBoundedEvs 1 maxReq
        (if x.ct2 = [] then rustAllocEvents newCap 1
         else rustReallocEvents x.ct2.length newCap 1)
      split
      · exact spqrBoundedEvs_rustAlloc1 hnew_pos hnew_lt hnew_le
      · exact spqrBoundedEvs_rustRealloc1 hnew_pos hnew_lt hnew_le
  have hspqr : SpqrBoundedEvs 4 maxReq (sendCt2InitEvs x.ct2 ++ sendCt2MacEvs x.ct2 x.mac) := by
    have happ := SpqrBoundedEvs.append h1 h2
    rw [Nat.max_self] at happ
    exact SpqrBoundedEvs.mono (by decide) (Nat.le_refl _) happ
  exact Or.inr ⟨_, _, rfl, hspqr, Or.inr ⟨_, _, rfl, rfl, freeOnlyEvs_sendCt2FreeEvs _⟩⟩

/-- Split `FitsEvents M lim st (sendCt2EncoderEvents ct2 mac)` into sequential `FitsEvents`
    obligations for initial allocation, MAC reservation, `encode_bytes`, and deallocation. -/
theorem fitsEvents_sendCt2EncoderEvents_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {ct2 mac : Bytes}
    (h : FitsEvents M lim st (sendCt2EncoderEvents ct2 mac)) :
    let st1 := M.stepEvents (sendCt2InitEvs ct2) st
    let st2 := M.stepEvents (sendCt2MacEvs ct2 mac) st1
    let st3 := M.stepEvents (encodeBytesAllocEvents (ct2.length + mac.length)) st2
    FitsEvents M lim st (sendCt2InitEvs ct2) ∧
    FitsEvents M lim st1 (sendCt2MacEvs ct2 mac) ∧
    FitsEvents M lim st2 (encodeBytesAllocEvents (ct2.length + mac.length)) ∧
    FitsEvents M lim st3 (sendCt2FreeEvs (sendCt2Cap2 ct2 mac)) := by
  unfold sendCt2EncoderEvents at h
  rcases (fitsEvents_append M lim _ _ st).mp h with ⟨h12, h34⟩
  rcases (fitsEvents_append M lim _ _ st).mp h12 with ⟨h1, h2⟩
  rw [M.stepEvents_append] at h34
  rcases (fitsEvents_append M lim _ _ _).mp h34 with ⟨h3, h4⟩
  exact ⟨h1, h2, h3, h4⟩

theorem stepEvents_sendCt2EncoderEvents (M : AllocCostModel) (ct2 mac : Bytes) (st : M.σ) :
    M.stepEvents (sendCt2EncoderEvents ct2 mac) st =
      M.stepEvents (sendCt2FreeEvs (sendCt2Cap2 ct2 mac))
        (M.stepEvents (encodeBytesAllocEvents (ct2.length + mac.length))
          (M.stepEvents (sendCt2MacEvs ct2 mac)
            (M.stepEvents (sendCt2InitEvs ct2) st))) := by
  unfold sendCt2EncoderEvents
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]

theorem doReserveEvents_eq_sendCt2MacEvs (v cap ptr : BitVec 64) (ct2 mac : Bytes)
    (hmac : mac ≠ []) (hcap_eq : cap.toNat = ct2.length) :
    doReserveEvents ⟨v, cap, ptr, ct2, mac.length⟩ = sendCt2MacEvs ct2 mac := by
  unfold doReserveEvents sendCt2MacEvs sendCt2Cap1
  simp only [hmac, ↓reduceIte]
  by_cases hc : ct2 = []
  · subst hc
    have hc0 : cap = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hcap_eq)
    simp [hc0]
  · have hpos : 0 < ct2.length := List.length_pos_iff.mpr hc
    have hc_ne : cap ≠ 0#64 := fun h0 => by
      subst h0; simp at hcap_eq; omega
    simp [hc, hc_ne, hcap_eq]

/-! ## 2. `HookSat` & Extended-Stack Callee Adapters -/

theorem hookSat_sessionShimBudget_of_noAllocShim {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym noAllocShimSpec) :
    HookSat H sym sessionShimBudgetSpec :=
  HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => by
    dsimp only [noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec,
      sessionShimBudgetSpec, sessionShimSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1.1, hpost.2⟩⟩

theorem hookSat_sessionMemcpyBudget_of_region {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym sessionMemcpyRegionBudgetSpec) :
    HookSat H sym sessionMemcpyBudgetSpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  refine ⟨(dst, src, bs), stackAt s0.sp 4096 ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hpost ⊢
    ac_nf at hpost ⊢

theorem encodeBytesSpecX_cl_of_encodeBytesSpec_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (encodeBytesSpec A lim))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl, hpre0⟩ := CryptoVerification.extract_withLsCodeLoaded hpre
  have hle : encodeBytesStack ≤ encodeBytesStackX := by decide
  have hsplit : stackAt s0.sp encodeBytesStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
        (encodeBytesStackX - encodeBytesStack) ∗
        stackAt s0.sp encodeBytesStack := by
    have h1 := stackAt_split_bottom s0.sp encodeBytesStack
      (encodeBytesStackX - encodeBytesStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
      (encodeBytesStackX - encodeBytesStack) ∗ R
  have hpre0' : s0.mem ⊨ (encodeBytesSpec A lim).pre x s0 ∗ R' := by
    dsimp only [encodeBytesSpecX, LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv,
      encodeBytesSpec, LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecOfEnv, R'] at hpre0 ⊢
    rw [hsplit] at hpre0
    ac_nf at hpre0 ⊢
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre0'⟩
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv,
      encodeBytesSpec,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecOfEnv, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [withLsCodeLoaded, encodeBytesSpec,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, encodeBytesSpec,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecOfEnv] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## 3. Budget-Threaded Framed Call Rules -/

theorem call_noAllocShim_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry noAllocShimSpec)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hsplit : P = A.pool lim st s ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf (A.pool lim st sf ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := ()) (F := A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec]
    rwa [emp_sepConj]
  · dsimp only [noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec]
    refine SepWP.pure_elim fun ⟨htr, hvm⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_sessionShim_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved sessionShimSpec))
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hsplit : P = A.pool lim st s ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf (A.pool lim st sf ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := ()) (F := A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, sessionShimSpec]
    rwa [emp_sepConj]
  · dsimp only [withVmPreserved, sessionShimSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun htr => ?_
    rw [← A.pool_of_vmPreserved hvm]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_rustAllocNoOom_budget [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim false))
    (size align : Nat) (st : M.σ)
    (hlay : RustLayoutOk size align)
    (hfit : FitsEvents M lim st (rustAllocEvents size align))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = align)
    (hsplit : P = (A.pool lim st s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWP prog target_pc sf
        ((A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack ∗
          A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (size, align, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hlay, hfit, by rw [hlr]; exact hlr_ls⟩, hm⟩
  · simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, hne0, _⟩ => ?_
    have hassoc :
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack ∗
          A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size) ∗ Frame =
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
          (stackAt sp_call allocHookStack ∗
            (A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      (hacp.2.1.trans htrace) hne0

theorem call_rustAllocNoOom_budgetBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliAllocNoOomSpecBase M A lim false))
    (size align : Nat) (st : M.σ)
    (hlay : RustLayoutOk size align)
    (hfit : FitsEvents M lim st (rustAllocEvents size align))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = align)
    (hsplit : P = (A.pool lim st s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWP prog target_pc sf
        ((A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack ∗
          A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (size, align, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliAllocNoOomSpecBase]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hlay, hfit⟩, hm⟩
  · simp only [rustCliAllocNoOomSpecBase, Bool.false_eq_true, ↓reduceIte]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, hne0, _⟩ => ?_
    have hassoc :
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack ∗
          A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size) ∗ Frame =
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
          (stackAt sp_call allocHookStack ∗
            (A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      (hacp.2.1.trans htrace) hne0

theorem call_rustDealloc_budget [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim))
    (p : BitVec 64) (size align : Nat) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hsplit : P = (A.pool lim st s ∗ A.live p size align ∗
      memRegion p size ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (p, size, align, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliDeallocBudgetSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, by rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [rustCliDeallocBudgetSpec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, _⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (hacp.2.1.trans htrace)

theorem call_rustDealloc_budgetBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliDeallocBudgetSpecBase M A lim))
    (p : BitVec 64) (size align : Nat) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hsplit : P = (A.pool lim st s ∗ A.live p size align ∗
      memRegion p size ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (p, size, align, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliDeallocBudgetSpecBase]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, hm⟩
  · dsimp only [rustCliDeallocBudgetSpecBase]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, _⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (hacp.2.1.trans htrace)

theorem call_memcpy_bytes_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    (dst src : BitVec 64) (bs : Bytes) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hsplit : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, hm⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm]
    have hassoc :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf) ∗ Frame =
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (A.pool lim st sf ∗ Frame) := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_memcpy_bytes_4K_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    {stk : Nat}
    (hcall : subroutine_ok prog entry (withStack (withVmPreserved sessionMemcpyRegionSpec) stk))
    (dst src : BitVec 64) (bs : Bytes) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hsplit : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      A.pool lim st s ∗ stackAt sp_call stk) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf ∗ stackAt sp_call stk) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by
      dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec] at h
      exact not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using h))
    (fun _ _ _ _ h => by
      dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec] at h
      exact not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using h))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    ac_nf at hm ⊢
  · dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec]
    rw [hsp]
    have hpull :
        ((⌜VmPreserved s sf⌝ ∗ ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
          (dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt sp_call stk) ∗ (A.pool lim st s ∗ Frame) =
        ⌜VmPreserved s sf⌝ ∗ (⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
          (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp_call stk) ∗ Frame)) := by
      ac_rfl
    rw [hpull]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_memcpy_relocate_cs_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  have hpre_eq : P = (memRegion dst n ∗ F src) ∗ (A.pool lim st s ∗ Frame) := by
    rw [hsplit]; ac_rfl
  rw [hpre_eq]
  refine SepWP.fold (relocate_pre_entails hrel dst src (A.pool lim st s ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ (A.pool lim st s ∗ Frame))
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWP.fold (relocate_post_entails dst src hlen (A.pool lim st sf ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq :
        (F dst ∗ memRegion src n) ∗ (A.pool lim st sf ∗ Frame) =
        (F dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame := by ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_memcpy_relocate_cs_4K_budget {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    {stk : Nat}
    (hcall : subroutine_ok prog entry (withStack (withVmPreserved sessionMemcpyRegionSpec) stk))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ A.pool lim st s ∗ stackAt sp_call stk) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((F dst ∗ memRegion src n ∗ A.pool lim st sf ∗ stackAt sp_call stk) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  have hpre_eq : P = (memRegion dst n ∗ F src) ∗ (stackAt sp_call stk ∗ A.pool lim st s ∗ Frame) := by
    rw [hsplit]; ac_rfl
  rw [hpre_eq]
  refine SepWP.fold (relocate_pre_entails hrel dst src
    (stackAt sp_call stk ∗ A.pool lim st s ∗ Frame)) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ (A.pool lim st s ∗ Frame))
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by
      dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec] at h
      exact not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using h))
    (fun _ _ _ _ h => by
      dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec] at h
      exact not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using h))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    ac_nf at hm ⊢
  · dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec]
    rw [hsp]
    have hpull :
        ((⌜VmPreserved s sf⌝ ∗ ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
          (dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt sp_call stk) ∗
          (relocatedHeap F bs ∗ (A.pool lim st s ∗ Frame)) =
        ⌜VmPreserved s sf⌝ ∗ (⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
          (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ relocatedHeap F bs ∗
            (stackAt sp_call stk ∗ A.pool lim st s ∗ Frame))) := by ac_rfl
    rw [hpull]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWP.fold (relocate_post_entails dst src hlen
      (stackAt sp_call stk ∗ A.pool lim st sf ∗ Frame)) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hpost_eq :
        (F dst ∗ memRegion src n) ∗ (stackAt sp_call stk ∗ A.pool lim st sf ∗ Frame) =
        (F dst ∗ memRegion src n ∗ A.pool lim st sf ∗ stackAt sp_call stk) ∗ Frame := by ac_rfl
    rw [hpost_eq]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_doReserve7Raw_cl_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (v cap ptr : BitVec 64) (bs : Bytes) (additional : Nat) (st : M.σ)
    (hlen : bs.length ≤ cap.toNat) (hptr : ptr ≠ 0#64)
    (h0 : cap = 0#64 → bs = [])
    (hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (doReserveEvents ⟨v, cap, ptr, bs, additional⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hsplit : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (ptr ↦ₛ bs) ∗ vecU8Tail A.repAlloc cap ptr bs ∗
      A.pool lim st s ∗ stackAt sp_call doReserveStack) ∗ Frame)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      let newCap := reserveCap cap.toNat bs.length additional
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      p' ≠ 0#64 →
      SepWP prog next_pc sf
        (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' newCap 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap - bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents ⟨v, cap, ptr, bs, additional⟩) st) sf ∗
          stackAt sp_call doReserveStack) ∗ Frame)
        (fun sm Pm =>
          LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨v, cap, ptr, bs, additional⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCodeLoaded, doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [withLsCodeLoaded, doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    have hbuf := slice_and_vecU8Tail_eq_doReserveBuf A.repAlloc cap ptr bs h0
    dsimp only [RustCliAllocBudget.repAlloc] at hbuf
    rw [← hbuf]
    have hfit_env : FitsEnv M lim st (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) :=
      fun _ hev => hev ▸ hfit
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfit_env⟩, hm⟩
  · dsimp only [withLsCodeLoaded, doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply of_sepWP_lscl hcl_sf (mid := next_pc)
    wp_pull_exists; rename_i p'
    wp_focus_pure; intro hp'
    have hassoc :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents ⟨v, cap, ptr, bs, additional⟩) st) sf ∗
          stackAt sp_call doReserveStack) ∗ Frame =
        (v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents ⟨v, cap, ptr, bs, additional⟩) st) sf ∗
          stackAt sp_call doReserveStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf p' hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hp'

theorem call_doReserve7Raw_budget
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (doReserveRawSpec M A lim))
    (v cap ptr : BitVec 64) (bs : Bytes) (additional : Nat) (st : M.σ)
    (hlen : bs.length ≤ cap.toNat) (hptr : ptr ≠ 0#64)
    (h0 : cap = 0#64 → bs = [])
    (hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (doReserveEvents ⟨v, cap, ptr, bs, additional⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hsplit : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (ptr ↦ₛ bs) ∗ vecU8Tail A.repAlloc cap ptr bs ∗
      A.pool lim st s ∗ stackAt sp_call doReserveStack) ∗ Frame)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      let newCap := reserveCap cap.toNat bs.length additional
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      p' ≠ 0#64 →
      SepWP prog next_pc sf
        (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' newCap 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap - bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents ⟨v, cap, ptr, bs, additional⟩) st) sf ∗
          stackAt sp_call doReserveStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := (⟨v, cap, ptr, bs, additional⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack]
    rw [hsp]
    have hbuf := slice_and_vecU8Tail_eq_doReserveBuf A.repAlloc cap ptr bs h0
    dsimp only [RustCliAllocBudget.repAlloc] at hbuf
    rw [← hbuf]
    have hfit_env : FitsEnv M lim st (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) :=
      fun _ hev => hev ▸ hfit
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfit_env⟩, hm⟩
  · dsimp only [doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    wp_pull_exists; rename_i p'
    wp_focus_pure; intro hp'
    have hassoc :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents ⟨v, cap, ptr, bs, additional⟩) st) sf ∗
          stackAt sp_call doReserveStack) ∗ Frame =
        (v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents ⟨v, cap, ptr, bs, additional⟩) st) sf ∗
          stackAt sp_call doReserveStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf p' hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hp'

theorem call_encodeBytesX_cl_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder) (st : M.σ)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    (hfit : FitsEvents M lim st (encodeBytesAllocEvents msg.length))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool lim st s ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st) sf ∗
          stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine SepWPp.call hcall (x := (⟨out, false, msgA, msg⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCodeLoaded, encodeBytesSpecX,
        LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [withLsCodeLoaded, encodeBytesSpecX,
        LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv,
      polyEncoderSize, bytesAt]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    have hfit_env : FitsEnv M lim st (EncodeBytesEnv msg.length) :=
      fun _ hev => hev ▸ hfit
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt, hfit_env⟩, hm⟩
  · dsimp only [withLsCodeLoaded, encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hex_pull :
        ((polyEncoderAt A.repAlloc out outEnc ∗
          ((msgA ↦ₛ msg) ∗
            ((∃∗ evs : List AllocEvent,
              ⌜EncodeBytesEnv msg.length evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt sp_call encodeBytesStackX))) ∗ Frame) =
        (∃∗ evs : List AllocEvent,
          ⌜EncodeBytesEnv msg.length evs⌝ ∗
            ((polyEncoderAt A.repAlloc out outEnc ∗ (msgA ↦ₛ msg) ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt sp_call encodeBytesStackX) ∗ Frame)) := by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      exact congrArg sepExists (funext fun evs => by ac_rfl)
    rw [hex_pull]
    wp_pull_exists; rename_i evs_enc
    refine SepWP.pure_elim fun hevs => ?_
    unfold EncodeBytesEnv at hevs
    subst hevs
    simpa only [sepConj_assoc] using
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem call_encodeBytesX_budget
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (encodeBytesSpecX A lim))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder) (st : M.σ)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    (hfit : FitsEvents M lim st (encodeBytesAllocEvents msg.length))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool lim st s ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st) sf ∗
          stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := (⟨out, false, msgA, msg⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [encodeBytesSpecX,
        LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [encodeBytesSpecX,
        LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv,
      polyEncoderSize, bytesAt]
    rw [hsp]
    have hfit_env : FitsEnv M lim st (EncodeBytesEnv msg.length) :=
      fun _ hev => hev ▸ hfit
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt, hfit_env⟩, hm⟩
  · dsimp only [encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hex_pull :
        ((polyEncoderAt A.repAlloc out outEnc ∗
          ((msgA ↦ₛ msg) ∗
            ((∃∗ evs : List AllocEvent,
              ⌜EncodeBytesEnv msg.length evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt sp_call encodeBytesStackX))) ∗ Frame) =
        (∃∗ evs : List AllocEvent,
          ⌜EncodeBytesEnv msg.length evs⌝ ∗
            ((polyEncoderAt A.repAlloc out outEnc ∗ (msgA ↦ₛ msg) ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt sp_call encodeBytesStackX) ∗ Frame)) := by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      exact congrArg sepExists (funext fun evs => by ac_rfl)
    rw [hex_pull]
    wp_pull_exists; rename_i evs_enc
    refine SepWP.pure_elim fun hevs => ?_
    unfold EncodeBytesEnv at hevs
    subst hevs
    simpa only [sepConj_assoc] using
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
