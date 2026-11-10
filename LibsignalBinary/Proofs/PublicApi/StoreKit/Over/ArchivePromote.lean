/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveNone
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.HeapDefs
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

/-!
# `SessionRecord::promote_state` on Empty `previous_sessions`

Proves `promote_state_over_gen_ok` (arbitrary `prevCap`) and `promote_state_over_okX`
(`prevCap = 0#64`, yielding capacity `4#64`) from `SerContractsX` and `growOneVecU8Spec`, together
with relocatable `[LibsignalPlacement]` counterparts on Block `47`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.LibsignalSpqrV1 (growOneVecU8Spec)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Callees at `promote_state`-Relative Offsets -/

theorem promote_rel_fnAddrX (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) (k : BitVec 64)
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff promoteStateName) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff name)) :
    (SP2Ext b ext).fnAddr promoteStateName + k = (SP2Ext b ext).fnAddr name := by
  simp only [SP2Ext, Program.fnAddr_rebase]
  rw [BitVec.add_assoc, hk]

/-- `archive_over_gen_ok` at its `promote_state`-relative offset. -/
theorem archive_prom_gen_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr promoteStateName +
        bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
      ((archiveOverGenSpec A).inImage img) := by
  rw [promote_rel_fnAddrX img.base ext archiveCurrentStateInnerName _
    (by rw [libsignalSessionCode_fnOff_promote, libsignalSessionCode_fnOff_archive]; rfl)]
  exact archive_over_gen_ok hC (encodeRaw_ok_of_serContractsX hC)
    (Proofs.libsignal.Hooks2.drop_session_structure_local1_ok_ext hC.alloc)

/-- `archive_over_okX` at its `promote_state`-relative offset. -/
theorem archive_prom_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr promoteStateName +
        bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
      ((archiveOverSpecX A).inImage img) := by
  rw [promote_rel_fnAddrX img.base ext archiveCurrentStateInnerName _
    (by rw [libsignalSessionCode_fnOff_promote, libsignalSessionCode_fnOff_archive]; rfl)]
  exact archive_over_okX hC (encodeRaw_ok_of_serContractsX hC)
    (Proofs.libsignal.Hooks2.drop_session_structure_local1_ok_ext hC.alloc)

/-- `memcpy` with the whole `promote_state` stack budget (the tail call runs on the caller's `sp`). -/
def memcpyPromSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp promoteStackX
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp promoteStackX

theorem memcpy_prom_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr promoteStateName +
        bv% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
      (memcpyPromSpecX.inImage img) := by
  have hmemcpy := hC.memcpy_ok_at promoteStateName
    (num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
    (by simp only [libsignalSessionCode_fnOff_promote, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 promoteStackX)
      (promoteStackX - CryptoVerification.LibsignalTripleRatchet.extHookStack))
    hmemcpy
    (fun ⟨_dst, _src, _bs⟩ s0 => ?_)
    (fun ⟨_dst, _src, _bs⟩ s0 _sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [memcpyPromSpecX, sessionMemcpySpec, libcMemcpySpec,
      stackAt_sub_split_ser s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack promoteStackX
        (by decide) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [memcpyPromSpecX, sessionMemcpySpec,
      stackAt_sub_split_ser s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack promoteStackX
        (by decide) (by decide)]
    exact Entails.of_eq (by ac_rfl)

/-! ## 2. Stack & Memory Shapes -/

/-- The promote stack: the archive stack below the 4 frame cells (`sp - 32 .. sp - 8`). -/
theorem stackAt_promote_splitX (sp : BitVec 64) :
    stackAt sp promoteStackX =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        stackAt (sp - 32#64) archiveStackX ∗
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp archiveStackX 4 (by decide)
  rw [show archiveStackX + 8 * 4 = promoteStackX by decide] at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, show BitVec.ofNat 64 (8 * 4) = 32#64 by rfl, hc4]
  simp only [sepExists_sepConj_right]

/-- Merge the archive stack and the 4 frame cells back into `stackAt sp promoteStackX`. -/
theorem stackAt_promote_mergeX (sp v0 v1 v2 v3 : BitVec 64) :
    (stackAt (sp - 32#64) archiveStackX ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) ⊢
      stackAt sp promoteStackX := by
  rw [stackAt_promote_splitX sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

theorem pointsTo64_memRegion_336_entails_344X (recPtr v : BitVec 64) :
    (((recPtr + 0x18#64) ↦₆₄ v) ∗ memRegion (recPtr + 0x20#64) 336) ⊢
      memRegion (recPtr + 0x18#64) 344 := by
  rw [show (344 : Nat) = 8 + 336 by rfl, memRegion_split _ 8 336 (by decide),
    show recPtr + 0x18#64 + BitVec.ofNat 64 8 = recPtr + 0x20#64 by rw [BitVec.add_assoc]; rfl]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

/-! ## 3. `promote_state` Proofs -/

gen_decodes libsignalSessionCode_tree promoteBin
  [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") →
   (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state" + 0x44)]

private def archiveOverGenSpecPrev (A : RustAlloc) : Spec ArchiveOverGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
      (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
      prevVecAt A x.recPtr x.prevCap x.prevPtr [] ∗
      sessionStateReprAt A (x.recPtr + 0x18#64) x.G x.sess ∗ A.pool ∗
      stackAt s.sp archiveStackX
  post := (archiveOverGenSpec A).post
  onPanic := allocPanic

set_option maxHeartbeats 800000 in
theorem promote_state_over_gen_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    PromoteStateOverGenOk img A ext := by
  have hfn : libsignalSessionCode.fnOff promoteStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") :=
    libsignalSessionCode_fnOff_promote
  have harch : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr promoteStateName +
        bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
      ((archiveOverGenSpecPrev A).inImage img) :=
    archive_prom_gen_okX hC
  have hmemcpy := memcpy_prom_okX (img := img) (A := A) (ext := ext) hC
  code_fetches_from CryptoVerification.libsignalSessionCode
    promoteBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state")) 0 0x44
  unfold PromoteStateOverGenOk promoteOverGenSpec
  simp only [prevVecAt_nil_eq]
  show subroutine_ok (SP2Ext img.base ext) _ _
  wppin_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, src, prevCap, prevPtr, G, sess, newBs⟩ := x
  dsimp only at *
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
  conv => arg 4; rw [stackAt_promote_splitX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v0
  apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro v3
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wppin_callc harch ((archiveOverGenSpecPrev A).inImage img)
    (⟨recPtr, prevCap, prevPtr, G, sess⟩ : ArchiveOverGenGhost)
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
  wp_steps
  refine SepWP.fold
    (pointsTo64_memRegion_336_entails_344X recPtr _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  refine SepWP.fold (stackAt_promote_mergeX s0.sp _ _ _ _) (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hlen : newBs.length = 344 := by assumption
  rw [← hlen]
  wppin_callc hmemcpy (memcpyPromSpecX.inImage img) (recPtr + 24#64, src, newBs)
  apply SepWPpIn.of_sepWP_ret
  wp_done

set_option maxHeartbeats 800000 in
theorem promote_state_over_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    PromoteStateOverOkX img A ext := by
  have hfn : libsignalSessionCode.fnOff promoteStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") :=
    libsignalSessionCode_fnOff_promote
  have harch := archive_prom_okX hC
  have hmemcpy := memcpy_prom_okX (img := img) (A := A) (ext := ext) hC
  code_fetches_from CryptoVerification.libsignalSessionCode
    promoteBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state")) 0 0x44
  unfold PromoteStateOverOkX promoteOverSpecX
  show subroutine_ok (SP2Ext img.base ext) _ _
  wppin_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, src, prevPtr, G, sess, newBs⟩ := x
  dsimp only at *
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
  conv => arg 4; rw [stackAt_promote_splitX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v0
  apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro v3
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wppin_callc harch ((archiveOverSpecX A).inImage img)
    (⟨recPtr, prevPtr, G, sess⟩ : ArchiveOverGhost)
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
  wp_steps
  refine SepWP.fold
    (pointsTo64_memRegion_336_entails_344X recPtr _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  refine SepWP.fold (stackAt_promote_mergeX s0.sp _ _ _ _) (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hlen : newBs.length = 344 := by assumption
  rw [← hlen]
  wppin_callc hmemcpy (memcpyPromSpecX.inImage img) (recPtr + 24#64, src, newBs)
  apply SepWPpIn.of_sepWP_ret
  wp_done

/-! ## 4. Relocatable `[LibsignalPlacement]` `promote_state` Proofs (Block `47`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem L1_ArchivePromote_Placed : True := trivial

/-- Relocatable `archive_over_gen_placed_ok_of_contracts` lifted onto `lsProg_47 H` at `lsmpl.base 51`. -/
theorem archive_prom_gen_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (archiveOverGenSpec A)) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl
    (archive_over_gen_placed_cl_of_contracts (callerProg := lsProg_47 H) hC hGrow
      (encodeRaw_placed_ok_of_serContractsX hC)
      (Proofs.libsignal.Hooks2.drop_session_structure_local1_placed_ok_ext hC.alloc))

/-- Relocatable `archive_over_placed_ok_of_contracts` lifted onto `lsProg_47 H` at `lsmpl.base 51`. -/
theorem archive_prom_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (archiveOverSpecX A)) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl
    (archive_over_placed_cl_of_contracts (callerProg := lsProg_47 H) hC hGrow
      (encodeRaw_placed_ok_of_serContractsX hC)
      (Proofs.libsignal.Hooks2.drop_session_structure_local1_placed_ok_ext hC.alloc))

/-- Relocatable `memcpy` contract lifted to `promoteStackX` on any block caller. -/
theorem memcpy_prom_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl memcpyPromSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 promoteStackX)
      (promoteStackX - CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.memcpy (callerProg := callerProg)))
    (fun ⟨_dst, _src, _bs⟩ s0 => ?_)
    (fun ⟨_dst, _src, _bs⟩ s0 _sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [memcpyPromSpecX, sessionMemcpySpec, libcMemcpySpec,
      stackAt_sub_split_ser s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack promoteStackX
        (by decide) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [memcpyPromSpecX, sessionMemcpySpec,
      stackAt_sub_split_ser s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack promoteStackX
        (by decide) (by decide)]
    exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable `PromoteStateOverGenPlacedOk` (Block `47`) from `SerContractsXPlaced` and
a Block `51`→`621` `grow_one` contract. -/
theorem promote_state_over_gen_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    PromoteStateOverGenPlacedOk A H := by
  have harch : subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (archiveOverGenSpecPrev A)) :=
    archive_prom_gen_placed_ok_of_contracts hC hGrow
  have hmemcpy := memcpy_prom_placed_okX (callerProg := lsProg_47 H) (A := A) hC
  unfold PromoteStateOverGenPlacedOk promoteOverGenSpec
  simp only [prevVecAt_nil_eq]
  show subroutine_ok (lsProg_47 H) _ _
  wpplscl_init x s0
  obtain ⟨recPtr, src, prevCap, prevPtr, G, sess, newBs⟩ := x
  dsimp only at *
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 51)
  conv => arg 4; rw [stackAt_promote_splitX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v0
  apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro v3
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc harch (withLsCodeLoaded lsmpl (archiveOverGenSpecPrev A))
    (⟨recPtr, prevCap, prevPtr, G, sess⟩ : ArchiveOverGenGhost)
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  wp_steps
  refine SepWP.fold
    (pointsTo64_memRegion_336_entails_344X recPtr _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  refine SepWP.fold (stackAt_promote_mergeX s0.sp _ _ _ _) (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hlen : newBs.length = 344 := by assumption
  rw [← hlen]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpyPromSpecX) (recPtr + 24#64, src, newBs)
  apply SepWPpLsCl.of_sepWP_ret
  wp_done

/-- Caller-block-polymorphic `withLsCl` form of `promote_state_over_gen_placed_ok_of_contracts`. -/
theorem promote_state_over_gen_placed_cl_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    subroutine_ok callerProg (lsmpl.base 47) (withLsCl lsmpl (promoteOverGenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (promote_state_over_gen_placed_ok_of_contracts hC hGrow)

set_option maxHeartbeats 800000 in
/-- Relocatable `PromoteStateOverPlacedOkX` (Block `47`) from `SerContractsXPlaced` and
a Block `51`→`621` `grow_one` contract. -/
theorem promote_state_over_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    PromoteStateOverPlacedOkX A H := by
  have harch := archive_prom_placed_ok_of_contracts hC hGrow
  have hmemcpy := memcpy_prom_placed_okX (callerProg := lsProg_47 H) (A := A) hC
  unfold PromoteStateOverPlacedOkX promoteOverSpecX
  show subroutine_ok (lsProg_47 H) _ _
  wpplscl_init x s0
  obtain ⟨recPtr, src, prevPtr, G, sess, newBs⟩ := x
  dsimp only at *
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 51)
  conv => arg 4; rw [stackAt_promote_splitX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v0
  apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro v3
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpplscl_callc harch (withLsCodeLoaded lsmpl (archiveOverSpecX A))
    (⟨recPtr, prevPtr, G, sess⟩ : ArchiveOverGhost)
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  wp_steps
  refine SepWP.fold
    (pointsTo64_memRegion_336_entails_344X recPtr _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  refine SepWP.fold (stackAt_promote_mergeX s0.sp _ _ _ _) (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hlen : newBs.length = 344 := by assumption
  rw [← hlen]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpyPromSpecX) (recPtr + 24#64, src, newBs)
  apply SepWPpLsCl.of_sepWP_ret
  wp_done

/-- Caller-block-polymorphic `withLsCl` form of `promote_state_over_placed_ok_of_contracts`. -/
theorem promote_state_over_placed_cl_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    subroutine_ok callerProg (lsmpl.base 47) (withLsCl lsmpl (promoteOverSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (promote_state_over_placed_ok_of_contracts hC hGrow)

end Placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
