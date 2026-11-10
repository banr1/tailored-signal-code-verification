/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Layout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommon

/-!
# `IdentityFiles::get_local_registration_id::{closure#0}` Layout and Callee Helpers

Symbolic relative offsets, cell-oriented callee wrappers (`shimCellsSpec`, `alloc14CellsSpec`), and
`112`-byte (`14`-cell) stack frame and `idRegIdOutAt` layout splits for `IdRegIdPoll`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

/-! ## Symbolic Relative Offsets and Callee Cell Wrappers -/

theorem reg_dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dirGetName =
      (tripleRatchetProgAtExt b ext).fnAddr idRegIdPollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::get" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") := by
  have h1 := idRegIdPoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idRegIdPollName, dirGetName, h1, h2]
  bv_omega

theorem reg_dealloc_fnOff_rel :
    libsignalSessionCode.fnOff idRegIdPollName +
      num% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
        "__rustc::__rust_dealloc") =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
  rw [idRegIdPoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")]

theorem reg_shim_fnOff_rel :
    libsignalSessionCode.fnOff idRegIdPollName +
      num% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2") =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
  rw [idRegIdPoll_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]

theorem reg_alloc_fnOff_rel :
    libsignalSessionCode.fnOff idRegIdPollName +
      num% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
        "__rustc::__rust_alloc") =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by
  rw [idRegIdPoll_fnOff, (ls_stub% "__rustc::__rust_alloc")]

theorem reg_handle_error_fnOff_rel :
    libsignalSessionCode.fnOff idRegIdPollName +
      num% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
        "alloc::raw_vec::handle_error") =
      libsignalSessionCode.fnOff handleErrorName := by
  rw [idRegIdPoll_fnOff, (ls_stub% "alloc::raw_vec::handle_error")]

theorem idRegIdPoll_adrp_40 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr idRegIdPollName + bv% (40)) &&&
      bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}" + 40)) := by
  rw [Program.fnAddr_rebase, idRegIdPoll_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem idRegIdPoll_adrp_156 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr idRegIdPollName + bv% (156)) &&&
      bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}" + 156)) := by
  rw [Program.fnAddr_rebase, idRegIdPoll_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem idRegIdPoll_adrp_216 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr idRegIdPollName + bv% (216)) &&&
      bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}" + 216)) := by
  rw [Program.fnAddr_rebase, idRegIdPoll_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

def shimCellsSpec (calleeStk : Nat) : Spec (BitVec 64) where
  pre := fun fsp s => ⌜s.sp = fsp⌝ ∗ stackAt fsp calleeStk
  post := fun fsp s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem shimAt_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hC : AllocContractsX img A ext)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdPollName +
        BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2")))
      ((shimCellsSpec calleeStk).inImage img) := by
  have hShim := shim_ok_at2_ext_x hC (name := idRegIdPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    reg_shim_fnOff_rel
  refine subroutine_ok_outcome_intro fun fsp R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (shimCellsSpec calleeStk).pre fsp s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [shimCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfsp, hmem⟩
  subst hfsp
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hpre0 : s0.mem ⊨ (session2ShimSpecX.inImage img).pre () s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [session2ShimSpecX, stkRem]
    convert hmem using 1; ac_rfl
  refine hShim.mono_outcome () (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, session2ShimSpecX, shimCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage, session2ShimSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, session2ShimSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, session2ShimSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

def alloc14CellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec (BitVec 64) where
  pre := fun fsp s =>
    ⌜s.readReg64 .x0 = 14#64 ∧ s.readReg64 .x1 = 1#64 ∧ s.sp = fsp⌝ ∗
      A.pool ∗ stackAt fsp calleeStk
  post := fun fsp s0 sf =>
    A.pool ∗ stackAt fsp calleeStk ∗
      if sf.readReg64 .x0 = 0#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
      else
        ⌜sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 14 1 ∗ memRegion (sf.readReg64 .x0) 14
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem alloc14At_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hC : AllocContractsX img A ext)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdPollName +
        BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
          "__rustc::__rust_alloc")))
      ((alloc14CellsSpec A calleeStk).inImage img) := by
  have hAlloc := alloc_ok_at_norm_ext_x hC (name := idRegIdPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"
      "__rustc::__rust_alloc"))
    reg_alloc_fnOff_rel
  refine subroutine_ok_outcome_intro fun fsp R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (alloc14CellsSpec A calleeStk).pre fsp s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [alloc14CellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi] at hmem
  have hlay : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hpre0 : s0.mem ⊨ ((rustAllocSpecWithStack A extHookStack).inImage img).pre
      (14, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [rustAllocSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [hx0]; rfl, by rw [hx1]; rfl, hlay⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hAlloc.mono_outcome (14, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, rustAllocSpecWithStack, alloc14CellsSpec] at hq ⊢
    by_cases hr0 : sf.readReg64 .x0 = 0#64
    · have hr0' : sf.readReg64 .x0 = (0 : BitVec 64) := hr0
      rw [if_pos hr0'] at hq
      rw [if_pos hr0, Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
    · have hr0' : sf.readReg64 .x0 ≠ (0 : BitVec 64) := hr0
      have hmod : (((sf.readReg64 .x0).toNat % 1 = 0 ∧ sf.trace = s0.trace) : Prop) =
          (sf.trace = s0.trace) := by
        simp [Nat.mod_one]
      rw [if_neg hr0', hmod] at hq
      rw [if_neg hr0, Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage, rustAllocSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, rustAllocSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, rustAllocSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem close_panic_subgoal (s0 : State) {sf : State} {t : List TraceEvent} {F R : SepProp}
    (hm : sf.mem ⊨ ((⌜(allocFailedEvent ∈ List.drop t.length sf.trace) ∧ t <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R)
    (htr : t = s0.trace) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

theorem utf8_read_len_eq : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  decide +kernel

theorem match_regId_ne_4 {bs : List (BitVec 8)} (h : bs.length ≠ 4) :
    (match bs with
      | [b0, b1, b2, b3] => Except.ok (b3 ++ b2 ++ b1 ++ b0)
      | _ => Except.error ()) = Except.error () := by
  cases bs with
  | nil => rfl
  | cons a l1 =>
    cases l1 with
    | nil => rfl
    | cons b l2 =>
      cases l2 with
      | nil => rfl
      | cons c l3 =>
        cases l3 with
        | nil => rfl
        | cons d l4 =>
          cases l4 with
          | nil => exact absurd rfl h
          | cons _ _ => rfl

theorem len_bv_ne_four_of_ne {n : Nat} (hlt : n < 2 ^ 63) (hne : n ≠ 4) :
    BitVec.ofNat 64 n ≠ 4#64 := by
  intro heq
  have h0 : (BitVec.ofNat 64 n).toNat = 4 := by rw [heq]; rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0
  exact hne h0

/-! ## Frame and Output Layout Splits (`0x70` = `112` B) -/

theorem cells_14_reg (sp : BitVec 64) :
    cells (sp - 112#64) 14 =
      memRegion (sp - 112#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 64#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 56#64) ↦₆₄ s30) ∗
      (∃∗ s23 : BitVec 64, (sp - 48#64) ↦₆₄ s23) ∗
      (∃∗ sPad : BitVec 64, (sp - 40#64) ↦₆₄ sPad) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  conv_lhs =>
    rw [show (14 : Nat) = 6 + 8 from rfl,
        ProofLib.cells_split_sub sp 112 64 6 8,
        show (8 : Nat) = 1 + 7 from rfl,
        ProofLib.cells_split_sub sp 64 56 1 7,
        show (7 : Nat) = 1 + 6 from rfl,
        ProofLib.cells_split_sub sp 56 48 1 6,
        show (6 : Nat) = 1 + 5 from rfl,
        ProofLib.cells_split_sub sp 48 40 1 5,
        show (5 : Nat) = 1 + 4 from rfl,
        ProofLib.cells_split_sub sp 40 32 1 4,
        show (4 : Nat) = 1 + 3 from rfl,
        ProofLib.cells_split_sub sp 32 24 1 3,
        show (3 : Nat) = 1 + 2 from rfl,
        ProofLib.cells_split_sub sp 24 16 1 2,
        show (2 : Nat) = 1 + 1 from rfl,
        ProofLib.cells_split_sub sp 16 8 1 1,
        ← ProofLib.memRegion_cells (sp - 112#64) 6 (by decide)]
  cells_unfold

theorem getResultAt_err_sp_112 (A : RustAlloc) (sp : BitVec 64) :
    getResultAt A (sp - 112#64) (.error ()) =
      ∃∗ fnPtr : BitVec 64, ∃∗ sBs : List (BitVec 8), ∃∗ sCap : BitVec 64, ∃∗ sPtr : BitVec 64,
        ((sp - 112#64) ↦₆₄ speWord 1) ∗
        ((sp - 104#64) ↦₃₂ sCap.truncate 32) ∗
        ((sp - 100#64) ↦₃₂ (sCap >>> 32).truncate 32) ∗
        ((sp - 96#64) ↦₆₄ sPtr) ∗
        ((sp - 88#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 80#64) ↦₆₄ fnPtr) ∗
        ((sp - 72#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") := by
  dsimp only [getResultAt, speAt, vecU8, strRefAt]
  simp_rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  rw [utf8_read_len_eq]
  have e8 : sp - 112#64 + 8#64 = sp - 104#64 := by bv_omega
  have e16 : sp - 104#64 + 8#64 = sp - 96#64 := by bv_omega
  have e24 : sp - 104#64 + 16#64 = sp - 88#64 := by bv_omega
  have e32 : sp - 112#64 + 32#64 = sp - 80#64 := by bv_omega
  have e40 : sp - 80#64 + 8#64 = sp - 72#64 := by bv_omega
  have e100 : sp - 104#64 + 4#64 = sp - 100#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32, e40]
  congr 1; funext fnPtr; congr 1; funext sBs; congr 1; funext sCap; congr 1; funext sPtr
  rw [PollCommon.cap_split_lo_hi_pointsTo64 (sp - 104#64) sCap, e100]
  ac_rfl

theorem getResultAt_ok_sp_112 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 112#64) (.ok bs) =
      ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
        ⌜bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bPtr ≠ 0#64⌝ ∗
        ((sp - 112#64) ↦₆₄ okTagVec) ∗
        ((sp - 104#64) ↦₃₂ bCap.truncate 32) ∗
        ((sp - 100#64) ↦₃₂ (bCap >>> 32).truncate 32) ∗
        ((sp - 96#64) ↦₆₄ bPtr) ∗
        ((sp - 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bPtr ↦ₛ bs) ∗ Store.IdTrustPoll.Helpers.vecU8BufRest A bCap bPtr bs.length ∗
        memRegion (sp - 80#64) 16 := by
  dsimp only [getResultAt, vecResultAt, vecU8]
  simp_rw [Store.IdTrustPoll.Helpers.vecU8At_eq_expose]
  have e8 : sp - 112#64 + 8#64 = sp - 104#64 := by bv_omega
  have e16 : sp - 104#64 + 8#64 = sp - 96#64 := by bv_omega
  have e24 : sp - 104#64 + 16#64 = sp - 88#64 := by bv_omega
  have e32 : sp - 112#64 + 32#64 = sp - 80#64 := by bv_omega
  have e100 : sp - 104#64 + 4#64 = sp - 100#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32]
  congr 1; funext bCap; congr 1; funext bPtr
  rw [PollCommon.cap_split_lo_hi_pointsTo64 (sp - 104#64) bCap, e100]
  ac_rfl

theorem sp_112_ok_fold_48 (sp : BitVec 64) (w0 : BitVec 64) (cLo cHi : BitVec 32)
    (w2 w3 : BitVec 64) :
    ((sp - 112#64) ↦₆₄ w0) ∗ ((sp - 104#64) ↦₃₂ cLo) ∗ ((sp - 100#64) ↦₃₂ cHi) ∗
      ((sp - 96#64) ↦₆₄ w2) ∗ ((sp - 88#64) ↦₆₄ w3) ∗
      memRegion (sp - 80#64) 16 ⊢
    memRegion (sp - 112#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 112#64) (n := 8) (k := 40)
        (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 4) (k := 36)
        (b' := sp - 100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 100#64) (n := 4) (k := 32)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 24)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 16)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _))
        (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
          (sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))))))

theorem sp_112_err_fold_48 (sp : BitVec 64) (w0 : BitVec 64) (cLo cHi : BitVec 32)
    (w2 w3 w4 w5 : BitVec 64) :
    ((sp - 112#64) ↦₆₄ w0) ∗ ((sp - 104#64) ↦₃₂ cLo) ∗ ((sp - 100#64) ↦₃₂ cHi) ∗
      ((sp - 96#64) ↦₆₄ w2) ∗ ((sp - 88#64) ↦₆₄ w3) ∗
      ((sp - 80#64) ↦₆₄ w4) ∗ ((sp - 72#64) ↦₆₄ w5) ⊢
    memRegion (sp - 112#64) 48 := by
  have h16 : ((sp - 80#64) ↦₆₄ w4) ∗ ((sp - 72#64) ↦₆₄ w5) ⊢ memRegion (sp - 80#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 8)
      (b' := sp - 72#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right h16)))))
    (sp_112_ok_fold_48 sp w0 cLo cHi w2 w3)

theorem out_48_reg_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ o0 : BitVec 64, out ↦₆₄ o0) ∗
      (∃∗ o8_lo : BitVec 32, (out + 8#64) ↦₃₂ o8_lo) ∗
      (∃∗ o8_hi : BitVec 32, (out + 12#64) ↦₃₂ o8_hi) ∗
      (∃∗ o16 : BitVec 64, (out + 16#64) ↦₆₄ o16) ∗
      (∃∗ o24 : BitVec 64, (out + 24#64) ↦₆₄ o24) ∗
      (∃∗ o32 : BitVec 64, (out + 32#64) ↦₆₄ o32) ∗
      (∃∗ o40 : BitVec 64, (out + 40#64) ↦₆₄ o40) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40)
        (b' := out + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 36)
        (b' := out + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 32)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 24)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 16)
        (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
        (b' := out + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out,
      memRegion_four (out + 8#64), memRegion_four (out + 12#64),
      ProofLib.memRegion_eight (out + 16#64), ProofLib.memRegion_eight (out + 24#64),
      ProofLib.memRegion_eight (out + 32#64), ProofLib.memRegion_eight (out + 40#64)]

theorem out_reg_err_read_fold (A : RustAlloc) (out sCap sPtr fnPtr : BitVec 64)
    (sBs : List (BitVec 8)) :
    (out ↦₆₄ speWord 1) ∗
      ((out + 8#64) ↦₃₂ sCap.truncate 32) ∗
      ((out + 12#64) ↦₃₂ (sCap >>> 32).truncate 32) ∗
      ((out + 16#64) ↦₆₄ sPtr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
      ((out + 32#64) ↦₆₄ fnPtr) ∗
      ((out + 40#64) ↦₆₄ 4#64) ∗
      (fnPtr ↦ᵣ utf8 "read") ⊢
    idRegIdOutAt A out (.error ()) := by
  dsimp only [idRegIdOutAt]
  refine Entails.sepExists_right (.proto (utf8 "read") .invalidState) ?_
  dsimp only [RunDrop.speOwnedAt, speAt]
  have e12 : out + 8#64 + 4#64 = out + 12#64 := by bv_omega
  have hcap : ((out + 8#64) ↦₃₂ sCap.truncate 32) ∗
      ((out + 12#64) ↦₃₂ (sCap >>> 32).truncate 32) = ((out + 8#64) ↦₆₄ sCap) := by
    rw [PollCommon.cap_split_lo_hi_pointsTo64 (out + 8#64) sCap, e12]
  have hvec :
      (((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (out + 8#64) bs := by
    have heq :
        (((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
          ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs =
        vecU8At A (out + 8#64) sCap sPtr sBs := by
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [heq]
    exact Entails.sepExists_right sBs
      (Entails.sepExists_right sCap (Entails.sepExists_right sPtr (Entails.refl _)))
  have hstr :
      ((out + 32#64) ↦₆₄ fnPtr) ∗ ((out + 40#64) ↦₆₄ 4#64) ∗ (fnPtr ↦ᵣ utf8 "read") ⊢
      strRefAt (out + 32#64) (utf8 "read") :=
    Entails.sepExists_right fnPtr (Entails.of_eq (by
      rw [utf8_read_len_eq]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]))
  have hgrp :
      (out ↦₆₄ speWord 1) ∗
        ((out + 8#64) ↦₃₂ sCap.truncate 32) ∗
        ((out + 12#64) ↦₃₂ (sCap >>> 32).truncate 32) ∗
        ((out + 16#64) ↦₆₄ sPtr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((out + 32#64) ↦₆₄ fnPtr) ∗
        ((out + 40#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") =
      (out ↦₆₄ speWord 1) ∗
        ((((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
          ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs) ∗
        (((out + 32#64) ↦₆₄ fnPtr) ∗ ((out + 40#64) ↦₆₄ 4#64) ∗ (fnPtr ↦ᵣ utf8 "read")) := by
    rw [← sepConj_assoc, sepConj_assoc (out ↦₆₄ speWord 1),
      ← sepConj_assoc ((out + 8#64) ↦₃₂ _), hcap]
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_right (sepConj_mono hvec hstr)

theorem out_reg_ok_fold (A : RustAlloc) (out : BitVec 64)
    (reg o12 : BitVec 32) (o16 o24 o32 o40 : BitVec 64) :
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗
      ((out + 12#64) ↦₃₂ o12) ∗ ((out + 16#64) ↦₆₄ o16) ∗
      ((out + 24#64) ↦₆₄ o24) ∗ ((out + 32#64) ↦₆₄ o32) ∗
      ((out + 40#64) ↦₆₄ o40) ⊢
    idRegIdOutAt A out (.ok reg) := by
  dsimp only [idRegIdOutAt]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 32)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 24)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 16)
        (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
        (b' := out + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
        (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
          (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _)))))

theorem out_reg_err_malformed_fold (A : RustAlloc) (out buf o32 o40 : BitVec 64)
    (bs14 : List (BitVec 8))
    (hbuf : buf ≠ 0#64) (hlen14 : bs14.length = 14) :
    (out ↦₆₄ speWord 1) ∗
      ((out + 8#64) ↦₃₂ 14#32) ∗ ((out + 12#64) ↦₃₂ 0#32) ∗
      ((out + 16#64) ↦₆₄ buf) ∗ ((out + 24#64) ↦₆₄ 14#64) ∗
      A.live buf 14 1 ∗ (buf ↦ₛ bs14) ∗
      ((out + 32#64) ↦₆₄ o32) ∗ ((out + 40#64) ↦₆₄ o40) ⊢
    idRegIdOutAt A out (.error ()) := by
  dsimp only [idRegIdOutAt]
  refine Entails.sepExists_right (.withString 1 (by decide)) ?_
  dsimp only [RunDrop.speOwnedAt]
  have e12 : out + 8#64 + 4#64 = out + 12#64 := by bv_omega
  have h14_64 : ((out + 8#64) ↦₃₂ 14#32) ∗ ((out + 12#64) ↦₃₂ 0#32) =
      ((out + 8#64) ↦₆₄ 14#64) := by
    have h := (PollCommon.cap_split_lo_hi_pointsTo64 (out + 8#64) 14#64).symm
    rw [e12] at h
    exact h
  have htail16 : ((out + 32#64) ↦₆₄ o32) ∗ ((out + 40#64) ↦₆₄ o40) ⊢
      memRegion (out + 32#64) 16 := by
    rw [ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
      (b' := out + 40#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
  have hvec14 :
      ((out + 8#64) ↦₆₄ 14#64) ∗ ((out + 16#64) ↦₆₄ buf) ∗ ((out + 24#64) ↦₆₄ 14#64) ∗
        A.live buf 14 1 ∗ (buf ↦ₛ bs14) ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (out + 8#64) bs := by
    refine Entails.sepExists_right bs14
      (Entails.sepExists_right 14#64 (Entails.sepExists_right buf ?_))
    rw [Store.IdTrustPoll.Helpers.vecU8At_eq_expose]
    have hpure : (bs14.length ≤ (14#64 : BitVec 64).toNat ∧
        (14#64 : BitVec 64).toNat < 2 ^ 63 ∧ buf ≠ 0#64) := by
      refine ⟨by rw [hlen14]; decide, by decide, hbuf⟩
    have hp_eq : ((bs14.length ≤ (14#64 : BitVec 64).toNat ∧
        (14#64 : BitVec 64).toNat < 2 ^ 63 ∧ buf ≠ 0#64) : Prop) = True :=
      propext ⟨fun _ => trivial, fun _ => hpure⟩
    rw [hp_eq]
    dsimp only [Store.IdTrustPoll.Helpers.vecU8BufRest]
    have hrest : (if (14#64 : BitVec 64) = 0#64 then emp
        else A.live buf (14#64 : BitVec 64).toNat 1 ∗
          memRegion (buf + BitVec.ofNat 64 bs14.length) ((14#64 : BitVec 64).toNat - bs14.length)) =
        A.live buf 14 1 := by
      rw [if_neg (by decide : (14#64 : BitVec 64) ≠ 0#64), hlen14]
      change A.live buf 14 1 ∗ memRegion (buf + 14#64) 0 = A.live buf 14 1
      rw [ProofLib.memRegion_zero, sepConj_emp]
    rw [hrest, hlen14, pure_true, emp_sepConj]
    exact Entails.of_eq (by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      ac_rfl)
  have hgrp :
      (out ↦₆₄ speWord 1) ∗
        ((out + 8#64) ↦₃₂ 14#32) ∗ ((out + 12#64) ↦₃₂ 0#32) ∗
        ((out + 16#64) ↦₆₄ buf) ∗ ((out + 24#64) ↦₆₄ 14#64) ∗
        A.live buf 14 1 ∗ (buf ↦ₛ bs14) ∗
        ((out + 32#64) ↦₆₄ o32) ∗ ((out + 40#64) ↦₆₄ o40) =
      (out ↦₆₄ speWord 1) ∗
        (((out + 8#64) ↦₆₄ 14#64) ∗ ((out + 16#64) ↦₆₄ buf) ∗ ((out + 24#64) ↦₆₄ 14#64) ∗
          A.live buf 14 1 ∗ (buf ↦ₛ bs14)) ∗
        (((out + 32#64) ↦₆₄ o32) ∗ ((out + 40#64) ↦₆₄ o40)) := by
    rw [← sepConj_assoc, sepConj_assoc (out ↦₆₄ speWord 1),
      ← sepConj_assoc ((out + 8#64) ↦₃₂ _), h14_64]
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_right (sepConj_mono hvec14 htail16)

def regPostAns (A : RustAlloc) (out : BitVec 64)
    (expected : Except Unit (BitVec 32)) (s0 sf : State) : SepProp :=
  ∃∗ ans : Except Unit (BitVec 32),
    ⌜ans = expected ∧ sf.trace = s0.trace⌝ ∗ idRegIdOutAt A out ans

theorem regPostAns_intro (A : RustAlloc) (out : BitVec 64)
    (expected ans : Except Unit (BitVec 32)) (s0 sf : State)
    (hpure : ans = expected ∧ sf.trace = s0.trace) :
    idRegIdOutAt A out ans ⊢ regPostAns A out expected s0 sf := by
  have htrue : ((ans = expected ∧ sf.trace = s0.trace) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  unfold regPostAns
  refine Entails.sepExists_right ans ?_
  rw [htrue, pure_true, emp_sepConj]
  exact Entails.refl _

theorem focus_regPostAns (A : RustAlloc) (out : BitVec 64)
    (expected ans : Except Unit (BitVec 32)) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hf : P = idRegIdOutAt A out ans ∗ R)
    (hpure : ans = expected ∧ s_ret.trace = s0.trace)
    (hnext : SepWP prog ret_pc s_ret (regPostAns A out expected s0 s_ret ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken (regPostAns_intro A out expected ans s0 s_ret hpure) (hf := hf) hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll
