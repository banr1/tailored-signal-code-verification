/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Sym
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StorePollCli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi

private theorem close_panic_subgoal {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem cells_26_split (sp : BitVec 64) :
    cells (sp - 208#64) 26 =
      storePollSlack sp ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 144#64) 4 ∗
        cells (sp - 96#64) 5 ∗ cells (sp - 48#64) 6 := by
  rw [show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 6 + 19 from rfl, cells_split_sub sp 200 152 6 19,
    show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
    show (18 : Nat) = 4 + 14 from rfl, cells_split_sub sp 144 112 4 14,
    show (14 : Nat) = 2 + 12 from rfl, cells_split_sub sp 112 96 2 12,
    show (12 : Nat) = 5 + 7 from rfl, cells_split_sub sp 96 56 5 7,
    show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6]
  dsimp only [storePollSlack]
  ac_rfl

private theorem cells_sub_4_eq (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

theorem serialize_cells_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializeCanonSpecX A).inImage img))
    (hle : serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializeCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (serializeCellsSpec A calleeStk).pre (recA, out, g, r, o0, o1, o2, o3, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStackX)
  let callG : E2E.Record.Serialization.SerializeGhost := ⟨recA, out, g, r⟩
  have hpre0 : s0.mem ⊨ ((serializeCanonSpecX A).inImage img).pre
      callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [serializeCanonSpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, serializeCanonSpecX, serializeCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨bCap, bPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, serializeCanonSpecX, E2E.Record.Serialization.allocPanic,
      serializeCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePollInner_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addrStk putStk : Nat}
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((serializeCanonSpecX A).inImage img))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hhi : max (max addrStk serializeStackX) (max putStk extHookStack) ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      ((cliStorePollInnerSpec A
        (max (max addrStk serializeStackX) (max putStk extHookStack))).inImage img) := by
  let calleeStk := max (max addrStk serializeStackX) (max putStk extHookStack)
  unfold Spec.inImage
  simp (config := { maxSteps := 2000000 }) only [cliStorePollInnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split, cells_sub_4_eq, cells_sub_5_eq, cells_sub_6_200_eq, cells_sub_6_48_eq,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff sessStorePollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
    sessStorePoll_fnOff
  have hAddrCells := addrText_cells_ok (calleeStk := calleeStk) hAddr (by omega) hhi
  have hSerCells := serialize_cells_ok_x (calleeStk := calleeStk) hSer (by omega) hhi
  have hPutCells := dirPut_cells_ok (calleeStk := calleeStk) hPut (by omega) hhi
  rw [Program.fnAddr_rel (name := sessStorePollName)
    hfn addressText_fnOff
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"
      "libsignal_cli::stores::address_text"))
    (by decide)] at hAddrCells
  rw [recordSerialize_fnAddr_eq] at hSerCells
  rw [dirPut_fnAddr_eq] at hPutCells
  code_fetches CryptoVerification.libsignalSessionCode cliStorePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) 216
  dsimp only [tripleRatchetProgAtExt] at hAddrCells hSerCells hPutCells ⊢
  clear hfn hAddr hSer hPut
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessStorePollName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"
      "libsignal_cli::stores::address_text"))
    hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv1
  wp_call_inImage hAddrCells hinv1
    (x.call.call.addrA, x.call.call.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_protocol::state::session::SessionRecord>::serialize"
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
    hinv_sf
  wp_steps
  apply SepWP.done (by wp_norm_goal; bv_omega) (by wp_norm_lhs)
  intro hinv2
  wp_call_inImage hSerCells hinv2
    (x.call.call.recA, s0.sp - 144#64,
      E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g, x.call.call.record,
      _, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
    hinv_sf_1
  wp_steps
  apply SepWP.done (by wp_norm_goal; bv_omega) (by wp_norm_lhs)
  intro hinv3
  wp_call_inImage hPutCells hinv3
    (x.self, x.dir, s0.sp - 200#64, addressText x.call.call.addr.val,
      s0.sp - 176#64, w, w_1, E2E.Record.encodeRecord x.call.call.record, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem sessStorePoll_cli_ok_of_ser {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (B : RunBudgets) (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hSer : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr recordSerializeName)
      ((serializeCanonSpecX A).inImage img))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr sessStorePollName)
      (sessStorePollSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0xd0 + max (max cliAddrTextStk serializeStackX)
      (max cliDirPutStk extHookStack) ≤ 516880 := by decide
  exact sessStorePoll_of_inner
    (fun hhi => sessStorePollInner_ok_x (addressText_cli_ok W himg hh) hSer
      (dirPut_cli_ok W himg hh) hhi)
    (by omega)

theorem sessStorePoll_ext_ok_of_ser {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr recordSerializeName)
      ((serializeCanonSpecX A).inImage img))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr sessStorePollName)
      (sessStorePollSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 208 + max (max cliAddrTextStk serializeStackX)
      (max cliDirPutStk extHookStack) ≤ 516880 := by decide
  exact sessStorePoll_of_inner
    (fun hhi => sessStorePollInner_ok_x (addressText_ext_ok himg hh) hSer
      (dirPut_ext_ok himg hh) hhi)
    (by omega)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StorePollCli
