/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchSome
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

private theorem ispoll_onPanic_sym {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    {x : IdPollGhost} {s0 sf : State} {P_f : SepProp}
    (hp : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf := by
  simp only [idSavePollSpec, Spec.inImage]
  exact Entails.pure_right hp (entails_anyHeap P_f)

private theorem sepWPp_post_mono {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (hQp : ∀ sf P_f, Qp1 sf P_f → Qp2 sf P_f)
    (hw : SepWPp prog ret s P Q1 Qp1) :
    SepWPp prog ret s P Q2 Qp2 := fun R hm hL => by
  rcases hw R hm hL with ⟨sf, hsteps, ⟨hpc_f, hrun_f, P_f, hm_f, hq⟩ | ⟨hst, P_f, hm_f, hqp⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f, hm_f, hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, P_f, hm_f, hQp sf P_f hqp⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Core layout-independent verification of `save_identity::{closure#0}`, parameterized over the
sub-callee frame index `getStk'` and `PublicKey::eq` stack budget `eqStk`. -/
theorem idSavePoll_ok_of_deps_core_gen {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk getStk' putStk eqStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyDecodeName)
      (identityKeyDecodeSpec A img))
    (hEqAt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (publicKeyEqAtSpec eqStk))
    (hget_le : getStk ≤ saveSubMax getStk' putStk)
    (heq_le : eqStk ≤ saveSubMax getStk' putStk)
    (hstk : saveMinStk getStk' putStk ≤ stk)
    (_hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName)
      (idSavePollSpec rd pathOk A img stk) := by
  have hGet' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::get" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (dirGetSpec rd pathOk A img getStk) := by
    rw [dirGet_fnAddr_eq]; exact hGet
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 68
  clear hfn hGet
  dsimp only [tripleRatchetProgAtExt] at hGet' ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  wpp_init x s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) :=
    fun _ _ hp => ispoll_onPanic_sym hp
  have hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32 := by omega
  have hdlen : x.peers.path.length < 2 ^ 32 := by omega
  have hclen : x.peers.changed.length < 2 ^ 32 := by omega
  have hpOk : pathOk (pathOf x.peers.path x.call.call.addr.val.name) := by assumption
  have hwf : ∀ (bs : List (BitVec 8)),
      DirGhost.get rd s0.fs.files x.peers x.call.call.addr.val.name = Except.ok bs → IdFileWf bs := by
    assumption
  refine sepWPp_post_mono
    (Q1 := fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
    (Qp1 := fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf)
    (fun sf P_f ⟨hsp_f, hcs_f, hent⟩ =>
      ⟨fun hm => Satisfies.mono (sepConj_mono_left hent) hm, hsp_f, hcs_f⟩)
    (fun sf P_f hent hm => Satisfies.mono (sepConj_mono_left hent) hm) ?_
  have hhi : stk ≤ 2 ^ 64 := by
    have hfoc : ∃ Rest : SepProp,
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        dirAt A (x.self + 40#64) x.peers ∗
        memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList ∗
        logOff img ∗ A.pool ∗ stackAt s0.sp stk ∗ R ⊢
        (stackAt s0.sp stk ∗ (x.call.fut ↦₆₄ x.self)) ∗ Rest := by
      refine ⟨?Rest, ?hfoc⟩
      case hfoc => unfold idSaveBoxAt; ispoll_close_frame
    rcases hfoc with ⟨Rest, hfoc⟩
    have h1 := Satisfies.mono hfoc hpre
    exact memRegion_bound_of_pointsTo64 (by simpa only [stackAt, sepConj_assoc] using h1)
  have hmin : saveMinStk getStk' putStk ≤ 2 ^ 64 := le_trans hstk hhi
  have hsub_hi : saveSubMax getStk' putStk ≤ 2 ^ 64 := by
    unfold saveMinStk at hmin; omega
  conv =>
    arg 4
    rw [stackAt_sub_split s0.sp hstk hhi, stackAt_savePoll_eq s0.sp hmin,
        protocolAddressAt_borrow A x.call.call.addr x.call.call.addrA]
    unfold savePollFrameSlots idSaveBoxAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4
  apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6
  apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c15
  apply SepWPp.exists_elim; intro s16
  apply SepWPp.exists_elim; intro s24
  apply SepWPp.exists_elim; intro s32
  apply SepWPp.exists_elim; intro s40
  apply SepWPp.exists_elim; intro s48
  apply SepWPp.exists_elim; intro s56w
  repeat' (apply SepWPp.exists_elim; intro _)
  examples_hide_fetches
  apply sepWPp_step_to_frozen hinv0 (mid := entry +
    bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::get" -
      ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_get hsym_get
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) hget_le hsub_hi]
    simp only [sepConj_assoc]
  have hx3_len : (BitVec.ofNat 64 x.call.call.addr.name.bytes.length).toNat =
      x.call.call.addr.name.bytes.length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ispoll_call_dirGet (ret_pc := entry + offAfterGet)
    hGet'
    { ret := s0.sp - 0x90#64
      self := x.self + 0x28#64
      dir := x.peers
      nameRo := false
      nameA := x.call.call.addr.name.ptr
      name := x.call.call.addr.name.bytes } ?ispollF
    (by wp_norm_goal) (by wp_norm_lhs)
    (spAligned_sub_d0 (by simpa only [State.spAligned, beq_iff_eq] using hsp_align) (by wp_norm_goal))
    (by wp_norm_goal) (by wp_norm_goal)
    ⟨hF_get, hsym_get⟩
    (by wp_norm_goal)
    (by wp_norm_goal)
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, hx3_len])
    hnlen hdlen hpOk hpan
    ?ispollPre ?_
  case ispollPre => ispoll_close_frame
  intro sm1 gr hpc1 hrun1 hsp1 hcs1 hinv1 hgr
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hsp1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true :=
    spAligned_sub_d0 (by simpa only [State.spAligned, beq_iff_eq] using hsp_align) hsp1
  simp only [fs_setPC, fs_setMem, fs_writeReg64, wp_norm, arm64_norm] at hgr
  have hentry' : (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName = entry := by
    unfold tripleRatchetProgAtExt Program.fnAddr
    simpa using hentry
  have hpc1' : sm1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offAfterGet := by
    rw [hentry']; exact hpc1
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) hget_le hsub_hi).symm
  change SepWPp (tripleRatchetProgAtExt img.base ext) _ _ _ _ _
  refine sepWPp_conseq (P' :=
      getResultAt A (s0.sp - 0x90#64) gr ∗
      dirAt A (x.self + 0x28#64) x.peers ∗
      memRegion x.call.out 48 ∗
      idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
      logOff img ∗ A.pool ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk' putStk) ∗
      stackAt (s0.sp - 0xd0#64) (saveSubMax getStk' putStk) ∗
      memRegion (s0.sp - 0xd0#64) 8 ∗
      overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
      ((s0.sp - 0xc1#64) ↦₈ c15) ∗
      ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
      ((s0.sp - 0xb8#64) ↦₈ s24) ∗
      memRegion (s0.sp - 0xb7#64) 7 ∗
      ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
      ((s0.sp - 0xa8#64) ↦₈ s40) ∗
      memRegion (s0.sp - 0xa7#64) 7 ∗
      ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
      ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
      savedCalleeSlots s0) (Entails.of_eq ?_) ?_
  · rw [protocolAddressAt_borrow A x.call.call.addr x.call.call.addrA]
    unfold idSaveBoxAt savedCalleeSlots
    simp only [wp_norm, arm64_norm]
    ispoll_ac_rfl
  rcases hgr with ⟨hgr_eq, htr1⟩
  rcases gr with ⟨⟩ | bs
  · exact ispoll_branch_err (rd := rd) (pathOk := pathOk) hstk hhi x
      c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
      hpc1' hrun1 hsp1 hsp_al1 hvregs_1 hx19_1 hx20_1 hx29_1 ⟨hgr_eq.symm, htr1⟩
  · rcases hwf bs hgr_eq.symm with rfl | ⟨k, hser⟩
    · exact ispoll_branch_ok_nil (pathOk := pathOk) hC hPut hstk hhi x
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
        hpc1' hrun1 hsp1 hsp_al1 hvregs_1 htr1 hinv1 hx19_1 hx20_1 hx24_1 hx29_1
        hnlen hclen hgr_eq
    · exact ispoll_branch_ok_some_gen (pathOk := pathOk) hC hPut hDec
        (by rw [hentry']; exact hEqAt) heq_le hstk hhi x k
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
        hpc1' hrun1 hsp1 hsp_al1 hvregs_1 htr1 hinv1 hx19_1 hx20_1 hx24_1 hx29_1
        hnlen hclen hser hgr_eq

/-- Core layout-independent verification of `save_identity::{closure#0}`. -/
theorem idSavePoll_ok_of_deps_core {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyDecodeName)
      (identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName)
      (idSavePollSpec rd pathOk A img stk) :=
  idSavePoll_ok_of_deps_core_gen hC hGet hPut hDec (ispoll_publicKeyEq_ok_at_64 hEq)
    (getStk_le_saveSubMax getStk putStk) (eqStk_le_saveSubMax getStk putStk) hstk hb

/-- Stacked 32-bit `black_box` (`PublicKeyEqOkExt32`) verification of `save_identity::{closure#0}`. -/
theorem idSavePoll_ok_of_deps_core_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyDecodeName)
      (identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hstk : saveMinStkExt getStk putStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName)
      (idSavePollSpec rd pathOk A img stk) :=
  idSavePoll_ok_of_deps_core_gen (getStk' := max getStk Getters.publicKeyEqStackExt)
    hC hGet hPut hDec (ispoll_publicKeyEq_ok_at_ext32 hEq)
    (by dsimp only [saveSubMax]; omega) (by dsimp only [saveSubMax]; omega)
    (by rwa [saveMinStk_max_eqStkExt]) hb

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
