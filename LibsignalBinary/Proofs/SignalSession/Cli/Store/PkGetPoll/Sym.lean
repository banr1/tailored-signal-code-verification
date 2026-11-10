/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Layout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Blocks
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Fetches
import ProofLib.SepLogic.WPp

/-!
# Symbolic Execution of `get_pre_key::{closure#0}`

Proves `pkGetPollInner_ok` against `pkGetPollInnerSpec` by composing the prologue, `decimal`,
`Dir::get`, and the error, missing-key, and `PreKeyRecord::deserialize` branches.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CliPkGetPollNorm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_peek_err_tag {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {e : SignalProtocolError} {d0 d1 d2 d3 d4 d5 d6 : BitVec 64}
    {Rest : SepProp} {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest)
    (h : d0 = errTag → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  subst heq
  have hent :
      pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest ⊢
        ⌜d0 = errTag⌝ ∗ (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest) := by
    dsimp only [pkDecPayload]
    apply Entails.pure_left; rintro ⟨he, rfl, hd1⟩
    exact Entails.pure_right rfl (Entails.pure_right ⟨he, rfl, hd1⟩ (Entails.refl _))
  exact SepWP.weaken_pre hent (SepWP.pure_elim h)

private theorem sepWP_peek_ok_hd0 {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {rec : PreKeyRecord} {d0 d1 d2 d3 d4 d5 d6 : BitVec 64}
    {Rest : SepProp} {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest)
    (h : d0 + 1#64 ≠ 0#64 → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  subst heq
  have hent :
      pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest ⊢
        ⌜d0 + 1#64 ≠ 0#64⌝ ∗ (pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest) := by
    dsimp only [pkDecPayload]
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hφ
    exact Entails.pure_right hφ.1 (Entails.pure_right hφ (Entails.refl _))
  exact SepWP.weaken_pre hent (SepWP.pure_elim h)

private theorem sepWPp_exists_right {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Rest : SepProp} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Rest ∗ P a) Q Qp) :
    SepWPp prog ret s (Rest ∗ (∃∗ a, P a)) Q Qp := by
  rw [sepExists_sepConj_right]
  exact SepWPp.exists_elim h

private theorem sepWPp_exists_mid {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {L R : SepProp} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (L ∗ (P a ∗ R)) Q Qp) :
    SepWPp prog ret s (L ∗ ((∃∗ a, P a) ∗ R)) Q Qp := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact SepWPp.exists_elim h

private theorem finish_epilogue {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} (pathOk : List (BitVec 8) → Prop)
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P R : SepProp}
    (h : SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0)) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ ans,
              ⌜ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
                  sf.trace = s0.trace⌝ ∗
              pkGetAnsAt A x.out ans) ∗
              (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
              dirAt A x.self x.dir ∗ A.pool ∗
              stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32 ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono h fun sf P_f _ _ ⟨hsp, hcs, hent⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  dsimp only [pkGetPollInnerSpec] at hm'
  simpa only [sepConj_assoc] using hm'

private theorem pkGetPoll_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr pkGetPollName =
      b + bv% (ls_off%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") := by
  have h1 := pkGetPoll_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetPollName, h1]

/-- Full symbolic proof of the inner specification `pkGetPollInnerSpec`. -/
theorem pkGetPollInner_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk : Nat}
    (hC : AllocContractsX img A ext)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hhi : max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)) ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName)
      ((pkGetPollInnerSpec rd pathOk A
        (max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))).inImage img) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
  have hDeallocCells := dealloc_buf_cells_ok (calleeStk := calleeStk) hC (by omega) hhi
  have hDecimalCells := decimal_cells_ok (calleeStk := calleeStk) hDecimal hFs (by omega) hhi
  have hGetCells := dirGet_cells_ok (calleeStk := calleeStk) hGet (by omega) hhi
  have hDecCells := pkDec_cells_ok (calleeStk := calleeStk) hDec (by omega) hhi
  have hDropCells := dropSpeWord_cells_ok (calleeStk := calleeStk) hDrop (by omega) hhi
  rw [decimal_fnAddr_eq] at hDecimalCells
  rw [dirGet_fnAddr_eq] at hGetCells
  rw [pkDec_fnAddr_eq] at hDecCells
  rw [dropSpe_fnAddr_eq] at hDropCells
  clear hC hDecimal hGet hDec hDrop hFs
  have hfn : libsignalSessionCode.fnOff pkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") :=
    pkGetPoll_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliPkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
    0 152
  code_fetches_range CryptoVerification.libsignalSessionCode cliPkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
    236 4
  clear hfn
  unfold Spec.inImage
  dsimp only [pkGetPollInnerSpec]
  dsimp only [tripleRatchetProgAtExt] at hDecimalCells hGetCells hDecCells ⊢
  generalize hfn_eq : (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr pkGetPollName = fnBase at *
  wpp_init x s0
  have hfn_restore : (tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName = fnBase :=
    (pkGetPoll_fnAddr_eq img.base ext).trans hfn_eq
  have hal0 : s0.spAligned = true := by assumption
  have hname0 : PkNameOk pathOk x.dir x.id := by assumption
  have hsize0 : PkSizeOk rd s0.fs.files x.dir x.id := by assumption
  obtain ⟨hnlen, hplen, hpok⟩ := hname0
  have hnlen_bv : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length :=
    Nat.mod_eq_of_lt (by omega)
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  refine SepWPp.weaken_pre
    (P' := ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 56 ∗ A.pool ∗
      stackAt (s0.sp - 256#64) calleeStk ∗ pkPollSlack s0.sp) ∗
      (cells (s0.sp - 256#64) 6 ∗ (cells (s0.sp - 200#64) 3 ∗
        (cells (s0.sp - 176#64) 2 ∗ (cells (s0.sp - 152#64) 7 ∗ cells (s0.sp - 96#64) 12)))))
    (by rw [cells_32_split]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [cells_sub_6_256_eq]
  apply sepWPp_exists_mid; intro v
  apply sepWPp_exists_mid; intro v_1
  apply sepWPp_exists_mid; intro v_2
  apply sepWPp_exists_mid; intro v_3
  apply sepWPp_exists_mid; intro v_4
  apply sepWPp_exists_mid; intro v_5
  rw [← sepConj_assoc, cells_sub_3_200_eq]
  apply sepWPp_exists_mid; intro v_6
  apply sepWPp_exists_mid; intro v_7
  apply sepWPp_exists_mid; intro v_8
  rw [← sepConj_assoc, cells_sub_2_176_eq]
  apply sepWPp_exists_mid; intro v_9
  apply sepWPp_exists_mid; intro v_10
  rw [← sepConj_assoc, cells_sub_7_152_eq]
  apply sepWPp_exists_mid; intro v_11
  apply sepWPp_exists_mid; intro v_12
  apply sepWPp_exists_mid; intro v_13
  apply sepWPp_exists_mid; intro v_14
  apply sepWPp_exists_mid; intro v_15
  apply sepWPp_exists_mid; intro v_16
  apply sepWPp_exists_mid; intro v_17
  rw [← sepConj_assoc, cells_sub_12_96_eq]
  apply sepWPp_exists_right; intro v_18
  apply sepWPp_exists_right; intro v_19
  apply sepWPp_exists_right; intro v_20
  apply sepWPp_exists_right; intro v_21
  apply sepWPp_exists_right; intro v_22
  apply sepWPp_exists_right; intro v_23
  apply sepWPp_exists_right; intro v_24
  apply sepWPp_exists_right; intro v_25
  apply sepWPp_exists_right; intro v_26
  apply sepWPp_exists_right; intro v_27
  apply sepWPp_exists_right; intro v_28
  apply sepWPp_exists_right; intro v_29
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
      "libsignal_cli::stores::decimal"))
    hinv0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre (Entails.of_eq (by unfold pkBoxKeep pkSavedRegs; ac_rfl))
    (P' := pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
      ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
      ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
      ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
      ((s0.sp - 200#64) ↦₆₄ v_6) ∗ ((s0.sp - 192#64) ↦₆₄ v_7) ∗ ((s0.sp - 184#64) ↦₆₄ v_8) ∗
      ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10) ∗
      ((s0.sp - 152#64) ↦₆₄ v_11) ∗ ((s0.sp - 144#64) ↦₆₄ v_12) ∗
      ((s0.sp - 136#64) ↦₆₄ v_13) ∗ ((s0.sp - 128#64) ↦₆₄ v_14) ∗
      ((s0.sp - 120#64) ↦₆₄ v_15) ∗ ((s0.sp - 112#64) ↦₆₄ v_16) ∗ ((s0.sp - 104#64) ↦₆₄ v_17)) ?_
  wp_call_inImage hDecimalCells hinv1 (x.id, s0.sp - 200#64, _, _, _, s0.sp - 256#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
      "<libsignal_cli::stores::Dir>::get"))
    hinv_sf
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  intro hinv2
  wp_call_inImage hGetCells hinv2
    (s0.sp - 152#64, x.self, x.dir, w_1, keyName x.id, _, _, _, _, _, _, s0.sp - 256#64)
  case panic =>
    intro sf_p _ hm
    exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
  have hget_post :
      w_2 = x.dir.get rd s0.fs.files (keyName x.id) ∧ sf_1.trace = s0.trace := by
    have htr_sf0 : sf.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
    have hfs_sf0 : sf.fs.files = s0.fs.files := by simp only [wp_norm, arm64_norm, *]
    exact ⟨by rw [← hfs_sf0]; exact ‹w_2 = _›, (‹sf_1.trace = sf.trace›).trans htr_sf0⟩
  refine SepWPp.weaken_pre
    (P' := dirGetPayload A w_2 w_3 w_4 w_5 w_6 w_7 w_8 ∗
      ((s0.sp - 152#64) ↦₆₄ w_3) ∗ ((s0.sp - 144#64) ↦₆₄ w_4) ∗
      ((s0.sp - 136#64) ↦₆₄ w_5) ∗ ((s0.sp - 128#64) ↦₆₄ w_6) ∗
      ((s0.sp - 120#64) ↦₆₄ w_7) ∗ ((s0.sp - 112#64) ↦₆₄ w_8) ∗
      ((s0.sp - 104#64) ↦₆₄ v_17) ∗
      (w_1 ↦ₛ keyName x.id) ∗ vecU8BufRest A w w_1 (keyName x.id) ∗
      pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
      ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
      ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
      ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
      ((s0.sp - 200#64) ↦₆₄ w) ∗ ((s0.sp - 192#64) ↦₆₄ w_1) ∗
      ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
      ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
    (Entails.of_eq (by ac_rfl)) ?_
  rcases w_2 with ⟨⟩ | ⟨⟩ | ⟨b0, rest⟩
  · -- `r = .error ()`
    dsimp only [dirGetPayload]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hw0 => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply bind_sepWP_state; intro s_err
    have htr_err : s_err.trace = sf_1.trace := by simp only [s_err, wp_norm, arm64_norm]
    have hAns_err :
        (PkAns.readErr : PkAns PreKeyRecord) =
            pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          s_err.trace = s0.trace :=
      ⟨by rw [← hget_post.1]; rfl, htr_err.trans hget_post.2⟩
    have hinv_err : ImgCallInv img s_err :=
      imgCallInv_of_mem_eq hinv_sf_1
        (by simp only [s_err, wp_norm, arm64_norm])
        (by simp only [s_err, wp_norm, arm64_norm])
    have hpc_err : s_err.pc = fnBase + bv% (200) := by
      simp only [s_err, wp_norm, arm64_norm, *]; try bv_omega
    rw [← hfn_restore] at hDeallocCells hpc_err
    apply finish_epilogue pathOk
    refine step_err_200 hDeallocCells
      w_4 w_5 w_6 w_7 w_8 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
      v v_1 v_2 v_3 v_4 v_5 v_9 v_10 v_17
      hinv_err hpc_err
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      (by simp only [s_err, wp_norm, arm64_norm, *])
      hAns_err
      ?_
    exact Entails.of_eq (by ac_rfl)
  · -- `r = .ok []`
    have ⟨hget_eq, htr_sf1⟩ :
        x.dir.get rd s0.fs.files (keyName x.id) = .ok [] ∧ sf_1.trace = s0.trace :=
      ⟨hget_post.1.symm, hget_post.2⟩
    have hAns_miss :
        PkAns.missing =
          pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
      rw [hget_eq]; rfl
    dsimp only [dirGetPayload]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hw3⟩ => ?_
    change w_6 = 0#64 at hw3
    subst hw0 hw3
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply bind_sepWP_state; intro s_miss
    have hinv_miss : ImgCallInv img s_miss :=
      imgCallInv_of_mem_eq hinv_sf_1
        (by simp only [s_miss, wp_norm, arm64_norm])
        (by simp only [s_miss, wp_norm, arm64_norm])
    have hpc_miss : s_miss.pc = fnBase + bv% (240) := by
      simp only [s_miss, wp_norm, arm64_norm, *]; try bv_omega
    have hm_run : s_miss.status = .Running := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_sp : s_miss.sp = s0.sp - 256#64 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_tr : s_miss.trace = s0.trace := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_19 : s_miss.readReg64 .x19 = x.fut := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_20 : s_miss.readReg64 .x20 = x.out := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_21 : s_miss.readReg64 .x21 = 0#64 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_22 : s_miss.readReg64 .x22 = w_1 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_23 : s_miss.readReg64 .x23 = w_4 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_24 : s_miss.readReg64 .x24 = w_5 := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_25 : s_miss.readReg64 .x25 = okTagVec := by simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_26 : s_miss.readReg64 .x26 = errTag := by
      simp only [s_miss, wp_norm, arm64_norm, *]; rfl
    have hm_27 : s_miss.readReg64 .x27 = s0.sp - 152#64 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_28 : s_miss.readReg64 .x28 = s0.readReg64 .x28 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_29 : s_miss.readReg64 .x29 = s0.sp - 96#64 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    have hm_vr : calleeSavedVRegs s_miss = calleeSavedVRegs s0 := by
      simp only [s_miss, wp_norm, arm64_norm, *]
    rw [← hfn_restore] at hDeallocCells hDropCells hpc_miss
    apply finish_epilogue pathOk
    refine step_ok_240 hDeallocCells hDropCells
      .missing []
      w_4 w_5 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
      errTag okTagVec (s0.readReg64 .x28) (s0.sp - 152#64) 0#64
      v_4 v_5 v v_1 v_2 v_3 v_9 v_10
      okTagVec w_4 w_5 0#64 w_7 w_8 v_17
      emp
      hinv_miss hpc_miss hm_run hm_sp hal0 hm_tr
      hm_19 hm_20 hm_21 hm_22 hm_23 hm_24 hm_25 hm_26 hm_27 hm_28 hm_29 hm_vr
      hAns_miss
      (Or.inl ⟨rfl, rfl, rfl⟩)
      ?_
    rw [emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · -- `r = .ok (b0 :: rest)`
    have ⟨hget_eq, htr_sf1⟩ :
        x.dir.get rd s0.fs.files (keyName x.id) = .ok (b0 :: rest) ∧ sf_1.trace = s0.trace :=
      ⟨hget_post.1.symm, hget_post.2⟩
    have hblen : (b0 :: rest).length < 2 ^ 32 := hsize0 (b0 :: rest) hget_eq
    have hpos : 0 < (b0 :: rest).length := by simp
    have hblen_bv : (BitVec.ofNat 64 (b0 :: rest).length).toNat = (b0 :: rest).length :=
      Nat.mod_eq_of_lt (by omega)
    have hblen_nz : BitVec.ofNat 64 (b0 :: rest).length ≠ 0#64 := by
      intro hz
      have h0 : (BitVec.ofNat 64 (b0 :: rest).length).toNat = 0 := congrArg BitVec.toNat hz
      omega
    have hblen_eq : (BitVec.ofNat 64 (b0 :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hblen_nz
    have hblen_ne : (BitVec.ofNat 64 (b0 :: rest).length != 0#64) = true :=
      bne_iff_ne.mpr hblen_nz
    dsimp only [dirGetPayload]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hw3⟩ => ?_
    subst hw0 hw3
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase - bv% (ls_rel%
        "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
      hinv_sf_1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
    intro hinv3
    wp_call_inImage hDecCells hinv3
      (w_5, b0 :: rest, s0.sp - 152#64, _, _, _, _, _, _, _, s0.sp - 256#64)
    case panic =>
      intro sf_p _ hm
      rw [← sepConj_assoc]
      exact close_panic_subgoal (by simp only [wp_norm, arm64_norm, *]) hm
    rcases hdec : PreKeyRecord.deserialize (b0 :: rest) with e | rec
    · apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (152)) hinv_sf_2
      refine sepWP_peek_err_tag (A := A) (e := e) (d0 := w_2) (d1 := w_3) (d2 := w_6) (d3 := w_9)
        (d4 := w_10) (d5 := w_11) (d6 := w_12)
        (Rest := ((s0.sp - 152#64) ↦₆₄ w_2) ∗ ((s0.sp - 144#64) ↦₆₄ w_3) ∗
          ((s0.sp - 136#64) ↦₆₄ w_6) ∗ ((s0.sp - 128#64) ↦₆₄ w_9) ∗
          ((s0.sp - 120#64) ↦₆₄ w_10) ∗ ((s0.sp - 112#64) ↦₆₄ w_11) ∗
          ((s0.sp - 104#64) ↦₆₄ w_12) ∗
          (w_5 ↦ₛ (b0 :: rest)) ∗ vecU8BufRest A w_4 w_5 (b0 :: rest) ∗
          (w_1 ↦ₛ keyName x.id) ∗ vecU8BufRest A w w_1 (keyName x.id) ∗
          pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
          ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
          ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
          ((s0.sp - 200#64) ↦₆₄ w) ∗ ((s0.sp - 192#64) ↦₆₄ w_1) ∗
          ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
        (by simp only [pointsToBytes_cons]; ac_rfl) fun hd0_tag => ?_
      have hd0_eq : (w_2 + 1#64 == 0#64) = true := by rw [hd0_tag]; rfl
      have hd0_ne : (w_2 + 1#64 != 0#64) = false := by rw [hd0_tag]; rfl
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv_de
      apply SepWPp.of_sepWP_ret
      apply bind_sepWP_state; intro s_de
      have hpc_de : s_de.pc = fnBase + bv% (152) := by
        simp only [s_de, wp_norm, arm64_norm, *]; try bv_omega
      have hAns_de :
          PkAns.decodeErr e =
            pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
        rw [hget_eq, pkAnsOf, hdec]
      rw [← hfn_restore] at hDeallocCells hpc_de
      apply finish_epilogue pathOk
      refine step_dec_err_152 hDeallocCells
        e (b0 :: rest)
        w_4 w_5 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
        w_2 w_3 w_6 w_9 w_10 w_11 w_12
        v v_1 v_2 v_3 v_9 v_10
        hinv_de hpc_de
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        hal0
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        (by simp only [s_de, wp_norm, arm64_norm, *])
        hd0_tag hAns_de
        ?_
      exact Entails.of_eq (by simp only [pointsToBytes_cons]; ac_rfl)
    · apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (240)) hinv_sf_2
      refine sepWP_peek_ok_hd0 (A := A) (rec := rec) (d0 := w_2) (d1 := w_3) (d2 := w_6) (d3 := w_9)
        (d4 := w_10) (d5 := w_11) (d6 := w_12)
        (Rest := ((s0.sp - 152#64) ↦₆₄ w_2) ∗ ((s0.sp - 144#64) ↦₆₄ w_3) ∗
          ((s0.sp - 136#64) ↦₆₄ w_6) ∗ ((s0.sp - 128#64) ↦₆₄ w_9) ∗
          ((s0.sp - 120#64) ↦₆₄ w_10) ∗ ((s0.sp - 112#64) ↦₆₄ w_11) ∗
          ((s0.sp - 104#64) ↦₆₄ w_12) ∗
          (w_5 ↦ₛ (b0 :: rest)) ∗ vecU8BufRest A w_4 w_5 (b0 :: rest) ∗
          (w_1 ↦ₛ keyName x.id) ∗ vecU8BufRest A w w_1 (keyName x.id) ∗
          pkBoxKeep x s0 ∗ dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
          ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
          ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
          ((s0.sp - 200#64) ↦₆₄ w) ∗ ((s0.sp - 192#64) ↦₆₄ w_1) ∗
          ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
        (by simp only [pointsToBytes_cons]; ac_rfl) fun hd0 => ?_
      have hd0_eq : (w_2 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hd0
      have hd0_ne : (w_2 + 1#64 != 0#64) = true := bne_iff_ne.mpr hd0
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv_ok
      apply SepWPp.of_sepWP_ret
      apply bind_sepWP_state; intro s_ok
      have hpc_ok : s_ok.pc = fnBase + bv% (240) := by
        simp only [s_ok, wp_norm, arm64_norm, *]; try bv_omega
      have hAns_ok :
          PkAns.found rec =
            pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
        rw [hget_eq, pkAnsOf, hdec]
      rw [← hfn_restore] at hDeallocCells hDropCells hpc_ok
      apply finish_epilogue pathOk
      refine step_ok_240 hDeallocCells hDropCells
        (.found rec) (b0 :: rest)
        w_4 w_5 w w_1 (BitVec.ofNat 64 (keyName x.id).length)
        w_2 w_3 w_6 w_9 w_10 w_11 w_12
        v v_1 v_2 v_3 v_9 v_10
        w_2 w_3 w_6 w_9 w_10 w_11 w_12
        (pkDecPayload A (.ok rec) w_2 w_3 w_6 w_9 w_10 w_11 w_12)
        hinv_ok hpc_ok
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        hal0
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        (by simp only [s_ok, wp_norm, arm64_norm, *])
        hAns_ok
        (Or.inr ⟨rec, rfl, hd0, rfl⟩)
        ?_
      exact Entails.of_eq (by simp only [pointsToBytes_cons]; ac_rfl)

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
