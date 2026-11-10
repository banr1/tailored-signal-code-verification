/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Symbolic Execution of `remove_pre_key::{closure#0}`

Composes the prologue, `decimal`, `Dir::get`, and post-`Dir::get` branch lemmas to prove
`pkRemovePoll_ok` against `pkRemovePollSpec`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0 setWidth_32_setWidth_64
  extractLsb_0_64_append extractLsb_64_64_append setWidth_64_append
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

/-- Top-level proof of `remove_pre_key::{closure#0}` against `pkRemovePollSpec`. -/
theorem pkRemovePoll_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : pollMinStk decStk getStk putStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName)
      (pkRemovePollSpec rd pathOk A img stk) := by
  rw [← decimal_fnAddr_eq img.base ext] at hDecimal
  rw [← dirGet_fnAddr_eq img.base ext] at hGet
  rw [← dirPut_fnAddr_eq img.base ext] at hPut
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hbrErr := @pkrm_branch_err img A ext rd pathOk decStk getStk putStk stk hC
  have hbrNil := @pkrm_branch_ok_nil img A ext rd pathOk decStk getStk putStk stk hC
  have hbrCons := @pkrm_branch_ok_cons img A ext rd pathOk decStk getStk putStk stk hC hDecimal hPut
  clear hFs hDecimal hPut hC
  refine ⟨(pkRemovePollSpec rd pathOk A img stk).pre x s0, R, hpre, ?_⟩
  generalize hQ_eq :
    (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq :
    (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).onPanic x s0 sf ∗ R)) = Qp
  have hpan_fn : ∀ (sf : State) (P_f : SepProp),
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f := by
    rw [← hQp_eq]
    intro sf P_f halloc hmf
    dsimp only [pkRemovePollSpec, Spec.inImage]
    simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf
  dsimp only [pkRemovePollSpec, Spec.inImage]
  refine SepWPp.pure_elim fun ⟨hinv0_F, hinv0_sym⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx0_0, hx8_0, ⟨hname_lt, hdir_lt, hpOk⟩, hdchg⟩ => ?_
  refine sepWPp_with_stk_bound (a := x.fut) (v := x.self)
    (Rest := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
      memRegion (x.fut + 0xd#64) 3 ∗ dirAt A x.self x.dir ∗
      memRegion x.out 48 ∗ A.pool)
    (Entails.of_eq (by unfold pkBoxAt; ac_rfl))
    fun hstk_hi => ?_
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdec_le : decStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hget_le : getStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}")) 88
  have hinv0 : ImgCallInv img s0 := ⟨hinv0_F, hinv0_sym⟩
  dsimp only [tripleRatchetProgAtExt] at hbrErr hbrNil hbrCons hDecFs hGet hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  rw [stackAt_sub_split s0.sp hstk hstk_hi,
      stackAt_pkRemove_eq s0.sp hmin_hi,
      subStack_split s0.sp hdec_le hmin_hi]
  unfold pkBoxAt pkRemoveFrameSlots
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun q_sp0 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => ?_
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "libsignal_cli::stores::decimal"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  refine sepWPp_name_state fun s1 hs1 => ?_
  have hs1_pc : s1.pc = fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "libsignal_cli::stores::decimal") := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_lr : s1.readReg64 Reg.lr = fnBase + bv% (68) := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_run : s1.status = .Running := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_sp : s1.sp = s0.sp - 0xc0#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_tr : s1.trace = s0.trace := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_fs : s1.fs = s0.fs := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x0 : s1.readReg64 .x0 = s0.sp - 0x78#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x1 : s1.readReg32 .x1 = x.id := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x19 : s1.readReg64 .x19 = x.fut := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x20 : s1.readReg64 .x20 = x.out := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x22 : s1.readReg64 .x22 = x.self := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x23 : s1.readReg64 .x23 = BitVec.setWidth 64 x.id := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_x28 : s1.readReg64 .x28 = s0.readReg64 .x28 := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_fp : s1.readReg64 .x29 = s0.sp - 0x60#64 := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_vregs : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
    rw [hs1]; simp only [arm64_norm, *]
  rw [← hs1] at hinv1
  clear hs1
  let F_dec1 : SepProp :=
    pkBoxAt x.fut x.self x.id 0#8 ∗
    dirAt A x.self x.dir ∗
    memRegion x.out 48 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - decStk) ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xa8#64) 48 ∗
    savedCalleeSlots s0
  refine pkrm_call_decimal_fs hDecFs
    { n := x.id, ret := s0.sp - 0x78#64 } F_dec1
    (s0 := s0)
    hs1_pc hs1_run (spAligned_sub_c0 hsp_align hs1_sp) hs1_lr hs1_tr hinv1
    (by rw [← hs1_fs, ← hs1_tr]; exact FsInv.of_entry s1)
    hs1_x0 hs1_x1 hpan_fn
    (Entails.of_eq (by
      rw [hs1_sp]
      unfold F_dec1 pkBoxAt savedCalleeSlots
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.lr]
      ac_rfl))
    fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hinvm1 hfsm1 htrm1 => ?_
  rw [hs1_sp]
  rcases hcsm1 with
    ⟨hx19_1, hx20_1, _, hx22_1, hx23_1, _, _, _, _, hx28_1, hfp_1, hvregs_1⟩
  have hsp_m1 : sm1.sp = s0.sp - 0xc0#64 := hspm1.trans hs1_sp
  have hsp_al1 : sm1.spAligned = true := spAligned_sub_c0 hsp_align hsp_m1
  have hx19_m1 : sm1.readReg64 .x19 = x.fut := hx19_1.trans hs1_x19
  have hx20_m1 : sm1.readReg64 .x20 = x.out := hx20_1.trans hs1_x20
  have hx22_m1 : sm1.readReg64 .x22 = x.self := hx22_1.trans hs1_x22
  have hx23_m1 : sm1.readReg64 .x23 = BitVec.setWidth 64 x.id := hx23_1.trans hs1_x23
  have hx28_m1 : sm1.readReg64 .x28 = s0.readReg64 .x28 := hx28_1.trans hs1_x28
  have hfp_m1 : sm1.readReg64 .x29 = s0.sp - 0x60#64 := hfp_1.trans hs1_fp
  have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := hvregs_1.trans hs1_vregs
  have htr_m1 : sm1.trace = s0.trace := htrm1.trans hs1_tr
  have hfiles_m1 : sm1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfsm1 htr_m1
  let nameBs := keyName x.id
  have hrestk1 :
      stackAt (s0.sp - 0xc0#64) decStk ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk) =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - getStk) ∗
      stackAt (s0.sp - 0xc0#64) getStk := by
    rw [sepConj_comm, ← subStack_split s0.sp hdec_le hmin_hi,
        subStack_split s0.sp hget_le hmin_hi]
  unfold F_dec1
  change SepWPp _ _ _
    ((vecU8 A (s0.sp - 0x78#64) nameBs ∗ stackAt (s0.sp - 0xc0#64) decStk ∗ A.pool) ∗ _) _ _
  rw [vecU8_eq_bytes_tail A (s0.sp - 0x78#64) nameBs (s0.sp - 0x70#64) (s0.sp - 0x68#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr =>
    SepWPp.pure_elim fun ⟨hnlen, hnlt, hnptr⟩ => ?_
  refine sepWPp_conseq
    (P' := ((stackAt (s0.sp - 0xc0#64) decStk ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk)) ∗
      ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
      ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      A.pool ∗
      pkBoxAt x.fut x.self x.id 0#8 ∗
      dirAt A x.self x.dir ∗
      memRegion x.out 48 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      memRegion (s0.sp - 0xa8#64) 48 ∗
      savedCalleeSlots s0))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hrestk1]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "<libsignal_cli::stores::Dir>::get"))
    hinvm1
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  have hx3_len : (BitVec.ofNat 64 nameBs.length).toNat = nameBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_name_state fun s2 hs2 => ?_
  have hs2_pc : s2.pc = fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "<libsignal_cli::stores::Dir>::get") := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_lr : s2.readReg64 Reg.lr = fnBase + bv% (88) := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_run : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_sp : s2.sp = s0.sp - 0xc0#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_tr : s2.trace = s0.trace := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_files : s2.fs.files = s0.fs.files := by
    have hs2_fs : s2.fs = sm1.fs := by rw [hs2]; simp only [arm64_norm, *]
    rw [hs2_fs]; exact hfiles_m1
  have hs2_x0 : s2.readReg64 .x0 = s0.sp - 0xa8#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x1 : s2.readReg64 .x1 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x2 : s2.readReg64 .x2 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x3 : (s2.readReg64 .x3).toNat = nameBs.length := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_x19 : s2.readReg64 .x19 = x.fut := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x20 : s2.readReg64 .x20 = x.out := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x21 : s2.readReg64 .x21 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x22 : s2.readReg64 .x22 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x23 : s2.readReg64 .x23 = BitVec.setWidth 64 x.id := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_x28 : s2.readReg64 .x28 = s0.readReg64 .x28 := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_fp : s2.readReg64 .x29 = s0.sp - 0x60#64 := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_vregs : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
    rw [hs2]; simp only [arm64_norm, *]
  rw [← hs2] at hinv2
  clear hs2
  let F_get : SepProp :=
    ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    vecU8Tail A nameCap namePtr nameBs ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - getStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8
  refine pkrm_call_dirGet hGet
    { ret := s0.sp - 0xa8#64, self := x.self, dir := x.dir,
      nameA := namePtr, name := nameBs, nameRo := false } F_get
    (s0 := s0)
    hs2_pc hs2_run (spAligned_sub_c0 hsp_align hs2_sp) hs2_lr hs2_tr hinv2
    hs2_x0 hs2_x1 hs2_x2 hs2_x3
    hname_lt hdir_lt hpOk hpan_fn
    (Entails.of_eq (by rw [hs2_sp]; unfold F_get; dsimp only; ac_rfl))
    fun sm2 gr hpcm2 hrunm2 hspm2 hcsm2 hinvm2 hgr => ?_
  rw [hs2_sp]
  rcases hcsm2 with
    ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, _, _, hx28_2, hfp_2, hvregs_2⟩
  have hsp_m2 : sm2.sp = s0.sp - 0xc0#64 := hspm2.trans hs2_sp
  have hx19_m2 : sm2.readReg64 .x19 = x.fut := hx19_2.trans hs2_x19
  have hx20_m2 : sm2.readReg64 .x20 = x.out := hx20_2.trans hs2_x20
  have hx21_m2 : sm2.readReg64 .x21 = namePtr := hx21_2.trans hs2_x21
  have hx22_m2 : sm2.readReg64 .x22 = x.self := hx22_2.trans hs2_x22
  have hx23_m2 : sm2.readReg64 .x23 = BitVec.setWidth 64 x.id := hx23_2.trans hs2_x23
  have hx28_m2 : sm2.readReg64 .x28 = s0.readReg64 .x28 := hx28_2.trans hs2_x28
  have hfp_m2 : sm2.readReg64 .x29 = s0.sp - 0x60#64 := hfp_2.trans hs2_fp
  have hvregs_m2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := hvregs_2.trans hs2_vregs
  have hgr0 : gr = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace :=
    ⟨by simpa only [nameBs, hs2_files] using hgr.1, hgr.2.trans hs2_tr⟩
  clear hs2_files hgr
  have hpost_get :
      ((getResultAt A (s0.sp - 0xa8#64) gr ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        stackAt (s0.sp - 0xc0#64) getStk ∗ A.pool) ∗ F_get) ⊢
      getResultAt A (s0.sp - 0xa8#64) gr ∗
        postGetCommon A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0 := by
    have hstk_merge :
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - getStk) ∗
        stackAt (s0.sp - 0xc0#64) getStk =
        stackAt (s0.sp - 0xc0#64) (subMax decStk getStk putStk) :=
      (subStack_split s0.sp hget_le hmin_hi).symm
    unfold F_get postGetCommon
    have hpull :
        ((getResultAt A (s0.sp - 0xa8#64) gr ∗ dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
          stackAt (s0.sp - 0xc0#64) getStk ∗ A.pool) ∗
          ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
          vecU8Tail A nameCap namePtr nameBs ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - getStk) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          memRegion x.out 48 ∗
          pkBoxAt x.fut x.self x.id 0#8) =
        ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - getStk) ∗
          stackAt (s0.sp - 0xc0#64) getStk) ∗
          (getResultAt A (s0.sp - 0xa8#64) gr ∗
            ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
            SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
            vecU8Tail A nameCap namePtr nameBs ∗
            ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
            memRegion (s0.sp - 0xb0#64) 8 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
            memRegion x.out 48 ∗
            pkBoxAt x.fut x.self x.id 0#8 ∗
            dirAt A x.self x.dir ∗
            A.pool)) := by
      ac_rfl
    rw [hpull, hstk_merge]
    exact Entails.of_eq (by ac_rfl)
  refine sepWPp_conseq hpost_get ?_
  subst hQ_eq hQp_eq
  rcases gr with ⟨⟩ | ⟨_ | ⟨b0, bsRest⟩⟩
  · apply sepWPp_of_sepWP_final
    exact hbrErr x R s0 sm2 nameCap namePtr nameBs q_sp0
      hstk hstk_hi hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hinvm2 hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2
  · apply sepWPp_of_sepWP_final
    exact hbrNil x R s0 sm2 nameCap namePtr nameBs q_sp0
      hstk hstk_hi hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hinvm2 hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2
  · exact hbrCons x R s0 sm2 b0 bsRest nameCap namePtr nameBs q_sp0
      hstk hstk_hi hdchg hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hinvm2
      hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx22_m2 hx23_m2

end CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
