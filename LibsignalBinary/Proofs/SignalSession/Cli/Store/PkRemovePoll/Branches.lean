/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Layout
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

/-!
# Post-`Dir::get` Branch Proofs for `remove_pre_key::{closure#0}`

Symbolic execution of the `Err`, `Ok([])`, and `Ok(b0 :: bsRest)` arms from `+0x058` to return in
`remove_pre_key::{closure#0}`.
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

theorem sepWPp_of_sepWP_final {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog ret s P Q) : SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_ret h

theorem sepWPp_name_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (k : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  k s rfl

theorem sepWP_to_sepWPp {prog : Program} {ret mid : BitVec 64} {s : State} {img : Obj.Image}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm P_m => ImgCallInv img sm → SepWPp prog ret sm P_m Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hinv.1 hinv.2 (h.mono fun _ _ _ _ hk hfz hsym => hk ⟨hfz, hsym⟩)

theorem getResultAt_ok_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 0xa8#64) (.ok bs) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 0xa8#64) ↦₆₄ okTagVec) ∗
        ((sp - 0xa0#64) ↦₆₄ cap) ∗
        ((sp - 0x98#64) ↦₆₄ ptr) ∗
        ((sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs ∗
        memRegion (sp - 0x88#64) 16) := by
  dsimp only [getResultAt, vecResultAt]
  have e1 : sp - 0xa8#64 + 8#64 = sp - 0xa0#64 := by bv_omega
  have e2 : sp - 0xa8#64 + 0x20#64 = sp - 0x88#64 := by bv_omega
  rw [e1, e2, vecU8_eq_bytes_tail A (sp - 0xa0#64) bs (sp - 0x98#64) (sp - 0x90#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepProp_ext <;>
    (refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))

theorem pkrm_post_entails (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (img : Obj.Image) (stk : Nat)
    (x : PkPollGhost) (s0 sf : State)
    (res : Except Unit Unit × DirGhost)
    (hres : res = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
      sf.trace = s0.trace) :
    (pkRemoveOutAt A x.out res.1 ∗ dirAt A x.self res.2 ∗
      pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool ∗ stackAt s0.sp stk) ⊢
      (pkRemovePollSpec rd pathOk A img stk).post x s0 sf := by
  simp only [pkRemovePollSpec, Spec.inImage, sepExists_sepConj_left, sepConj_assoc]
  exact Entails.sepExists_right res (Entails.pure_right hres (Entails.refl _))

theorem finish_common_reassemble (A : RustAlloc) (s0 : State) (x : PkPollGhost)
    {decStk getStk putStk stk : Nat}
    (hstk : pollMinStk decStk getStk putStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64)
    (res : Except Unit Unit × DirGhost) (q_sp0 : BitVec 128) :
    (pkRemoveOutAt A x.out res.1 ∗
      dirAt A x.self res.2 ∗
      memRegion (s0.sp - 0xa8#64) 48 ∗
      memRegion (s0.sp - 0x78#64) 24 ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      savedCalleeSlots s0 ∗
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      pkBoxAt x.fut x.self x.id 1#8 ∗
      A.pool) ⊢
    pkRemoveOutAt A x.out res.1 ∗ dirAt A x.self res.2 ∗
      pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool ∗ stackAt s0.sp stk := by
  have hrstk := restore_pollStack s0 hstk hstk_hi q_sp0
  have hgroup :
      (pkRemoveOutAt A x.out res.1 ∗
        dirAt A x.self res.2 ∗
        memRegion (s0.sp - 0xa8#64) 48 ∗
        memRegion (s0.sp - 0x78#64) 24 ∗
        ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
        memRegion (s0.sp - 0xb0#64) 8 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - extHookStack) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
        pkBoxAt x.fut x.self x.id 1#8 ∗
        A.pool) =
      ((pkRemoveOutAt A x.out res.1 ∗ dirAt A x.self res.2 ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          memRegion (s0.sp - 0xa8#64) 48 ∗
          memRegion (s0.sp - 0x78#64) 24 ∗
          savedCalleeSlots s0)) := by
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right hrstk) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Shared post-`Dir::get` spatial state before inspecting `gr`. -/
def postGetCommon (A : RustAlloc) (s0 : State) (x : PkPollGhost)
    (decStk getStk putStk stk : Nat)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128) : SepProp :=
  ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
  ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
  ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
  SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
  vecU8Tail A nameCap namePtr nameBs ∗
  ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
  memRegion (s0.sp - 0xb0#64) 8 ∗
  savedCalleeSlots s0 ∗
  stackAt (s0.sp - 0xc0#64) (subMax decStk getStk putStk) ∗
  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
  memRegion x.out 48 ∗
  pkBoxAt x.fut x.self x.id 0#8 ∗
  dirAt A x.self x.dir ∗
  A.pool

/-- Branch A (`+0x058` on `gr = .error ()`): frees `name` if `nameCap ≠ 0`, moves the 48-byte SPE
to `out`, leaves `dirAt` unchanged, and returns `(.error (), x.dir)`. -/
theorem pkrm_branch_err {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (x : PkPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hgr : Except.error () = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (88))
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img sm2)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0xa8#64) (.error ()) ∗
        postGetCommon A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hne : (speWord 1 + 2#64 == 0#64) = false := speWord_one_add_two_ne_zero
  have hdealloc := pkrm_dealloc_ok_at hC
  have hep := @pkrm_epilogue_108 img ext
  clear hC
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    88 16
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    192 32
  dsimp only [tripleRatchetProgAtExt] at hep hdealloc hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  unfold postGetCommon
  change SepWP _ _ _ (speAt A (utf8 "read") (s0.sp - 0xa8#64) .invalidState ∗ _) _
  rw [speAt_read_invalidState_eq A (s0.sp - 0xa8#64) (s0.sp - 0xa0#64) (s0.sp - 0x98#64)
        (s0.sp - 0x90#64) (s0.sp - 0x88#64)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega),
      subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun errBs => SepWP.exists_elim fun errCap =>
    SepWP.exists_elim fun errPtr => SepWP.exists_elim fun fnPtr => ?_
  let q_err : BitVec 128 := BitVec.ofNat 64 (utf8 "read").length ++ fnPtr
  let F_err : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa0#64) ↦₆₄ errCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ errPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
    ((s0.sp - 0x88#64) ↦₁₂₈ q_err) ∗
    speReadHeap A errBs errCap errPtr fnPtr ∗
    ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    dirAt A x.self x.dir
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f :
        (Except.error (), x.dir) =
          pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace :=
      ⟨by rw [← hgr.1]; rfl, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (pkrm_post_entails rd pathOk A img stk x s0 sf (.error (), x.dir) hres_f)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.error (), x.dir) q_err)
    have hout := speAt_read_invalidState_intro A x.out errBs errCap errPtr fnPtr
    have hslot := slot_a8_err_collapse s0.sp (speWord 1) errCap errPtr
      (BitVec.ofNat 64 errBs.length) q_err
    have h24 := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
      nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
    have hgrp :
        epilogueOut s0 x (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err =
        (((x.out ↦₆₄ speWord 1) ∗ ((x.out + 8#64) ↦₆₄ errCap) ∗
          ((x.out + 0x10#64) ↦₆₄ errPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((x.out + 0x20#64) ↦₁₂₈ q_err) ∗
          speReadHeap A errBs errCap errPtr fnPtr) ∗
        (((s0.sp - 0xa8#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa0#64) ↦₆₄ errCap) ∗
          ((s0.sp - 0x98#64) ↦₆₄ errPtr) ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((s0.sp - 0x88#64) ↦₁₂₈ q_err)) ∗
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (dirAt A x.self x.dir ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_err) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗
          A.pool)) := by
      unfold epilogueOut F_err q_err; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hout (sepConj_mono hslot (sepConj_mono_left h24))) ?_
    exact Entails.of_eq (by ac_rfl)
  have hb8 : s0.sp - 0xc0#64 + 8#64 = s0.sp - 184#64 := by bv_omega
  have h80 : s0.sp - 0x88#64 + 8#64 = s0.sp - 128#64 := by bv_omega
  unfold Arm64.pointsTo128
  simp only [hb8, h80, extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (264)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _hinv_108
    refine hep x s0 _
      (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err _
      (stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        unfold epiloguePre F_err q_err Arm64.pointsTo128
        simp only [hb8, h80, extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))
  · obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_da
    have ⟨hF_da, hsym_da⟩ := hinv_da
    apply SepWP.seq_inImage (mid := fnBase + bv% (220)) hinv_da
    wp_call hdealloc (namePtr, nameCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_dc
    apply SepWP.seq_inImage (mid := fnBase + bv% (264)) hinv_dc
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _hinv_108
    refine hep x s0 _
      (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err _
      (stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_err)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        unfold epiloguePre F_err q_err Arm64.pointsTo128
        simp only [hsp, hb8, h80, extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))

/-- Branch B (`+0x058` on `gr = .ok []`): frees `bytes` and `name` if `cap ≠ 0`, stores `-2` at
`[out]`, leaves `dirAt` unchanged, and returns `(.ok (), x.dir)`. -/
theorem pkrm_branch_ok_nil {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (x : PkPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hgr : Except.ok ([] : List (BitVec 8)) = x.dir.get rd s0.fs.files (keyName x.id) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (88))
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img sm2)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0xa8#64) (.ok []) ∗
        postGetCommon A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hdealloc := pkrm_dealloc_ok_at hC
  have hff4 := pkrm_finish_f4 hC
  clear hC
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    88 20
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    224 20
  dsimp only [tripleRatchetProgAtExt] at hff4 hdealloc hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  unfold postGetCommon
  rw [getResultAt_ok_unpack A s0.sp [], subStack_split s0.sp hext_le hmin_hi]
  simp only [List.length_nil, sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun bytesCap => SepWP.exists_elim fun bytesPtr =>
    SepWP.pure_elim fun ⟨_hblen, hblt, _hbptr⟩ => ?_
  let F_nil : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ 0#64) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    dirAt A x.self x.dir
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x okTagVec bytesCap bytesPtr 0#64 q_sp0 ∗
        ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_nil) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f :
        (Except.ok (), x.dir) =
          pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace :=
      ⟨by rw [← hgr.1]; rfl, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (pkrm_post_entails rd pathOk A img stk x s0 sf (.ok (), x.dir) hres_f)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.ok (), x.dir) q_sp0)
    have hok := pkRemoveOutAt_ok_reassemble A x.out bytesCap bytesPtr 0#64 q_sp0
    have hslot := slot_a8_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
    have h24 := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
      nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
    have hgrp :
        epilogueOut s0 x okTagVec bytesCap bytesPtr 0#64 q_sp0 ∗
          ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F_nil =
        (((x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.out + 8#64) ↦₆₄ bytesCap) ∗ ((x.out + 0x10#64) ↦₆₄ bytesPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ 0#64) ∗ ((x.out + 0x20#64) ↦₁₂₈ q_sp0)) ∗
        (((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗ ((s0.sp - 0x90#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 0x88#64) 16) ∗
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (dirAt A x.self x.dir ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗
          A.pool)) := by
      unfold epilogueOut F_nil okTagVec; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hok (sepConj_mono hslot (sepConj_mono_left h24))) ?_
    exact Entails.of_eq (by ac_rfl)
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.fold (vecU8_free_zero A bytesPtr (bs := []) (Nat.zero_le _)) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (244)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_f4
    refine hff4 x s0 _ nameCap namePtr nameBs okTagVec 0#64 bytesPtr 0#64 q_sp0 _ F_nil
      hnlen hnlt hnptr
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hinv_f4
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    refine SepWP.fold (vecU8_free_ne A (ptr := bytesPtr) hbcap (Nat.zero_le _) hblt)
      (by sep_focus) ?_
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_da
    have ⟨hF_da, hsym_da⟩ := hinv_da
    apply SepWP.seq_inImage (mid := fnBase + bv% (244)) hinv_da
    wp_call hdealloc (bytesPtr, bytesCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_f4
    refine hff4 x s0 _ nameCap namePtr nameBs okTagVec bytesCap bytesPtr 0#64 q_sp0 _ F_nil
      hnlen hnlt hnptr
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hinv_f4
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_nil; simp only [hsp, sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

/-- Branch C (`+0x058` on `gr = .ok (b0 :: bsRest)`): frees `bytes` and `name`, calls `decimal`
again, materializes empty `Vec<u8>` `[0, 1, 0]` at `sp + 0x18`, calls `Dir::put::<String>` to set
`x.dir.put (keyName x.id) []`, and returns `(.ok (), x.dir.put (keyName x.id) [])`. -/
theorem pkrm_branch_ok_cons {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
          "libsignal_cli::stores::decimal"))
      (decimalSpec A img decStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName -
        bv% (ls_rel%
          "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
      (dirPutSpec A img putStk))
    (x : PkPollGhost) (R : SepProp) (s0 sm2 : State)
    (b0 : BitVec 8) (bsRest : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hdchg : x.dir.changed.length < 2 ^ 32)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hgr : Except.ok (b0 :: bsRest) = x.dir.get rd s0.fs.files (keyName x.id) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (88))
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img sm2)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr)
    (hx22 : sm2.readReg64 .x22 = x.self)
    (hx23 : sm2.readReg64 .x23 = BitVec.setWidth 64 x.id) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0xa8#64) (.ok (b0 :: bsRest)) ∗
        postGetCommon A s0 x decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).onPanic x s0 sf ∗ R)) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdec_le : decStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hput_le : putStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hpan_fn : ∀ (sf : State) (P_f : SepProp),
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).onPanic x s0 sf ∗ R) := by
    intro sf P_f halloc hmf
    dsimp only [pkRemovePollSpec, Spec.inImage]
    simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf
  have hdb6c := @pkrm_drop_both_6c img A ext hC
  have hep := @pkrm_epilogue_108 img ext
  clear hC
  unfold postGetCommon
  rw [getResultAt_ok_unpack A s0.sp (b0 :: bsRest), subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr =>
    SepWPp.pure_elim fun ⟨hblen, hblt, hbptr⟩ => ?_
  have hbcap : bytesCap ≠ 0#64 := by
    intro hc; subst hc
    simp at hblen
  have hlen_beq : (BitVec.ofNat 64 (b0 :: bsRest).length == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h1 := congrArg BitVec.toNat heq
    have h2 : bsRest.length + 1 < 2 ^ 64 := by
      have : (b0 :: bsRest).length = bsRest.length + 1 := rfl
      omega
    simp only [List.length_cons, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at h1
    exact Nat.succ_ne_zero _ h1
  let F_drop : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8 ∗
    dirAt A x.self x.dir
  apply sepWP_to_sepWPp (mid := (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (148)) hinv
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    88 20
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    148 44
  dsimp only [tripleRatchetProgAtExt] at hDec hPut hep hdb6c hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  apply SepWP.seq_inImage (mid := fnBase + bv% (108)) hinv
  wp_steps
  let _ := hlen_beq
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv_6c
  refine hdb6c s0 _ bytesCap bytesPtr (b0 :: bsRest) nameCap namePtr nameBs _ F_drop
    hbcap hblen hblt hbptr hnlen hnlt hnptr
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_align
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hinv_6c
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by unfold F_drop; sep_focus)
    fun sm3 hpcm3 hrunm3 hspm3 _hinvm3 htrm3
      hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3 => ?_
  apply SepWP.done hpcm3 (by wp_norm_lhs)
  intro hinvm3
  have hx19_m3 : sm3.readReg64 .x19 = x.fut := hx19_3.trans (by simp only [arm64_norm, *])
  have hx20_m3 : sm3.readReg64 .x20 = x.out := hx20_3.trans (by simp only [arm64_norm, *])
  have hx22_m3 : sm3.readReg64 .x22 = x.self := hx22_3.trans (by simp only [arm64_norm, *])
  have hx23_m3 : sm3.readReg64 .x23 = BitVec.setWidth 64 x.id :=
    hx23_3.trans (by simp only [arm64_norm, *])
  have hx24_m3 : sm3.readReg64 .x24 = bytesCap := hx24_3
  have hx25_m3 : sm3.readReg64 .x25 = bytesPtr := hx25_3
  have hx26_m3 : sm3.readReg64 .x26 = okTagVec := hx26_3.trans (by simp only [arm64_norm, *])
  have hx27_m3 : sm3.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length :=
    hx27_3.trans (by simp only [arm64_norm, *])
  have htr_m3 : sm3.trace = s0.trace :=
    htrm3.trans (by simp only [hgr.2, arm64_norm, *])
  have hsp_al3 : sm3.spAligned = true := spAligned_sub_c0 hsp_align hspm3
  clear htrm3 hx19_3 hx20_3 hx22_3 hx23_3 hx26_3 hx27_3 hdb6c
  have hrestk_dec :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - decStk) ∗
      stackAt (s0.sp - 0xc0#64) decStk := by
    rw [← subStack_split s0.sp hext_le hmin_hi, subStack_split s0.sp hdec_le hmin_hi]
  have h24_name := header3_entails_memRegion24
    (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
    nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
  let F_dec2 : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - decStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8 ∗
    dirAt A x.self x.dir
  have hprep_dec :
      (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗
        A.pool ∗ F_drop) ⊢
      (memRegion (s0.sp - 0x78#64) 24 ∗ stackAt (s0.sp - 0xc0#64) decStk ∗ A.pool) ∗ F_dec2 := by
    have hpull :
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          A.pool ∗ F_drop) =
        ((((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
          (memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
              (subMax decStk getStk putStk - extHookStack) ∗
            stackAt (s0.sp - 0xc0#64) extHookStack) ∗
          A.pool ∗
          (((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
            ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
            ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
            ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
            memRegion (s0.sp - 0x88#64) 16 ∗
            ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
            memRegion (s0.sp - 0xb0#64) 8 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
            memRegion x.out 48 ∗
            pkBoxAt x.fut x.self x.id 0#8 ∗
            dirAt A x.self x.dir)) := by
      unfold F_drop; ac_rfl
    rw [hpull, hrestk_dec]
    refine Entails.trans (sepConj_mono_left h24_name) ?_
    unfold F_dec2; exact Entails.of_eq (by ac_rfl)
  refine sepWPp_conseq hprep_dec ?_
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "libsignal_cli::stores::decimal"))
    hinvm3
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv_dec2
  refine sepWPp_name_state fun s4 hs4 => ?_
  have hs4_pc : s4.pc = fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "libsignal_cli::stores::decimal") := by
    rw [hs4]; simp only [arm64_norm, *]
  have hs4_lr : s4.readReg64 Reg.lr = fnBase + bv% (160) := by
    rw [hs4]; simp only [arm64_norm, *]
  have hs4_run : s4.status = .Running := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_sp : s4.sp = s0.sp - 0xc0#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_tr : s4.trace = s0.trace := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x0 : s4.readReg64 .x0 = s0.sp - 0x78#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x1 : s4.readReg32 .x1 = x.id := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x19 : s4.readReg64 .x19 = x.fut := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x20 : s4.readReg64 .x20 = x.out := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x22 : s4.readReg64 .x22 = x.self := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x24 : s4.readReg64 .x24 = bytesCap := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x25 : s4.readReg64 .x25 = bytesPtr := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x26 : s4.readReg64 .x26 = okTagVec := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x27 : s4.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := by
    rw [hs4]; simp only [arm64_norm, *]
  have hs4_x28 : s4.readReg64 .x28 = s0.readReg64 .x28 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_fp : s4.readReg64 .x29 = s0.sp - 0x60#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_vregs : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [hs4]; simp only [arm64_norm, *]
  rw [← hs4] at hinv_dec2
  clear hs4
  refine pkrm_call_decimal hDec
    { n := x.id, ret := s0.sp - 0x78#64 } F_dec2
    (s0 := s0)
    hs4_pc hs4_run (spAligned_sub_c0 hsp_align hs4_sp) hs4_lr hs4_tr hinv_dec2
    hs4_x0 hs4_x1 hpan_fn
    (Entails.of_eq (by rw [hs4_sp]))
    fun sm4 hpcm4 hrunm4 hspm4 hcsm4 hinvm4 htrm4 => ?_
  rw [hs4_sp]
  rcases hcsm4 with
    ⟨hx19_4, hx20_4, _, hx22_4, _, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩
  have hsp_m4 : sm4.sp = s0.sp - 0xc0#64 := hspm4.trans hs4_sp
  have hsp_al4 : sm4.spAligned = true := spAligned_sub_c0 hsp_align hsp_m4
  have hx19_m4 : sm4.readReg64 .x19 = x.fut := hx19_4.trans hs4_x19
  have hx20_m4 : sm4.readReg64 .x20 = x.out := hx20_4.trans hs4_x20
  have hx22_m4 : sm4.readReg64 .x22 = x.self := hx22_4.trans hs4_x22
  have hx24_m4 : sm4.readReg64 .x24 = bytesCap := hx24_4.trans hs4_x24
  have hx25_m4 : sm4.readReg64 .x25 = bytesPtr := hx25_4.trans hs4_x25
  have hx26_m4 : sm4.readReg64 .x26 = okTagVec := hx26_4.trans hs4_x26
  have hx27_m4 : sm4.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length :=
    hx27_4.trans hs4_x27
  have hx28_m4 : sm4.readReg64 .x28 = s0.readReg64 .x28 := hx28_4.trans hs4_x28
  have hfp_m4 : sm4.readReg64 .x29 = s0.sp - 0x60#64 := hfp_4.trans hs4_fp
  have hvregs_m4 : calleeSavedVRegs sm4 = calleeSavedVRegs s0 := hvregs_4.trans hs4_vregs
  have htr_m4 : sm4.trace = s0.trace := htrm4.trans hs4_tr
  have hrestk_put :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - decStk) ∗
      stackAt (s0.sp - 0xc0#64) decStk =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - putStk) ∗
      stackAt (s0.sp - 0xc0#64) putStk := by
    rw [← subStack_split s0.sp hdec_le hmin_hi, subStack_split s0.sp hput_le hmin_hi]
  unfold F_dec2
  refine sepWPp_conseq
    (P' := ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk) ∗
        stackAt (s0.sp - 0xc0#64) decStk) ∗
      ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
      ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
      ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
      vecU8 A (s0.sp - 0x78#64) (keyName x.id) ∗
      dirAt A x.self x.dir ∗
      A.pool ∗
      ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
      memRegion (s0.sp - 0x88#64) 16 ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      savedCalleeSlots s0 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      memRegion x.out 48 ∗
      pkBoxAt x.fut x.self x.id 0#8))
    (Entails.of_eq (by unfold keyName; ac_rfl)) ?_
  rw [hrestk_put]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    hinvm4
  wp_steps
  apply SepWP.done (by simp only [arm64_norm]; bv_omega) (by wp_norm_lhs)
  intro hinv_put
  refine sepWPp_name_state fun s5 hs5 => ?_
  have hs5_pc : s5.pc = fnBase - bv% (ls_rel%
      "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") := by
    rw [hs5]; simp only [arm64_norm, *]; bv_omega
  have hs5_lr : s5.readReg64 Reg.lr = fnBase + bv% (188) := by
    rw [hs5]; simp only [arm64_norm, *]
  have hs5_run : s5.status = .Running := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_sp : s5.sp = s0.sp - 0xc0#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_tr : s5.trace = s0.trace := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x0 : s5.readReg64 .x0 = x.self := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x1 : s5.readReg64 .x1 = s0.sp - 0x78#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x2 : s5.readReg64 .x2 = s0.sp - 0xa8#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x19 : s5.readReg64 .x19 = x.fut := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x20 : s5.readReg64 .x20 = x.out := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x24 : s5.readReg64 .x24 = bytesCap := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x25 : s5.readReg64 .x25 = bytesPtr := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x26 : s5.readReg64 .x26 = okTagVec := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x27 : s5.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := by
    rw [hs5]; simp only [arm64_norm, *]
  have hs5_x28 : s5.readReg64 .x28 = s0.readReg64 .x28 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_vregs : calleeSavedVRegs s5 = calleeSavedVRegs s0 := by
    rw [hs5]; simp only [arm64_norm, *]
  rw [← hs5] at hinv_put
  clear hs5
  let F_put : SepProp :=
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - putStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8
  refine pkrm_call_dirPut hPut
    { self := x.self, dir := x.dir,
      nameV := s0.sp - 0x78#64, name := keyName x.id,
      bytesV := s0.sp - 0xa8#64, bytes := [] } F_put
    (s0 := s0)
    hs5_pc hs5_run (spAligned_sub_c0 hsp_align hs5_sp) hs5_lr hs5_tr hinv_put
    hs5_x0 hs5_x1 hs5_x2 hdchg hpan_fn
    (by
      rw [hs5_sp]
      have hemp_v := vecU8_empty_of_zero_one_zero A
        (s0.sp - 0xa8#64) (s0.sp - 0xa0#64) (s0.sp - 0x98#64) (by bv_omega) (by bv_omega)
      refine Entails.trans (Q :=
        (((s0.sp - 0xa8#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa0#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0x98#64) ↦₆₄ 0#64)) ∗
        (dirAt A x.self x.dir ∗ vecU8 A (s0.sp - 0x78#64) (keyName x.id) ∗
          stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool ∗ F_put))
        (Entails.of_eq (by unfold F_put; ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hemp_v) ?_
      exact Entails.of_eq (by dsimp only; ac_rfl))
    fun sm5 hpcm5 hrunm5 hspm5 hcsm5 hinvm5 htrm5 => ?_
  rw [hs5_sp]
  rcases hcsm5 with
    ⟨hx19_5, hx20_5, _, _, _, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs_5⟩
  have hsp_m5 : sm5.sp = s0.sp - 0xc0#64 := hspm5.trans hs5_sp
  have hx19_m5 : sm5.readReg64 .x19 = x.fut := hx19_5.trans hs5_x19
  have hx20_m5 : sm5.readReg64 .x20 = x.out := hx20_5.trans hs5_x20
  have hx24_m5 : sm5.readReg64 .x24 = bytesCap := hx24_5.trans hs5_x24
  have hx25_m5 : sm5.readReg64 .x25 = bytesPtr := hx25_5.trans hs5_x25
  have hx26_m5 : sm5.readReg64 .x26 = okTagVec := hx26_5.trans hs5_x26
  have hx27_m5 : sm5.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length :=
    hx27_5.trans hs5_x27
  have hx28_m5 : sm5.readReg64 .x28 = s0.readReg64 .x28 := hx28_5.trans hs5_x28
  have hvregs_m5 : calleeSavedVRegs sm5 = calleeSavedVRegs s0 := hvregs_5.trans hs5_vregs
  have htr_m5 : sm5.trace = s0.trace := htrm5.trans hs5_tr
  apply sepWPp_of_sepWP_final
  have hrestk_ext :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - putStk) ∗
      stackAt (s0.sp - 0xc0#64) putStk =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack := by
    rw [← subStack_split s0.sp hput_le hmin_hi, subStack_split s0.sp hext_le hmin_hi]
  let F_end : SepProp :=
    dirAt A x.self (x.dir.put (keyName x.id) []) ∗
    memRegion (s0.sp - 0x78#64) 24 ∗
    memRegion (s0.sp - 0xa8#64) 24 ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    stackAt (s0.sp - 0xc0#64) extHookStack ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    A.pool
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x okTagVec bytesCap bytesPtr
        (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 ∗ F_end) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f :
        (Except.ok (), x.dir.put (keyName x.id) []) =
          pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace :=
      ⟨by rw [← hgr.1]; rfl, htr_eq⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (pkrm_post_entails rd pathOk A img stk x s0 sf (.ok (), x.dir.put (keyName x.id) []) hres_f)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.ok (), x.dir.put (keyName x.id) []) q_sp0)
    have hok := pkRemoveOutAt_ok_reassemble A x.out bytesCap bytesPtr
      (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0
    have hslot := slot_a8_put_collapse s0.sp (BitVec.ofNat 64 (b0 :: bsRest).length)
    have hgrp :
        epilogueOut s0 x okTagVec bytesCap bytesPtr
          (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 ∗ F_end =
        (((x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.out + 8#64) ↦₆₄ bytesCap) ∗ ((x.out + 0x10#64) ↦₆₄ bytesPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
          ((x.out + 0x20#64) ↦₁₂₈ q_sp0)) ∗
        (memRegion (s0.sp - 0xa8#64) 24 ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
          memRegion (s0.sp - 0x88#64) 16) ∗
        (dirAt A x.self (x.dir.put (keyName x.id) []) ∗
          memRegion (s0.sp - 0x78#64) 24 ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗
          A.pool)) := by
      unfold epilogueOut F_end okTagVec; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hok (sepConj_mono_left hslot)) ?_
    exact Entails.of_eq (by ac_rfl)
  apply SepWP.seq_inImage (mid := fnBase + bv% (264)) hinvm5
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro _hinv_108
  refine hep x s0 _ okTagVec bytesCap bytesPtr (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 _
    F_end
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_align
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by
      have hpull :
          ((dirAt A x.self (x.dir.put (keyName x.id) []) ∗
              memRegion (s0.sp - 0x78#64) 24 ∗ memRegion (s0.sp - 0xa8#64) 24 ∗
              stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool) ∗ F_put) =
          ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
              (subMax decStk getStk putStk - putStk) ∗
            stackAt (s0.sp - 0xc0#64) putStk) ∗
          epiloguePre s0 x q_sp0 ∗
          (dirAt A x.self (x.dir.put (keyName x.id) []) ∗
            memRegion (s0.sp - 0x78#64) 24 ∗
            memRegion (s0.sp - 0xa8#64) 24 ∗
            ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
            memRegion (s0.sp - 0x88#64) 16 ∗
            memRegion (s0.sp - 0xb0#64) 8 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
            A.pool)) := by
        unfold F_put epiloguePre; ac_rfl
      rw [hpull, hrestk_ext]
      unfold F_end; exact Entails.of_eq (by ac_rfl))
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

end CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
