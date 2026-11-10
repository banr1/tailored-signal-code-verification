/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof -- shake: keep

/-!
# `Ok` and `Err` Tails of Empty-State `spqr::recv`

Proves symbolic execution of the common `Err(MsgDecode)` epilogue and the `Ok` path through
`spqr::decode_state` and `memcpy`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The untouched stack frame pieces of `spqr::recv` after the prologue (`s0.sp - 4992` frame). -/
def recvStackRest (sp f0 f8 f16 f24 b50 b58 b60 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 :
    BitVec 64) : SepProp :=
  memRegion (sp - 131072#64) 109696 ∗
  stackAt (sp - 4992#64) extHookStack ∗
  ((sp - 4992#64) ↦₆₄ f0) ∗
  ((sp - 4984#64) ↦₆₄ f8) ∗
  ((sp - 4976#64) ↦₆₄ f16) ∗
  ((sp - 4968#64) ↦₆₄ f24) ∗
  memRegion (sp - 4960#64) 320 ∗
  memRegion (sp - 4640#64) 448 ∗
  ((sp - 4192#64) ↦₆₄ 0#64) ∗
  memRegion (sp - 4184#64) 1128 ∗
  memRegion (sp - 3056#64) 352 ∗
  memRegion (sp - 2704#64) 608 ∗
  ((sp - 2096#64) ↦₆₄ b50) ∗
  ((sp - 2088#64) ↦₆₄ b58) ∗
  ((sp - 2080#64) ↦₆₄ b60) ∗
  memRegion (sp - 2072#64) 1976 ∗
  ((sp - 96#64) ↦₆₄ s29) ∗
  ((sp - 88#64) ↦₆₄ s30) ∗
  ((sp - 80#64) ↦₆₄ s28) ∗
  ((sp - 72#64) ↦₆₄ s27) ∗
  ((sp - 64#64) ↦₆₄ s26) ∗
  ((sp - 56#64) ↦₆₄ s25) ∗
  ((sp - 48#64) ↦₆₄ s24) ∗
  ((sp - 40#64) ↦₆₄ s23) ∗
  ((sp - 32#64) ↦₆₄ s22) ∗
  ((sp - 24#64) ↦₆₄ s21) ∗
  ((sp - 16#64) ↦₆₄ s20) ∗
  ((sp - 8#64) ↦₆₄ s19)

theorem recvStackRest_entails (sp f0 f8 f16 f24 b50 b58 b60 p
    s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64) :
    (memRegion (sp - 131072#64) 109696 ∗
      stackAt (sp - 4992#64) extHookStack ∗
      ((sp - 4992#64) ↦₆₄ f0) ∗
      ((sp - 4984#64) ↦₆₄ f8) ∗
      ((sp - 4976#64) ↦₆₄ f16) ∗
      ((sp - 4968#64) ↦₆₄ f24) ∗
      memRegion (sp - 4960#64) 320 ∗
      memRegion (sp - 4640#64) 448 ∗
      ((sp - 4192#64) ↦₆₄ p) ∗
      memRegion (sp - 4184#64) 1128 ∗
      memRegion (sp - 3056#64) 352 ∗
      memRegion (sp - 2704#64) 608 ∗
      ((sp - 2096#64) ↦₆₄ b50) ∗
      ((sp - 2088#64) ↦₆₄ b58) ∗
      ((sp - 2080#64) ↦₆₄ b60) ∗
      memRegion (sp - 2072#64) 1976 ∗
      ((sp - 96#64) ↦₆₄ s29) ∗
      ((sp - 88#64) ↦₆₄ s30) ∗
      ((sp - 80#64) ↦₆₄ s28) ∗
      ((sp - 72#64) ↦₆₄ s27) ∗
      ((sp - 64#64) ↦₆₄ s26) ∗
      ((sp - 56#64) ↦₆₄ s25) ∗
      ((sp - 48#64) ↦₆₄ s24) ∗
      ((sp - 40#64) ↦₆₄ s23) ∗
      ((sp - 32#64) ↦₆₄ s22) ∗
      ((sp - 24#64) ↦₆₄ s21) ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19)) ⊢
    stackAt sp spqrRecvStack := by
  rw [stackAt_spqrRecv_split sp]
  have ex : ∀ (a v : BitVec 64), (a ↦₆₄ v) ⊢ (∃∗ x : BitVec 64, a ↦₆₄ x) :=
    fun _ v => Entails.sepExists_intro v
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) ?_)))
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (ex _ _) ?_))
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_))
  refine sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (Entails.refl _) ?_)))
  refine sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) ?_)))
  refine sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) ?_)))
  exact sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (sepConj_mono (ex _ _) (ex _ _)))

set_option maxHeartbeats 800000 in
/-- Common `Err(MsgDecode)` tail from `+0x114` (`+276`, `0x54740`) to `ret` (`+0x430`, `0x54a5c`). -/
theorem step_recv_err_tail (img : Obj.Image) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (F : SepProp)
    (st msg : VecArg) (ret : BitVec 64)
    (r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrRecvEmptyCodeSpec0 A S img F).post (st, msg, ret) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : S.recv st.bytes msg.bytes = .error false)
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hP : P =
      st.at A ∗ msg.at A ∗
      ((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ memRegion (ret + 32#64) 16) ∗
      F ∗ A.pool ∗
      recvStackRest s0.sp f0 f8 f16 f24 b50 b58 b60
        (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
    (ls_lemma% fnOff "spqr::recv")
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 276 16
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 1040 36
  clear hfn
  rcases htr with ⟨htr, hvregs⟩
  subst hpost hP
  unfold recvStackRest
  simp only [spqrRecvEmptyCodeSpec0, spqrRecvCodeSpec0, Spec.inImage, herr]
  dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base
    hooks).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.fold (recv_err_result_fold A ret r2 r3) (by sep_focus) ?_
  refine SepWP.fold (recvStackRest_entails s0.sp f0 f8 f16 f24 b50 b58 b60 0#64
    (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 1600000 in
/-- Common `Ok` tail from `+0x138` (`+312`, `0x54764`) to `ret` (`+0x430`, `0x54a5c`). -/
theorem step_recv_ok_tail (img : Obj.Image) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (F : SepProp)
    (hmc : subroutine_ok (libsignalSessionCode.rebase base hooks)
      ((libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img))
    (st msg : VecArg) (ret : BitVec 64) (version : BitVec 8)
    (r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrRecvEmptyCodeSpec0 A S img F).post (st, msg, ret) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hst : st.bytes = [])
    (hok : S.recv st.bytes msg.bytes = .ok ([], none))
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName + 312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hP : P =
      st.at A ∗ msg.at A ∗
      ((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ memRegion (ret + 32#64) 16) ∗
      F ∗ A.pool ∗
      recvStackRest s0.sp f0 f8 f16 f24 b50 b58 b60
        (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
    (hI : RecvImgInv img s) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
    (ls_lemma% fnOff "spqr::recv")
  have hdec := decode_recv_ok_at_F base hooks A
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 312 44
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 384 64
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 744 8
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 780 12
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 884 8
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 912 24
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 952 12
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 1020 8
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 1040 36
  clear hfn
  rcases htr with ⟨htr, hvregs⟩
  subst hpost hP
  unfold recvStackRest
  simp only [spqrRecvEmptyCodeSpec0, spqrRecvCodeSpec0, Spec.inImage, hok]
  dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc hdec hmc ⊢
  generalize_entry (libsignalSessionCode.rebase base
    hooks).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  apply sepWP_seq_recvImg (mid := entry + bv% (ls_off% "memcpy" - ls_off% "spqr::recv")) hI
  wp_steps
  wp_apply
  wp_simp_pre only [hsp, decodeEmpty_recv_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call hmc (s0.sp, pqChainNone, pqInnerNone)
  -- `memcpyRecvPcsSpecS` returns `stackAt <call-site sp> extHookStack`, which `wp_call` normalizes
  -- to the post-`decode_state` `sf.sp`; restate it at the frame address `s0.sp - 4992`.
  have hsf_sp : sf.sp = s0.sp - 4992#64 := by simp only [wp_norm, arm64_norm, *]
  wp_steps
  wp_if hver
  · wp_steps
    refine SepWP.fold (dst_recv_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
    refine SepWP.fold (decode_recv_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone) (by sep_focus) ?_
    refine SepWP.fold (recv_ok_result_fold A ret) (by sep_focus) ?_
    conv => arg 4; simp only [hsf_sp]
    refine SepWP.fold (recvStackRest_entails s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 d1 d2 d3 0#64
      (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
    wp_done
  · wp_steps
    refine SepWP.fold (dst_recv_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
    refine SepWP.fold (decode_recv_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone) (by sep_focus) ?_
    refine SepWP.fold (recv_ok_result_fold A ret) (by sep_focus) ?_
    conv => arg 4; simp only [hsf_sp]
    refine SepWP.fold (recvStackRest_entails s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 d1 d2 d3 0#64
      (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
    wp_done

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
