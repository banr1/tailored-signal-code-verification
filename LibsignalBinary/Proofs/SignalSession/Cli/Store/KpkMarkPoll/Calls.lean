/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

/-! ## Relative Callee Address Equations & Hook Lifts -/

theorem decimal_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName +
      bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "libsignal_cli::stores::decimal") =
      (tripleRatchetProgAtExt b ext).fnAddr decimalName := by
  have h1 := kpkMarkPoll_fnOff
  have h2 := decimal_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPollName, decimalName, h1, h2]
  bv_omega

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName +
      bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "<libsignal_cli::stores::Dir>::get") =
      (tripleRatchetProgAtExt b ext).fnAddr dirGetName := by
  have h1 := kpkMarkPoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPollName, dirGetName, h1, h2]
  bv_omega

theorem dirPut_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName -
      bv% (ls_rel%
        "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr dirPutName := by
  have h1 := kpkMarkPoll_fnOff
  have h2 := dirPut_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPollName, dirPutName, h1, h2]
  bv_omega

theorem publicKeySerialize_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName -
      bv% (ls_rel%
        "<libsignal_core::curve::PublicKey>::serialize"
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName := by
  have h1 := kpkMarkPoll_fnOff
  have h2 : libsignalSessionCode.fnOff publicKeySerializeName =
      num% (ls_off% "<libsignal_core::curve::PublicKey>::serialize") :=
    ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPollName,
    publicKeySerializeName, h1, h2]
  bv_omega

theorem cliDoReserve_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName -
      bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr cliDoReserveName := by
  have h1 := kpkMarkPoll_fnOff
  have h2 : libsignalSessionCode.fnOff cliDoReserveName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
    ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPollName,
    cliDoReserveName, h1, h2]
  bv_omega

theorem cliConcat_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName +
      bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") =
      (tripleRatchetProgAtExt b ext).fnAddr cliConcatName := by
  have h1 := kpkMarkPoll_fnOff
  have h2 : libsignalSessionCode.fnOff cliConcatName =
      num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") :=
    ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPollName,
    cliConcatName, h1, h2]
  bv_omega

theorem kpk_dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hC (name := kpkMarkPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_dealloc"))
    (by rw [kpkMarkPoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem kpk_shim_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hC (name := kpkMarkPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))

theorem kpk_alloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hC (name := kpkMarkPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_alloc"))

theorem kpk_memcpy_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "memcpy"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hC (name := kpkMarkPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "memcpy"))

theorem kpk_panic_handle_error {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := b) (ext := ext) (name := kpkMarkPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "alloc::raw_vec::handle_error"))

theorem kpk_bcmp_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "bcmp"))
      cliBcmpSpec :=
  hook_ok_at (hname := cliBcmpName) kpkMarkPoll_fnOff
    (by decide)
    (by decide)
    (fun _ => (ls_hook% "bcmp") _)
    (by simp [Rust.isPanicSymbol, cliBcmpName])
    hBcmp

/-! ## State Preservation & `SepWPp` Call Combinators -/

theorem files_eq_of_fsInv_trace_eq {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (hinv : FsInv F0 T0 s) (ht : s.trace = T0) : s.fs.files = F0 :=
  files_eq_at_callback hinv (ht.trans (List.append_nil T0).symm) .nil

theorem setWidth_32_setWidth_64 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by
  ext i _hi; simp

theorem spAligned_sub_f0 {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 0xf0#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem layoutOk_u8_of_ne_zero {cap : BitVec 64} (hc : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h => hc (BitVec.eq_of_toNat_eq h))
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem sepWPp_conseq {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (h : P ⊢ P')
    (hw : SepWPp prog ret s P' Q Qp) : SepWPp prog ret s P Q Qp :=
  fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_with_stk_bound {prog : Program} {ret : BitVec 64} {s : State}
    {stk : Nat} {a v : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P ⊢ stackAt s.sp stk ∗ (a ↦₆₄ v) ∗ Rest)
    (hw : stk ≤ 2 ^ 64 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := fun R hm hL => by
  have hm' : s.mem ⊨ memRegion (s.sp - BitVec.ofNat 64 stk) stk ∗ ((a ↦₆₄ v) ∗ (Rest ∗ R)) := by
    have h1 := Satisfies.mono (sepConj_mono_left hfoc) hm
    simpa only [stackAt, sepConj_assoc] using h1
  exact hw (memRegion_bound_of_pointsTo64 hm') R hm hL

theorem sepWPp_of_sepWP_fs {prog : Program} {img : Obj.Image}
    {mid ret : BitVec 64} {s : State} {P : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent}
    {Q Qp : State → SepProp → Prop}
    (hFs : TraceFsSound prog) (hinv : ImgCallInv img s) (hfs : FsInv F0 T0 s)
    (h : SepWP prog mid s P
      (fun sm Pm => ImgCallInv img sm → FsInv F0 T0 sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨_, _, Pm, hsm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_steps hsteps) (hfs.of_steps hFs hsteps) R hsm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem kpk_call_panicking_raw {α : Type} {prog : Program} {img : Obj.Image}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_conseq hpre ?_
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2
    hpc hrun hsp_align hlr
    (fun R' hm => by rwa [sepConj_assoc] at hm)
    (fun sm code R' _ hpost => hexit_imp code sm R' hpost)
    (fun sm _ ⟨R', hpost⟩ => ?_)
    (fun sm hpcm hrunm hspm hcsm hfz hsym => hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sm R' _ hpost => (hoom_imp sm (F ∗ R') hpost).elim)
  have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
    simpa [allocFailedIn, htr] using hpan_imp sm R' hpost
  exact hpan sm _ halloc0

theorem kpk_call_decimal_fs {prog : Program} {img : Obj.Image} {A : RustAlloc} {decStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (decimalSpec A img decStk) s0_files s0_trace))
    (xg : DecimalGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      FsInv s0_files s0_trace sm → sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (decimalText xg.n.toNat) ∗ stackAt s.sp decStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hfs
      (Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _)))
  · intro sm R' hpost
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfsm htrm)

theorem kpk_call_decimal {prog : Program} {img : Obj.Image} {A : RustAlloc} {decStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (decimalSpec A img decStk))
    (xg : DecimalGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (decimalText xg.n.toNat) ∗ stackAt s.sp decStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [decimalSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [decimalSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [decimalSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [decimalSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem kpk_call_dirGet_fs {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (dirGetSpec rd pathOk A img getStk) s0_files s0_trace))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      FsInv s0_files s0_trace sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFsInv, dirGetSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hfs (Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _)))
  · intro sm R' hpost
    simp only [withFsInv, dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFsInv, dirGetSpec, Spec.inImage]
    kpk_sep_norm
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hinvm hfsm hgr)

theorem kpk_call_dirGet {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpec rd pathOk A img getStk))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirGetSpec, Spec.inImage]
    kpk_sep_norm
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hinvm hgr)

theorem kpk_call_dirPut {prog : Program} {img : Obj.Image} {A : RustAlloc} {putStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutSpec A img putStk))
    (xg : DirPutGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameV)
    (hx2 : s.readReg64 .x2 = xg.bytesV) (hlen : xg.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ vecU8 A xg.nameV xg.name ∗
      vecU8 A xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((dirAt A xg.self (xg.dir.put xg.name xg.bytes) ∗
          memRegion xg.nameV 24 ∗ memRegion xg.bytesV 24 ∗
          stackAt s.sp putStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirPutSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirPutSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirPutSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirPutSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirPutSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem kpk_call_serialize {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee ((publicKeySerializeSpecX A).inImage img))
    (xg : PublicKeySerializeCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.self)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.self ↦ₛ xg.pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.readReg64 .x0 ≠ 0#64 → sm.readReg64 .x1 = 33#64 → sm.trace = s.trace →
      SepWPp prog ret sm
        (((xg.self ↦ₛ xg.pk.bytes.toList) ∗
          A.live (sm.readReg64 .x0) 33 1 ∗ ((sm.readReg64 .x0) ↦ₛ xg.pk.serialize) ∗
          A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Spec.inImage, publicKeySerializeSpecX, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right hx0 (Entails.refl _))
  · intro sm R' hpost
    simp only [Spec.inImage, publicKeySerializeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [Spec.inImage, publicKeySerializeSpecX] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [Spec.inImage, publicKeySerializeSpecX] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [Spec.inImage, publicKeySerializeSpecX, boxU8Buf, PublicKey.serialize,
      List.cons_ne_nil, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1, htrm⟩ => ?_
    have h33 : (djbType :: xg.pk.bytes.toList).length = 33 := publicKey_serialize_length xg.pk
    rw [h33]
    rw [show (xg.self ↦ₛ xg.pk.bytes.toList) ∗ ⌜sm.readReg64 Reg.x0 ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
          A.live (sm.readReg64 Reg.x0) 33 1 ∗ ((sm.readReg64 Reg.x0) ↦ₛ (djbType :: xg.pk.bytes.toList)) ∗
          A.pool ∗ stackAt s.sp publicKeySerializeStackX ∗ F =
        ⌜sm.readReg64 Reg.x0 ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
          (((xg.self ↦ₛ xg.pk.bytes.toList) ∗
            A.live (sm.readReg64 Reg.x0) 33 1 ∗ ((sm.readReg64 Reg.x0) ↦ₛ xg.pk.serialize) ∗
            A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F) by
          unfold PublicKey.serialize; ac_rfl]
    refine SepWPp.pure_elim fun ⟨hp0, _⟩ => ?_
    exact hnext sm hpcm hrunm hspm hcsm hinvm hp0 hx1 htrm

theorem kpk_call_concat2 {prog : Program} {img : Obj.Image} {A : RustAlloc} {stk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee ((kpkConcat2PosSpec A stk).inImage img))
    (xg : Concat2PosCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.outVec) (hx1 : s.readReg64 .x1 = xg.slicesA)
    (hx2 : s.readReg64 .x2 = 2#64)
    (hpos0 : 0 < xg.bs0.length) (hpos1 : 0 < xg.bs1.length)
    (hmax : xg.bs0.length + xg.bs1.length < 2 ^ 63)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.outVec 24 ∗
      (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
      ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
      (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗ A.pool ∗ stackAt s.sp stk) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.outVec (xg.bs0 ++ xg.bs1) ∗
          (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
          ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
          (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗ A.pool ∗ stackAt s.sp stk) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Spec.inImage, kpkConcat2PosSpec, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hpos0, hpos1, hmax⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [Spec.inImage, kpkConcat2PosSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [Spec.inImage, kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [Spec.inImage, kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [Spec.inImage, kpkConcat2PosSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem kpk_call_reserve_fs {prog : Program} {img : Obj.Image} {A : RustAlloc} {resStack : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) s0_files s0_trace))
    (xg : DoReserveCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (vecU8At A xg.v xg.cap xg.ptr xg.bs ∗ A.pool ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      FsInv s0_files s0_trace sm → sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hfs (Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩ (Entails.refl _)))
  · intro sm R' hpost
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf, doReserveSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf, doReserveSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf, doReserveSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf, Spec.inImage]
    kpk_sep_norm
    refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun htrm => ?_
    have hp'_pull :
        vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack ∗ F =
        (vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F := by
      ac_rfl
    rw [hp'_pull]
    intro R' hm hL
    have hp'_ne : p' ≠ 0#64 := by
      have hm1 : sm.mem ⊨ vecU8At A xg.v
          (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          ((A.pool ∗ stackAt s.sp resStack) ∗ F ∗ R') := by
        simpa only [sepConj_assoc] using hm
      unfold vecU8At at hm1
      rw [sepConj_assoc] at hm1
      have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
      rw [satisfies_pure_sepConj] at hm2
      exact hm2.1.2.2
    exact hnext sm p' hpcm hrunm hspm hcsm hinvm hfsm htrm hp'_ne R' hm hL

theorem kpk_call_reserve {prog : Program} {img : Obj.Image} {A : RustAlloc} {resStack : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (xg : DoReserveCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (vecU8At A xg.v xg.cap xg.ptr xg.bs ∗ A.pool ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [SpqrV1.Varint.doReserveSpecOf, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [SpqrV1.Varint.doReserveSpecOf, Spec.inImage]
    kpk_sep_norm
    refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun htrm => ?_
    have hp'_pull :
        vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack ∗ F =
        (vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F := by
      ac_rfl
    rw [hp'_pull]
    intro R' hm hL
    have hp'_ne : p' ≠ 0#64 := by
      have hm1 : sm.mem ⊨ vecU8At A xg.v
          (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          ((A.pool ∗ stackAt s.sp resStack) ∗ F ∗ R') := by
        simpa only [sepConj_assoc] using hm
      unfold vecU8At at hm1
      rw [sepConj_assoc] at hm1
      have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
      rw [satisfies_pure_sepConj] at hm2
      exact hm2.1.2.2
    exact hnext sm p' hpcm hrunm hspm hcsm hinvm htrm hp'_ne R' hm hL

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
