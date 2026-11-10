/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainResolve
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Chain Resolution & `send_key` Composition (`0x314d8..0x317fc`)

Composes the post-`States::send` chain resolution, optional `add_epoch`, `send_key`, `Chain::into_pb`,
and error/panic epilogue steps (`0x314d8 -> 0x317fc / 0x31a3c / panic`) in `spqr::send::<HookRng>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.States CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.States.Leaves

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Callee Relative Addresses -/

@[simp, arm64_norm] theorem chainFromPb_fnOff : libsignalSessionCode.fnOff chainFromPbName = 0x5ac7c := (ls_lemma% fnOff "<spqr::chain::Chain>::from_pb")
@[simp, arm64_norm] theorem chainFromVN_fnOff : libsignalSessionCode.fnOff chainFromVersionNegotiationName = 0x4f1ec := (ls_lemma% fnOff "spqr::chain_from_version_negotiation")
@[simp, arm64_norm] theorem chainAddEpoch_fnOff : libsignalSessionCode.fnOff chainAddEpochName = 0x5bc0c := (ls_lemma% fnOff "<spqr::chain::Chain>::add_epoch")
@[simp, arm64_norm] theorem chainSendKey_fnOff : libsignalSessionCode.fnOff chainSendKeyName = 0x5b9b8 := (ls_lemma% fnOff "<spqr::chain::Chain>::send_key")
@[simp, arm64_norm] theorem chainIntoPb_fnOff : libsignalSessionCode.fnOff chainIntoPbName = 0x5b11c := (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb")

theorem spqrSend_chainFromPb_addr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 172860#64 = (tripleRatchetProgAtExt b ext).fnAddr chainFromPbName := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, spqrSend_fnOff, chainFromPb_fnOff]; bv_omega
theorem spqrSend_chainFromVN_addr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 125100#64 = (tripleRatchetProgAtExt b ext).fnAddr chainFromVersionNegotiationName := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, spqrSend_fnOff, chainFromVN_fnOff]; bv_omega
theorem spqrSend_chainAddEpoch_addr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 176844#64 = (tripleRatchetProgAtExt b ext).fnAddr chainAddEpochName := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, spqrSend_fnOff, chainAddEpoch_fnOff]; bv_omega
theorem spqrSend_chainSendKey_addr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 176248#64 = (tripleRatchetProgAtExt b ext).fnAddr chainSendKeyName := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, spqrSend_fnOff, chainSendKey_fnOff]; bv_omega
theorem spqrSend_chainIntoPb_addr (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 174044#64 = (tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, spqrSend_fnOff, chainIntoPb_fnOff]; bv_omega

private theorem stackAt_callee_split (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide) :
    stackAt sp spqrSendCalleeStack = memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hle' : n ≤ 123008 := hle
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd
  rwa [Nat.add_sub_of_le hle] at h

private theorem of_sepWP_inImage_b1 {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (img : Obj.Image) (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext ⟨hsteps.frozenLoaded hinv.1, hsteps.symtab_eq.trans hinv.2⟩ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

private theorem panic_frame_anyHeap {m : Memory} {φ₁ φ₂ : Prop} {F Fr : SepProp}
    (himp : φ₁ → φ₂) (hm : m ⊨ ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr) : m ⊨ (⌜φ₂⌝ ∗ anyHeap) ∗ Fr := by
  have h1 : ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr ⊢ ⌜φ₁⌝ ∗ ((anyHeap ∗ F) ∗ Fr) := Entails.of_eq (by ac_rfl)
  have hm' := Satisfies.mono h1 hm; rw [satisfies_pure_sepConj] at hm'
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right (himp hm'.1) (entails_anyHeap _))) hm'.2

private theorem panic_not_exited {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False := ((satisfies_pure_sepConj _ _ _).mp h).1

private theorem corePanic_extern_at (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt? ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::panicking::panic")) = some Rust.panicked :=
  panic_at_sym_ext b ext spqrSendName "core::panicking::panic" num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::panicking::panic")
    (by rw [spqrSend_fnOff, (ls_stub% "core::panicking::panic")]) (hs := by rw [(ls_stub% "core::panicking::panic")]; decide)
    (hstub := fun H => by rw [(ls_stub% "core::panicking::panic")]; exact (ls_hook% "core::panicking::panic") H) (hp := by decide +kernel)

private theorem panicSubOverflow_extern_at (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt? ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::panicking::panic_const::panic_const_sub_overflow")) = some Rust.panicked :=
  panic_at_sym_ext b ext spqrSendName "core::panicking::panic_const::panic_const_sub_overflow" num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::panicking::panic_const::panic_const_sub_overflow")
    (by rw [spqrSend_fnOff, (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")])
    (hs := by rw [(ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")]; decide)
    (hstub := fun H => by rw [(ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")]; exact (ls_hook% "core::panicking::panic_const::panic_const_sub_overflow") H)
    (hp := by decide +kernel)

theorem call_inImage_calleeStack_anyPanic {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post φ_pan φ_out : State → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜φ_pan sf⌝ ∗ anyHeap))
    (hpan_imp : ∀ sm : State, φ_pan sm → φ_out sm)
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → ImgCallInv img sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp_frozen (x := x) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun hsp_al hlr
    (fun R' hm => ?_) ?_ ?_ ?_ ?_
  · change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ spec.pre x s) ∗ (F_ext ∗ R')
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
    rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
    rw [hP, stackAt_callee_split sp n hle] at hm
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hm
  · intro sm code R' _ hpost
    change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost; rw [hexit_eq code sm] at hpost
    exact panic_not_exited hpost
  · intro sm _ _ hmFr
    change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr; rw [hpan_eq sm] at hmFr
    exact panic_frame_anyHeap (hpan_imp sm) hmFr
  · intro sm hpcm hrunm hspm hcsm hfz hsym
    have heq : (spec.inImage img).post x s sm ∗ F_ext =
        ⌜φ_post sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F) := by
      change spec.post x s sm ∗ F_ext = _
      rw [hspec_post sm, hsp, stackAt_callee_split sp n hle]
      dsimp only [F_ext]; ac_rfl
    rw [heq]; refine SepWPp.pure_left fun hφ_post => ?_
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    exact hnext sm hpcm hrunm hspm hφ_post ⟨hfz, hsym⟩ hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  · intro sm R' _ hpost
    change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost; rw [hoom_eq sm] at hpost
    exact (panic_not_exited hpost).elim

theorem pure_elim_focus_b1 {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P' Q Qp)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp := by
  rw [hf]
  exact SepWPp.pure_left h

theorem sepWPp_at_panic_stub {prog : Program} {ret : BitVec 64}
    {s : State} {P Fr : SepProp} {Q : State → SepProp → Prop} {φ_out : State → Prop}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked) (hφ : φ_out (Rust.panicked s)) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  intro R' hm hL
  have hstep : Step prog s (Rust.panicked s) := Step.extern hrun hext (Memory.KeepsFrozen.refl s.mem) rfl
  have hmem : (Rust.panicked s).mem ⊨ (⌜φ_out (Rust.panicked s)⌝ ∗ anyHeap) ∗ R' :=
    Satisfies.mono (sepConj_mono_left (Entails.pure_right hφ (entails_anyHeap P))) hm
  exact ⟨Rust.panicked s, Steps.step hstep (Steps.refl _), Or.inr (Or.inl ⟨rfl, ⌜φ_out (Rust.panicked s)⌝ ∗ anyHeap, hmem, id⟩)⟩

theorem step_epilogue_from_31a54 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = x23) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion s.sp 0x60 ∗ chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s0.sp ∧
        Arm64.CalleeSavedPreserved s0 sf ∧ (Q ⊢ stackAt s0.sp spqrSendStack ∗ Frame)) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp]; exact spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hstep1 := step_epilogue_31a54 s x23 (memRegion s.sp 0x60 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
      stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame) hpc hrun hx23 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hvregs1, hP1⟩
  have hjoin : memRegion (s.sp + 0x60#64) 80 ∗ (memRegion s.sp 0x60 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
      stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame) ⊢
      stackAt s1.sp spqrSendCalleeStack ∗ memRegion s1.sp 0x1f20 ∗ spqrSendSavedRegs s1.sp s0 ∗ Frame := by
    rw [hsp1, ProofLib.memRegion_split' (b := s.sp) (n := 0x60) (k := 0x1f20 - 0x60) (b' := s.sp + 0x60#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := s.sp + 0x60#64) (n := 80) (k := 0x1f20 - 0xb0) (b' := s.sp + 0xb0#64) rfl (by bv_omega) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre (Entails.trans hP1 hjoin) (SepWP.mono (step_epilogue_31a74 s0 s1 Frame hpc1 hrun1 (hsp1.trans hsp) hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Q _ _ ⟨hrunf, htrf, hspf, hcsf, hQ⟩; exact ⟨hrunf, htrf.trans htr1, hspf, hcsf, hQ⟩

theorem step_epilogue_from_31a3c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (vn : Option VersionNegotiationPB) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = x23) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion s.sp 0x30 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s.sp s0 ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s0.sp ∧
        Arm64.CalleeSavedPreserved s0 sf ∧ (Q ⊢ stackAt s0.sp spqrSendStack ∗ A.pool ∗ Frame)) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp]; exact spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hstep1 := step_epilogue_31a3c hdealloc s vn x23
    (memRegion s.sp 0x30 ∗ chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗ spqrSendSavedRegs s.sp s0 ∗ Frame) hpc hrun hx23 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx23_1, hvregs1, hP1⟩
  have hjoin : memRegion (s.sp + 0x30#64) 48 ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
      (memRegion s.sp 0x30 ∗ chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0xb0#64) (0x1f20 - 0xb0) ∗ spqrSendSavedRegs s.sp s0 ∗ Frame) ⊢
      memRegion s1.sp 0x60 ∗ chainOrigSlotAt s1.sp x23 ∗ memRegion (s1.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
        stackAt s1.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s1.sp s0 ∗ (A.pool ∗ Frame) := by
    rw [hsp1, ProofLib.memRegion_split' (b := s.sp) (n := 0x30) (k := 48) (b' := s.sp + 0x30#64) rfl rfl (by decide)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre (Entails.trans hP1 hjoin) (SepWP.mono (step_epilogue_from_31a54 s0 s1 x23 (A.pool ∗ Frame) hpc1 hrun1 (hsp1.trans hsp) hx23_1 hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Q _ _ ⟨hrunf, htrf, hspf, hcsf, hQ⟩
  exact ⟨hrunf, htrf.trans htr1, hspf, hcsf, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

def sendResolveChain (hkdf : HkdfFn) (chain : Option ChainPB) (vn : Option VersionNegotiationPB) : SpqrApiResult (Option Chain) :=
  match chain with
  | none => match vn with
    | some v => if BitVec.slt Version.v0.toI32 v.minVersion then do
        let c ← SpqrApiResult.ofError (chainFromVersionNegotiation hkdf v); pure (some c)
      else pure none
    | none => .error (.err .chainNotAvailable)
  | some pb => do let c ← SpqrApiResult.ofError (Chain.fromPb pb); pure (some c)

def sendStepChain (hkdf : HkdfFn) (chain : Option Chain) (key : Option EpochSecret) (epoch : BitVec 64) :
    SpqrApiResult (BitVec 32 × Bytes × Option ChainPB) :=
  match chain with
  | none => if key.isNone then pure (0#32, ([] : Bytes), (none : Option ChainPB)) else .error (.panic .sendKeySomeWithoutChain)
  | some chain0 => do
    let chain1 ← match key with | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret) | none => pure chain0
    if epoch == 0#64 then .error (.panic .sendEpochUnderflow) else do
      let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf (epoch - 1#64)); pure (idx, mk, some chain2.intoPb)

def sendChainPhase (hkdf : HkdfFn) (chain : Option ChainPB) (vn : Option VersionNegotiationPB)
    (key : Option EpochSecret) (epoch : BitVec 64) : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB) := do
  let ch ← sendResolveChain hkdf chain vn; sendStepChain hkdf ch key epoch

theorem sendAfterStates_eq_bind_sendChainPhase (D : SpqrApiDeps) (hkdf : HkdfFn)
    (statePb : PqRatchetStatePB D.V1StatePB) (msg : D.MessageV1) (key : Option EpochSecret) (state : D.States) :
    sendAfterStates D hkdf statePb msg key state =
      match sendChainPhase hkdf statePb.chain statePb.versionNegotiation key (D.msgEpoch msg) with
      | .error e => .error e
      | .ok (index, msgKey, chainPb) =>
        let msgBytes := D.msgSerialize msg index
        match msgBytes with
        | [] => .error (.panic .sendMsgEmpty)
        | b0 :: _ =>
          if b0 != Version.v1.toU8 then .error (.panic .sendMsgBadVersion)
          else .ok { state := D.encodeState { inner := some (D.statesIntoPb state), versionNegotiation := statePb.versionNegotiation, chain := chainPb },
                     msg := msgBytes, key := if msgKey.isEmpty then none else some msgKey } := by
  unfold sendAfterStates sendChainPhase sendResolveChain sendStepChain
  cases statePb.chain with
  | none =>
    cases statePb.versionNegotiation with
    | none => rfl
    | some v =>
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]; split
      · rcases SpqrApiResult.ofError (chainFromVersionNegotiation hkdf v) with _ | c
        · rfl
        · dsimp only; rcases key with _ | es <;> dsimp only
          · split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]
          · rcases SpqrApiResult.ofChainPanic (c.addEpoch hkdf es) with _ | c1
            · rfl
            · dsimp only; split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]
      · dsimp only; split <;> rfl
  | some pb =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rcases SpqrApiResult.ofError (Chain.fromPb pb) with _ | c
    · rfl
    · dsimp only; rcases key with _ | es <;> dsimp only
      · split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]
      · rcases SpqrApiResult.ofChainPanic (c.addEpoch hkdf es) with _ | c1
        · rfl
        · dsimp only; split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]

theorem sendResolveChain_raw_le (hkdf : HkdfFn) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) {c : Chain} (h : sendResolveChain hkdf chain vn = .ok (some c)) :
    Top.StateSize.rawChain c.intoPb ≤ Top.StateSize.optRaw Top.StateSize.rawChain chain + 296 := by
  unfold sendResolveChain at h; cases chain with
  | none =>
    cases vn with
    | none => contradiction
    | some v =>
      dsimp only at h; split at h
      · rcases Top.StateSize.except_bind_eq_ok h with ⟨c', hc', heq⟩
        rw [SpqrApiResult.ofError_eq_ok] at hc'; have hc_eq := Option.some.inj (Except.ok.inj heq); subst hc_eq
        have hle := Top.StateSize.chainFromVersionNegotiation_raw_le hkdf v hc'; simp only [Top.StateSize.optRaw_none]; omega
      · nomatch h
  | some pb =>
    dsimp only at h; rcases Top.StateSize.except_bind_eq_ok h with ⟨c', hc', heq⟩
    rw [SpqrApiResult.ofError_eq_ok] at hc'; have hc_eq := Option.some.inj (Except.ok.inj heq); subst hc_eq
    have heq_raw := Top.StateSize.Chain.fromPb_raw_eq hc'; simp only [Top.StateSize.optRaw_some]; omega

private theorem vecDequeRingBuf_expose_len_le {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr head : BitVec 64) (xs : List α) :
    vecDequeRingBuf A stride align elem cap ptr head xs ⊢ ⌜xs.length ≤ cap.toNat⌝ ∗ vecDequeRingBuf A stride align elem cap ptr head xs := by
  unfold vecDequeRingBuf; apply Entails.pure_left; intro hpure; exact Entails.pure_right hpure.1 (Entails.pure_right hpure (Entails.refl _))

private theorem vecDequeAt_expose_len_le {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (v cap ptr head : BitVec 64) (xs : List α) :
    vecDequeAt A stride align elem v cap ptr head xs ⊢ ⌜xs.length ≤ cap.toNat⌝ ∗ vecDequeAt A stride align elem v cap ptr head xs := by
  unfold vecDequeAt; refine Entails.trans (sepConj_mono_right (vecDequeRingBuf_expose_len_le A stride align elem cap ptr head xs)) ?_
  rw [← sepConj_assoc, sepConj_comm (vecDequeHeader v cap ptr head (BitVec.ofNat 64 xs.length)), sepConj_assoc]; exact Entails.refl _

theorem chainAt_entails_links_grow_ok (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) (hbnd : c.links.length ≤ 2 ^ 54) :
    chainAt A a G c ⊢ ⌜c.links.length < G.linksCap.toNat ∨ max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63⌝ ∗ chainAt A a G c := by
  unfold chainAt; apply Entails.pure_left; intro hlen_eq
  refine Entails.trans (sepConj_mono_left (vecDequeAt_expose_len_le A chainEpochSize chainEpochAlign
    (chainEpochAt A) a G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links))) ?_
  rw [sepConj_assoc]; apply Entails.pure_left; intro hle_zip
  have hzip_len : (G.epochs.zip c.links).length = c.links.length := by rw [List.length_zip, hlen_eq, Nat.min_self]
  have hle : c.links.length ≤ G.linksCap.toNat := by rwa [hzip_len] at hle_zip
  exact Entails.pure_right (links_len_or_grow_ok hle hbnd) (Entails.pure_right hlen_eq (Entails.refl _))

theorem step_panic_key_without_chain_317d8 (img : Obj.Image) (ext : String → Option (State → State))
    {ret : BitVec 64} {s : State} {P Fr : SepProp} {Q : State → SepProp → Prop} {φ_out : State → Prop}
    (hinv : ImgCallInv img s) (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3964#64)
    (hrun : s.status = .Running) (hx21 : s.readReg64 .x21 ≠ LibsignalTripleRatchetRepr.noneCap)
    (hφ : ∀ sf : State, sf.trace = s.trace → φ_out sf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 12004#64) img hinv
  refine SepWP.mono (step_min_version_zero_panic_317d8 s P hpc hrun hx21) ?_
  rintro s1 P1 hpc1 hrun1 ⟨_, htr1, _, hP1⟩ hinv1; subst hP1
  apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::panicking::panic")) img hinv1
  refine SepWP.mono (step_panic_33740 s1 P1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨_, htr2, _, _⟩ _
  exact sepWPp_at_panic_stub hrun2 (by rw [hpc2]; exact corePanic_extern_at img.base ext) (hφ (Rust.panicked s2) (rfl.trans (htr2.trans htr1)))

theorem step_panic_epoch_zero_315dc (img : Obj.Image) (ext : String → Option (State → State))
    {ret : BitVec 64} {s : State} {P Fr : SepProp} {Q : State → SepProp → Prop} {φ_out : State → Prop}
    (hinv : ImgCallInv img s) (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3456#64)
    (hrun : s.status = .Running) (hx22 : s.readReg64 .x22 = 0#64) (hφ : ∀ sf : State, sf.trace = s.trace → φ_out sf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 13552#64) img hinv
  refine SepWP.mono (step_send_key_zero_315dc s P hpc hrun hx22) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hs1, hP1⟩ hinv1; subst hs1; subst hP1
  apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::panicking::panic_const::panic_const_sub_overflow")) img hinv1
  refine SepWP.mono (step_panic_33d4c _ P1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨_, htr2, _, _⟩ _
  exact sepWPp_at_panic_stub hrun2 (by rw [hpc2]; exact panicSubOverflow_extern_at img.base ext) (hφ (Rust.panicked s2) (rfl.trans htr2))

theorem step_from_pb_err_31510_to_31a3c {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x21 x27 x23 : BitVec 64) (err : Error)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3252#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64) s
      (chainErrorAt (s.sp + 0x1260#64) err ∗ memRegion (s.sp + 0x1060#64) 24 ∗
        memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 24 ∗
          memRegion (s.sp + 0x190#64) 928 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_post_from_pb_err_31510 s err
    (memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
      chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc hrun hx26 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx27_1, hvregs1, hP1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_pull_exists; rename_i w1 w2 w3; wp_conv_pre => rw [← hsp1]
  have hstep2 := step_err_31764 hb hdealloc hdrop_states s1 ret x21 x27 x23 w1 w2 w3 st1 key
    (memRegion (s1.sp + 0x1260#64) 88 ∗ Frame) hpc1 hrun1 (hx19_1.trans hx19) (hx21_1.trans hx21) (hx27_1.trans hx27) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩; rw [hsp1] at hspf hQ
  exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

theorem step_from_vn_err_31674_to_31a3c {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x21 x27 x23 : BitVec 64) (err : Error)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3608#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64) s
      (chainErrorAt (s.sp + 0x1260#64) err ∗ memRegion (s.sp + 0x590#64) 24 ∗
        memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 24 ∗
          memRegion (s.sp + 0x190#64) 928 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ chunkedStatesLocal1JumpTableAt b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_post_from_vn_err_31674 hb hdrop_states s ret err st1
    (optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ Frame) hpc hrun hx19 hx26 hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx21_1, hx23_1, hx27_1, hvregs1, hP1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_conv_pre => rw [← hsp1]
  have hstep2 := step_drop_key_31784 hdealloc s1 x21 x27 x23 key
    (spqrSendResultAt A ret none ∗ memRegion (s1.sp + 0x1260#64) 88 ∗ memRegion (s1.sp + 0x590#64) 24 ∗
      memRegion (s1.sp + 0x190#64) 928 ∗ chunkedStatesLocal1JumpTableAt b ∗ Frame)
    hpc1 hrun1 (hx21_1.trans hx21) (hx27_1.trans hx27) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩; rw [hsp1] at hspf hQ
  exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

theorem step_vn_none_3164c_to_31a3c {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext)
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x21 x27 x23 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3568#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx27 : s.readReg64 .x27 = x27) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64) s
      (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) none ∗
        memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) none ∗
          memRegion (s.sp + 0x190#64) 928 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗
          chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_from_vn_none_3164c (A := A) s
    (memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
      chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc hrun hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx27_1, hvregs1, hP1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_conv_pre => rw [← hsp1]
  have hstep2 := step_err_31794 hb hdealloc hdrop_states s1 ret x21 x27 x23 st1 key
    (ProtoRepr.optVersionNegotiationPBAt A (s1.sp + 0x30#64) none ∗ Frame)
    hpc1 hrun1 (hx19_1.trans hx19) (hx21_1.trans hx21) (hx27_1.trans hx27) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩; rw [hsp1] at hspf hQ
  exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

theorem step_send_key_err_315f4_to_31a3c {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F b))
    (s : State) (ret x23 : BitVec 64) (err : Error)
    (c : Chain) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 3480#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = x23) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64) s
      (sendKeyErrAt (s.sp + 0x1260#64) err ∗ memRegion ret 72 ∗
        chainRepr A (s.sp + 0x590#64) c ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret none ∗ memRegion (s.sp + 0x1260#64) 40 ∗
          memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x190#64) 928 ∗
          chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstep1 := step_post_send_key_err_315f4 s err
    (memRegion ret 72 ∗ chainRepr A (s.sp + 0x590#64) c ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
      chunkedStatesLocal1JumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc hrun hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s1 P1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, _, _, _, hx23_1, _, _, _, _, hvregs1, hP1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWP.weaken_pre hP1 ?_; wp_pull_exists; rename_i d0 d1 w2 w3; wp_conv_pre => rw [← hsp1]
  have hstep2 := step_err_31600 hb hdealloc hdrop_slice hdrop_states s1 ret x23 1#64 d0 d1 w2 w3 c st1 Frame
    hpc1 hrun1 (hx19_1.trans hx19) (hx23_1.trans hx23) hsp1_align
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep2 ?_)
  intro sf Q _ _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩; rw [hsp1] at hspf hQ
  exact ⟨hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, Entails.trans hQ (Entails.of_eq (by ac_rfl))⟩

/-! ## 5. Phase 3b–3c Chain Resolution & Step Composition (`0x314d8 -> 0x317fc / 0x31a3c / panic`) -/

def sendKeyIntoPbChain (hkdf : HkdfFn) (c1 : Chain) (msgEpoch : Epoch) :
    SpqrApiResult (BitVec 32 × Bytes × Option ChainPB) :=
  if msgEpoch == 0#64 then .error (.panic .sendEpochUnderflow) else do
    let (c2, (idx, msgKey)) ← SpqrApiResult.ofChainResult (c1.sendKey hkdf (msgEpoch - 1#64)); pure (idx, msgKey, some c2.intoPb)

noncomputable def sendChainTargetPC (b : BitVec 64) (ext : String → Option (State → State))
    (res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)) : BitVec 64 :=
  match res with
  | .ok _ => (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4000#64
  | .error _ => (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4576#64

def sendChainPost {F : ShaCompress} (A : RustAlloc) (img : Obj.Image)
    (s0 : State) (sp ret x23 : BitVec 64) (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)) (sf : State) (Q : SepProp) : Prop :=
  match res with
  | .ok (idx, msgKey, chainPb) =>
    sf.status = .Running ∧ sf.trace = s0.trace ∧ sf.sp = sp ∧ ImgCallInv img sf ∧
    sf.readReg64 .x19 = ret ∧ sf.readReg64 .x22 = BitVec.ofNat 64 msgKey.length ∧
    sf.readReg64 .x23 = x23 ∧ sf.readReg32 .x24 = idx ∧ sf.readReg64 .x26 = sp + 0x1260#64 ∧
    sf.readReg64 .x28 = sp + 0x1060#64 ∧
    (sf.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ sf.readReg32 .x20 = 0#32) ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    (Q ⊢ optChainPBRegSlotAt A (sp + 0xd90#64) (sf.readReg64 .x25) chainPb ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
      chunkedStatesAt A (sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
  | .error (.err _) =>
    sf.status = .Running ∧ sf.trace = s0.trace ∧ sf.sp = sp ∧ ImgCallInv img sf ∧ sf.readReg64 .x23 = x23 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    (Q ⊢ spqrSendResultAt A ret none ∗ memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xd90#64) 72 ∗
      memRegion (sp + 0x28#64) 8 ∗ memRegion (sp + 0x8#64) 8 ∗
      memRegion (sp + 0x190#64) 928 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
  | .error (.panic _) => False

private theorem readReg32_of_readReg64_eq {s1 s2 : State} {r : Reg} (h : s1.readReg64 r = s2.readReg64 r) :
    s1.readReg32 r = s2.readReg32 r := by unfold State.readReg32; rw [h]
private theorem flag_preserve {s1 s2 : State}
    (h : s1.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s1.readReg32 .x20 = 0#32)
    (hx20 : s2.readReg64 .x20 = s1.readReg64 .x20) (hx21 : s2.readReg64 .x21 = s1.readReg64 .x21) :
    s2.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s2.readReg32 .x20 = 0#32 :=
  h.imp (hx21.trans ·) ((readReg32_of_readReg64_eq hx20).trans ·)
private theorem flag_of_csinc_315b8 {s : State} {x21 : BitVec 64} (hx21 : s.readReg64 .x21 = x21)
    (hx20 : s.readReg32 .x20 = (if (x21 + 1#64 != 0#64) = true then 0#32 else 1#32)) :
    s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32 := by
  by_cases h : x21 = LibsignalTripleRatchetRepr.noneCap
  · exact Or.inl (hx21.trans h)
  · refine Or.inr (hx20.trans ?_)
    have hne : (x21 + 1#64 != 0#64) = true := by unfold LibsignalTripleRatchetRepr.noneCap at h; simp only [bne_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [hne]
private theorem memRegion_1260_88_eq_32_56 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 32 ∗ memRegion (sp + 0x1280#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 32) (k := 56) (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1260_88_eq_40_48 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 40 ∗ memRegion (sp + 0x1288#64) 48 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 40) (k := 48) (b' := sp + 0x1288#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_80_8 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 80 ∗ memRegion (sp + 0x5e0#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 80) (k := 8) (b' := sp + 0x5e0#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_24_64 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 24 ∗ memRegion (sp + 0x5a8#64) 64 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 64) (b' := sp + 0x5a8#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1060_80_eq_24_56 (sp : BitVec 64) :
    memRegion (sp + 0x1060#64) 80 = memRegion (sp + 0x1060#64) 24 ∗ memRegion (sp + 0x1078#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 24) (k := 56) (b' := sp + 0x1078#64) rfl (by bv_omega) (by decide)

theorem step_chain_5dc_to_7fc {A : RustAlloc} {F : ShaCompress} (img : Obj.Image)
    (hkdf : HkdfFn) {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
    (hsend_key : ChainSendKeyOkX img hkdf A ext) (hinto_pb : ChainIntoPbOkX img A ext)
    (s0 s : State) (ret x23 : BitVec 64) (c1 : Chain) (msgEpoch : Epoch)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame Fr : SepProp) (φ_out : State → Prop)
    (hinv : ImgCallInv img s) (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3456#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = msgEpoch)
    (hx23 : s.readReg64 .x23 = x23) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (((sendKeyIntoPbChain hkdf c1 msgEpoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (sendChainTargetPC img.base ext (sendKeyIntoPbChain hkdf c1 msgEpoch)) s
      (chainRepr A (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPost A img s0 s.sp ret x23 st1 Frame (sendKeyIntoPbChain hkdf c1 msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  by_cases hep0 : msgEpoch = 0#64
  · refine step_panic_epoch_zero_315dc img ext hinv hpc hrun (hx22.trans hep0) fun sf htr_f => ?_
    exact hφ sf (Or.inl ⟨by unfold sendKeyIntoPbChain; simp [hep0]; rfl, htr_f.trans htr⟩)
  · have hep0_beq : (msgEpoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep0
    have hpre_sk := step_pre_send_key_315dc s
      (chainRepr A (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc hrun (by rw [hx22]; exact hep0)
    apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176248#64) img hinv
    refine SepWP.mono hpre_sk ?_
    rintro s1 P1 hpc1 hrun1 ⟨_, htr1, hsp1, hx8_1, hx0_1, hx1_1, hx30_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, _, hx26_1, _, hx28_1, hvregs1, rfl⟩ hinv1
    dsimp only [chainRepr]; rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro G
    rw [memRegion_1260_88_eq_40_48 s.sp]
    have hcall_sk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176248#64)
        ((chainSendKeySpecX hkdf A).inImage img) := by rw [spqrSend_chainSendKey_addr]; exact hsend_key
    refine call_inImage_calleeStack_anyPanic (s.sp) chainSendKeyStackX (by decide)
      (x := ⟨s.sp + 0x1260#64, s.sp + 0x590#64, msgEpoch - 1#64, G, c1⟩)
      (T_pre := memRegion (s.sp + 0x1260#64) 40 ∗ chainAt A (s.sp + 0x590#64) G c1 ∗ A.pool)
      (T_post := fun _ => sendKeyPostAt A (s.sp + 0x590#64) (s.sp + 0x1260#64) c1 (Chain.sendKey hkdf c1 (msgEpoch - 1#64)) ∗ A.pool)
      (F := memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
      hcall_sk hinv1 hpc1 hrun1 hsp1 hsp_align hx30_1
      (by dsimp only [chainSendKeySpecX]; ac_rfl) (And.intro hx0_1 (And.intro (hx1_1.trans (congrArg (· - 1#64) hx22)) hx8_1))
      (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun sm hpan => by
        rcases hpan with ⟨hpan_sk, htr_sm⟩ | ⟨halloc, hpref⟩
        · refine hφ sm (Or.inl ⟨?_, htr_sm.trans (htr1.trans htr)⟩)
          unfold sendKeyIntoPbChain; simp only [hep0_beq, Bool.false_eq_true, ↓reduceIte]
          cases h : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
          | ok _ => rw [h] at hpan_sk; contradiction
          | error e => cases e with
            | err _ => rw [h] at hpan_sk; contradiction
            | panic _ => rfl
        · exact hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr1, htr] at halloc, by rwa [htr1, htr] at hpref⟩))
      (fun _ => by dsimp only [chainSendKeySpecX]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hx19_2 hx20_2 hx21_2 _ hx23_2 _ _ hx26_2 _ hx28_2 hvregs2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
    have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
    have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
    have hx19_20 : s2.readReg64 .x19 = ret := hx19_2.trans (hx19_1.trans hx19)
    have hx23_20 : s2.readReg64 .x23 = x23 := hx23_2.trans (hx23_1.trans hx23)
    have hx26_20 : s2.readReg64 .x26 = s.sp + 0x1260#64 := hx26_2.trans (hx26_1.trans hx26)
    have hx28_20 : s2.readReg64 .x28 = s.sp + 0x1060#64 := hx28_2.trans (hx28_1.trans hx28)
    have hflag2 := flag_preserve (flag_preserve hflag hx20_1 hx21_1) hx20_2 hx21_2
    cases hsk : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
    | error e =>
      cases e with
      | panic p => dsimp only [sendKeyPostAt]; exact pure_elim_focus_b1 False (fun h => h.elim)
      | err err =>
        have hres : sendKeyIntoPbChain hkdf c1 msgEpoch = .error (.err err) := by unfold sendKeyIntoPbChain; simp [hep0_beq, hsk]; rfl
        rw [hres]; dsimp only [sendChainTargetPC, sendChainPost, sendKeyPostAt]
        apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv2
        have herr_step := step_send_key_err_315f4_to_31a3c hb hdealloc hdrop_slice hdrop_states s2 ret x23 err c1 st1
          (memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame) hpc2 hrun2 hx19_20 hx23_20 hsp2_align
        rw [hsp2] at herr_step
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono herr_step ?_)
        rintro sf Q hpcf hrunf ⟨_, htrf, hspf, hx23f, hvregsf, hQ⟩ hinvf
        refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr2_0, hspf, hinvf, hx23f, hvregsf.trans hvregs2_0, ?_⟩
        rw [memRegion_1260_88_eq_40_48 s.sp]; exact Entails.trans hQ (Entails.of_eq (by ac_rfl))
    | ok val =>
      rcases val with ⟨c2, idx, msgKey⟩
      have hres : sendKeyIntoPbChain hkdf c1 msgEpoch = .ok (idx, msgKey, some c2.intoPb) := by unfold sendKeyIntoPbChain; simp [hep0_beq, hsk]; rfl
      rw [hres]; dsimp only [sendChainTargetPC, sendChainPost, sendKeyPostAt]
      have hok1 := step_post_send_key_ok_315f4 (A := A) s2 idx msgKey
        (chainRepr A (s.sp + 0x590#64) c2 ∗ memRegion (s.sp + 0x1288#64) 48 ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
          memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc2 hrun2 hsp2_align
      rw [hsp2] at hok1
      apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3712#64) img hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hok1 ?_)
      rintro s3 P3 hpc3 hrun3 ⟨_, htr3, hsp3, hx24_3, hx19_3, hx20_3, hx21_3, _, hx23_3, _, hx26_3, _, hx28_3, hvregs3, hP3⟩ hinv3
      refine SepWPp.weaken_pre hP3 ?_
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
      have hok2 := step_pre_chain_into_pb_316dc (A := A) s3 idx msgKey c2
        (memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc3 hrun3 hsp3_align
      rw [hsp3] at hok2
      apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 174044#64) img hinv3
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hok2 ?_)
      rintro s4 P4 hpc4 hrun4 ⟨_, htr4, hsp4, hx0_4, hx8_4, hx30_4, hx22_4, hx19_4, hx20_4, hx21_4, hx23_4, hx24_4, hx26_4, _, hx28_4, hvregs4, hP4⟩ hinv4
      refine SepWPp.weaken_pre hP4 ?_
      apply SepWPp.exists_elim; intro G2; apply SepWPp.exists_elim; intro mkCap; apply SepWPp.exists_elim; intro mkPtr
      have hcall_into : subroutine_ok (tripleRatchetProgAtExt img.base ext)
          ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 174044#64)
          ((chainIntoPbSpecX A).inImage img) := by rw [spqrSend_chainIntoPb_addr]; exact hinto_pb
      have htr4_0 : s4.trace = s0.trace := htr4.trans (htr3.trans htr2_0)
      refine call_inImage_calleeStack_anyPanic (s.sp) chainIntoPbStackX (by decide)
        (x := ⟨s.sp + 0x1060#64, s.sp + 0x1260#64, G2, c2⟩)
        (T_pre := memRegion (s.sp + 0x1060#64) 80 ∗ chainAt A (s.sp + 0x1260#64) G2 c2 ∗ A.pool)
        (T_post := fun _ => ProtoRepr.chainPBAt A (s.sp + 0x1060#64) c2.intoPb ∗ memRegion (s.sp + 0x1260#64) 88 ∗ A.pool)
        (F := ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
        hcall_into hinv4 hpc4 hrun4 hsp4 hsp_align hx30_4
        (by dsimp only [chainIntoPbSpecX]; ac_rfl) (And.intro hx8_4 hx0_4)
        (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
        (fun sm ⟨halloc, hpref⟩ => hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr4_0] at halloc, by rwa [htr4_0] at hpref⟩))
        (fun _ => by dsimp only [chainIntoPbSpecX]; ac_rfl) ?_
      intro s5 hpc5 hrun5 hsp5 htr5 hinv5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 _ hx26_5 _ hx28_5 hvregs5
      have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5]; exact hsp_align
      have hx28_50 : s5.readReg64 .x28 = s5.sp + 0x1060#64 := by rw [hsp5]; exact hx28_5.trans (hx28_4.trans (hx28_3.trans hx28_20))
      have hflag5 := flag_preserve (flag_preserve (flag_preserve hflag2 hx20_3 hx21_3) hx20_4 hx21_4) hx20_5 hx21_5
      have hok3 := step_post_chain_into_pb_31734 (A := A) s5 c2.intoPb
        (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc5 hrun5 hx28_50 hsp5_align
      rw [hsp5] at hok3
      apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4000#64) img hinv5
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hok3 ?_)
      rintro sf Q hpcf hrunf ⟨_, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx26f, _, hx28f, hvregsf, hQ⟩ hinvf
      refine SepWPp.done hpcf hrunf
        ⟨hrunf, htrf.trans (htr5.trans htr4_0), hspf, hinvf,
         hx19f.trans (hx19_5.trans (hx19_4.trans (hx19_3.trans hx19_20))),
         hx22f.trans (hx22_5.trans hx22_4),
         hx23f.trans (hx23_5.trans (hx23_4.trans (hx23_3.trans hx23_20))),
         hx24f.trans ((readReg32_of_readReg64_eq hx24_5).trans (hx24_4.trans hx24_3)),
         hx26f.trans (hx26_5.trans (hx26_4.trans (hx26_3.trans hx26_20))),
         hx28f.trans (hx28_5.trans (hx28_4.trans (hx28_3.trans hx28_20))),
         flag_preserve hflag5 hx20f hx21f,
         hvregsf.trans (hvregs5.trans (hvregs4.trans (hvregs3.trans hvregs2_0))), ?_⟩
      refine Entails.trans hQ (Entails.trans (Entails.of_eq (show
        optChainPBRegSlotAt A (s.sp + 0xd90#64) (sf.readReg64 .x25) (some c2.intoPb) ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) =
        (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
          (optChainPBRegSlotAt A (s.sp + 0xd90#64) (sf.readReg64 .x25) (some c2.intoPb) ∗
            memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) by ac_rfl)) ?_)
      have hex_mk : ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ⊢
          ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey :=
        Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.refl _))
      exact Entails.trans (sepConj_mono_left hex_mk) (Entails.of_eq (by ac_rfl))

private theorem panic_inImage_calleeStack_anyPanic {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp} {φ_pre : Prop} {φ_pan φ_out : State → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜φ_pan sf⌝ ∗ anyHeap))
    (hpan_imp : ∀ sm : State, φ_pan sm → φ_out sm) (hspec_post : ∀ sf, spec.post x s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp_frozen (x := x) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun hsp_al rfl
    (fun R' hm => ?_) ?_ ?_ ?_ ?_
  · change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ spec.pre x s) ∗ (F_ext ∗ R')
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
    rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
    rw [hP, stackAt_callee_split sp n hle] at hm
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hm
  · intro sm code R' _ hpost
    change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost; rw [hexit_eq code sm] at hpost
    exact panic_not_exited hpost
  · intro sm _ _ hmFr
    change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr; rw [hpan_eq sm] at hmFr
    exact panic_frame_anyHeap (hpan_imp sm) hmFr
  · intro sm _ _ _ _ _ _
    change SepWPp prog ret sm (spec.post x s sm ∗ F_ext) Q _
    rw [hspec_post sm]; exact SepWPp.pure_left False.elim
  · intro sm R' _ hpost
    change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost; rw [hoom_eq sm] at hpost
    exact (panic_not_exited hpost).elim

private theorem addsPState64_noneCap_z : (addsPState64 LibsignalTripleRatchetRepr.noneCap 1#64).z = true := by
  unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap; decide

private theorem addsPState64_z_false_of_ne_noneCap {x21 : BitVec 64} (hne : x21 ≠ LibsignalTripleRatchetRepr.noneCap) :
    (addsPState64 x21 1#64).z = false := by
  unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap at *
  simp only [Bool.false_eq_true, ↓reduceIte, beq_eq_false_iff_ne]; intro h; apply hne; bv_omega

private theorem setPC_preserves {s1 s : State} {pc : BitVec 64} (h : s1 = s.setPC pc) :
    s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧ (∀ r, s1.readReg64 r = s.readReg64 r) := by
  subst h; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem step_chain_5b8_to_7fc {A : RustAlloc} {F : ShaCompress} (img : Obj.Image)
    (hkdf : HkdfFn) {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
    (hadd_epoch : ChainAddEpochOkX img hkdf A ext)
    (hsend_key : ChainSendKeyOkX img hkdf A ext) (hinto_pb : ChainIntoPbOkX img A ext)
    (s0 s : State) (ret x21 x27 x23 : BitVec 64) (c0 : Chain) (hc0_len : c0.links.length ≤ 2 ^ 54)
    (key : Option EpochSecret) (msgEpoch : Epoch) (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame Fr : SepProp) (φ_out : State → Prop) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3420#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hpstate : s.pstate = addsPState64 x21 1#64)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (((sendStepChain hkdf (some c0) key msgEpoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (sendChainTargetPC img.base ext (sendStepChain hkdf (some c0) key msgEpoch)) s
      (optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ chainRepr A (s.sp + 0x590#64) c0 ∗
        memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPost A img s0 s.sp ret x23 st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) (sendStepChain hkdf (some c0) key msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  cases key with
  | none =>
    have heq_step : sendStepChain hkdf (some c0) none msgEpoch = sendKeyIntoPbChain hkdf c0 msgEpoch := rfl
    rw [heq_step]; dsimp only [optEpochSecretRegSlotAt]; rw [sepConj_assoc]
    apply pure_elim_focus_b1 (x21 = LibsignalTripleRatchetRepr.noneCap); intro hx21_none
    have hz : s.pstate.z = true := by rw [hpstate, hx21_none]; exact addsPState64_noneCap_z
    apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3456#64) img hinv
    refine SepWP.mono (step_branch_key_none_315b8 s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hs1, rfl⟩ hinv1
    rcases setPC_preserves hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩
    have hstep := step_chain_5dc_to_7fc img hkdf hb hdealloc hdrop_slice hdrop_states hsend_key hinto_pb
      s0 s1 ret x23 c0 msgEpoch st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) Fr φ_out
      hinv1 hpc1 hrun1 (htr1.trans htr) ((hreg1 .x19).trans hx19) ((hreg1 .x22).trans hx22) ((hreg1 .x23).trans hx23)
      (by rw [hsp1]; exact (hreg1 .x26).trans hx26) (by rw [hsp1]; exact (hreg1 .x28).trans hx28)
      (flag_preserve hflag (hreg1 .x20) (hreg1 .x21)) (by rw [hsp1]; exact hsp_align) hφ (hvregs1.trans hvregs)
    rw [hsp1] at hstep; exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hstep
  | some es =>
    have hexp_ne : optEpochSecretRegSlotAt A s.sp x21 x27 (some es) ⊢
        ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗ optEpochSecretRegSlotAt A s.sp x21 x27 (some es) := by
      dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne
      exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))
    refine SepWPp.weaken_pre (sepConj_mono_left hexp_ne) ?_; rw [sepConj_assoc]
    apply pure_elim_focus_b1 (x21 ≠ LibsignalTripleRatchetRepr.noneCap); intro hx21_ne
    have hz : s.pstate.z = false := by rw [hpstate]; exact addsPState64_z_false_of_ne_noneCap hx21_ne
    apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3424#64) img hinv
    refine SepWP.mono (step_branch_key_some_315b8 s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hs1, rfl⟩ hinv1
    rcases setPC_preserves hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩
    have hx19_1 : s1.readReg64 .x19 = ret := (hreg1 .x19).trans hx19
    have hx21_1 : s1.readReg64 .x21 = x21 := (hreg1 .x21).trans hx21
    have hx22_1 : s1.readReg64 .x22 = msgEpoch := (hreg1 .x22).trans hx22
    have hx23_1 : s1.readReg64 .x23 = x23 := (hreg1 .x23).trans hx23
    have hx26_1 : s1.readReg64 .x26 = s.sp + 0x1260#64 := (hreg1 .x26).trans hx26
    have hx27_1 : s1.readReg64 .x27 = x27 := (hreg1 .x27).trans hx27
    have hx28_1 : s1.readReg64 .x28 = s.sp + 0x1060#64 := (hreg1 .x28).trans hx28
    rw [memRegion_1260_88_eq_32_56 s.sp]
    have hpre_ae := step_pre_add_epoch_315bc (A := A) s1 es
      (chainRepr A (s.sp + 0x590#64) c0 ∗ memRegion (s.sp + 0x1280#64) 56 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc1 hrun1 (by rw [hsp1]; exact hsp_align)
    rw [hsp1, hx21_1, hx27_1] at hpre_ae
    apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176844#64) img hinv1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hpre_ae ?_)
    rintro s2 P2 hpc2 hrun2 ⟨_, htr2, hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, _, hx28_2, hvregs2, hP2⟩ hinv2
    have hP2' : P2 ⊢ chainRepr A (s.sp + 0x590#64) c0 ∗ epochSecretAt A (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗
        memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame :=
      Entails.trans hP2 (Entails.of_eq (by ac_rfl))
    refine SepWPp.weaken_pre hP2' ?_; dsimp only [chainRepr]; rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro G0
    refine SepWPp.weaken_pre (sepConj_mono_left (chainAt_entails_links_grow_ok A (s.sp + 0x590#64) G0 c0 hc0_len)) ?_
    rw [sepConj_assoc]
    apply pure_elim_focus_b1 (c0.links.length < G0.linksCap.toNat ∨ max (2 * G0.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63); intro hgrow
    have hcall_ae : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176844#64)
        ((chainAddEpochSpecX hkdf A).inImage img) := by rw [spqrSend_chainAddEpoch_addr]; exact hadd_epoch
    have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
    have hpan_ae : ∀ sm : State, (((Chain.addEpoch hkdf c0 es).isOk = false ∧ sm.trace = s2.trace) ∨
        (allocFailedIn s2 sm ∧ s2.trace <+: sm.trace)) → φ_out sm := by
      intro sm hpan; rcases hpan with ⟨hpan_ae, htr_sm⟩ | ⟨halloc, hpref⟩
      · refine hφ sm (Or.inl ⟨?_, htr_sm.trans htr2_0⟩)
        unfold sendStepChain; dsimp only [Bind.bind, Except.bind]
        cases h : Chain.addEpoch hkdf c0 es with
        | ok _ => rw [h] at hpan_ae; contradiction
        | error p => rfl
      · exact hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr2_0] at halloc, by rwa [htr2_0] at hpref⟩)
    cases hae : Chain.addEpoch hkdf c0 es with
    | error p =>
      exact panic_inImage_calleeStack_anyPanic (s.sp) chainAddEpochStackX (by decide)
        (x := ⟨s.sp + 0x590#64, s.sp + 0x1260#64, G0, ⟨x21, x27⟩, c0, es⟩)
        (T_pre := chainAt A (s.sp + 0x590#64) G0 c0 ∗ epochSecretAt A (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗ A.pool)
        (F := memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
        hcall_ae hinv2 hpc2 hrun2 hsp2 hsp_align (by dsimp only [chainAddEpochSpecX]; ac_rfl)
        (And.intro hx0_2 (And.intro hx1_2 hgrow)) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl) hpan_ae
        (fun _ => by dsimp only [chainAddEpochSpecX]; rw [hae])
    | ok c1 =>
      refine call_inImage_calleeStack_anyPanic (s.sp) chainAddEpochStackX (by decide)
        (x := ⟨s.sp + 0x590#64, s.sp + 0x1260#64, G0, ⟨x21, x27⟩, c0, es⟩)
        (T_pre := chainAt A (s.sp + 0x590#64) G0 c0 ∗ epochSecretAt A (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗ A.pool)
        (T_post := fun _ => chainRepr A (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 32 ∗ A.pool)
        (F := memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
        hcall_ae hinv2 hpc2 hrun2 hsp2 hsp_align hx30_2 (by dsimp only [chainAddEpochSpecX]; ac_rfl)
        (And.intro hx0_2 (And.intro hx1_2 hgrow)) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl) hpan_ae
        (fun _ => by dsimp only [chainAddEpochSpecX]; rw [hae]; ac_rfl) ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hinv3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 _ _ hx26_3 _ hx28_3 hvregs3
      have heq_step : sendStepChain hkdf (some c0) (some es) msgEpoch = sendKeyIntoPbChain hkdf c1 msgEpoch := by
        unfold sendStepChain sendKeyIntoPbChain; simp [hae]; rfl
      rw [heq_step]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
      have hx19_30 : s3.readReg64 .x19 = ret := hx19_3.trans (hx19_2.trans hx19_1)
      have hx22_30 : s3.readReg64 .x22 = msgEpoch := hx22_3.trans (hx22_2.trans hx22_1)
      have hx23_30 : s3.readReg64 .x23 = x23 := hx23_3.trans (hx23_2.trans hx23_1)
      have hx26_30 : s3.readReg64 .x26 = s3.sp + 0x1260#64 := by rw [hsp3]; exact hx26_3.trans (hx26_2.trans hx26_1)
      have hx28_30 : s3.readReg64 .x28 = s3.sp + 0x1060#64 := by rw [hsp3]; exact hx28_3.trans (hx28_2.trans hx28_1)
      have hflag3 := flag_preserve (flag_preserve (flag_preserve hflag (hreg1 .x20) (hreg1 .x21)) hx20_2 (hx21_2.trans hx21_1.symm)) hx20_3 hx21_3
      have hstep := step_chain_5dc_to_7fc img hkdf hb hdealloc hdrop_slice hdrop_states hsend_key hinto_pb
        s0 s3 ret x23 c1 msgEpoch st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) Fr φ_out
        hinv3 hpc3 hrun3 (htr3.trans htr2_0) hx19_30 hx22_30 hx23_30 hx26_30 hx28_30 hflag3 hsp3_align (by rwa [heq_step] at hφ)
        (hvregs3.trans (hvregs2.trans (hvregs1.trans hvregs)))
      rw [hsp3, memRegion_1260_88_eq_32_56 s.sp] at hstep
      exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hstep

theorem vn_some_pack (A : RustAlloc) (pin : VecPin) (a : BitVec 64) (v : VersionNegotiationPB) :
    ChainFromVersionNegotiation.versionNegotiationPBAt A pin a v ⊢ ProtoRepr.optVersionNegotiationPBAt A a (some v) := by
  dsimp only [ProtoRepr.optVersionNegotiationPBAt]; rw [versionNegotiationPBAt_eq_exists_pin A a v]
  exact Entails.sepExists_right pin (Entails.refl _)

private theorem optEpochSecretRegSlotAt_some_ne (A : RustAlloc) (sp x21 x27 : BitVec 64) (es : EpochSecret) :
    optEpochSecretRegSlotAt A sp x21 x27 (some es) ⊢
      ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗ optEpochSecretRegSlotAt A sp x21 x27 (some es) := by
  dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne
  exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))

private theorem sendChainPost_congr_frame {F : ShaCompress} (A : RustAlloc) (img : Obj.Image)
    (s0 : State) (sp ret x23 : BitVec 64) (st1 : States spqrPolyApi (spqrAuthApi F))
    {Fr1 Fr2 : SepProp} (hFr : Fr1 = Fr2) (res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)) :
    sendChainPost A img s0 sp ret x23 st1 Fr1 res = sendChainPost A img s0 sp ret x23 st1 Fr2 res := by rw [hFr]

theorem step_chain_resolve_314d8_to_7fc {A : RustAlloc} {F : ShaCompress} (img : Obj.Image)
    (hkdf : HkdfFn) {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
    (hfrom_pb : ChainFromPbOkX img A ext) (hfrom_vn : ChainFromVersionNegotiationOkX img hkdf A ext)
    (hadd_epoch : ChainAddEpochOkX img hkdf A ext)
    (hsend_key : ChainSendKeyOkX img hkdf A ext) (hinto_pb : ChainIntoPbOkX img A ext)
    (s0 s : State) (ret x21 x27 x23 : BitVec 64)
    (chain : Option ChainPB) (hchain_raw : Top.StateSize.optRaw Top.StateSize.rawChain chain + 296 ≤ 2 ^ 54)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (msgEpoch : Epoch)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame Fr : SepProp) (φ_out : State → Prop)
    (hinv : ImgCallInv img s) (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace)
    (hx23_none : x23 = LibsignalTripleRatchetRepr.noneCap ↔ chain = none) (hpstate : s.pstate = addsPState64 x23 1#64)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = s.sp + 0x550#64) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (((sendChainPhase hkdf chain vn key msgEpoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (sendChainTargetPC img.base ext (sendChainPhase hkdf chain vn key msgEpoch)) s
      (ProtoRepr.optChainPBAt A (s.sp + 0x60#64) chain ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPost A img s0 s.sp ret x23 st1
        (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame)
        (sendChainPhase hkdf chain vn key msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  cases chain with
  | none =>
    have hx23_eq : x23 = LibsignalTripleRatchetRepr.noneCap := hx23_none.mpr rfl
    have hz : s.pstate.z = true := by rw [hpstate, hx23_eq]; exact addsPState64_noneCap_z
    have horig_eq : ProtoRepr.optChainPBAt A (s.sp + 0x60#64) none = chainOrigSlotAt s.sp x23 := by
      have hx23_eq' : x23 = ChainFromVersionNegotiation.noneCap := hx23_eq
      rw [hx23_eq', chainOrigSlotAt_none]
      dsimp only [ProtoRepr.optChainPBAt, ChainFromVersionNegotiation.noneCap, LibsignalTripleRatchetRepr.noneCap]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [horig_eq]
    apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3568#64) img hinv
    refine SepWP.mono (step_branch_chain_none_314d8 s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hs1, rfl⟩ hinv1
    rcases setPC_preserves hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩
    have hx19_1 : s1.readReg64 .x19 = ret := (hreg1 .x19).trans hx19; have hx21_1 : s1.readReg64 .x21 = x21 := (hreg1 .x21).trans hx21
    have hx22_1 : s1.readReg64 .x22 = msgEpoch := (hreg1 .x22).trans hx22; have hx23_1 : s1.readReg64 .x23 = x23 := (hreg1 .x23).trans hx23
    have hx25_1 : s1.readReg64 .x25 = s.sp + 0x550#64 := (hreg1 .x25).trans hx25; have hx26_1 : s1.readReg64 .x26 = s.sp + 0x1260#64 := (hreg1 .x26).trans hx26
    have hx27_1 : s1.readReg64 .x27 = x27 := (hreg1 .x27).trans hx27; have hx28_1 : s1.readReg64 .x28 = s.sp + 0x1060#64 := (hreg1 .x28).trans hx28
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    cases vn with
    | none =>
      have heq_ph : sendChainPhase hkdf none none key msgEpoch = .error (.err .chainNotAvailable) := rfl
      rw [heq_ph]
      have hstep := step_vn_none_3164c_to_31a3c hb hdealloc hdrop_states s1 ret x21 x27 x23 st1 key
        (chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
          memRegion (s.sp + 0x8#64) 8 ∗ Frame) hpc1 hrun1 hx19_1 hx21_1 hx23_1 hx27_1 hsp1_align
      rw [hsp1] at hstep
      apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv1
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
      rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
      exact SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans (htr1.trans htr), hspf, hinvf, hx23f, hvregsf.trans (hvregs1.trans hvregs), Entails.trans hQf (Entails.of_eq (by ac_rfl))⟩
    | some v =>
      by_cases hgt : BitVec.slt 0#32 v.minVersion = true
      · have hpre_vn := step_pre_from_vn_3164c (A := A) s1 v
          (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
            memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          hpc1 hrun1 hgt hsp1_align
        rw [hsp1] at hpre_vn
        apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 125100#64) img hinv1
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hpre_vn ?_)
        rintro s2 P2 hpc2 hrun2 ⟨_, htr2, hsp2, hx0_2, hx8_2, hx30_2, hx19_2, _, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hvregs2, hP2⟩ hinv2
        refine SepWPp.weaken_pre hP2 ?_; apply SepWPp.exists_elim; intro pin
        have hcall_vn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
            ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 125100#64)
            ((chainFromVersionNegotiationSpecX hkdf A).inImage img) := by rw [spqrSend_chainFromVN_addr]; exact hfrom_vn
        have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
        refine call_inImage_calleeStack_anyPanic (s.sp) chainFromVersionNegotiationStackX (by decide)
          (x := ⟨s.sp + 0x1260#64, s.sp + 0x30#64, pin, v⟩)
          (T_pre := memRegion (s.sp + 0x1260#64) 88 ∗ ChainFromVersionNegotiation.versionNegotiationPBAt A pin (s.sp + 0x30#64) v ∗ A.pool)
          (T_post := fun _ => chainResultAt A (s.sp + 0x1260#64) (chainFromVersionNegotiation hkdf v) ∗
            ChainFromVersionNegotiation.versionNegotiationPBAt A pin (s.sp + 0x30#64) v ∗ A.pool)
          (F := chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
            memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
            memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
          hcall_vn hinv2 hpc2 hrun2 hsp2 hsp_align hx30_2 (by dsimp only [chainFromVersionNegotiationSpecX]; ac_rfl)
          (And.intro hx8_2 hx0_2) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
          (fun sm ⟨halloc, hpref⟩ => hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr2_0] at halloc, by rwa [htr2_0] at hpref⟩))
          (fun _ => by dsimp only [chainFromVersionNegotiationSpecX]; ac_rfl) ?_
        intro s3 hpc3 hrun3 hsp3 htr3 hinv3 hx19_3 _ hx21_3 hx22_3 hx23_3 _ hx25_3 hx26_3 hx27_3 hx28_3 hvregs3
        have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
        have htr3_0 : s3.trace = s0.trace := htr3.trans htr2_0
        have hvregs3_0 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans (hvregs2.trans (hvregs1.trans hvregs))
        have hx19_30 : s3.readReg64 .x19 = ret := hx19_3.trans (hx19_2.trans hx19_1); have hx21_30 : s3.readReg64 .x21 = x21 := hx21_3.trans (hx21_2.trans hx21_1)
        have hx22_30 : s3.readReg64 .x22 = msgEpoch := hx22_3.trans (hx22_2.trans hx22_1); have hx23_30 : s3.readReg64 .x23 = x23 := hx23_3.trans (hx23_2.trans hx23_1)
        have hx25_30 : s3.readReg64 .x25 = s3.sp + 0x550#64 := by rw [hsp3]; exact hx25_3.trans (hx25_2.trans hx25_1)
        have hx26_30 : s3.readReg64 .x26 = s3.sp + 0x1260#64 := by rw [hsp3]; exact hx26_3.trans (hx26_2.trans hx26_1)
        have hx27_30 : s3.readReg64 .x27 = x27 := hx27_3.trans (hx27_2.trans hx27_1)
        have hx28_30 : s3.readReg64 .x28 = s3.sp + 0x1060#64 := by rw [hsp3]; exact hx28_3.trans (hx28_2.trans hx28_1)
        refine SepWPp.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vn_some_pack A pin (s.sp + 0x30#64) v))))) ?_
        cases hfvn : chainFromVersionNegotiation hkdf v with
        | error err =>
          have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = .error (.err err) := by
            unfold sendChainPhase sendResolveChain; simp [Version.toI32, hgt, hfvn, SpqrApiResult.ofError]; rfl
          rw [heq_ph]; dsimp only [chainResultAt]; rw [memRegion_590_88_eq_24_64 s.sp]
          have hstep := step_from_vn_err_31674_to_31a3c hb hdealloc hdrop_states s3 ret x21 x27 x23 err st1 key
            (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
              memRegion (s.sp + 0x5a8#64) 64 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
              memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
              memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
            hpc3 hrun3 hx19_30 hx21_30 hx23_30 hx26_30 hx27_30 hsp3_align
          rw [hsp3] at hstep
          apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv3
          refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
          rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
          refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr3_0, hspf, hinvf, hx23f, hvregsf.trans hvregs3_0, ?_⟩
          rw [memRegion_590_88_eq_24_64 s.sp]; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))
        | ok c0 =>
          have hres : sendResolveChain hkdf none (some v) = .ok (some c0) := by unfold sendResolveChain; simp [Version.toI32, hgt, hfvn, SpqrApiResult.ofError]
          have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = sendStepChain hkdf (some c0) key msgEpoch := by unfold sendChainPhase; rw [hres]; rfl
          have hc0_len : c0.links.length ≤ 2 ^ 54 :=
            Nat.le_trans (chain_links_length_le_rawChain c0) (Nat.le_trans (sendResolveChain_raw_le hkdf none (some v) hres) hchain_raw)
          rw [heq_ph, sendChainPost_congr_frame A img s0 s.sp ret x23 st1
            (Fr2 := memRegion (s.sp + 0x1bc0#64) 16 ∗ (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)) (by ac_rfl)]
          dsimp only [chainResultAt]
          have hstep_ok := step_post_from_vn_ok_31674 (A := A) s3 c0
            (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
              optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
              memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
              chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            hpc3 hrun3 hx25_30 hx26_30 hsp3_align
          rw [hsp3] at hstep_ok
          apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3420#64) img hinv3
          refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep_ok ?_)
          rintro s4 P4 hpc4 hrun4 ⟨_, htr4, hsp4, hpst4, hx20_4, hx19_4, hx21_4, hx22_4, hx23_4, _, _, hx26_4, hx27_4, hx28_4, hvregs4, hP4⟩ hinv4
          have hstep_5b8 := step_chain_5b8_to_7fc img hkdf hb hdealloc hdrop_slice hdrop_states hadd_epoch hsend_key hinto_pb
            s0 s4 ret x21 x27 x23 c0 hc0_len key msgEpoch st1
            (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)
            Fr φ_out hinv4 hpc4 hrun4 (htr4.trans htr3_0) (by rw [hx21_30] at hpst4; exact hpst4)
            (hx19_4.trans hx19_30) (hx21_4.trans hx21_30) (hx22_4.trans hx22_30) (hx23_4.trans hx23_30)
            (by rw [hsp4, ← hsp3]; exact hx26_4.trans hx26_30) (hx27_4.trans hx27_30)
            (by rw [hsp4, ← hsp3]; exact hx28_4.trans hx28_30)
            (flag_of_csinc_315b8 (hx21_4.trans hx21_30) (by rw [hx21_30] at hx20_4; exact hx20_4))
            (by rw [hsp4]; exact hsp_align) (by rwa [heq_ph] at hφ) (hvregs4.trans hvregs3_0)
          rw [hsp4] at hstep_5b8; exact SepWPp.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) hstep_5b8
      · have hle : BitVec.slt 0#32 v.minVersion = false := Bool.eq_false_iff.mpr hgt
        have hres : sendResolveChain hkdf none (some v) = .ok none := by unfold sendResolveChain; simp [Version.toI32, hle]; rfl
        have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = sendStepChain hkdf none key msgEpoch := by unfold sendChainPhase; rw [hres]; rfl
        rw [heq_ph]
        have hstep_le := step_from_vn_le_zero_3164c (A := A) s1 v
          (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
            memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          hpc1 hrun1 hle hsp1_align
        rw [hsp1] at hstep_le
        apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3964#64) img hinv1
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep_le ?_)
        rintro s2 P2 hpc2 hrun2 ⟨_, htr2, hsp2, hx19_2, _, hx21_2, _, hx23_2, _, _, hx26_2, _, hx28_2, hvregs2, hP2⟩ hinv2
        have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
        have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
        refine SepWPp.weaken_pre hP2 ?_
        cases key with
        | none =>
          have heq_st : sendStepChain hkdf none none msgEpoch = .ok (0#32, [], none) := rfl
          rw [heq_st]; dsimp only [optEpochSecretRegSlotAt]
          have hpull : ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              (chainOrigSlotAt s.sp x23 ∗ (⌜x21 = LibsignalTripleRatchetRepr.noneCap⌝ ∗ memRegion (s.sp + 0x1bc0#64) 16) ∗
                memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
                memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
                memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
                chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) ⊢
              ⌜x21 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
              (memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗
                (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
                  memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
                  memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
                  memRegion (s.sp + 0xde0#64) 80 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
                  chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := Entails.of_eq (by ac_rfl)
          refine SepWPp.weaken_pre hpull ?_; apply pure_elim_focus_b1 (x21 = LibsignalTripleRatchetRepr.noneCap); intro hx21_none
          have hstep_ok := step_min_version_zero_ok_317d8 (A := A) s2
            (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
              memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
              memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
              memRegion (s.sp + 0xde0#64) 80 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
              chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            hpc2 hrun2 (hx21_2.trans (hx21_1.trans hx21_none)) hsp2_align
          rw [hsp2] at hstep_ok
          apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4000#64) img hinv2
          refine SepWP.mono hstep_ok ?_
          rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx24f, hx22f, _, _, hx19f, hx21f, hx23f, hx26f, _, hx28f, hvregsf, hQf⟩ hinvf
          exact SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr2_0, hspf, hinvf,
            hx19f.trans (hx19_2.trans hx19_1), hx22f, hx23f.trans (hx23_2.trans hx23_1),
            hx24f, hx26f.trans (hx26_2.trans hx26_1), hx28f.trans (hx28_2.trans hx28_1),
            Or.inl (hx21f.trans (hx21_2.trans (hx21_1.trans hx21_none))),
            hvregsf.trans hvregs2_0,
            Entails.trans hQf (Entails.of_eq (by ac_rfl))⟩
        | some es =>
          have hpull : ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 (some es) ∗
                memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
                memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
                memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
                chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) ⊢
              ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗
              (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
                optEpochSecretRegSlotAt A s.sp x21 x27 (some es) ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
                memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
                memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
                memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
                chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) :=
            Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (optEpochSecretRegSlotAt_some_ne A s.sp x21 x27 es)))) (Entails.of_eq (by ac_rfl))
          refine SepWPp.weaken_pre hpull ?_; apply pure_elim_focus_b1 (x21 ≠ LibsignalTripleRatchetRepr.noneCap); intro hx21_ne
          refine step_panic_key_without_chain_317d8 img ext hinv2 hpc2 hrun2 (by rw [hx21_2, hx21_1]; exact hx21_ne) fun sf htr_f => ?_
          exact hφ sf (Or.inl ⟨by rw [heq_ph]; rfl, htr_f.trans htr2_0⟩)
  | some pb =>
    have hx23_ne : x23 ≠ LibsignalTripleRatchetRepr.noneCap := fun h => by have := hx23_none.mp h; contradiction
    have hz : s.pstate.z = false := by rw [hpstate]; exact addsPState64_z_false_of_ne_noneCap hx23_ne
    dsimp only [ProtoRepr.optChainPBAt]; rw [memRegion_590_88_eq_80_8 s.sp]
    have hpre_pb := step_pre_from_pb_314d8 (A := A) s pb
      (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        memRegion (s.sp + 0x5e0#64) 8 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
        memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      hpc hrun hz (by rw [hx23]; exact hx23_ne) hsp_align
    apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 172860#64) img hinv
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hpre_pb ?_)
    rintro s1 P1 hpc1 hrun1 ⟨_, htr1, hsp1, hx0_1, hx8_1, hx30_1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hvregs1, hP1⟩ hinv1
    rw [hx23] at hP1; refine SepWPp.weaken_pre hP1 ?_; apply SepWPp.exists_elim; intro gPb
    have hcall_pb : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 172860#64)
        ((chainFromPbSpecX A).inImage img) := by rw [spqrSend_chainFromPb_addr]; exact hfrom_pb
    have htr1_0 : s1.trace = s0.trace := htr1.trans htr
    refine call_inImage_calleeStack_anyPanic (s.sp) chainFromPbStackX (by decide)
      (x := ⟨s.sp + 0x1260#64, s.sp + 0x590#64, gPb, pb⟩)
      (T_pre := memRegion (s.sp + 0x1260#64) 88 ∗ chainPBAt A gPb (s.sp + 0x590#64) pb ∗ A.pool)
      (T_post := fun _ => chainResultAt A (s.sp + 0x1260#64) (Chain.fromPb pb) ∗ memRegion (s.sp + 0x590#64) 80 ∗ A.pool)
      (F := chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x5e0#64) 8 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
      hcall_pb hinv1 hpc1 hrun1 hsp1 hsp_align hx30_1 (by dsimp only [chainFromPbSpecX]; ac_rfl)
      (And.intro hx8_1 hx0_1) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun sm ⟨halloc, hpref⟩ => hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr1_0] at halloc, by rwa [htr1_0] at hpref⟩))
      (fun _ => by dsimp only [chainFromPbSpecX]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hx19_2 _ hx21_2 hx22_2 hx23_2 _ hx25_2 hx26_2 hx27_2 hx28_2 hvregs2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
    have htr2_0 : s2.trace = s0.trace := htr2.trans htr1_0
    have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
    have hx19_20 : s2.readReg64 .x19 = ret := hx19_2.trans (hx19_1.trans hx19); have hx21_20 : s2.readReg64 .x21 = x21 := hx21_2.trans (hx21_1.trans hx21)
    have hx22_20 : s2.readReg64 .x22 = msgEpoch := hx22_2.trans (hx22_1.trans hx22); have hx23_20 : s2.readReg64 .x23 = x23 := hx23_2.trans (hx23_1.trans hx23)
    have hx25_20 : s2.readReg64 .x25 = s2.sp + 0x550#64 := by rw [hsp2]; exact hx25_2.trans (hx25_1.trans hx25)
    have hx26_20 : s2.readReg64 .x26 = s2.sp + 0x1260#64 := by rw [hsp2]; exact hx26_2.trans (hx26_1.trans hx26)
    have hx27_20 : s2.readReg64 .x27 = x27 := hx27_2.trans (hx27_1.trans hx27)
    have hx28_20 : s2.readReg64 .x28 = s2.sp + 0x1060#64 := by rw [hsp2]; exact hx28_2.trans (hx28_1.trans hx28)
    cases hfpb : Chain.fromPb pb with
    | error err =>
      have heq_ph : sendChainPhase hkdf (some pb) vn key msgEpoch = .error (.err err) := by
        unfold sendChainPhase sendResolveChain; simp [hfpb, SpqrApiResult.ofError]; rfl
      rw [heq_ph]; dsimp only [chainResultAt]; rw [memRegion_1060_80_eq_24_56 s.sp]
      have hstep := step_from_pb_err_31510_to_31a3c hb hdealloc hdrop_states s2 ret x21 x27 x23 err st1 key
        (memRegion (s.sp + 0x590#64) 80 ∗ memRegion (s.sp + 0x5e0#64) 8 ∗ chainOrigSlotAt s.sp x23 ∗
          ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗ memRegion (s.sp + 0x1078#64) 56 ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
        hpc2 hrun2 hx19_20 hx21_20 hx23_20 hx26_20 hx27_20 hsp2_align
      rw [hsp2] at hstep
      apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
      rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
      refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr2_0, hspf, hinvf, hx23f, hvregsf.trans hvregs2_0, ?_⟩
      rw [memRegion_590_88_eq_80_8 s.sp, memRegion_1060_80_eq_24_56 s.sp]; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))
    | ok c0 =>
      have hres : sendResolveChain hkdf (some pb) vn = .ok (some c0) := by unfold sendResolveChain; simp [hfpb, SpqrApiResult.ofError]
      have heq_ph : sendChainPhase hkdf (some pb) vn key msgEpoch = sendStepChain hkdf (some c0) key msgEpoch := by unfold sendChainPhase; rw [hres]; rfl
      have hc0_len : c0.links.length ≤ 2 ^ 54 :=
        Nat.le_trans (chain_links_length_le_rawChain c0) (Nat.le_trans (sendResolveChain_raw_le hkdf (some pb) vn hres) hchain_raw)
      rw [heq_ph, sendChainPost_congr_frame A img s0 s.sp ret x23 st1
        (Fr2 := memRegion (s.sp + 0x1bc0#64) 16 ∗ (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)) (by ac_rfl)]
      dsimp only [chainResultAt]; rw [memRegion_1060_80_eq_24_56 s.sp]
      have hstep_ok := step_post_from_pb_ok_31510 (A := A) s2 c0
        (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x1078#64) 56 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        hpc2 hrun2 hx25_20 hx26_20 hsp2_align
      rw [hsp2] at hstep_ok
      apply of_sepWP_inImage_b1 (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3420#64) img hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by rw [memRegion_590_88_eq_80_8 s.sp]; ac_rfl)) (SepWP.mono hstep_ok ?_)
      rintro s3 P3 hpc3 hrun3 ⟨_, htr3, hsp3, hpst3, hx20_3, hx19_3, hx21_3, hx22_3, hx23_3, _, _, hx26_3, hx27_3, hx28_3, hvregs3, hP3⟩ hinv3
      have hstep_5b8 := step_chain_5b8_to_7fc img hkdf hb hdealloc hdrop_slice hdrop_states hadd_epoch hsend_key hinto_pb
        s0 s3 ret x21 x27 x23 c0 hc0_len key msgEpoch st1
        (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)
        Fr φ_out hinv3 hpc3 hrun3 (htr3.trans htr2_0) (by rw [hx21_20] at hpst3; exact hpst3)
        (hx19_3.trans hx19_20) (hx21_3.trans hx21_20) (hx22_3.trans hx22_20) (hx23_3.trans hx23_20)
        (by rw [hsp3, ← hsp2]; exact hx26_3.trans hx26_20) (hx27_3.trans hx27_20)
        (by rw [hsp3, ← hsp2]; exact hx28_3.trans hx28_20)
        (flag_of_csinc_315b8 (hx21_3.trans hx21_20) (by rw [hx21_20] at hx20_3; exact hx20_3))
        (by rw [hsp3]; exact hsp_align) (by rwa [heq_ph] at hφ) (hvregs3.trans hvregs2_0)
      rw [hsp3, memRegion_1060_80_eq_24_56 s.sp] at hstep_5b8; exact SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (by ac_rfl))) hstep_5b8

end CryptoVerification.SpqrV1.Top.Send
