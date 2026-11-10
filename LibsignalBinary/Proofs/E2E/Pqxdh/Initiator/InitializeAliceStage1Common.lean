/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceDecode -- shake: keep

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFill_ok_at_tripleRatchet
  rngFillAfter0Spec)
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore
@[simp, arm64_norm] abbrev calculateAgreementStack : Nat := ResponderCore.calculateAgreementStack
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
ls_attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  CryptoVerification.libsignalSessionCode_fnOff_0x3e6e0
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memmove")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_fmt")
  (ls_stub% "<usize as core::fmt::Display>::fmt")
  (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "libsignal_session_rng_fill")
  (ls_stub% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
@[simp, arm64_norm] abbrev initializeAliceSessionSym : String :=
    "libsignal_protocol::ratchet::initialize_alice_session::<libsignal_pqxdh_e2e::PqxdhRng>"
@[simp, arm64_norm]
abbrev kyberEncapsStub : String := "libcrux_ml_kem::mlkem1024::kyber::encapsulate"
structure KyberEncapsCall where
  pkPtr    : BitVec 64
  pk1568   : Bytes
  coinsPtr : BitVec 64
  coins32  : Bytes
  outPtr   : BitVec 64
def kyberEncapsOutBytes (P : Primitives) (pk coins : Bytes) : Bytes :=
    match P.kemEncaps pk coins with
  | some (ss, ct) => ct ++ ss
  | none          => []
def kyberEncapsStubSpec (P : Primitives) : Spec KyberEncapsCall where
  pre := fun g s => ⌜s.readReg64 .x0 = g.pkPtr ∧ s.readReg64 .x1 = g.coinsPtr ∧ s.readReg64 .x8 =
    g.outPtr ∧ g.pk1568.length = 1568 ∧ g.coins32.length = 32 ∧
      (P.kemEncaps g.pk1568 g.coins32).isSome⌝ ∗ (g.pkPtr ↦ₛ bytesToBv8 g.pk1568) ∗
        (g.coinsPtr ↦ₛ bytesToBv8 g.coins32) ∗ memRegion g.outPtr 1600 ∗ stackAt s.sp pqxdhHookStack
  post := fun g s0 sf => ⌜sf.trace = s0.trace⌝ ∗ (g.pkPtr ↦ₛ bytesToBv8 g.pk1568) ∗
      (g.coinsPtr ↦ₛ bytesToBv8 g.coins32) ∗
      (g.outPtr ↦ₛ fitBv8 1600 (kyberEncapsOutBytes P g.pk1568 g.coins32)) ∗
        stackAt s0.sp pqxdhHookStack
theorem kyberEncapsStub_ok_at {P : Primitives} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hEncaps : HookSat absHooks kyberEncapsStub
      (kyberEncapsStubSpec P)) {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff kyberEncapsStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k)
      (kyberEncapsStubSpec P) := hook_ok_at (hname := kyberEncapsStub) rfl hk
        (by rw [(ls_stub% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")]; decide)
    (fun H =>
      by rw [(ls_stub% "libcrux_ml_kem::mlkem1024::kyber::encapsulate")]; exact (ls_hook% "libcrux_ml_kem::mlkem1024::kyber::encapsulate") H)
      (by decide +kernel) (by
      rcases hEncaps with ⟨fn, hfn, hok⟩
      exact ⟨fn, by rw [← hfn]; rfl, hok⟩)
def PanicOomProp (s0 sf : State) (Pf : SepProp) : Prop := ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)
private theorem of_sepWP_frozen_ia {prog : Program} {img : Obj.Image} (mid : BitVec 64) {ret :
    BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} (hF : img.FrozenLoaded s)
    (h : SepWP prog mid s P (fun sm Pm => img.FrozenLoaded sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  have h1p : SepWPp prog mid s P (fun sm Pm =>
    img.FrozenLoaded sm → SepWPp prog ret sm Pm Q Qp) Qp := SepWPp.of_sepWP_ret h
  unfold SepWPp at h1p ⊢; intro R hm hL
  rcases h1p R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hnext⟩ | hpan⟩
  · rcases hnext (hF.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', hout⟩; exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩
theorem SepWPp.bind_frozen {prog : Program} {img : Obj.Image} {mid target : BitVec 64} {s : State}
    {P : SepProp} {Qm post Qp : State → SepProp → Prop} (hF : img.FrozenLoaded s) (h1 : SepWPp prog
      mid s P Qm Qp) (h2 : ∀ sm Pm, sm.pc = mid → sm.status =
      .Running → img.FrozenLoaded sm → Qm sm Pm → SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢; intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen) hQ R hmm (hsteps.codeLoaded
      hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩
theorem SepWPp.call_frame_frozen {α : Type} {prog : Program} {img : Obj.Image} {ret entry ret_pc :
    BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop} {P T F : SepProp} {Q Qp : State →
    SepProp → Prop} (hF : img.FrozenLoaded s) (hcall : subroutine_ok prog entry spec) (hpc : s.pc =
    entry) (hrun : s.status = .Running) (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr =
      ret_pc) (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F) (hexit : ∀ sf code R',
    sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False) (hpanic : ∀ sf,
    sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F)) (hnext : ∀ sf : State, sf.pc =
      ret_pc → sf.status = .Running → sf.sp =
        s.sp → CalleeSavedPreserved s sf → img.FrozenLoaded sf → SepWPp prog ret sf (spec.post x s
        sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.bind_frozen (mid := ret_pc)
    (Qm := fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = (spec.post x s sm ∗ F)) hF
    (ProofLib.SepWPp.call_frame (x := x) hcall hpc hrun hsp hlr hspec hφ hP hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' _ hoom_post => by
        rw [hoom sf] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim))
    (fun sm _ hpcm hrunm hFm ⟨hspm, hcsm, hPm⟩ => hPm ▸ hnext sm hpcm hrunm hspm hcsm hFm)
def pqxdhCalculateAgreementFrozenSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) : Spec
    (BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) :=
      { pqxdhCalculateAgreementBaseSpec P A img with
    pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
      ⌜img.FrozenLoaded s ∧ s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 =
        ret ∧ s.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
        (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt sp calculateAgreementStack }
theorem calculateAgreement_frozen_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (himg : Obj.Loads
    libsignalSessionImage img) (hag : PqxdhCalculateAgreementOk_trap P A img C absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks) ((trTrapProgAt img.base C
      absHooks).fnAddr calculateAgreementSym) (pqxdhCalculateAgreementFrozenSpec P A img) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp
  dsimp only [pqxdhCalculateAgreementFrozenSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hF, hx⟩, hpre⟩
  have hpre' : s0.mem ⊨ (pqxdhCalculateAgreementSpec P A img).pre (ourA, our, theirA, their, ret,
    sp) s0 ∗ R := by
    dsimp only [pqxdhCalculateAgreementSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx, ?_⟩; have hro := rodata_0x7ff6a himg hF.roData hpre
    refine Satisfies.mono (Entails.of_eq ?_) hro; ac_rfl
  refine (Arm64.subroutine_ok.to_outcome hag (ourA, our, theirA, their, ret, sp) R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only [pqxdhCalculateAgreementSpec] at hq
    have hq' : sf.mem ⊨ ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
        ((pqxdhCalculateAgreementFrozenSpec P A img).post (ourA, our, theirA, their, ret,
        sp) s0 sf ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hq
      dsimp only [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec]; ac_rfl
    exact Satisfies.of_sep_right hq'
  · exact Or.inr hpan
theorem calculateAgreement_frozen_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {absHooks : String → Option (State → State)} (himg : Obj.Loads
    libsignalSessionImage img) (hag : PqxdhCalculateAgreementOk P A img C ctl absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr calculateAgreementSym) (pqxdhCalculateAgreementFrozenSpec P A img) := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp
  dsimp only [pqxdhCalculateAgreementFrozenSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hF, hx⟩, hpre⟩
  have hpre' : s0.mem ⊨ (pqxdhCalculateAgreementSpec P A img).pre (ourA, our, theirA, their, ret,
    sp) s0 ∗ R := by
    dsimp only [pqxdhCalculateAgreementSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx, ?_⟩; have hro := rodata_0x7ff6a himg hF.roData hpre
    refine Satisfies.mono (Entails.of_eq ?_) hro; ac_rfl
  refine (Arm64.subroutine_ok.to_outcome hag (ourA, our, theirA, their, ret, sp) R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only [pqxdhCalculateAgreementSpec] at hq
    have hq' : sf.mem ⊨ ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
        ((pqxdhCalculateAgreementFrozenSpec P A img).post (ourA, our, theirA, their, ret,
        sp) s0 sf ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hq
      dsimp only [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec]; ac_rfl
    exact Satisfies.of_sep_right hq'
  · exact Or.inr hpan
theorem calcErr_entails_at_add3648 (fsp : BitVec 64) : ((fsp + 3648#64) ↦₆₄ 1#64) ∗ (∃∗
    hi : BitVec 56, (fsp + 3656#64) ↦₆₄ (hi ++ 3#8)) ∗ (∃∗ u2 : BitVec 64, (fsp + 3664#64) ↦₆₄ u2) ⊢
      ∃∗ u2 : BitVec 64, ∃∗ hi : BitVec 56, ((fsp + 3648#64) ↦₆₄ 1#64) ∗ ((fsp + 3656#64) ↦₆₄ (hi ++
        3#8)) ∗ ((fsp + 3664#64) ↦₆₄ u2) := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.refl _
theorem boxSliceU8_32_entails_at_add3648 (A : RustAlloc) (fsp : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 32) : ((fsp + 3648#64) ↦₆₄ 0#64) ∗ boxSliceU8 A (fsp + 3656#64) bs ⊢ ∃∗
      dh_ptr : BitVec 64, ((fsp + 3648#64) ↦₆₄ 0#64) ∗ ((fsp + 3656#64) ↦₆₄ dh_ptr) ∗ ((fsp +
        3664#64) ↦₆₄ 32#64) ∗ (dh_ptr ↦ₛ bs) ∗ A.live dh_ptr 32 1 := by
  refine Entails.trans (sepConj_mono_right (boxSliceU8_32_entails A (fsp + 3656#64) bs hbs)) ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun dh_ptr => Entails.sepExists_right dh_ptr ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)
theorem stackAt_calc_split_alloc (fsp : BitVec 64) : stackAt fsp calculateAgreementStack =
    stackAt fsp allocHookStack ∗ memRegion (fsp - 4256#64) 160 := by
  have h1 := stackAt_split_top fsp 160 allocHookStack (by decide)
  have h2 : (160 + allocHookStack : Nat) = calculateAgreementStack := by decide
  have h3 : BitVec.ofNat 64 (160 + allocHookStack) = 4256#64 := rfl; rw [h3] at h1
  rw [← h2, h1, sepConj_comm]
theorem cells3_add3648_to_memRegion24 (sp w0 w1 w2 : BitVec 64) : ((sp + 3648#64) ↦₆₄ w0) ∗ ((sp +
    3656#64) ↦₆₄ w1) ∗ ((sp + 3664#64) ↦₆₄ w2) ⊢ memRegion (sp + 3648#64) 24 := by
  rw [(memRegion_cells (sp + 3648#64) 3 (by decide) : memRegion (sp + 3648#64) 24 = cells (sp +
    3648#64) 3)]; have h := cells_3_merge (sp + 3648#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h; exact h
theorem allowPanic_hag_base {P : Primitives} {A : RustAlloc} {img : Obj.Image} {s0 s : State} {F :
    SepProp} {x : BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64} (htr : s.trace =
    s0.trace) : ∀ sf, sf.status =
      .Panicked → PanicOomProp s0 sf ((pqxdhCalculateAgreementFrozenSpec P A img).onPanic x s sf ∗
      F) := by
  intro sf _ R hm
  dsimp only [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec, rustPanicOnOom]
    at hm
  exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
theorem SepWPp_call_hag_alice {prog : Program} {ret : BitVec 64} {s : State} {P_pre : SepProp} {Q :
    State → SepProp → Prop} {s0 : State} {F : SepProp} {call_pc ret_pc fsp : BitVec 64} {P :
    Primitives} {A : RustAlloc} {img : Obj.Image} (hWF : StructuralPrims P) (hag : subroutine_ok
    prog call_pc (pqxdhCalculateAgreementFrozenSpec P A img)) (hF : img.FrozenLoaded s) (ourA :
    BitVec 64) (our : Bytes) (theirA : BitVec 64) (their : Bytes) (hpc : s.pc =
      call_pc) (hrun : s.status = .Running) (hfsp_align : fsp &&& 15#64 == 0#64) (hsp_eq : s.sp =
    fsp) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hx : s.readReg64 Reg.x0 =
    ourA ∧ s.readReg64 Reg.x1 = theirA ∧ s.readReg64 Reg.x8 = fsp + 3648#64 ∧ s.sp = fsp ∧
      our.length = 32 ∧ their.length = 32) (hP : P_pre = (((ourA ↦ₛ bytesToBv8 our) ∗
    (theirA ↦ₛ bytesToBv8 their) ∗ memRegion (fsp + 3648#64) 24 ∗ A.pool ∗
      stackAt fsp calculateAgreementStack) ∗ F)) (herr : P.x25519 our their =
      List.replicate 32 0 → ∀ (sf : State) (hi : BitVec 56) (u2 : BitVec 64), sf.pc =
      ret_pc → sf.status = .Running → sf.sp = fsp → CalleeSavedPreserved s sf → sf.trace =
        s0.trace → img.FrozenLoaded sf → SepWPp prog ret sf (((fsp + 3648#64) ↦₆₄ 1#64) ∗ ((fsp +
          3656#64) ↦₆₄ (hi ++ 3#8)) ∗ ((fsp + 3664#64) ↦₆₄ u2) ∗ (ourA ↦ₛ bytesToBv8 our) ∗
          (theirA ↦ₛ bytesToBv8 their) ∗ A.pool ∗ stackAt fsp calculateAgreementStack ∗
            F) Q (PanicOomProp s0)) (hok : P.x25519 our their ≠ List.replicate 32 0 →
      ∀ (sf : State) (dh_ptr : BitVec 64), sf.pc = ret_pc → sf.status = .Running → sf.sp = fsp →
        CalleeSavedPreserved s sf → sf.trace =
        s0.trace → img.FrozenLoaded sf → SepWPp prog ret sf (((fsp + 3648#64) ↦₆₄ 0#64) ∗ ((fsp +
        3656#64) ↦₆₄ dh_ptr) ∗ ((fsp + 3664#64) ↦₆₄ 32#64) ∗
            (dh_ptr ↦ₛ bytesToBv8 (P.x25519 our their)) ∗ A.live dh_ptr 32 1 ∗
            (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗ A.pool ∗
            stackAt fsp calculateAgreementStack ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P_pre Q (PanicOomProp s0) := by
  have hsp_align_s : s.spAligned = true := by unfold State.spAligned; rw [hsp_eq]; exact hfsp_align
  refine SepWPp.call_frame_frozen (x := (ourA, our, theirA, their, fsp + 3648#64, fsp))
    hF hag hpc hrun hsp_align_s hlr rfl ⟨hF, hx⟩ hP (fun _ _ _ _ hm =>
      allowPanic_not_exited hm) (allowPanic_hag_base htr)
    (fun sf hpc_f hrun_f hsp_f hcs_f hF_f => ?_)
  dsimp only [pqxdhCalculateAgreementFrozenSpec, pqxdhCalculateAgreementBaseSpec,
    pqxdhCalculateAgreementResultAt]
  rw [htr, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_; by_cases hdh : P.x25519 our their = List.replicate 32 0
  · simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.fold (calcErr_entails_at_add3648 fsp) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun u2 => ?_; rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun hi => ?_; simp only [sepConj_assoc]
    exact herr hdh sf hi u2 hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f
  · have hdh_bv_len : (bytesToBv8 (P.x25519 our their)).length = 32 := by
      simp [bytesToBv8, hWF.x25519_len our their]
    simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.fold (boxSliceU8_32_entails_at_add3648 A fsp hdh_bv_len) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun dh_ptr => ?_
    simp only [sepConj_assoc]
    exact hok hdh sf dh_ptr hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f
def aliceOpkParamAt (a : BitVec 64) (opk? : Option (UInt32 × Bytes)) : SepProp := match opk? with
  | none => (a ↦₈ 0#8) ∗ memRegion (a + 1#64) 32
  | some (_, opkPk) => (a ↦₈ 1#8) ∗ ((a + 1#64) ↦ₛ bytesToBv8 opkPk)
def dhSecretsPrefix (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) : Bytes := match dh4? with
  | none     => F_X25519 ++ dh1 ++ dh2 ++ dh3
  | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4
theorem dhSecretsPrefix_append_ss (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (ss : Bytes) :
    dhSecretsPrefix dh1 dh2 dh3 dh4? ++ ss = buildSecrets dh1 dh2 dh3 dh4? ss := by
  cases dh4? <;> rfl
def dhSecretsRemAt (secretsPtr : BitVec 64) (opkB? : Option (UInt32 × Bytes)) : SepProp :=
    match opkB? with
  | none   => memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32
  | some _ => memRegion (secretsPtr + 160#64) 32
def dhSecretsLen (opkB? : Option (UInt32 × Bytes)) : BitVec 64 := match opkB? with
  | none   => 128#64
  | some _ => 160#64
theorem memRegion32_480_eq (fsp : BitVec 64) : memRegion (fsp + 480#64) 32 = ∃∗ u0 : BitVec 64, ∃∗
    u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ((fsp + 480#64) ↦₆₄ u0) ∗ ((fsp +
        488#64) ↦₆₄ u1) ∗ ((fsp + 496#64) ↦₆₄ u2) ∗ ((fsp + 504#64) ↦₆₄ u3) := by
  rw [(memRegion_cells (fsp + 480#64) 4 (by decide) : memRegion (fsp + 480#64) 32 = cells (fsp +
    480#64) 4)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem memRegion24_456_eq (fsp : BitVec 64) : memRegion (fsp + 456#64) 24 = ∃∗ v_456 : BitVec 64,
    ∃∗ v_464 : BitVec 64, ∃∗ v_472 : BitVec 64, ((fsp + 456#64) ↦₆₄ v_456) ∗ ((fsp +
      464#64) ↦₆₄ v_464) ∗ ((fsp + 472#64) ↦₆₄ v_472) := by
  rw [(memRegion_cells (fsp + 456#64) 3 (by decide) : memRegion (fsp + 456#64) 24 = cells (fsp +
    456#64) 3)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem cells4_480_entails_memRegion32 (fsp u0 u1 u2 u3 : BitVec 64) : ((fsp + 480#64) ↦₆₄ u0) ∗
    ((fsp + 488#64) ↦₆₄ u1) ∗ ((fsp + 496#64) ↦₆₄ u2) ∗ ((fsp +
      504#64) ↦₆₄ u3) ⊢ memRegion (fsp + 480#64) 32 := by
  rw [memRegion32_480_eq]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
    (Entails.sepExists_right u3 (Entails.refl _))))
theorem ek_480_entails_memRegion32 (fsp : BitVec 64) (inp : InitiateInput) (hsz :
    WellSizedInitiateInput inp) :
    ((fsp + 480#64) ↦ₛ bytesToBv8 inp.ekASk) ⊢ memRegion (fsp + 480#64) 32 := by
  rcases hsz with ⟨_, _, hekSk_len, _, _, _, _, _, _, _, _, _⟩
  have hlen : (bytesToBv8 inp.ekASk).length = 32 := (by simp [bytesToBv8, hekSk_len]); rw [← hlen]
  exact pointsToBytes_entails_memRegion _ _
theorem cells3_456_entails_memRegion24 (fsp v0 v1 v2 : BitVec 64) : ((fsp + 456#64) ↦₆₄ v0) ∗
    ((fsp + 464#64) ↦₆₄ v1) ∗ ((fsp + 472#64) ↦₆₄ v2) ⊢ memRegion (fsp + 456#64) 24 := by
  rw [memRegion24_456_eq]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.refl _)))
def mkWord32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0
def word32Bytes (u : BitVec 32) : List (BitVec 8) :=
    [u.extractLsb' 0 8, u.extractLsb' 8 8, u.extractLsb' 16 8, u.extractLsb' 24 8]
def words32Bytes (us : List (BitVec 32)) : List (BitVec 8) := us.flatMap word32Bytes
def word32At (bs : List (BitVec 8)) (off : Nat) : BitVec 32 :=
  mkWord32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
def kemCoinBytesOf128 (rng128 : List (BitVec 8)) : List (BitVec 8) :=
    [rng128.getD 0 0#8, rng128.getD 4 0#8, rng128.getD 8 0#8, rng128.getD 12 0#8,
   rng128.getD 16 0#8, rng128.getD 20 0#8, rng128.getD 24 0#8, rng128.getD 28 0#8,
   rng128.getD 32 0#8, rng128.getD 36 0#8, rng128.getD 40 0#8, rng128.getD 44 0#8,
   rng128.getD 48 0#8, rng128.getD 52 0#8, rng128.getD 56 0#8, rng128.getD 60 0#8,
   rng128.getD 64 0#8, rng128.getD 68 0#8, rng128.getD 72 0#8, rng128.getD 76 0#8,
   rng128.getD 80 0#8, rng128.getD 84 0#8, rng128.getD 88 0#8, rng128.getD 92 0#8,
   rng128.getD 96 0#8, rng128.getD 100 0#8, rng128.getD 104 0#8, rng128.getD 108 0#8,
   rng128.getD 112 0#8, rng128.getD 116 0#8, rng128.getD 120 0#8, rng128.getD 124 0#8]
@[local simp, local arm64_norm] theorem setWidth8_bv32 (u : BitVec 32) :
    u.setWidth 8 = u.extractLsb' 0 8 := by bv_bits
@[local simp, local arm64_norm] theorem extractLsb8_zero32_append (u : BitVec 32) :
    (0#32 ++ u).extractLsb' 0 8 = u.extractLsb' 0 8 := by bv_bits
@[local simp, local arm64_norm] theorem setWidth8_zero32_append (u : BitVec 32) :
    (0#32 ++ u).setWidth 8 = u.extractLsb' 0 8 := by bv_bits
@[local simp, local arm64_norm] theorem extractLsb8_zeroExtend64_bv32 (u : BitVec 32) :
    (BitVec.zeroExtend 64 u).extractLsb' 0 8 = u.extractLsb' 0 8 := by bv_bits
@[local simp, local arm64_norm] theorem setWidth8_zeroExtend64_bv32 (u : BitVec 32) :
    (BitVec.zeroExtend 64 u).setWidth 8 = u.extractLsb' 0 8 := by bv_bits
@[local simp, local arm64_norm] theorem setWidth32_zeroExtend64_bv32 (u : BitVec 32) :
    (BitVec.zeroExtend 64 u).setWidth 32 = u := by bv_bits
@[local simp, local arm64_norm] theorem extractLsb32_zeroExtend64_bv32 (u : BitVec 32) :
    (BitVec.zeroExtend 64 u).extractLsb' 0 32 = u := by bv_bits
@[simp] theorem extractLsb0_mkWord32 (b0 b1 b2 b3 : BitVec 8) :
    (mkWord32 b0 b1 b2 b3).extractLsb' 0 8 = b0 := by unfold mkWord32; bv_bits
@[simp] theorem extractLsb8_mkWord32 (b0 b1 b2 b3 : BitVec 8) :
    (mkWord32 b0 b1 b2 b3).extractLsb' 8 8 = b1 := by unfold mkWord32; bv_bits
@[simp] theorem extractLsb16_mkWord32 (b0 b1 b2 b3 : BitVec 8) :
    (mkWord32 b0 b1 b2 b3).extractLsb' 16 8 = b2 := by unfold mkWord32; bv_bits
@[simp] theorem extractLsb24_mkWord32 (b0 b1 b2 b3 : BitVec 8) :
    (mkWord32 b0 b1 b2 b3).extractLsb' 24 8 = b3 := by unfold mkWord32; bv_bits
@[simp] theorem extractLsb0_word32At (bs : List (BitVec 8)) (off : Nat) :
    (word32At bs off).extractLsb' 0 8 = bs.getD off 0#8 := by simp [word32At]
theorem pointsTo32_eq_pointsToBytes_word32Bytes (p : BitVec 64) (u : BitVec 32) :
    (p ↦₃₂ u) = (p ↦ₛ word32Bytes u) := by
  unfold Arm64.pointsTo32 word32Bytes
  rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
    pointsToBytes_nil]; simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
theorem pointsTo32_entails_memRegion4 (p : BitVec 64) (u : BitVec 32) :
    (p ↦₃₂ u) ⊢ memRegion p 4 := by
  rw [pointsTo32_eq_pointsToBytes_word32Bytes]
  exact pointsToBytes_entails_memRegion p (word32Bytes u)
theorem tapeAfter_word32Bytes_four (ctl cur : BitVec 64) (u : BitVec 32) (rest : List (BitVec 8)) :
    tapeAfter ctl cur (word32Bytes u ++ rest) 4 = (cur ↦₃₂ u) ∗ tapeAfter ctl (cur + 4#64) rest 0 :=
      by
  unfold tapeAfter
  have hlen : (word32Bytes u ++ rest).length - 4 = rest.length := by simp [word32Bytes]
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have hpts : (cur ↦ₛ (word32Bytes u ++ rest)) = (cur ↦₃₂ u) ∗ ((cur + 4#64) ↦ₛ rest) := by
    rw [pointsToBytes_append, show (word32Bytes u).length = 4 from rfl, h4, ←
      pointsTo32_eq_pointsToBytes_word32Bytes]
  rw [hlen, h4, hpts, BitVec.add_zero, Nat.sub_zero]; ac_rfl
def sp2Rng4Spec (ctl : BitVec 64) :
    Spec (BitVec 64 × BitVec 32 × BitVec 64 × BitVec 32 × List (BitVec 8)) where
  pre := fun (destPtr, w, cur, u, rest) s => ⌜s.readReg64 .x0 = destPtr ∧ s.readReg64 .x1 = 4#64⌝ ∗
    (destPtr ↦₃₂ w) ∗ tapeAfter ctl cur (word32Bytes u ++ rest) 0
  post := fun (destPtr, _, cur, u, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (destPtr ↦₃₂ u) ∗ (cur ↦₃₂ u) ∗ tapeAfter ctl (cur + 4#64) rest 0
theorem sp2Rng4_ok_at {img : Obj.Image} {C : Crypto} {ctl : BitVec 64} {absHooks : String → Option
    (State → State)} {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "libsignal_session_rng_fill" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks) ((tripleRatchetProgAt img.base C ctl
      absHooks).fnAddr name + BitVec.ofNat 64 k)
      (sp2Rng4Spec ctl) := by
  have hrng := rngFill_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl) (abs :=
    absHooks) (name := name) (k := k) hk
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro ⟨destPtr, w, cur, u, rest⟩ R s0 hpc hrun hpre hsp; dsimp only [sp2Rng4Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  have hx1_nat : (s0.readReg64 .x1).toNat = 4 := by rw [hx1]; rfl
  have hpre' : s0.mem ⊨ (rngFillAfter0Spec ctl).pre (destPtr, 4, cur, word32Bytes u ++ rest) s0 ∗
    R := by
    dsimp only [rngFillAfter0Spec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left (pointsTo32_entails_memRegion4
      destPtr w))) hpre
  refine (Arm64.subroutine_ok.to_outcome hrng (destPtr, 4, cur, word32Bytes u ++ rest) R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only [rngFillAfter0Spec] at hq
    have htake : ((word32Bytes u ++ rest) ++ List.replicate 4 0#8).take 4 = word32Bytes u := by
      rw [List.append_assoc, List.take_append_of_le_length (by simp [word32Bytes]),
        List.take_of_length_le (by simp [word32Bytes])]
    have hmin : min 4 (word32Bytes u ++ rest).length = 4 := by simp [word32Bytes]
    rw [htake, hmin, ← pointsTo32_eq_pointsToBytes_word32Bytes destPtr u,
      tapeAfter_word32Bytes_four ctl cur u rest] at hq; dsimp only [sp2Rng4Spec]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · exact Or.inr hpan
theorem words32Bytes_cons (u : BitVec 32) (us : List (BitVec 32)) : words32Bytes (u :: us) =
    word32Bytes u ++ words32Bytes us := rfl
theorem words32Bytes_nil :
    words32Bytes [] = [] := rfl
theorem pointsToBytes_word32Bytes_append (base : BitVec 64) (u : BitVec 32) (bs : List (BitVec 8)) :
    (base ↦ₛ (word32Bytes u ++ bs)) = (base ↦₃₂ u) ∗ ((base + 4#64) ↦ₛ bs) := by
  rw [pointsToBytes_append, show (word32Bytes u).length = 4 from rfl, ←
    pointsTo32_eq_pointsToBytes_word32Bytes]
theorem pointsToBytes_words32Bytes_cons (base : BitVec 64) (u : BitVec 32) (us : List (BitVec 32)) :
    (base ↦ₛ words32Bytes (u :: us)) = (base ↦₃₂ u) ∗ ((base + 4#64) ↦ₛ words32Bytes us) :=
      pointsToBytes_word32Bytes_append base u (words32Bytes us)
theorem pointsToBytes_words32Bytes_nil (base : BitVec 64) : (base ↦ₛ words32Bytes []) = emp :=
    pointsToBytes_nil base
def rngSlots1a (fsp : BitVec 64) (w_68 w_72 w_76 w_80 w_84 w_88 w_92 : BitVec 32) : SepProp :=
    ((fsp + 68#64) ↦₃₂ w_68) ∗ ((fsp + 72#64) ↦₃₂ w_72) ∗ ((fsp + 76#64) ↦₃₂ w_76) ∗ ((fsp +
  80#64) ↦₃₂ w_80) ∗ ((fsp + 84#64) ↦₃₂ w_84) ∗ ((fsp + 88#64) ↦₃₂ w_88) ∗ ((fsp + 92#64) ↦₃₂ w_92)
def rngSlots1b (fsp : BitVec 64) (w_36 w_40 w_44 w_48 w_52 w_56 w_60 w_64 : BitVec 32) : SepProp :=
    ((fsp + 36#64) ↦₃₂ w_36) ∗ ((fsp + 40#64) ↦₃₂ w_40) ∗ ((fsp + 44#64) ↦₃₂ w_44) ∗ ((fsp +
  48#64) ↦₃₂ w_48) ∗ ((fsp + 52#64) ↦₃₂ w_52) ∗ ((fsp + 56#64) ↦₃₂ w_56) ∗ ((fsp +
    60#64) ↦₃₂ w_60) ∗ ((fsp + 64#64) ↦₃₂ w_64)
def rngSlots2a (fsp : BitVec 64) (w_4 w_8 w_12 w_16 w_20 w_24 w_28 w_32 : BitVec 32) : SepProp :=
    ((fsp + 4#64) ↦₃₂ w_4) ∗ ((fsp + 8#64) ↦₃₂ w_8) ∗ ((fsp + 12#64) ↦₃₂ w_12) ∗ ((fsp +
  16#64) ↦₃₂ w_16) ∗ ((fsp + 20#64) ↦₃₂ w_20) ∗ ((fsp + 24#64) ↦₃₂ w_24) ∗ ((fsp +
    28#64) ↦₃₂ w_28) ∗ ((fsp + 32#64) ↦₃₂ w_32)
def kemCoinSlots64 (fsp : BitVec 64) (v_2080 v_2088 v_2096 v_2104 : BitVec 64) : SepProp :=
    ((fsp + 2080#64) ↦₆₄ v_2080) ∗ ((fsp + 2088#64) ↦₆₄ v_2088) ∗ ((fsp + 2096#64) ↦₆₄ v_2096) ∗
  ((fsp + 2104#64) ↦₆₄ v_2104)
theorem pointsTo64_to_pointsTo8 (p : BitVec 64) (v : BitVec 64) : (p ↦₆₄ v) =
    (p ↦₈ v.extractLsb' 0 8) ∗ ((p + 1#64) ↦₈ v.extractLsb' 8 8) ∗ ((p +
      2#64) ↦₈ v.extractLsb' 16 8) ∗ ((p + 3#64) ↦₈ v.extractLsb' 24 8) ∗ ((p +
      4#64) ↦₈ v.extractLsb' 32 8) ∗ ((p + 5#64) ↦₈ v.extractLsb' 40 8) ∗ ((p +
        6#64) ↦₈ v.extractLsb' 48 8) ∗ ((p + 7#64) ↦₈ v.extractLsb' 56 8) := by
  unfold Arm64.pointsTo64; simp only [BitVec.add_zero]
theorem pointsTo8_32_eq_pointsToBytes_2080 (base : BitVec 64) (coinsBv : List (BitVec 8)) (u0 u1 u2
    u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28
     u29 u30 u31 : BitVec 32) (hcoins : coinsBv = [u0.extractLsb' 0 8, u1.extractLsb' 0 8,
    u2.extractLsb' 0 8, u3.extractLsb' 0 8, u4.extractLsb' 0 8, u5.extractLsb' 0 8,
      u6.extractLsb' 0 8, u7.extractLsb' 0 8, u8.extractLsb' 0 8, u9.extractLsb' 0 8,
      u10.extractLsb' 0 8, u11.extractLsb' 0 8, u12.extractLsb' 0 8, u13.extractLsb' 0 8,
      u14.extractLsb' 0 8, u15.extractLsb' 0 8, u16.extractLsb' 0 8, u17.extractLsb' 0 8,
      u18.extractLsb' 0 8, u19.extractLsb' 0 8, u20.extractLsb' 0 8, u21.extractLsb' 0 8,
      u22.extractLsb' 0 8, u23.extractLsb' 0 8, u24.extractLsb' 0 8, u25.extractLsb' 0 8,
      u26.extractLsb' 0 8, u27.extractLsb' 0 8, u28.extractLsb' 0 8, u29.extractLsb' 0 8,
      u30.extractLsb' 0 8, u31.extractLsb' 0 8]) : ((base + 2080#64) ↦₈ u0.extractLsb' 0 8) ∗
    ((base + 2081#64) ↦₈ u1.extractLsb' 0 8) ∗ ((base + 2082#64) ↦₈ u2.extractLsb' 0 8) ∗ ((base +
      2083#64) ↦₈ u3.extractLsb' 0 8) ∗ ((base + 2084#64) ↦₈ u4.extractLsb' 0 8) ∗ ((base +
    2085#64) ↦₈ u5.extractLsb' 0 8) ∗ ((base + 2086#64) ↦₈ u6.extractLsb' 0 8) ∗ ((base +
    2087#64) ↦₈ u7.extractLsb' 0 8) ∗ ((base + 2088#64) ↦₈ u8.extractLsb' 0 8) ∗ ((base +
      2089#64) ↦₈ u9.extractLsb' 0 8) ∗ ((base + 2090#64) ↦₈ u10.extractLsb' 0 8) ∗ ((base +
    2091#64) ↦₈ u11.extractLsb' 0 8) ∗ ((base + 2092#64) ↦₈ u12.extractLsb' 0 8) ∗ ((base +
    2093#64) ↦₈ u13.extractLsb' 0 8) ∗ ((base + 2094#64) ↦₈ u14.extractLsb' 0 8) ∗ ((base +
      2095#64) ↦₈ u15.extractLsb' 0 8) ∗ ((base + 2096#64) ↦₈ u16.extractLsb' 0 8) ∗ ((base +
    2097#64) ↦₈ u17.extractLsb' 0 8) ∗ ((base + 2098#64) ↦₈ u18.extractLsb' 0 8) ∗ ((base +
    2099#64) ↦₈ u19.extractLsb' 0 8) ∗ ((base + 2100#64) ↦₈ u20.extractLsb' 0 8) ∗ ((base +
      2101#64) ↦₈ u21.extractLsb' 0 8) ∗ ((base + 2102#64) ↦₈ u22.extractLsb' 0 8) ∗ ((base +
    2103#64) ↦₈ u23.extractLsb' 0 8) ∗ ((base + 2104#64) ↦₈ u24.extractLsb' 0 8) ∗ ((base +
    2105#64) ↦₈ u25.extractLsb' 0 8) ∗ ((base + 2106#64) ↦₈ u26.extractLsb' 0 8) ∗ ((base +
      2107#64) ↦₈ u27.extractLsb' 0 8) ∗ ((base + 2108#64) ↦₈ u28.extractLsb' 0 8) ∗ ((base +
    2109#64) ↦₈ u29.extractLsb' 0 8) ∗ ((base + 2110#64) ↦₈ u30.extractLsb' 0 8) ∗
    ((base + 2111#64) ↦₈ u31.extractLsb' 0 8) = ((base + 2080#64) ↦ₛ coinsBv) := by
  subst hcoins
  simp only [pointsToBytes_cons, pointsToBytes_nil, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
theorem pointsTo32_memRegion1596_merge_3648 (base : BitVec 64) (w : BitVec 32) : ((base +
    3648#64) ↦₃₂ w) ∗ memRegion (base + 3652#64) 1596 ⊢ memRegion (base + 3648#64) 1600 := by
  have h1 : (base + 3648#64) + BitVec.ofNat 64 4 = base + 3652#64 := by bv_omega
  have h2 := memRegion_split (base + 3648#64) 4 1596 (by decide); rw [h1] at h2
  rw [show (1600 : Nat) = 4 + 1596 from rfl, h2]
  exact sepConj_mono_left (pointsTo32_entails_memRegion4 (base + 3648#64) w)
theorem rngSlots_entails_memRegion92 (fsp : BitVec 64) (w_4 w_8 w_12 w_16 w_20 w_24 w_28 w_32 w_36
    w_40 w_44 w_48 w_52 w_56 w_60 w_64 w_68 w_72 w_76 w_80 w_84 w_88 w_92 : BitVec 32) : rngSlots2a
    fsp w_4 w_8 w_12 w_16 w_20 w_24 w_28 w_32 ∗
      rngSlots1b fsp w_36 w_40 w_44 w_48 w_52 w_56 w_60 w_64 ∗
    rngSlots1a fsp w_68 w_72 w_76 w_80 w_84 w_88 w_92 ⊢ memRegion (fsp + 4#64) 92 := by
  dsimp only [rngSlots2a, rngSlots1b, rngSlots1a]
  simp only [pointsTo32_eq_pointsToBytes_word32Bytes, word32Bytes]
  have h1 : ((fsp + 4#64) ↦ₛ [w_4.extractLsb' 0 8, w_4.extractLsb' 8 8, w_4.extractLsb' 16 8,
      w_4.extractLsb' 24 8]) ∗ ((fsp + 8#64) ↦ₛ [w_8.extractLsb' 0 8, w_8.extractLsb' 8 8,
    w_8.extractLsb' 16 8, w_8.extractLsb' 24 8]) ∗ ((fsp + 12#64) ↦ₛ [w_12.extractLsb' 0 8,
    w_12.extractLsb' 8 8, w_12.extractLsb' 16 8, w_12.extractLsb' 24 8]) ∗ ((fsp +
    16#64) ↦ₛ [w_16.extractLsb' 0 8, w_16.extractLsb' 8 8, w_16.extractLsb' 16 8,
      w_16.extractLsb' 24 8]) ∗ ((fsp + 20#64) ↦ₛ [w_20.extractLsb' 0 8, w_20.extractLsb' 8 8,
    w_20.extractLsb' 16 8, w_20.extractLsb' 24 8]) ∗ ((fsp + 24#64) ↦ₛ [w_24.extractLsb' 0 8,
    w_24.extractLsb' 8 8, w_24.extractLsb' 16 8, w_24.extractLsb' 24 8]) ∗ ((fsp +
    28#64) ↦ₛ [w_28.extractLsb' 0 8, w_28.extractLsb' 8 8, w_28.extractLsb' 16 8,
      w_28.extractLsb' 24 8]) ∗ ((fsp + 32#64) ↦ₛ [w_32.extractLsb' 0 8, w_32.extractLsb' 8 8,
    w_32.extractLsb' 16 8, w_32.extractLsb' 24 8]) ∗ ((fsp + 36#64) ↦ₛ [w_36.extractLsb' 0 8,
    w_36.extractLsb' 8 8, w_36.extractLsb' 16 8, w_36.extractLsb' 24 8]) ∗ ((fsp +
    40#64) ↦ₛ [w_40.extractLsb' 0 8, w_40.extractLsb' 8 8, w_40.extractLsb' 16 8,
      w_40.extractLsb' 24 8]) ∗ ((fsp + 44#64) ↦ₛ [w_44.extractLsb' 0 8, w_44.extractLsb' 8 8,
    w_44.extractLsb' 16 8, w_44.extractLsb' 24 8]) ∗ ((fsp + 48#64) ↦ₛ [w_48.extractLsb' 0 8,
    w_48.extractLsb' 8 8, w_48.extractLsb' 16 8, w_48.extractLsb' 24 8]) ∗ ((fsp +
    52#64) ↦ₛ [w_52.extractLsb' 0 8, w_52.extractLsb' 8 8, w_52.extractLsb' 16 8,
      w_52.extractLsb' 24 8]) ∗ ((fsp + 56#64) ↦ₛ [w_56.extractLsb' 0 8, w_56.extractLsb' 8 8,
    w_56.extractLsb' 16 8, w_56.extractLsb' 24 8]) ∗ ((fsp + 60#64) ↦ₛ [w_60.extractLsb' 0 8,
    w_60.extractLsb' 8 8, w_60.extractLsb' 16 8, w_60.extractLsb' 24 8]) ∗ ((fsp +
    64#64) ↦ₛ [w_64.extractLsb' 0 8, w_64.extractLsb' 8 8, w_64.extractLsb' 16 8,
      w_64.extractLsb' 24 8]) ∗ ((fsp + 68#64) ↦ₛ [w_68.extractLsb' 0 8, w_68.extractLsb' 8 8,
    w_68.extractLsb' 16 8, w_68.extractLsb' 24 8]) ∗ ((fsp + 72#64) ↦ₛ [w_72.extractLsb' 0 8,
    w_72.extractLsb' 8 8, w_72.extractLsb' 16 8, w_72.extractLsb' 24 8]) ∗ ((fsp +
    76#64) ↦ₛ [w_76.extractLsb' 0 8, w_76.extractLsb' 8 8, w_76.extractLsb' 16 8,
      w_76.extractLsb' 24 8]) ∗ ((fsp + 80#64) ↦ₛ [w_80.extractLsb' 0 8, w_80.extractLsb' 8 8,
    w_80.extractLsb' 16 8, w_80.extractLsb' 24 8]) ∗ ((fsp + 84#64) ↦ₛ [w_84.extractLsb' 0 8,
    w_84.extractLsb' 8 8, w_84.extractLsb' 16 8, w_84.extractLsb' 24 8]) ∗ ((fsp +
    88#64) ↦ₛ [w_88.extractLsb' 0 8, w_88.extractLsb' 8 8, w_88.extractLsb' 16 8,
      w_88.extractLsb' 24 8]) ∗ ((fsp + 92#64) ↦ₛ [w_92.extractLsb' 0 8, w_92.extractLsb' 8 8,
    w_92.extractLsb' 16 8, w_92.extractLsb' 24 8]) = ((fsp + 4#64) ↦ₛ [w_4.extractLsb' 0 8,
      w_4.extractLsb' 8 8, w_4.extractLsb' 16 8, w_4.extractLsb' 24 8, w_8.extractLsb' 0 8,
       w_8.extractLsb' 8 8, w_8.extractLsb' 16 8, w_8.extractLsb' 24 8, w_12.extractLsb' 0 8,
       w_12.extractLsb' 8 8, w_12.extractLsb' 16 8, w_12.extractLsb' 24 8, w_16.extractLsb' 0 8,
       w_16.extractLsb' 8 8, w_16.extractLsb' 16 8, w_16.extractLsb' 24 8, w_20.extractLsb' 0 8,
       w_20.extractLsb' 8 8, w_20.extractLsb' 16 8, w_20.extractLsb' 24 8, w_24.extractLsb' 0 8,
       w_24.extractLsb' 8 8, w_24.extractLsb' 16 8, w_24.extractLsb' 24 8, w_28.extractLsb' 0 8,
       w_28.extractLsb' 8 8, w_28.extractLsb' 16 8, w_28.extractLsb' 24 8, w_32.extractLsb' 0 8,
       w_32.extractLsb' 8 8, w_32.extractLsb' 16 8, w_32.extractLsb' 24 8, w_36.extractLsb' 0 8,
       w_36.extractLsb' 8 8, w_36.extractLsb' 16 8, w_36.extractLsb' 24 8, w_40.extractLsb' 0 8,
       w_40.extractLsb' 8 8, w_40.extractLsb' 16 8, w_40.extractLsb' 24 8, w_44.extractLsb' 0 8,
       w_44.extractLsb' 8 8, w_44.extractLsb' 16 8, w_44.extractLsb' 24 8, w_48.extractLsb' 0 8,
       w_48.extractLsb' 8 8, w_48.extractLsb' 16 8, w_48.extractLsb' 24 8, w_52.extractLsb' 0 8,
       w_52.extractLsb' 8 8, w_52.extractLsb' 16 8, w_52.extractLsb' 24 8, w_56.extractLsb' 0 8,
       w_56.extractLsb' 8 8, w_56.extractLsb' 16 8, w_56.extractLsb' 24 8, w_60.extractLsb' 0 8,
       w_60.extractLsb' 8 8, w_60.extractLsb' 16 8, w_60.extractLsb' 24 8, w_64.extractLsb' 0 8,
       w_64.extractLsb' 8 8, w_64.extractLsb' 16 8, w_64.extractLsb' 24 8, w_68.extractLsb' 0 8,
       w_68.extractLsb' 8 8, w_68.extractLsb' 16 8, w_68.extractLsb' 24 8, w_72.extractLsb' 0 8,
       w_72.extractLsb' 8 8, w_72.extractLsb' 16 8, w_72.extractLsb' 24 8, w_76.extractLsb' 0 8,
       w_76.extractLsb' 8 8, w_76.extractLsb' 16 8, w_76.extractLsb' 24 8, w_80.extractLsb' 0 8,
       w_80.extractLsb' 8 8, w_80.extractLsb' 16 8, w_80.extractLsb' 24 8, w_84.extractLsb' 0 8,
       w_84.extractLsb' 8 8, w_84.extractLsb' 16 8, w_84.extractLsb' 24 8, w_88.extractLsb' 0 8,
       w_88.extractLsb' 8 8, w_88.extractLsb' 16 8, w_88.extractLsb' 24 8,
       w_92.extractLsb' 0 8, w_92.extractLsb' 8 8, w_92.extractLsb' 16 8, w_92.extractLsb' 24 8]) :=
       by
    simp only [pointsToBytes_cons, pointsToBytes_nil, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepConj_assoc]
  simp only [sepConj_assoc]; rw [h1]; exact pointsToBytes_entails_memRegion (fsp + 4#64) _
theorem memRegion32_eq_rngSlots2a (fsp : BitVec 64) : memRegion (fsp + 4#64) 32 = ∃∗
    w_32 : BitVec 32, ∃∗ w_28 : BitVec 32, ∃∗ w_24 : BitVec 32, ∃∗ w_20 : BitVec 32, ∃∗
      w_16 : BitVec 32, ∃∗ w_12 : BitVec 32, ∃∗ w_8 : BitVec 32, ∃∗ w_4 : BitVec 32,
        rngSlots2a fsp w_4 w_8 w_12 w_16 w_20 w_24 w_28 w_32 := by
  rw [ProofLib.memRegion_split' (b := fsp + 4#64) (n := 4) (k := 28) (b' :=
    fsp + 8#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 8#64) (n :=
      4) (k := 24) (b' := fsp + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 12#64) (n := 4) (k := 20) (b' :=
        fsp + 16#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 16#64) (n := 4) (k := 16) (b' := fsp + 20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 20#64) (n := 4) (k := 12) (b' :=
        fsp + 24#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 24#64) (n := 4) (k := 8) (b' := fsp + 28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 28#64) (n := 4) (k := 4) (b' :=
        fsp + 32#64) rfl (by bv_omega) (by decide), memRegion_four, memRegion_four, memRegion_four,
      memRegion_four, memRegion_four, memRegion_four, memRegion_four, memRegion_four]
  simp only [rngSlots2a, sepExists_sepConj_left, sepExists_sepConj_right]
theorem memRegion32_eq_rngSlots1b (fsp : BitVec 64) : memRegion (fsp + 36#64) 32 = ∃∗
    w_64 : BitVec 32, ∃∗ w_60 : BitVec 32, ∃∗ w_56 : BitVec 32, ∃∗ w_52 : BitVec 32, ∃∗
      w_48 : BitVec 32, ∃∗ w_44 : BitVec 32, ∃∗ w_40 : BitVec 32, ∃∗ w_36 : BitVec 32,
        rngSlots1b fsp w_36 w_40 w_44 w_48 w_52 w_56 w_60 w_64 := by
  rw [ProofLib.memRegion_split' (b := fsp + 36#64) (n := 4) (k := 28) (b' :=
    fsp + 40#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 40#64) (n :=
      4) (k := 24) (b' := fsp + 44#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 44#64) (n := 4) (k := 20) (b' :=
        fsp + 48#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 48#64) (n := 4) (k := 16) (b' := fsp + 52#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 52#64) (n := 4) (k := 12) (b' :=
        fsp + 56#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 56#64) (n := 4) (k := 8) (b' := fsp + 60#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 60#64) (n := 4) (k := 4) (b' :=
        fsp + 64#64) rfl (by bv_omega) (by decide), memRegion_four, memRegion_four, memRegion_four,
      memRegion_four, memRegion_four, memRegion_four, memRegion_four, memRegion_four]
  simp only [rngSlots1b, sepExists_sepConj_left, sepExists_sepConj_right]
theorem memRegion28_eq_rngSlots1a (fsp : BitVec 64) : memRegion (fsp + 68#64) 28 = ∃∗
    w_92 : BitVec 32, ∃∗ w_88 : BitVec 32, ∃∗ w_84 : BitVec 32, ∃∗ w_80 : BitVec 32, ∃∗
      w_76 : BitVec 32, ∃∗ w_72 : BitVec 32, ∃∗ w_68 : BitVec 32,
        rngSlots1a fsp w_68 w_72 w_76 w_80 w_84 w_88 w_92 := by
  rw [ProofLib.memRegion_split' (b := fsp + 68#64) (n := 4) (k := 24) (b' :=
    fsp + 72#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 72#64) (n :=
      4) (k := 20) (b' := fsp + 76#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 76#64) (n := 4) (k := 16) (b' :=
        fsp + 80#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 80#64) (n := 4) (k := 12) (b' := fsp + 84#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 84#64) (n := 4) (k := 8) (b' :=
        fsp + 88#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 88#64) (n := 4) (k := 4) (b' := fsp + 92#64) rfl (by bv_omega) (by decide),
      memRegion_four, memRegion_four, memRegion_four, memRegion_four, memRegion_four,
        memRegion_four, memRegion_four]
  simp only [rngSlots1a, sepExists_sepConj_left, sepExists_sepConj_right]
theorem memRegion32_eq_kemCoinSlots64_2080 (fsp : BitVec 64) : memRegion (fsp + 2080#64) 32 = ∃∗
    v_2080 : BitVec 64, ∃∗ v_2088 : BitVec 64, ∃∗ v_2096 : BitVec 64, ∃∗ v_2104 : BitVec 64,
        kemCoinSlots64 fsp v_2080 v_2088 v_2096 v_2104 := by
  rw [(memRegion_cells (fsp + 2080#64) 4 (by decide) : memRegion (fsp + 2080#64) 32 = cells (fsp +
    2080#64) 4)]
  simp only [cells, kemCoinSlots64, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_right]
theorem stackAt_pqxdh_eq_alloc (fsp : BitVec 64) :
    stackAt fsp pqxdhHookStack = stackAt fsp allocHookStack := rfl
theorem stackAt_calculateAgreement_eq_pqxdh (fsp : BitVec 64) : stackAt fsp calculateAgreementStack
    = memRegion (fsp - 4256#64) 160 ∗ stackAt fsp pqxdhHookStack := by
  rw [stackAt_calc_split_alloc fsp, sepConj_comm]
theorem pointsToBytes_merge4_32 (cur : BitVec 64) (l0 l1 l2 l3 : List (BitVec 8)) (h0 : l0.length =
    32) (h1 : l1.length = 32) (h2 : l2.length = 32) : (cur ↦ₛ l0) ∗ ((cur + 32#64) ↦ₛ l1) ∗ ((cur +
    64#64) ↦ₛ l2) ∗ ((cur + 96#64) ↦ₛ l3) = (cur ↦ₛ (l0 ++ l1 ++ l2 ++ l3)) := by
  simp only [List.append_assoc, pointsToBytes_append, h0, h1, h2, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem getD_drop_bv8 (bs : List (BitVec 8)) (k i : Nat) :
    (bs.drop k).getD i 0#8 = bs.getD (k + i) 0#8 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
theorem word32At_drop (bs : List (BitVec 8)) (k off : Nat) :
    word32At (bs.drop k) off = word32At bs (k + off) := by
  simp only [word32At, getD_drop_bv8, Nat.add_assoc]
theorem take4_eq_word32Bytes (bs : List (BitVec 8)) (h : 4 ≤ bs.length) :
    bs.take 4 = word32Bytes (word32At bs 0) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · simp [word32Bytes, word32At]
theorem take8_eq_words32Bytes (bs : List (BitVec 8)) (h : 8 ≤ bs.length) :
    bs.take 8 = words32Bytes [word32At bs 0, word32At bs 4] := by
  rw [show bs.take 8 = bs.take (4 + 4) from rfl, List.take_add, take4_eq_word32Bytes bs
    (by omega), take4_eq_word32Bytes (bs.drop 4) (by simp; omega), word32At_drop]; rfl
theorem take16_eq_words32Bytes (bs : List (BitVec 8)) (h : 16 ≤ bs.length) :
    bs.take 16 = words32Bytes [word32At bs 0, word32At bs 4, word32At bs 8, word32At bs 12] := by
  rw [show bs.take 16 = bs.take (8 + 8) from rfl, List.take_add, take8_eq_words32Bytes bs
    (by omega), take8_eq_words32Bytes (bs.drop 8) (by simp; omega), word32At_drop, word32At_drop]
  rfl
theorem take32_eq_words32Bytes (bs : List (BitVec 8)) (h : 32 ≤ bs.length) : bs.take 32 =
    words32Bytes [word32At bs 0, word32At bs 4, word32At bs 8, word32At bs 12,
                    word32At bs 16, word32At bs 20, word32At bs 24, word32At bs 28] := by
  rw [show bs.take 32 = bs.take (16 + 16) from rfl, List.take_add, take16_eq_words32Bytes bs
    (by omega), take16_eq_words32Bytes (bs.drop 16) (by simp; omega),
      word32At_drop, word32At_drop, word32At_drop, word32At_drop]; rfl
theorem rng128_eq_words32Bytes_append (bs : List (BitVec 8)) (h : bs.length = 128) : bs =
    words32Bytes [word32At bs 0, word32At bs 4, word32At bs 8, word32At bs 12, word32At bs 16,
      word32At bs 20, word32At bs 24, word32At bs 28] ++ words32Bytes [word32At bs 32,
      word32At bs 36, word32At bs 40, word32At bs 44, word32At bs 48, word32At bs 52,
        word32At bs 56, word32At bs 60] ++ words32Bytes [word32At bs 64, word32At bs 68,
      word32At bs 72, word32At bs 76, word32At bs 80, word32At bs 84, word32At bs 88,
        word32At bs 92] ++ words32Bytes [word32At bs 96, word32At bs 100, word32At bs 104,
      word32At bs 108, word32At bs 112, word32At bs 116, word32At bs 120, word32At bs 124] := by
  have htake : bs = bs.take (32 + (32 + (32 + 32))) := (List.take_of_length_le (by omega)).symm
  conv_lhs => rw [htake]
  rw [List.take_add, List.take_add, List.take_add, take32_eq_words32Bytes bs
    (by omega), take32_eq_words32Bytes (bs.drop 32) (by simp; omega), List.drop_drop,
      take32_eq_words32Bytes (bs.drop (32 + 32))
        (by simp; omega), List.drop_drop, take32_eq_words32Bytes (bs.drop (32 + 32 + 32))
        (by simp; omega)]; simp only [word32At_drop, List.append_assoc]
abbrev initiatorModelPrims (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives) (W :
    CryptoVerification.E2E.PEParams) : Primitives :=
  ResponderCore.ofSignalPqxdhPrimitives (CryptoVerification.E2E.modelPrims X W)
@[simp] theorem e2e_toU8_length (bs : List (BitVec 8)) : (CryptoVerification.E2E.toU8 bs).length =
    bs.length := ResponderCore.toU8_length bs
@[simp] theorem e2e_vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) :
    (CryptoVerification.E2E.vecU8 v).length = n := ResponderCore.vecU8_length v
@[simp] theorem e2e_bytesToBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : bytesToBv8
    (CryptoVerification.E2E.vecU8 v) = v.toList := ResponderCore.bytesToBv8_vecU8 v
theorem readVecN_of_pointsToBytes {m : Memory} {a : BitVec 64} {n : Nat} {bs : List UInt8} {R :
    SepProp} (hlen : bs.length = n) (h : m ⊨ (a ↦ₛ bytesToBv8 bs) ∗ R) :
    CryptoVerification.E2E.readVecN m a n = CryptoVerification.E2E.u8Vec n bs := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes a (bytesToBv8 bs)).read h
  have hlen' : (bytesToBv8 bs).length = n := by simp [bytesToBv8, hlen]
  have hof : (CryptoVerification.E2E.ofU8 bs).length = n := by
    simp [CryptoVerification.E2E.ofU8, hlen]
  have hof_eq : bytesToBv8 bs = CryptoVerification.E2E.ofU8 bs :=
    ResponderCore.bytesToBv8_eq_ofU8 bs
  rw [hlen'] at hread; apply Subtype.ext
  dsimp only [CryptoVerification.E2E.readVecN, CryptoVerification.E2E.u8Vec,
    CryptoVerification.E2E.fitVec]
  rw [hread, hof_eq, List.take_append_of_le_length (Nat.le_of_eq hof.symm),
    List.take_of_length_le (Nat.le_of_eq hof)]
private theorem fitBv8_kyberEncapsOutBytes_eq_of_len {P : Primitives}
    (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hEncapsEq : ∀ pk r : Bytes, pk.length = 1568 → P.kemEncaps pk r =
      let (ct, ss) :=
        encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (pk r : Bytes) (hpk : pk.length = 1568) :
    let o := encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
    fitBv8 1600 (kyberEncapsOutBytes P pk r) = o.1.toList ++ o.2.toList := by
  intro o; unfold kyberEncapsOutBytes; rw [hEncapsEq pk r hpk]; dsimp only; unfold fitBv8
  rw [bytesToBv8_append, e2e_bytesToBv8_vecU8, e2e_bytesToBv8_vecU8]
  have hlen : (o.1.toList ++ o.2.toList).length = 1600 := by
    rw [List.length_append, o.1.toList_length, o.2.toList_length]
  rw [hlen, List.take_of_length_le (by rw [hlen]), Nat.sub_self, List.replicate_zero,
    List.append_nil]
theorem kemEncapsHook_ok_of_len {P : Primitives}
    (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hEncapsEq : ∀ pk r : Bytes, pk.length = 1568 → P.kemEncaps pk r =
      let (ct, ss) :=
        encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct)) :
    HookOk (CryptoVerification.E2E.kemEncapsHook encaps) (kyberEncapsStubSpec P) := by
  unfold CryptoVerification.E2E.kemEncapsHook
  refine retHook_ok fun ⟨pkPtr, pk1568, coinsPtr, coins32, outPtr⟩ R s0 _ hpre _ => ?_
  simp only [kyberEncapsStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hpk_len, hcoins_len, _⟩, hmem⟩
  have hpk : CryptoVerification.E2E.readVecN s0.mem pkPtr 1568 =
    CryptoVerification.E2E.u8Vec 1568 pk1568 := readVecN_of_pointsToBytes hpk_len hmem
  have hmem_coins : s0.mem ⊨ (coinsPtr ↦ₛ bytesToBv8 coins32) ∗ ((pkPtr ↦ₛ bytesToBv8 pk1568) ∗
      (memRegion outPtr 1600 ∗ (stackAt s0.sp pqxdhHookStack ∗ R))) := by
    ac_nf at hmem ⊢
  have hcoins : CryptoVerification.E2E.readVecN s0.mem coinsPtr 32 =
    CryptoVerification.E2E.u8Vec 32 coins32 := readVecN_of_pointsToBytes hcoins_len hmem_coins
  let o :=
    encaps (CryptoVerification.E2E.u8Vec 1568 pk1568) (CryptoVerification.E2E.u8Vec 32 coins32)
  have hsplit : memRegion outPtr 1600 = memRegion outPtr 1568 ∗ memRegion (outPtr + 0x620#64) 32 :=
    ProofLib.memRegion_split' (b := outPtr) (n := 1568) (k := 32) (b' :=
      outPtr + 0x620#64) rfl (by bv_omega) (by decide)
  rw [hsplit] at hmem
  have hmem1 : s0.mem ⊨ memRegion outPtr o.1.toList.length ∗ (memRegion (outPtr + 0x620#64) 32 ∗
    (pkPtr ↦ₛ bytesToBv8 pk1568) ∗
       (coinsPtr ↦ₛ bytesToBv8 coins32) ∗ stackAt s0.sp pqxdhHookStack ∗ R) := by
    rw [o.1.toList_length]; ac_nf at hmem ⊢
  have hlen1 : o.1.toList.length ≤ 2 ^ 64 := by rw [o.1.toList_length]; decide
  have hkf1 := keepsFrozen_writeBytes_of_memRegion o.1.toList hlen1 hmem1
  have hw1 := satisfies_writeBytes o.1.toList hlen1 hmem1
  have hmem2 : (s0.mem.writeBytes outPtr o.1.toList) ⊨ memRegion (outPtr +
      0x620#64) o.2.toList.length ∗ ((outPtr ↦ₛ o.1.toList) ∗ (pkPtr ↦ₛ bytesToBv8 pk1568) ∗
       (coinsPtr ↦ₛ bytesToBv8 coins32) ∗ stackAt s0.sp pqxdhHookStack ∗ R) := by
    rw [o.2.toList_length]; ac_nf at hw1 ⊢
  have hlen2 : o.2.toList.length ≤ 2 ^ 64 := by rw [o.2.toList_length]; decide
  have hkf2 := hkf1.trans (keepsFrozen_writeBytes_of_memRegion o.2.toList hlen2 hmem2)
  have hw2 := satisfies_writeBytes o.2.toList hlen2 hmem2
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0, hx1, hx8, hpk, hcoins]; exact hkf2
  · dsimp only [kyberEncapsStubSpec, retHook, CryptoVerification.LibsignalAesCbc.returnToLinkRegister]
    rw [hx0, hx1, hx8, hpk, hcoins, State.trace_setPC,
      fitBv8_kyberEncapsOutBytes_eq_of_len encaps hEncapsEq pk1568 coins32 hpk_len]
    have hmerge : (outPtr ↦ₛ (o.1.toList ++ o.2.toList)) = (outPtr ↦ₛ o.1.toList) ∗ ((outPtr +
      0x620#64) ↦ₛ o.2.toList) := (by rw [pointsToBytes_append, o.1.toList_length]); rw [hmerge]
    simp only [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨rfl, ?_⟩; ac_nf at hw2 ⊢
theorem kemEncapsHook_ok {P : Primitives} (encaps : List.Vector (BitVec 8) 1568 → List.Vector
    (BitVec 8) 32 → List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32) (hEncapsEq : ∀ pk r :
      Bytes, P.kemEncaps pk r =
        let (ct, ss) :=
          encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
        some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct)) :
    HookOk (CryptoVerification.E2E.kemEncapsHook encaps) (kyberEncapsStubSpec P) :=
  kemEncapsHook_ok_of_len encaps fun pk r _ => hEncapsEq pk r
theorem kemEncapsHook_ok_initiatorModelPrims
    (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives) (W : CryptoVerification.E2E.PEParams) :
    HookOk (CryptoVerification.E2E.kemEncapsHook W.Q.encaps)
      (kyberEncapsStubSpec (initiatorModelPrims X W)) :=
  kemEncapsHook_ok_of_len W.Q.encaps fun pk r hpk => by
    simp only [initiatorModelPrims, ResponderCore.ofSignalPqxdhPrimitives,
      CryptoVerification.E2E.modelPrims, CryptoVerification.E2E.blockLevelPrims,
      SignalPqxdh.kyberPkLen, hpk, beq_self_eq_true, ↓reduceIte]
@[simp, arm64_norm]
private theorem bv_add_sub_lit (x a b : BitVec 64) : (x + a) - b = x + (a - b) := by bv_omega
@[simp, arm64_norm] private theorem bv_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x
def initAliceSavedRegs (fsp : BitVec 64) (s0 : State) : SepProp :=
    ((fsp + 5296#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((fsp +
  5304#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((fsp + 5312#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((fsp +
    5320#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗ ((fsp + 5328#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
  ((fsp + 5336#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗ ((fsp + 5344#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((fsp + 5352#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗ ((fsp + 5360#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
    ((fsp + 5368#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((fsp +
  5376#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((fsp + 5384#64) ↦₆₄ s0.readReg64 (.gpr 19#5))
theorem memRegion96_5296_eq (fsp : BitVec 64) : memRegion (fsp + 5296#64) 96 = ∃∗ w0 : BitVec 64, ∃∗
    w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗
      w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        ∃∗ w11 : BitVec 64, ((fsp + 5296#64) ↦₆₄ w0) ∗ ((fsp + 5304#64) ↦₆₄ w1) ∗ ((fsp +
        5312#64) ↦₆₄ w2) ∗ ((fsp + 5320#64) ↦₆₄ w3) ∗ ((fsp + 5328#64) ↦₆₄ w4) ∗ ((fsp +
        5336#64) ↦₆₄ w5) ∗ ((fsp + 5344#64) ↦₆₄ w6) ∗ ((fsp + 5352#64) ↦₆₄ w7) ∗ ((fsp +
        5360#64) ↦₆₄ w8) ∗ ((fsp + 5368#64) ↦₆₄ w9) ∗ ((fsp + 5376#64) ↦₆₄ w10) ∗ ((fsp +
        5384#64) ↦₆₄ w11) := by
  rw [(memRegion_cells (fsp + 5296#64) 12 (by decide) : memRegion (fsp + 5296#64) 96 = cells (fsp +
    5296#64) 12)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem initAliceSavedRegs_entails_memRegion96 (fsp : BitVec 64) (s0 : State) :
    initAliceSavedRegs fsp s0 ⊢ memRegion (fsp + 5296#64) 96 := by
  rw [memRegion96_5296_eq fsp]; dsimp only [initAliceSavedRegs]
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.refl _))))))))))))
theorem memRegion1568_512_split_probe (fsp : BitVec 64) : memRegion (fsp + 512#64) 1568 =
    memRegion (fsp + 512#64) 688 ∗ (∃∗ w1200 : BitVec 64, (fsp +
      1200#64) ↦₆₄ w1200) ∗ memRegion (fsp + 1208#64) 872 := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 688) (k := 880) (b' :=
    fsp + 1200#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      fsp + 1200#64) (n := 8) (k := 872) (b' :=
        fsp + 1208#64) rfl (by bv_omega) (by decide), memRegion_eight (fsp + 1200#64)]
theorem memRegion1568_512_merge_probe (fsp : BitVec 64) (v : BitVec 64) : memRegion (fsp +
    512#64) 688 ∗ ((fsp + 1200#64) ↦₆₄ v) ∗ memRegion (fsp + 1208#64) 872 ⊢
      memRegion (fsp + 512#64) 1568 := by
  rw [memRegion1568_512_split_probe fsp]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right v (Entails.refl _)))
theorem pointsTo64_entails_memRegion8 (fsp : BitVec 64) (v : BitVec 64) :
    (fsp ↦₆₄ v) ⊢ memRegion fsp 8 := by
  rw [memRegion_eight fsp]; exact Entails.sepExists_right v (Entails.refl _)
theorem memRegion96_fsp_split8 (fsp : BitVec 64) : memRegion fsp 96 = memRegion fsp 8 ∗
    memRegion (fsp + 8#64) 88 :=
  ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 88) (b' := fsp + 8#64) rfl rfl (by decide)
theorem memRegion96_fsp_split4 (fsp : BitVec 64) : memRegion fsp 96 = memRegion fsp 4 ∗
    memRegion (fsp + 4#64) 92 :=
  ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 92) (b' := fsp + 4#64) rfl rfl (by decide)
theorem memRegion1600_3648_split24 (fsp : BitVec 64) : memRegion (fsp + 3648#64) 1600 =
    memRegion (fsp + 3648#64) 24 ∗ memRegion (fsp + 3672#64) 1576 :=
  ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 24) (k := 1576) (b' :=
    fsp + 3672#64) rfl (by bv_omega) (by decide)
def aliceErrResultAt (outPtr tagWord : BitVec 64) : SepProp :=
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ ((outPtr + 8#64) ↦₆₄ tagWord) ∗ memRegion (outPtr +
  16#64) 40
theorem memRegion16_eq_cells2 (base : BitVec 64) : memRegion base 16 = ∃∗ w0 : BitVec 64, ∃∗
    w1 : BitVec 64, (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) := by
  rw [(memRegion_cells base 2 (by decide) : memRegion base 16 = cells base 2)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem cells2_entails_memRegion16 (base : BitVec 64) (w0 w1 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ⊢ memRegion base 16 := by
  rw [memRegion16_eq_cells2 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.refl _))
theorem memRegion32_eq_cells4 (base : BitVec 64) : memRegion base 32 = ∃∗ w0 : BitVec 64, ∃∗
    w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
        ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) := by
  rw [(memRegion_cells base 4 (by decide) : memRegion base 32 = cells base 4)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem cells4_entails_memRegion32 (base : BitVec 64) (w0 w1 w2 w3 : BitVec 64) : (base ↦₆₄ w0) ∗
    ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base +
      24#64) ↦₆₄ w3) ⊢ memRegion base 32 := by
  rw [memRegion32_eq_cells4 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.refl _))))
theorem memRegion40_eq_cells5 (base : BitVec 64) : memRegion base 40 = ∃∗ w0 : BitVec 64, ∃∗
    w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, (base ↦₆₄ w0) ∗
      ((base + 8#64) ↦₆₄ w1) ∗
        ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗ ((base + 32#64) ↦₆₄ w4) := by
  rw [(memRegion_cells base 5 (by decide) : memRegion base 40 = cells base 5)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
theorem cells5_entails_memRegion40 (base : BitVec 64) (w0 w1 w2 w3 w4 : BitVec 64) : (base ↦₆₄ w0) ∗
    ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗ ((base +
      32#64) ↦₆₄ w4) ⊢ memRegion base 40 := by
  rw [memRegion40_eq_cells5 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.refl _)))))
theorem memRegion56_eq_cells7 (base : BitVec 64) : memRegion base 56 = ∃∗ w0 : BitVec 64, ∃∗
    w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗
      w6 : BitVec 64, (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base +
        24#64) ↦₆₄ w3) ∗
        ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) ∗ ((base + 48#64) ↦₆₄ w6) := by
  rw [(memRegion_cells base 7 (by decide) : memRegion base 56 = cells base 7)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
def CalleeSavedGprsPreserved (s s' : State) : Prop :=
  s'.readReg64 .x19 = s.readReg64 .x19 ∧
  s'.readReg64 .x20 = s.readReg64 .x20 ∧
  s'.readReg64 .x21 = s.readReg64 .x21 ∧
  s'.readReg64 .x22 = s.readReg64 .x22 ∧
  s'.readReg64 .x23 = s.readReg64 .x23 ∧
  s'.readReg64 .x24 = s.readReg64 .x24 ∧
  s'.readReg64 .x25 = s.readReg64 .x25 ∧
  s'.readReg64 .x26 = s.readReg64 .x26 ∧
  s'.readReg64 .x27 = s.readReg64 .x27 ∧
  s'.readReg64 .x28 = s.readReg64 .x28 ∧
  s'.readReg64 .fp = s.readReg64 .fp
