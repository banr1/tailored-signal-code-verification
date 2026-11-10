/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsDeserialize
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsKeysAddresses
import LibsignalBinary.Proofs.E2E.Bin.SegCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.E2E.StoreNew.Proof
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-! # Store-Initialization and Save-Identity Segment Proofs for `libsignal_e2e::open` (`0x43bfc..0x43c6c`) -/

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.InMem

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

namespace OpenStoreSegsCombinators

theorem sepWP_bind_segExit_open_tripleRatchetProgAt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (g : OpenGhost) (R : SepProp) {P F : SepProp} {target_pc : BitVec 64} {s0 s : State}
    {post : State → SepProp → Prop} {next : State → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hm : s.mem ⊨ P ∗ F)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target_pc s P post)
    (hcont : ∀ s1 P_f, Steps (binProg img C ctl abs) s s1 →
      s1.pc = target_pc → s1.status = .Running → (s1.mem ⊨ P_f ∗ F) → post s1 P_f →
      SegExit (binProg img C ctl abs) (openSpec A img) g R s0 s1 next) :
    SegExit (binProg img C ctl abs) (openSpec A img) g R s0 s next := by
  intro hL; have hprog : binProg img C ctl abs = tripleRatchetProgAt img.base C ctl abs :=
    tripleRatchetProg_eq_tripleRatchetProgAt himg (C := C) (ctl := ctl) (abs := abs)
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ := SepWP.elim hwp hm (hprog ▸ hL)
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hst1' : Steps (binProg img C ctl abs) s s1 := hprog ▸ hst1
  obtain ⟨sf, hst2, hout⟩ := hcont s1 P_f hst1' hpc1 hrun1 hm1 hpost1 (hst1'.codeLoaded hL)
  exact ⟨sf, Steps.trans hst1' hst2, hout⟩

theorem segExit_of_subroutine_ok_codeLoaded {α β : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {calleeEntry : BitVec 64} {calleeSpec : Spec β} {gc : β} {Rc : SepProp} {s0 s1 : State} {next : State → Prop}
    (hCallee : subroutine_ok prog calleeEntry calleeSpec)
    (hpc : s1.pc = calleeEntry) (hrun : s1.status = .Running) (hal : s1.spAligned = true)
    (hpre : s1.mem ⊨ calleeSpec.pre gc s1 ∗ Rc)
    (hpost : ∀ s2, prog.CodeLoaded s1.mem → Steps prog s1 s2 →
      (Returned s1 s2 ∧ CallingConventionPreserved s1 s2 ∧ s2.mem ⊨ calleeSpec.post gc s1 s2 ∗ Rc) →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hpanic : ∀ s2, s2.status = .Panicked → s2.mem ⊨ calleeSpec.onPanic gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hexit : ∀ code s2, s2.mem ⊨ calleeSpec.onExit gc code s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onExit g code s0 s2 ∗ R)
    (hoom : ∀ s2, s2.mem ⊨ calleeSpec.onOom gc s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onOom g s0 s2 ∗ R := by intro _ h; exact (not_satisfies_false_sepConj (h : _ ⊨ ⌜False⌝ ∗ _)).elim) :
    SegExit prog spec g R s0 s1 next := by
  intro hL
  exact segExit_of_subroutine_ok hCallee hpc hrun hal hpre
    (fun s2 hst hok => hpost s2 hL hst hok)
    hpanic hexit
    (fun s2 hoom_s2 hmo => Or.inr (Or.inr (Or.inr (Or.inr ⟨hoom_s2, hoom s2 hmo⟩))))
    hL

theorem segExit_of_tripleRatchetProgAt_subroutine_ok {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {α β : Type}
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) {spec : Spec α} {g : α} {R : SepProp}
    {calleeEntry : BitVec 64} {calleeSpec : Spec β} {gc : β} {Rc : SepProp} {s0 s1 : State} {next : State → Prop}
    (hCallee : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) calleeEntry calleeSpec)
    (hpc : s1.pc = calleeEntry) (hrun : s1.status = .Running) (hal : s1.spAligned = true)
    (hpre : s1.mem ⊨ calleeSpec.pre gc s1 ∗ Rc)
    (hpost : ∀ s2, (binProg img C ctl abs).CodeLoaded s1.mem →
      Steps (binProg img C ctl abs) s1 s2 →
      (Returned s1 s2 ∧ CallingConventionPreserved s1 s2 ∧ s2.mem ⊨ calleeSpec.post gc s1 s2 ∗ Rc) →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hpanic : ∀ s2, s2.status = .Panicked → s2.mem ⊨ calleeSpec.onPanic gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hexit : ∀ code s2, s2.mem ⊨ calleeSpec.onExit gc code s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onExit g code s0 s2 ∗ R)
    (hoom : ∀ s2, s2.mem ⊨ calleeSpec.onOom gc s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onOom g s0 s2 ∗ R := by intro _ h; exact (not_satisfies_false_sepConj (h : _ ⊨ ⌜False⌝ ∗ _)).elim) :
    SegExit (binProg img C ctl abs) spec g R s0 s1 next := by
  have hprog : binProg img C ctl abs = tripleRatchetProgAt img.base C ctl abs := tripleRatchetProg_eq_tripleRatchetProgAt himg
  exact segExit_of_subroutine_ok_codeLoaded (hprog.symm ▸ hCallee) hpc hrun hal hpre hpost hpanic hexit hoom

theorem emptyHashMapAt_eq_emptyTableAt (b out k0 k1 : BitVec 64) :
    emptyHashMapAt (b + emptyCtrlOff) out k0 k1 = HashbrownBin.emptyTableAt b out k0 k1 := by
  unfold emptyHashMapAt StoreNew.emptyHashMapAt StoreNew.emptyRawTableAt StoreNew.randomStateAt
    HashbrownBin.emptyTableAt emptyCtrlOff HashbrownBin.emptyCtrlGroupOff
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem open_onPanic_of_trace_eq (A : RustAlloc) (img : Obj.Image) (g : OpenGhost)
    (R Rc : SepProp) (s0 s1 s2 : State) (htr : s1.trace = s0.trace)
    (hpan : s2.status = .Panicked)
    (hm : s2.mem ⊨ (⌜allocFailedIn s1 s2 ∧ s1.trace <+: s2.trace⌝ ∗ anyHeap) ∗ (Rc ∗ R)) :
    SubroutineOutcome (openSpec A img) g R s0 s2 := by
  right; left; refine ⟨hpan, ?_⟩
  dsimp only [openSpec, Spec.inImage]; rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hfail, hpref⟩, hm⟩; unfold allocFailedIn at hfail ⊢; rw [htr] at hfail hpref
  refine ⟨⟨hfail, hpref⟩, ?_⟩
  have hany : anyHeap ∗ Rc ⊢ anyHeap := ProofLib.entails_anyHeap _
  exact Satisfies.mono (sepConj_mono_left hany) (by ac_sat hm)

theorem memRegion_24_eq_three_words (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) := by
  rw [memRegion_split a 8 16 (by decide), memRegion_split (a + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply RawByteMove.sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u0 =>
      Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.of_eq (by ac_rfl))))
  · exact Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_right u2 (Entails.sepExists_right u1 (Entails.sepExists_right u0 (Entails.of_eq (by ac_rfl))))

theorem memRegion_open_0x258_poll_split (sp : BitVec 64) :
    memRegion (sp + 0x258#64) 0x138 =
      memRegion (sp + 0x258#64) 0xe8 ∗ memRegion (sp + 0x340#64) 48 ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u0) ∗ ((sp + 0x378#64) ↦₆₄ u1) ∗ ((sp + 0x380#64) ↦₆₄ u2)) ∗
      memRegion (sp + 0x388#64) 8 := by
  rw [memRegion_split' (b := sp + 0x258#64) (b' := sp + 0x340#64) (N := 0x138) (n := 0xe8) (k := 80) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x370#64) (N := 80) (n := 48) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x370#64) (b' := sp + 0x388#64) (N := 32) (n := 24) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_24_eq_three_words (sp + 0x370#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_open_0x258_poll_join (sp w0 w1 w2 w3 : BitVec 64) :
    (memRegion (sp + 0x258#64) 0xe8 ∗ ((sp + 0x340#64) ↦₆₄ w0) ∗ memRegion (sp + 0x348#64) 40 ∗
     ((sp + 0x370#64) ↦₆₄ w1) ∗ ((sp + 0x378#64) ↦₆₄ w2) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗
     memRegion (sp + 0x388#64) 8) ⊢ memRegion (sp + 0x258#64) 0x138 := by
  have h48 : (((sp + 0x340#64) ↦₆₄ w0) ∗ memRegion (sp + 0x348#64) 40) ⊢ memRegion (sp + 0x340#64) 48 := by
    rw [memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x348#64) (N := 48) (n := 8) (k := 40) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
  rw [memRegion_open_0x258_poll_split sp]; refine sepConj_mono_right ?_
  rw [← sepConj_assoc ((sp + 0x340#64) ↦₆₄ w0)]; refine sepConj_mono h48 ?_
  rw [← sepConj_assoc ((sp + 0x370#64) ↦₆₄ w1), ← sepConj_assoc (((sp + 0x370#64) ↦₆₄ w1) ∗ _)]
  exact sepConj_mono_left (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl)))))

end OpenStoreSegsCombinators

open OpenStoreSegsCombinators

/-! ## Segment 5: `open_seg_stores_init'` (`+0x1c4..+0x1e0`, 7 insns) -/

private theorem memRegion_bottom_storesInit_sessionStoreNew (sp0 sp1 : BitVec 64) (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - (0x20 + extHookStack)) ∗ stackAt sp1 (0x20 + extHookStack) :=
  memRegion_bottom_open_split sp0 sp1 (0x20 + extHookStack) hsp (by decide) (by decide)

private theorem memRegion_bottom_storesInit_identityStoreNew (sp0 sp1 : BitVec 64) (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - 0x30) ∗ stackAt sp1 0x30 :=
  memRegion_bottom_open_split sp0 sp1 0x30 hsp (by decide) (by decide)

private def sessionStoreNewFrozenSpec (img : Obj.Image) :
    Spec (BitVec 64 × Option (BitVec 64 × BitVec 64)) where
  pre := fun (out, st) s =>
    ⌜img.FrozenLoaded s ∧ s.readReg64 .x8 = out⌝ ∗
      memRegion out 48 ∗ tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗ stackAt s.sp (0x20 + extHookStack)
  post := fun (out, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
        emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
          tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
      stackAt s0.sp (0x20 + extHookStack)

private def identityStoreNewInitFrozenSpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × Role × BitVec 64 × BitVec 64) where
  pre := fun (out, kpPtr, me, k0, k1) s =>
    ⌜img.FrozenLoaded s ∧ s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧ s.readReg32 .x1 = 0#32⌝ ∗
      memRegion out 120 ∗ (kpPtr ↦ₛ me.keyPairBytes) ∗
      tlsKeysInitAt (s.tpidrEl0 + tlsKeysTpoff) k0 k1 ∗ stackAt s.sp 0x30
  post := fun (out, kpPtr, me, k0, k1) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
      emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 me.keyPairBytes 0#32 ∗
      tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1 ∗
      (kpPtr ↦ₛ me.keyPairBytes) ∗ stackAt s0.sp 0x30

private theorem sessionStore_new_frozen_ok (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr inMemSessionStoreNewName) (sessionStoreNewFrozenSpec img) := by
  refine subroutine_ok_intro fun ⟨out, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [sessionStoreNewFrozenSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx8⟩, hpre⟩; have hro := StoreNew.storeNewRoDataAt_intro himg hF hpre
  cases st with
  | none =>
    dsimp only [tlsKeysAt, StoreNew.tlsKeysAt, tlsKeysUninitAt, StoreNew.tlsKeysUninitAt] at hro
    have hro' : s0.mem ⊨ (∃∗ k0Old : BitVec 64, ∃∗ k1Old : BitVec 64, ∃∗ tag : BitVec 8,
        ⌜tag ≠ 1#8⌝ ∗ tlsKeysRawAt (s0.tpidrEl0 + tlsKeysTpoff) k0Old k1Old tag) ∗
        (StoreNew.storeNewRoDataAt img.base tlsKeysTpoff (img.base + emptyCtrlOff) ∗
         memRegion out 48 ∗ stackAt s0.sp (0x20 + extHookStack) ∗ R) := by ac_sat hro
    rw [sepExists_sepConj_left, satisfies_sepExists] at hro'; rcases hro' with ⟨k0Old, hro'⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hro'; rcases hro' with ⟨k1Old, hro'⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hro'; rcases hro' with ⟨tag, hro'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hro'; rcases hro' with ⟨htag, hro'⟩
    refine reaches_of_ghost (StoreNew.sessionStore_new_uninit_base_ok img.base C ctl abs (base_aligned_of_loads himg) hRk)
      ⟨out, tlsKeysTpoff, img.base + emptyCtrlOff, k0Old, k1Old, tag⟩ emp hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simp only [StoreNew.sessionStoreNewUninitBaseSpec, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8, htag⟩, by ac_sat hro'⟩
    · simp only [StoreNew.sessionStoreNewUninitBaseSpec, sessionStoreNewFrozenSpec, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, Satisfies.drop_left hpost⟩
  | some ks =>
    rcases ks with ⟨k0, k1⟩; dsimp only [tlsKeysAt, StoreNew.tlsKeysAt] at hro
    have hstk := StoreNew.stackAt_sessionStoreNew_frame_split s0.sp; rw [hstk] at hro
    refine reaches_of_ghost (StoreNew.sessionStore_new_init_base_ok img.base C ctl abs (base_aligned_of_loads himg))
      ⟨out, tlsKeysTpoff, img.base + emptyCtrlOff, k0, k1⟩ (stackAt (s0.sp - 32#64) extHookStack)
      hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simp only [StoreNew.sessionStoreNewInitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hx8, by ac_sat hro⟩
    · simp only [StoreNew.sessionStoreNewInitBaseSpec, sessionStoreNewFrozenSpec, hstk, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨htr, _⟩, hpost⟩; have hpost' := Satisfies.drop_left hpost; refine ⟨htr, ?_⟩
      have hex : (emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗ tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ⊢
          ∃∗ k0' : BitVec 64, ∃∗ k1' : BitVec 64, emptyHashMapAt (img.base + emptyCtrlOff) out k0' k1' ∗
            tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0' + 1#64) k1' :=
        Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))
      exact Satisfies.mono (sepConj_mono_left hex) (by ac_sat hpost')

private theorem identityStore_new_init_frozen_ok (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr inMemIdentityStoreNewName) (identityStoreNewInitFrozenSpec img) := by
  refine subroutine_ok_refine (StoreNew.identityStore_new_init_base_ok img.base C ctl abs (base_aligned_of_loads himg))
    fun ⟨out, kpPtr, me, k0, k1⟩ R s0 hpre => ?_
  simp only [identityStoreNewInitFrozenSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx8, hx0, hx1⟩, hpre⟩; have hro := StoreNew.storeNewRoDataAt_intro himg hF hpre
  have hlen : me.keyPairBytes.length = 64 := by cases me <;> decide
  refine ⟨⟨out, kpPtr, me.keyPairBytes, 0#32, tlsKeysTpoff, img.base + emptyCtrlOff, k0, k1⟩, ?_, fun sf hpost => ?_⟩
  · simp only [StoreNew.identityStoreNewInitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hlen⟩, by simpa only [sepConj_assoc] using hro⟩
  · simp only [StoreNew.identityStoreNewInitBaseSpec, identityStoreNewInitFrozenSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpure, hpost⟩; exact ⟨hpure, Satisfies.drop_left hpost⟩

def addrPreAt (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  ∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64, ∃∗ mb : BitVec 8,
    ⌜g.name.cap = 36#64 ∧ g.name.bytes.length = 36 ∧ g.name.ptr ≠ 0#64 ∧ g.device = 1#8⌝ ∗
    (a ↦₆₄ m0) ∗ ((a + 8#64) ↦₆₄ m1) ∗ ((a + 16#64) ↦₆₄ m2) ∗ ((a + 24#64) ↦₈ mb) ∗
    memRegion (a + 25#64) 7 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr 36 1

/-- Binary seam slots at `+0x1e0`. -/
def openSeamSlots_0x1e0' (A : RustAlloc) (img : Obj.Image)
    (g : OpenGhost) (role : Role) (s : State) : SepProp :=
  ⌜s.readReg64 .x20 = 36#64 ∧ s.readReg64 .x22 = 36#64 ∧
    s.readReg64 .x24 = s.sp + 0x170#64 ∧ (s.readReg64 .x26).truncate 8 = 1#8⌝ ∗
    (∃∗ G, ⌜BinCanonSession G g.sess⌝ ∗ sessionRecordAt A s.sp ⟨0#64, 8#64, some G⟩ ⟨some g.sess⟩) ∗
    (∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost,
      ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
        s.readReg64 .x21 = gMe.name.ptr ∧ s.readReg64 .x23 = gPeer.name.ptr⌝ ∗
        addrPreAt A gMe (s.sp + 0x170#64) ∗ addrPreAt A gPeer (s.sp + 0x190#64)) ∗
    inMemSessionStoreAt A img (s.sp + 0x1b0#64) role.peer none ∗
    inMemIdentityStoreAt A img (s.sp + 0x1e0#64) role none ∗
    memRegion (s.sp + 0x258#64) 0xc8 ∗
    ((s.sp + 0x320#64) ↦ₛ role.peer.idKey.publicKey.bytes.toList) ∗
    memRegion (s.sp + 0x340#64) 0x50

private theorem addrPreAt_of_memRegion_32 (A : RustAlloc) (r : Role) (ptr a : BitVec 64)
    (hptr : ptr ≠ 0#64) :
    (memRegion a 0x20 ∗ (ptr ↦ₛ r.nameBytes) ∗ A.live ptr 36 1) ⊢
      addrPreAt A ⟨⟨36#64, ptr, r.nameBytes⟩, 1#8⟩ a := by
  have hlen : r.nameBytes.length = 36 := role_nameBytes_length r
  rw [memRegion_split' (b := a) (b' := a + 24#64) (N := 0x20) (n := 24) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_24_eq_three_words a,
      memRegion_split' (b := a + 24#64) (b' := a + 25#64) (N := 8) (n := 1) (k := 7) (by decide) (by bv_lin) (by decide),
      ProofLib.memRegion_one (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun mb => Entails.sepExists_elim fun m0 =>
    Entails.sepExists_elim fun m1 => Entails.sepExists_elim fun m2 => ?_
  unfold addrPreAt
  refine Entails.sepExists_right m0 (Entails.sepExists_right m1
    (Entails.sepExists_right m2 (Entails.sepExists_right mb ?_)))
  exact Entails.pure_right ⟨rfl, hlen, hptr, rfl⟩ (Entails.of_eq (by ac_rfl))

private theorem memRegion_open_0x170_stores_split (sp : BitVec 64) :
    memRegion (sp + 0x170#64) 0x170 =
      memRegion (sp + 0x170#64) 0x20 ∗ memRegion (sp + 0x190#64) 0x20 ∗
      memRegion (sp + 0x1b0#64) 48 ∗ memRegion (sp + 0x1e0#64) 120 ∗ memRegion (sp + 0x258#64) 0x88 := by
  rw [memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x190#64) (N := 0x170) (n := 0x20) (k := 0x150) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x1b0#64) (N := 0x150) (n := 0x20) (k := 0x130) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1e0#64) (N := 0x130) (n := 48) (k := 256) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x1e0#64) (b' := sp + 0x258#64) (N := 256) (n := 120) (k := 0x88) (by decide) (by bv_lin) (by decide)]

private theorem memRegion_open_0x258_join_0xc8 (sp : BitVec 64) (role : Role) :
    (memRegion (sp + 0x258#64) 0x88 ∗ ((sp + 0x2e0#64) ↦ₛ role.keyPairBytes)) ⊢
      memRegion (sp + 0x258#64) 0xc8 := by
  have hkp : ((sp + 0x2e0#64) ↦ₛ role.keyPairBytes) ⊢ memRegion (sp + 0x2e0#64) 0x40 := by
    have hlen : role.keyPairBytes.length = 0x40 := by cases role <;> decide
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 0x2e0#64) role.keyPairBytes; rwa [hlen] at h
  rw [memRegion_split' (b := sp + 0x258#64) (b' := sp + 0x2e0#64) (N := 0xc8) (n := 0x88) (k := 0x40) (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono_right hkp

private theorem emptyIdentityKeyStoreAt_entails_inMemIdentityStoreAt
    (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (role : Role) (k0 k1 : BitVec 64) :
    emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 role.keyPairBytes 0#32 ⊢
      inMemIdentityStoreAt A img out role none := by
  dsimp only [inMemIdentityStoreAt, emptyIdentityKeyStoreAt, StoreNew.emptyIdentityKeyStoreAt]
  exact Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.of_eq (by ac_rfl)))

private theorem emptyHashMapAt_entails_inMemSessionStoreAt
    (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (peer : Role) (k0 k1 : BitVec 64) :
    emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ⊢ inMemSessionStoreAt A img out peer none := by
  dsimp only [inMemSessionStoreAt]; exact Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))

variable (C : Crypto) (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (ctl : BitVec 64)
  (abs : String → Option (State → State))

/-! ## Segment 6: `open_seg_save_identity'` (`+0x1e0..+0x234`, 21 insns) -/

private theorem truncate32_truncate8 (v : BitVec 64) :
    (v.truncate 32).truncate 8 = v.truncate 8 := by bv_omega

private theorem role_peer_keyBytes_length (r : Role) :
    r.peer.idKey.publicKey.bytes.toList.length = 32 := r.peer.idKey.publicKey.bytes.toList_length

private theorem table4SingleAt_identityBucketEntryAt_entails_inMemIdentityStoreAt
    (A : RustAlloc) (img : Obj.Image) (out k0 k1 : BitVec 64) (role : Role)
    (gPeer clonedG : AddrGhost) (k : Nat) (hPeer : gPeer.val = role.peer.addrVal)
    (hcName : clonedG.name.bytes = gPeer.name.bytes) (hcDev : clonedG.device = gPeer.device) :
    (((out + 48#64) ↦ₛ role.keyPairBytes) ∗ ((out + 112#64) ↦₃₂ 0#32) ∗ memRegion (out + 116#64) 4 ∗
     HashbrownBin.table4SingleAt A HashbrownBin.identityBucketStride out k0 k1 k
       gPeer.name.bytes gPeer.device (HashbrownBin.identityBucketEntryAt A clonedG role.peer.idKey.publicKey.bytes.toList)) ⊢
      inMemIdentityStoreAt A img out role (some role.peer.idKey) := by
  have hPeerName : gPeer.name.bytes = role.peer.nameBytes := by injection hPeer with h1 _
  have hPeerDev : gPeer.device = 1#8 := by injection hPeer with _ h2
  have hcVal : clonedG.val = role.peer.addrVal := by unfold AddrGhost.val Role.addrVal; rw [hcName, hcDev, hPeerName, hPeerDev]
  unfold inMemIdentityStoreAt
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_); rw [hPeerName, hPeerDev]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  exact Entails.sepExists_right k (Entails.sepExists_right clonedG (Entails.pure_right hcVal (Entails.refl _)))

private theorem protocolAddressAt_of_addrPreAt_post (A : RustAlloc) (g : AddrGhost) (a : BitVec 64)
    (hcap : g.name.cap = 36#64) (hlen : g.name.bytes.length = 36)
    (hptr : g.name.ptr ≠ 0#64) (hdev : g.device = 1#8) :
    ((a ↦₆₄ 36#64) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗
     ((a + 24#64) ↦₈ 1#8) ∗ memRegion (a + 25#64) 7 ∗
     (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr 36 1) ⊢ protocolAddressAt A g a := by
  have hcap_ne : (36#64 : BitVec 64) ≠ 0#64 := by decide
  unfold protocolAddressAt vecGhostAt vecU8At RustHeap.vecHeader
  simp only [hcap, hlen, hdev, hcap_ne, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜36 ≤ 36 ∧ 36 < 9223372036854775808 ∧ g.name.ptr ≠ 0#64⌝ ∗
      ((a ↦₆₄ 36#64) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗
       ((a + 24#64) ↦₈ 1#8) ∗ memRegion (a + 25#64) 7 ∗
       (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr 36 1) = _ by ac_rfl))
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)

private theorem memRegion_open_0x340_poll_split (sp : BitVec 64) :
    memRegion (sp + 0x340#64) 0x50 =
      memRegion (sp + 0x340#64) 48 ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u0) ∗ ((sp + 0x378#64) ↦₆₄ u1) ∗ ((sp + 0x380#64) ↦₆₄ u2)) ∗
      memRegion (sp + 0x388#64) 8 := by
  rw [memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x370#64) (N := 0x50) (n := 48) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x370#64) (b' := sp + 0x388#64) (N := 32) (n := 24) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_24_eq_three_words (sp + 0x370#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_open_0x258_save_join (sp w0 w1 w2 w3 : BitVec 64) (v32 : BitVec 32)
    (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    (memRegion (sp + 0x258#64) 0xc8 ∗ ((sp + 0x320#64) ↦ₛ bs) ∗
     ((sp + 0x340#64) ↦₆₄ w0) ∗ ((sp + 0x348#64) ↦₃₂ v32) ∗ memRegion (sp + 0x34c#64) 36 ∗
     ((sp + 0x370#64) ↦₆₄ w1) ∗ ((sp + 0x378#64) ↦₆₄ w2) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗
     memRegion (sp + 0x388#64) 8) ⊢ memRegion (sp + 0x258#64) 0x138 := by
  have h32 : ((sp + 0x320#64) ↦ₛ bs) ⊢ memRegion (sp + 0x320#64) 0x20 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 0x320#64) bs; rwa [hbs] at h
  have h40 : (((sp + 0x348#64) ↦₃₂ v32) ∗ memRegion (sp + 0x34c#64) 36) ⊢ memRegion (sp + 0x348#64) 40 := by
    rw [memRegion_split' (b := sp + 0x348#64) (b' := sp + 0x34c#64) (N := 40) (n := 4) (k := 36) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)
  have he8 : (memRegion (sp + 0x258#64) 0xc8 ∗ ((sp + 0x320#64) ↦ₛ bs)) ⊢ memRegion (sp + 0x258#64) 0xe8 := by
    rw [memRegion_split' (b := sp + 0x258#64) (b' := sp + 0x320#64) (N := 0xe8) (n := 0xc8) (k := 0x20) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_right h32
  refine Entails.trans ?_ (memRegion_open_0x258_poll_join sp w0 w1 w2 w3)
  rw [← sepConj_assoc (memRegion (sp + 0x258#64) 0xc8)]
  refine sepConj_mono he8 (sepConj_mono_right ?_)
  rw [← sepConj_assoc ((sp + 0x348#64) ↦₃₂ v32)]; exact sepConj_mono_left h40

end CryptoVerification.E2E.Bin
