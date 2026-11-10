/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
/-!
# `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`: Post-Loop (`0x29f90 .. 0x2a588`) and Epilogue
(`0x2a034 .. 0x2a050`) -/

@[expose] public section namespace CryptoVerification.E2E.Pqxdh.ResponderWire
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
theorem SepWPp.call_noPanic_tryFrom {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α) (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf → SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) :=
  Wire.SepWPp.call_noPanic_tryFrom x (subroutine_ok_inImage_of_subroutine_ok img hcall)
    hpc hrun hsp hF hsym hlr hspec hφ hP hnext hexit hpan hoom
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8
/-! ## 1. `Wire.vecU8Buf` Slice Exposure and Shared Cleanup Tails (`0x2a53c .. 0x2a588` → `0x2a034`)
  -/
/-- The allocation/excess-capacity part of `Wire.vecU8Buf A cap ptr bs` without `(ptr ↦ₛ bs)`. -/
def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat -
       bs.length))
theorem vecU8Buf_to_slice_rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs := by
  unfold Wire.vecU8Buf vecU8Rest
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [pure_true_emp ⟨hle, hlt, hptr⟩, emp_sepConj]
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    apply entails_of_eq; ac_rfl
theorem slice_rest_to_vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs ⊢ Wire.vecU8Buf A cap ptr bs := by
  unfold Wire.vecU8Buf vecU8Rest
  rw [sepConj_comm (ptr ↦ₛ bs), sepConj_assoc]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [pure_true_emp ⟨hle, hlt, hptr⟩, emp_sepConj]
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    apply entails_of_eq; ac_rfl
/-- Tail `0x2a33c .. 0x2a344` (`+2060 .. +2068` → `+1284` / `0x2a034`):
`mov w2, #1; bl __rust_dealloc; b 0x2a034`, freeing `(x0 = ptr, x1 = cap)`. -/
theorem cleanup_33c_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)} (hS : TripleRatchetHooks C A S abs)
    {s0 s : State} {sp' ptr cap : BitVec 64} (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2060#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (_hpos : 0 < cap.toNat) (_hlt : cap.toNat < 2 ^ 63) (_hptr : ptr ≠ 0#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧ (Pf ⊢ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcall := dealloc_ok_at_prekey hS.alloc (b := img.base) (C := C) (ctl := ctl)
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2060 12
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2060#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_noPanic_tryFrom (ptr, cap.toNat, 1) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2068#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp allocHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1)
    (by simp [rustDeallocSpec, arm64_norm])
    ⟨hx0, by simp [hx1], rfl⟩ (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 _
  dsimp only [rustDeallocSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨PostEpilogueState.of_steps hF3 hsym3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
    (by simp [htr2, htr, arm64_norm]), ?_⟩
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl
/-- Tail `0x2a57c .. 0x2a588` (`+2636 .. +2648` → `+2060` → `+1284`):
frees `Wire.vecU8Buf A bkCap bkPtr bk` (`[sp'+80] = bkPtr, [sp'+88] = bkCap`) and reaches `0x2a034`.
-/ theorem cleanup_57c_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)} (hS : TripleRatchetHooks C A S abs)
    {s0 s : State} {sp' bkCap bkPtr : BitVec 64} (bk : List (BitVec 8))
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2636#64)
    (hrun : s.status = .Running) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧ (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' +
        88#64) ↦₆₄ bkCap) ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @cleanup_33c_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2636 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hnext hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2636#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  by_cases hcap : bkCap = 0#64
  · clear hnext
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_end hF hsym ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact ⟨PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
      (by simp [htr, arm64_norm]), Entails.refl _⟩
  · refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A bkCap bkPtr bk
        hcap)))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre
      (P' := (A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗ A.pool ∗
        stackAt sp' smallRootStack) ∗ (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm])) (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt hptr)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
/-- Tail `0x2a568 .. 0x2a57c` (`+2616 .. +2636` → `+1284`):
frees `Wire.vecU8Buf A ikCap ikPtr ik` (`x23 = ikCap, [sp'+104] = ikPtr`) and chains into
`cleanup_57c_wp`. -/
theorem cleanup_568_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)} (hS : TripleRatchetHooks C A S abs)
    {s0 s : State} {sp' ikCap ikPtr bkCap bkPtr : BitVec 64} (ik bk : List (BitVec 8))
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2616#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗
        stackAt sp' smallRootStack)
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcall := dealloc_ok_at_prekey hS.alloc (b := img.base) (C := C) (ctl := ctl)
  have hnext := @cleanup_57c_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2616 20
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hnext hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2616#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  by_cases hcap : ikCap = 0#64
  · clear hcall
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2636#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack) ∗ ((sp' +
          104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext bk
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm])) (by simp [arm64_norm]) (by simp [hrun, arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  · refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_dealloc A ikCap ikPtr ik hcap))))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.call_noPanic_tryFrom (ikPtr, ikCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + 2636#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt s.sp allocHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1)
      (by simp [rustDeallocSpec, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 _
    dsimp only [rustDeallocSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack) ∗ ((sp' +
          104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext bk (PostEpilogueState.of_steps hF2 hsym2 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
        (by simp [htr2, htr, arm64_norm])) hpc2 hrun2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
/-- Tail `0x2a558 .. 0x2a568` (`+2600 .. +2616` → `+1284`):
frees `Wire.vecU8Buf A msgCap msgPtr msg` when `msgCap ≠ 0#64` (`x26 = msgCap, [sp'+96] = msgPtr`)
and chains into `cleanup_568_wp`. -/
theorem cleanup_558_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)} (hS : TripleRatchetHooks C A S abs)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8)) (hcap : msgCap ≠ 0#64) (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2600#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧ (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' +
        88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ A.pool ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcall := dealloc_ok_at_prekey hS.alloc (b := img.base) (C := C) (ctl := ctl)
  have hnext := @cleanup_568_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2600 16
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcall hnext hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2600#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A msgCap msgPtr msg hcap)))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_noPanic_tryFrom (msgPtr, msgCap.toNat, 1) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2616#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
      stackAt s.sp allocHookStack)
    (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1)
    (by simp [rustDeallocSpec, hsp_eq, arm64_norm])
    ⟨rfl, rfl, rfl⟩ (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [rustDeallocSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨_, _, _, _, hx23_cs, _⟩
  have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, hx23, arm64_norm]
  refine SepWPp.mono_pre
    (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗
        stackAt sp' smallRootStack) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr))
    (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (hnext ik bk (PostEpilogueState.of_steps hF2 hsym2 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
        (by simp [htr2, htr, arm64_norm]))
      hpc2 hrun2 hx23_2)
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; ac_rfl
/-- Tail `0x2a554 .. 0x2a588` (`+2596 .. +2648` → `+1284`):
frees `msgVec`, `ikVec`, `bkVec` and reaches `0x2a034`. -/
theorem cleanup_554_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)} (hS : TripleRatchetHooks C A S abs)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8)) (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2596#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧ (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' +
        88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ A.pool ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have h558 := @cleanup_558_wp img C A S ctl abs hS s0
  have h568 := @cleanup_568_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2596 4
  clear hfn
  dsimp only [tripleRatchetProgAt] at h558 h568 hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2596#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  by_cases hcap : msgCap = 0#64
  · clear h558
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗
          stackAt sp' smallRootStack) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (h568 ik bk
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm])) (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx23, arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  · clear h568
    have hbeq : (msgCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h558 msg ik bk hcap
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm])
/-! ## 2. Segment 1: `0x29f90 .. 0x2a0f4` → `0x2a1b4` (`+1120 .. +1476` → `+1668`) -/
theorem deserialize_djb_ok (v : List.Vector (BitVec 8) 32) :
    PublicKey.deserialize (0x05#8 :: v.toList) = .ok ⟨v⟩ := by
  rcases v with ⟨l, hl⟩
  simp [PublicKey.deserialize, djbType, hl, List.take_of_length_le (Nat.le_of_eq hl)]
theorem post_vecU8At_lt (A : RustAlloc) (addr cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A addr cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8At A addr cap ptr bs := by
  rw [vecU8At_eq_header_buf]
  refine Entails.trans (sepConj_mono_right (post_vecU8Buf_lt A cap ptr bs)) ?_
  rw [sepConj_pure_left_comm]
  exact Entails.refl _
theorem post_vecU8At2_lt (A : RustAlloc) (a1 c1 p1 a2 c2 p2 : BitVec 64) (b1 b2 : List (BitVec 8)) :
    vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 ⊢
      ⌜c1.toNat < 2 ^ 63 ∧ c2.toNat < 2 ^ 63⌝ ∗ vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 := by
  refine Entails.trans (sepConj_mono (post_vecU8At_lt A a1 c1 p1 b1) (post_vecU8At_lt A a2 c2 p2
    b2)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun h1 => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun h2 => ?_
  rw [pure_true_emp ⟨h1, h2⟩, emp_sepConj]
  exact Entails.refl _
theorem post_vecU8At4_lt (A : RustAlloc) (a1 c1 p1 a2 c2 p2 a3 c3 p3 a4 c4 p4 : BitVec 64)
    (b1 b2 b3 b4 : List (BitVec 8)) :
    vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 ∗ vecU8At A a3 c3 p3 b3 ∗ vecU8At A a4 c4 p4 b4 ⊢
      ⌜c1.toNat < 2 ^ 63 ∧ c2.toNat < 2 ^ 63 ∧ c3.toNat < 2 ^ 63 ∧ c4.toNat < 2 ^ 63⌝ ∗
        vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 ∗
      vecU8At A a3 c3 p3 b3 ∗ vecU8At A a4 c4 p4 b4 := by
  rw [← sepConj_assoc (vecU8At A a1 c1 p1 b1) (vecU8At A a2 c2 p2 b2)]
  refine Entails.trans (sepConj_mono (post_vecU8At2_lt A a1 c1 p1 a2 c2 p2 b1 b2)
    (post_vecU8At2_lt A a3 c3 p3 a4 c4 p4 b3 b4)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨h1, h2⟩ => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨h3, h4⟩ => ?_
  rw [pure_true_emp ⟨h1, h2, h3, h4⟩, emp_sepConj]
  apply entails_of_eq; ac_rfl
/-- Stack spill layout at `sp' + 16 .. sp' + 112` (96 bytes) after `0x2a0a4`. -/
def seg1SpillsAt (sp' : BitVec 64) (x : PreKeyTryFromArgs) (opkVal : BitVec 32)
    (bkCap bkPtr msgPtr ikPtr : BitVec 64) : SepProp :=
  ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' +
    28#64) ↦₃₂ x.spkId) ∗
  ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
  ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₆₄ 33#64) ∗
  memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
    80#64) ↦₆₄ bkPtr) ∗
  ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr)
theorem memRegion96_seg1_unpack (sp' : BitVec 64) :
    memRegion (sp' + 16#64) 96 ⊢
      ∃∗ w16 : BitVec 32, ∃∗ w20 : BitVec 32, ∃∗ w24 : BitVec 32, ∃∗ w28 : BitVec 32,
      ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 32, ∃∗ w52 : BitVec 32,
      ∃∗ w56 : BitVec 64, ∃∗ w68 : BitVec 32, ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64,
      ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64,
        ((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗ ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' +
        28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗ ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' +
        52#64) ↦₃₂ w52) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗ memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) := by
  rw [show (96 : Nat) = 4 + (4 + (4 + (4 + (8 + (8 + (4 + (4 + (8 + (4 + (4 + (8 + (8 + (8 + (8 +
    8)))))))))))))) by decide, memRegion_split (sp' + 16#64) 4 92 (by decide),
    memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 48
      (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 +
      8#64) 4 44 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64) 4 40 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64) 8 32 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight (sp' + 32#64), ProofLib.memRegion_eight (sp' + 40#64),
    ProofLib.memRegion_eight (sp' + 56#64), ProofLib.memRegion_eight (sp' + 72#64),
    ProofLib.memRegion_eight (sp' + 80#64), ProofLib.memRegion_eight (sp' + 88#64),
    ProofLib.memRegion_eight (sp' + 96#64), ProofLib.memRegion_eight (sp' + 104#64)]
  refine Entails.trans (sepConj_mono (memRegion_four_entails (sp' + 16#64))
    (sepConj_mono (memRegion_four_entails (sp' + 20#64))
      (sepConj_mono (memRegion_four_entails (sp' + 24#64))
        (sepConj_mono (memRegion_four_entails (sp' + 28#64)) (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (memRegion_four_entails (sp' + 48#64))
              (sepConj_mono (memRegion_four_entails (sp' + 52#64))
                (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left (memRegion_four_entails (sp' + 68#64))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w104 => Entails.sepExists_elim fun w96 =>
    Entails.sepExists_elim fun w88 => Entails.sepExists_elim fun w80 =>
    Entails.sepExists_elim fun w72 => Entails.sepExists_elim fun w68 =>
    Entails.sepExists_elim fun w56 => Entails.sepExists_elim fun w52 =>
    Entails.sepExists_elim fun w48 => Entails.sepExists_elim fun w40 =>
    Entails.sepExists_elim fun w32 => Entails.sepExists_elim fun w28 =>
    Entails.sepExists_elim fun w24 => Entails.sepExists_elim fun w20 =>
    Entails.sepExists_elim fun w16 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w16)
  refine Entails.trans ?_ (Entails.sepExists_intro w20)
  refine Entails.trans ?_ (Entails.sepExists_intro w24)
  refine Entails.trans ?_ (Entails.sepExists_intro w28)
  refine Entails.trans ?_ (Entails.sepExists_intro w32)
  refine Entails.trans ?_ (Entails.sepExists_intro w40)
  refine Entails.trans ?_ (Entails.sepExists_intro w48)
  refine Entails.trans ?_ (Entails.sepExists_intro w52)
  refine Entails.trans ?_ (Entails.sepExists_intro w56)
  refine Entails.trans ?_ (Entails.sepExists_intro w68)
  refine Entails.trans ?_ (Entails.sepExists_intro w72)
  refine Entails.trans ?_ (Entails.sepExists_intro w80)
  refine Entails.trans ?_ (Entails.sepExists_intro w88)
  refine Entails.trans ?_ (Entails.sepExists_intro w96)
  refine Entails.trans ?_ (Entails.sepExists_intro w104)
  exact Entails.refl _
theorem post_headers_entails_memRegion80 (sp' ikCap ikPtr msgCap msgPtr : BitVec 64)
    (msgLen : BitVec 64) (regId opkT opkV spkId kpkId : BitVec 32) :
    vecHeader (sp' + 360#64) ikCap ikPtr 33#64 ∗ vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ regId) ∗ ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' +
      420#64) ↦₃₂ opkV) ∗
    ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' +
      436#64) ↦₃₂ kpkId) ⊢
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 := by
  have h1 := vecHeader_entails_memRegion24 (sp' + 360#64) ikCap ikPtr 33#64
  have h2 := vecHeader_entails_memRegion24 (sp' + 384#64) msgCap msgPtr msgLen
  have h3 : ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ regId) ⊢ memRegion (sp' + 408#64) 8 :=
    by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      408#64) 1#32 regId
  have h4 : ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' + 420#64) ↦₃₂ opkV) ⊢ memRegion (sp' + 416#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      416#64) opkT opkV
  have h5 : ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ⊢ memRegion (sp' + 424#64) 8 :=
    by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      424#64) 1#32 spkId
  have h6 : ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ kpkId) ⊢ memRegion (sp' + 432#64) 8 :=
    by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      432#64) 1#32 kpkId
  rw [show (72 : Nat) = 24 + (24 + (8 + (8 + 8))) by decide,
    memRegion_split (sp' + 360#64) 24 48 (by decide),
    memRegion_split (sp' + 360#64 + 24#64) 24 24 (by decide),
    memRegion_split (sp' + 360#64 + 24#64 + 24#64) 8 16 (by decide),
    memRegion_split (sp' + 360#64 + 24#64 + 24#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q := memRegion (sp' + 360#64) 24 ∗ memRegion (sp' + 384#64) 24 ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗ memRegion (sp' + 424#64) 8 ∗
        memRegion (sp' + 432#64) 8) ?_ ?_
  · rw [← sepConj_assoc ((sp' + 408#64) ↦₃₂ 1#32), ← sepConj_assoc ((sp' + 416#64) ↦₃₂ opkT),
        ← sepConj_assoc ((sp' + 424#64) ↦₃₂ 1#32)]
    exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 h6))))
  · apply entails_of_eq; ac_rfl
/-- Step 1A: `0x29f90 .. 0x2a0ac` (`+1120 .. +1404`): loads headers/fields from `sp' + 312 .. 440`,
spills them to `sp' + 16 .. 104`, and executes the first `drop_in_place<SignalProtocolError>` call.
-/ theorem post_seg1a_f90_to_0ac_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hDropSpe : CryptoVerification.LibsignalTripleRatchet.DropSpeOk img C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {opkVal : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗ vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes ∗ vecU8At A (sp' +
        360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A (sp' + 384#64) msgCap msgPtr x.inner ∗ ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' +
        412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ ((sp' + 424#64) ↦₃₂ 1#32) ∗
        ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗ A.pool ∗
        stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧ kyberCap.toNat < 2 ^ 63 ∧ bkCap.toNat < 2 ^ 63 ∧
        ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
        sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 =
        kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 312#64) 48 ∗
        memRegion (sp' + 360#64) 72 ∗
          memRegion (sp' + 432#64) 8 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗
          Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗ A.pool ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  have hcallSpe := dropSpe_ok_at_prekey hDropSpe
  clear hDropSpe
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 1120 24
  responder_wire_fetches_from img.base H hfn 0x29c14 1256 8
  responder_wire_fetches_from img.base H hfn 0x29c14 1316 88
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcallSpe hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1404#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709389828#64) _
      at hcallSpe
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h27 := hregs.x27
  have h22 := hregs.x22
  have h21 := hregs.x21
  have h20 := hregs.x20
  have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  rw [← sepConj_assoc (vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes),
      ← sepConj_assoc (vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes),
      ← sepConj_assoc (vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes)]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp') (sepConj_mono_left (post_vecU8At4_lt A
        (sp' + 312#64) kyberCap kyberPtr (sp' + 336#64) bkCap bkPtr
        (sp' + 360#64) ikCap ikPtr (sp' + 384#64) msgCap msgPtr
        x.kyberBytes x.bkBytes x.ikBytes x.inner))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w16 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w24 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w32 => SepWPp.exists_pre fun w40 =>
    SepWPp.exists_pre fun w48 => SepWPp.exists_pre fun w52 =>
    SepWPp.exists_pre fun w56 => SepWPp.exists_pre fun w68 =>
    SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
    SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
    SepWPp.exists_pre fun w104 => ?_
  rw [← sepConj_assoc ((sp' + 16#64) ↦₃₂ w16), ← sepConj_assoc (_ ∗ ((sp' + 20#64) ↦₃₂ w20)),
      ← sepConj_assoc (_ ∗ ((sp' + 24#64) ↦₃₂ w24)), ← sepConj_assoc (_ ∗ ((sp' + 28#64) ↦₃₂ w28)),
      ← sepConj_assoc (_ ∗ ((sp' + 32#64) ↦₆₄ w32)), ← sepConj_assoc (_ ∗ ((sp' + 40#64) ↦₆₄ w40)),
      ← sepConj_assoc (_ ∗ ((sp' + 48#64) ↦₃₂ w48)), ← sepConj_assoc (_ ∗ ((sp' + 52#64) ↦₃₂ w52)),
      ← sepConj_assoc (_ ∗ ((sp' + 56#64) ↦₆₄ w56)),
      ← sepConj_assoc (_ ∗ memRegion (sp' + 64#64) 4),
      ← sepConj_assoc (_ ∗ ((sp' + 68#64) ↦₃₂ w68)), ← sepConj_assoc (_ ∗ ((sp' + 72#64) ↦₆₄ w72)),
      ← sepConj_assoc (_ ∗ ((sp' + 80#64) ↦₆₄ w80)), ← sepConj_assoc (_ ∗ ((sp' + 88#64) ↦₆₄ w88)),
      ← sepConj_assoc (_ ∗ ((sp' + 96#64) ↦₆₄ w96)), sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun ⟨hky_lt, hbk_lt, hik_lt, hmsg_lt⟩ => ?_
  rw [vecU8At_eq_header_buf A (sp' + 312#64), vecU8At_eq_header_buf A (sp' + 336#64),
      vecU8At_eq_header_buf A (sp' + 360#64), vecU8At_eq_header_buf A (sp' + 384#64)]
  simp only [PreKeyTryFromArgs.kyberBytes_length, PreKeyTryFromArgs.bkBytes_length,
    PreKeyTryFromArgs.ikBytes_length]
  have hky_ne := cap_add2_ne_of_lt hky_lt
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709389828#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
      ((sp' + 352#64) ↦₆₄ 33#64) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr 1569#64 bkCap bkPtr 33#64
  have hhdr80 := post_headers_entails_memRegion80 sp' ikCap ikPtr msgCap msgPtr
    (BitVec.ofNat 64 x.inner.length) x.regId (opkTag x) opkVal x.spkId x.kpkId
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (P' := (speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗
      stackAt s.sp dropSpeStack) ∗
      (seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 360#64) 72 ∗
        memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
    (by
      rw [hspe, hstackSpe, hsp_eq]
      dsimp only [seg1SpillsAt]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ 33#64)) ∗ (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ 33#64) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' +
          400#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
          ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
          ((sp' + 436#64) ↦₃₂ x.kpkId)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool ∗ stackAt sp' dropSpeStack ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
          ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₆₄ 33#64) ∗
          memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
          80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_noPanic_tryFrom ⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 1404#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    (φ := img.FrozenLoaded _ ∧ s.symtab = img.symtab)
    (by simp [dropSpeSpec, Spec.inImage, hsp_eq, arm64_norm])
    ⟨hF1, hsym⟩ (by sep_focus)
    ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [dropSpeSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  refine SepWP.done hpc2 hrun2 ?_
  intro hF3 hsym3
  refine ⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF3, hsym3, by simp [htr2, htr,
    arm64_norm]⟩, hky_lt, hbk_lt, hik_lt, hmsg_lt,
    by simp [hx29_cs, h29, arm64_norm],
    by simp [hx28_cs, arm64_norm],
    by simp [hx27_cs, h27, arm64_norm],
    by simp [hx26_cs, arm64_norm],
    by simp [hx25_cs, arm64_norm],
    by simp [hx24_cs, arm64_norm],
    by simp [hx23_cs, arm64_norm],
    by simp [hx22_cs, h22, arm64_norm],
    by simp [hx21_cs, h21, arm64_norm],
    by simp [hx20_cs, h20, arm64_norm],
    by simp [hx19_cs, h19, arm64_norm], ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]
  apply entails_of_eq; ac_rfl
theorem post_memRegion48_split8 (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 := by
  rw [memRegion_split a 8 40 (by decide), ProofLib.memRegion_eight a]
  rw [sepExists_sepConj_left]
  exact Entails.refl _
theorem post_memRegion48_split33_15 (sp' : BitVec 64) :
    memRegion (sp' + 312#64) 48 = memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 := by
  simpa [BitVec.add_assoc, BitVec.reduceAdd] using memRegion_split (sp' + 312#64) 33 15 (by decide)
/-- Step 1B: `0x2a0ac .. 0x2a0f4` → `0x2a1b4` (`+1404 .. +1476` → `+1668`):
executes `drop_in_place<SignalProtocolError>` #2, #3, #4 and calls `PublicKey::deserialize`
(`0x3db50`) on `x.bkBytes`, branching to `0x2a1b4` (`+1668`). -/
theorem post_seg1b_0ac_to_1b4_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDropSpe : CryptoVerification.LibsignalTripleRatchet.DropSpeOk img C A ctl abs)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1404#64)
    (hrun : s.status = .Running) (hik_lt : ikCap.toNat < 2 ^ 63) (hmsg_lt : msgCap.toNat < 2 ^ 63)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = 1#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1668#64) s
      (((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ memRegion (sp' + 312#64) 48 ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 =
        kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 =
        kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
        ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
          memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ logOff img ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallSpe := dropSpe_ok_at_prekey hDropSpe
  have hcallDeser := deserialize_ok_at_prekey (C := C) (ctl := ctl) (abs := abs) himg
  clear hDropSpe
  have hik_eq := cap_add1_eq_of_lt hik_lt
  have hmsg_eq := cap_add1_eq_of_lt hmsg_lt
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 1404 76
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcallSpe hcallDeser hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1668#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1404#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709389828#64) _
      at hcallSpe
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 81952#64) _ at hcallDeser
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  -- Drop #2 (+1404 .. +1420)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (post_memRegion48_split8 (sp' +
      312#64))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_pre fun w312_1 => ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 18446744073709389828#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_noPanic_tryFrom (⟨sp' + 312#64, [],
    .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 1424#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt sp' dropSpeStack)
    (φ := img.FrozenLoaded _ ∧ s.symtab = img.symtab)
    (by simp [dropSpeSpec, Spec.inImage, hsp_eq, arm64_norm])
    ⟨hF1, hsym⟩ (by rw [hspe, hstackSpe]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [dropSpeSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_2, hx27, arm64_norm]
  have h26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_2, hx26, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = 1#64 := by simp [hx24_2, hx24, arm64_norm]
  -- Drop #3 (+1424 .. +1440)
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312_2 => ?_
  refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + 18446744073709389828#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine SepWPp.call_noPanic_tryFrom (⟨sp' + 312#64, [],
    .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hF3 hsym3
    (ret_pc := entry + 1444#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt sp' dropSpeStack)
    (φ := img.FrozenLoaded _ ∧ s2.symtab = img.symtab)
    (by simp [dropSpeSpec, Spec.inImage, hsp2_eq, arm64_norm])
    ⟨hF3, hsym2⟩ (by simp only [hspe, hsp_eq, arm64_norm]; sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hF4 hsym4 hcs4
  dsimp only [dropSpeSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr4 => ?_
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    hx29_4⟩
  have hsp4_eq : s4.sp = sp' := by tryFromPost_sp [hsp4, hsp2_eq]
  have h29_4 : s4.readReg64 .x29 = sp' + 512#64 := by simp [hx29_4, h29_2, arm64_norm]
  have h27_4 : s4.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_4, h27_2, arm64_norm]
  have h24_4 : s4.readReg64 .x24 = 1#64 := by simp [hx24_4, h24_2, arm64_norm]
  -- Drop #4 (+1444 .. +1456)
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312_3 => ?_
  refine SepWPp.of_sepWP_frozen hF4 hsym4 (mid := entry + 18446744073709389828#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) ?_
  intro hF5 hsym5
  refine SepWPp.call_noPanic_tryFrom (⟨sp' + 312#64, [],
    .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp4_align) hF5 hsym5
    (ret_pc := entry + 1460#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt sp' dropSpeStack)
    (φ := img.FrozenLoaded _ ∧ s4.symtab = img.symtab)
    (by simp [dropSpeSpec, Spec.inImage, hsp4_eq, arm64_norm])
    ⟨hF5, hsym4⟩ (by simp only [hspe, hsp2_eq, arm64_norm]; sep_focus)
    ?_
  clear hcallSpe
  intro s6 hpc6 hrun6 hsp6 hsp6_align hF6 hsym6 hcs6
  dsimp only [dropSpeSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr6 => ?_
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6,
    hx29_6⟩
  have hsp6_eq : s6.sp = sp' := by tryFromPost_sp [hsp6, hsp4_eq]
  have h29_6 : s6.readReg64 .x29 = sp' + 512#64 := by simp [hx29_6, h29_4, arm64_norm]
  -- PublicKey::deserialize (+1460 .. +1468)
  refine SepWPp.mono_pre
    (P' := ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ (bkPtr ↦ₛ x.bkBytes) ∗
      vecU8Rest A bkCap bkPtr x.bkBytes ∗
      memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ logOff img ∗ A.pool ∗
        stackAt sp' smallRootStack)
    (by
      rw [post_memRegion48_split33_15 sp']
      simp only [hstackSpe, hsp4_eq, sepConj_assoc, arm64_norm]
      refine Entails.trans
        (Q := Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ (memRegion (sp' + 312#64) 33 ∗
        memRegion (sp' + 345#64) 15 ∗
            A.pool ∗ stackAt sp' dropSpeStack ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
            80#64) ↦₆₄ bkPtr) ∗ logOff img ∗
            memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left (vecU8Buf_to_slice_rest A bkCap bkPtr x.bkBytes)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.of_sepWP_frozen hF6 hsym6 (mid := entry + 81952#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun6, arm64_norm]) ?_
  intro hF7 hsym7
  have hbk_deser : PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩ := deserialize_djb_ok x.baseKey
  have hbk_len : (33#64 : BitVec 64).toNat = x.bkBytes.length := by simp
  have hbk_lt63 : x.bkBytes.length < 2 ^ 63 := by simp
  refine SepWPp.call_noPanic_tryFrom (bkPtr, x.bkBytes, ⟨x.baseKey⟩, sp' + 312#64) hcallDeser
    (by simp [arm64_norm]) (by simp [hrun6, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp6_align) hF7 hsym7
    (ret_pc := entry + 1472#64) (by simp [arm64_norm])
    (T := (bkPtr ↦ₛ x.bkBytes) ∗ memRegion (sp' + 312#64) 33 ∗ logOff img)
    (φ := bkPtr = bkPtr ∧ (33#64 : BitVec 64).toNat = x.bkBytes.length ∧ sp' + 312#64 = sp' +
      312#64 ∧ x.bkBytes.length < 2 ^ 63 ∧ PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩)
    (by simp [deserializeOk33Spec, arm64_norm])
    ⟨rfl, hbk_len, rfl, hbk_lt63, hbk_deser⟩ (by sep_focus)
    ?_
  clear hcallDeser
  intro s8 hpc8 hrun8 hsp8 hsp8_align hF8 hsym8 hcs8
  dsimp only [deserializeOk33Spec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr8 => ?_
  rcases hcs8 with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8,
    hx29_8⟩
  have hsp8_eq : s8.sp = sp' := by tryFromPost_sp [hsp8, hsp6_eq]
  have h29_8 : s8.readReg64 .x29 = sp' + 512#64 := by simp [hx29_8, h29_6, arm64_norm]
  -- Branch at +1472 .. +1476 (`ldurb w8, [x29, #-200]`; `tbz w8, #0, #192`)
  refine SepWPp.of_sepWP_end hF8 hsym8 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun8, arm64_norm]) ?_
  intro hF9 hsym9
  refine ⟨⟨by simp [hsp8_eq, arm64_norm],
      by simpa [State.spAligned, arm64_norm] using hsp8_align,
      hF9, hsym9, by simp [htr8, htr6, htr4, htr2, htr, arm64_norm]⟩,
    by simp [h29_8, arm64_norm],
    by simp [hx28_8, hx28_6, hx28_4, hx28_2, hx28, arm64_norm],
    by simp [hx27_8, hx27_6, h27_4, arm64_norm],
    by simp [hx26_8, hx26_6, hx26_4, h26_2, arm64_norm],
    by simp [hx25_8, hx25_6, hx25_4, hx25_2, hx25, arm64_norm],
    by simp [hx24_8, hx24_6, h24_4, arm64_norm],
    by simp [hx23_8, hx23_6, hx23_4, hx23_2, hx23, arm64_norm],
    by simp [hx22_8, hx22_6, hx22_4, hx22_2, hx22, arm64_norm],
    by simp [hx21_8, hx21_6, hx21_4, hx21_2, hx21, arm64_norm],
    by simp [hx20_8, hx20_6, hx20_4, hx20_2, hx20, arm64_norm],
    by simp [hx19_8, hx19_6, hx19_4, hx19_2, hx19, arm64_norm], ?_⟩
  have hrepack := slice_rest_to_vecU8Buf A bkCap bkPtr x.bkBytes
  refine Entails.trans
    (Q := (bkPtr ↦ₛ x.bkBytes) ∗ vecU8Rest A bkCap bkPtr x.bkBytes ∗ (((sp' + 312#64) ↦₈ 0#8) ∗
      ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
        logOff img ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 345#64) 15 ∗ A.pool ∗ stackAt sp' smallRootStack))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← sepConj_assoc (bkPtr ↦ₛ x.bkBytes)]
  refine Entails.trans (sepConj_mono_left hrepack) ?_
  apply entails_of_eq; ac_rfl
/-! ## 4. Segment 2: `0x2a1b4 .. 0x2a22c` → `0x2a360` (`+1668 .. +1788` → `+2096`) -/
def spUnused112 (sp' : BitVec 64) : SepProp :=
  memRegion (sp' + 121#64) 7 ∗ memRegion (sp' + 134#64) 2 ∗ memRegion (sp' + 143#64) 1
theorem memRegion32_112_pack (sp' w112 : BitVec 64)
    (w128 : BitVec 32) (w132 : BitVec 16) (b120 c0 c1 c2 c3 c4 c5 c6 : BitVec 8) :
    spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' +
      128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ⊢
      memRegion (sp' + 112#64) 32 := by
  have hs1 := memRegion_split (sp' + 112#64) 8 24 (by decide)
  have hs2 := memRegion_split (sp' + 112#64 + 8#64) 1 23 (by decide)
  have hs3 := memRegion_split (sp' + 112#64 + 8#64 + 1#64) 7 16 (by decide)
  have hs4 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64) 4 12 (by decide)
  have hs5 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 10 (by decide)
  have hs6 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64) 2 8 (by decide)
  have hs7 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64 + 2#64) 7 1
    (by decide)
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [spUnused112]
  refine Entails.trans (Q := ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      memRegion (sp' + 121#64) 7 ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
        memRegion (sp' + 134#64) 2 ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗ memRegion (sp' + 143#64) 1)
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono (pointsTo64_entails_memRegion (sp' + 112#64) w112)
    (sepConj_mono (pointsTo8_entails_memRegion (sp' + 120#64) b120)
      (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 128#64) w128)
        (sepConj_mono (pointsTo16_entails_memRegion (sp' + 132#64) w132)
          (sepConj_mono_right (sepConj_mono_left
            (sevenBytesHeadAt_entails_memRegion7 (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6)))))))
theorem memRegion32_112_unpack (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 32 ⊢
      ∃∗ w112 : BitVec 64, ∃∗ b120 : BitVec 8, ∃∗ w128 : BitVec 32, ∃∗ w132 : BitVec 16,
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
        spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
        ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗ sevenBytesHeadAt (sp' +
        136#64) c0 c1 c2 c3 c4 c5 c6 := by
  have hs1 := memRegion_split (sp' + 112#64) 8 24 (by decide)
  have hs2 := memRegion_split (sp' + 120#64) 1 23 (by decide)
  have hs3 := memRegion_split (sp' + 121#64) 7 16 (by decide)
  have hs4 := memRegion_split (sp' + 128#64) 4 12 (by decide)
  have hs5 := memRegion_split (sp' + 132#64) 2 10 (by decide)
  have hs6 := memRegion_split (sp' + 134#64) 2 8 (by decide)
  have hs7 := memRegion_split (sp' + 136#64) 7 1 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, ProofLib.memRegion_eight (sp' + 112#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (post_memRegion_one_entails (sp' + 120#64))
      (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 128#64))
        (sepConj_mono (post_memRegion_two_entails (sp' + 132#64))
          (sepConj_mono_right (sepConj_mono_left (post_memRegion_seven_entails (sp' +
          136#64))))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w112 => Entails.sepExists_elim fun b120 =>
    Entails.sepExists_elim fun w128 => Entails.sepExists_elim fun w132 =>
    Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 => Entails.sepExists_elim fun c5 =>
    Entails.sepExists_elim fun c6 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w112)
  refine Entails.trans ?_ (Entails.sepExists_intro b120)
  refine Entails.trans ?_ (Entails.sepExists_intro w128)
  refine Entails.trans ?_ (Entails.sepExists_intro w132)
  refine Entails.trans ?_ (Entails.sepExists_intro c0)
  refine Entails.trans ?_ (Entails.sepExists_intro c1)
  refine Entails.trans ?_ (Entails.sepExists_intro c2)
  refine Entails.trans ?_ (Entails.sepExists_intro c3)
  refine Entails.trans ?_ (Entails.sepExists_intro c4)
  refine Entails.trans ?_ (Entails.sepExists_intro c5)
  refine Entails.trans ?_ (Entails.sepExists_intro c6)
  dsimp only [spUnused112]
  apply entails_of_eq; ac_rfl
theorem deser_ok_entails_vecHeader_region (sp' : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
      313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      ∃∗ w320 : BitVec 64, ∃∗ w328 : BitVec 64,
        ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗ ((sp' +
        320#64) ↦₆₄ w320) ∗ ((sp' + 328#64) ↦₆₄ w328) ∗ memRegion (sp' + 336#64) 24 := by
  have h1 : ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗ memRegion (sp' +
        320#64) 40 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      deser_ok_entails_spe_region (sp' + 312#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  refine Entails.trans h1 ?_
  rw [memRegion_split (sp' + 320#64) 8 32 (by decide),
      memRegion_split (sp' + 320#64 + 8#64) 8 24 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight (sp' + 320#64), ProofLib.memRegion_eight (sp' + 328#64),
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w328 => Entails.sepExists_elim fun w320 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w320)
  refine Entails.trans ?_ (Entails.sepExists_intro w328)
  exact Entails.refl _
/-- Step 2: `0x2a1b4 .. 0x2a22c` → `0x2a360` (`+1668 .. +1788` → `+2096`):
loads all 32 bytes of `x.baseKey` from `sp' + 313#64`, spills them to stack slots,
and converts `x.kyberBytes` via `into_boxed_slice` (`0x1afd4`), jumping to `0x2a360` (`+2096`). -/
theorem post_seg2_1b4_to_360_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hIntoBox : IntoBoxedSliceOk img.base C A ctl abs) {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr ikCap msgCap : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1668#64)
    (hrun : s.status = .Running) (hky_lt : kyberCap.toNat < 2 ^ 63)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = 0x44#64) (hx21 : s.readReg64 .x21 = x.ptr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length) (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ memRegion (sp' + 112#64) 32 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' +
        313#64) ↦ₛ x.baseKey.toList) ∗ memRegion (sp' + 345#64) 15 ∗
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        ∃ kyberBoxPtr : BitVec 64,
          PostEpilogueState img s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 =
          kyberBoxPtr ∧ sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
          sf.readReg64 .x25 = 1569#64 ∧
          sf.readReg64 .x24 = sp' + 312#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 =
          0x44#64 ∧ sf.readReg64 .x21 = x.ptr ∧
          sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' +
          68#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 72#64) ↦₆₄ w15) ∗ spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' +
            120#64) ↦₈ b31) ∗
            ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' +
            136#64) b0 b1 b2 b3 b4 b5 b6 ∗
            memRegion (sp' + 312#64) 48 ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗ A.pool ∗
            stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallBox := intoBoxedSlice_ok_at_prekey hIntoBox
  clear hIntoBox
  have hky_eq := cap_add1_eq_of_lt hky_lt
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 1668 124
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcallBox hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2096#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1668#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709491136#64) _
      at hcallBox
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstackBox := stackAt_sub_split sp' intoBoxedSliceStack smallRootStack (by decide) (by decide)
  rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion_four_entails (sp' + 12#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (memRegion32_112_unpack sp')))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w112 => SepWPp.exists_pre fun b120 =>
    SepWPp.exists_pre fun w128 => SepWPp.exists_pre fun w132 =>
    SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
    SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
    SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
    SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun w12 => ?_
  dsimp only [pkLayoutAt]
  -- Phase 1: +1668 .. +1680
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1680#64) ?_
  dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  -- Switch `sp' + 313#64` to tail layout for `ldur w9, [x29, #-196]` at +1680
  have h313_tail := sevenBytesHeadAt_eq_tailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' +
        132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
        313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗
        stackAt sp' smallRootStack)
    (by
      rw [← h313_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  -- Phase 2: +1680 .. +1704
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + 1704#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  -- Switch `sp' + 313#64` back to head layout and `sp' + 136#64` to tail layout for `stur w9, [sp,
  -- #139]` at +1704
  have h136_tail := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' +
        132#64) ↦₁₆ w132) ∗
      sevenBytesTailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
        313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗
        stackAt sp' smallRootStack)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 313#64), ← h136_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  -- Phase 3: +1704 .. +1768
  refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + 1768#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF3 hsym3
  -- Collapse `sp' + 312..360` into `vecHeader` words + `memRegion (sp' + 336#64) 24` and switch
  -- `sp' + 136` back to head
  have h136_head := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6
  have hcollapse :=
    deser_ok_entails_vecHeader_region sp' b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  refine SepWPp.mono_pre (P' := (∃∗ w320 : BitVec 64, ∃∗ w328 : BitVec 64,
        ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗ ((sp' +
        320#64) ↦₆₄ w320) ∗ ((sp' + 328#64) ↦₆₄ w328) ∗
        memRegion (sp' + 336#64) 24) ∗ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' +
        40#64) ↦₆₄ 1569#64) ∗
      ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗ ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' +
        132#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h136_head]
      dsimp only [sevenBytesTailAt]
      refine Entails.trans ?_ (sepConj_mono_left hcollapse)
      dsimp only [sevenBytesHeadAt, pkRestAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w320 => SepWPp.exists_pre fun w328 => ?_
  -- Phase 4: +1768 .. +1776 (into_boxed_slice call)
  refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + 18446744073709491136#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF4 hsym4
  have hvec_ky : vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes =
      ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
      ((sp' + 328#64) ↦₆₄ 1569#64) ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [PreKeyTryFromArgs.kyberBytes_length, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
  refine SepWPp.call_tryFrom (⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩ : VecArg) hcallBox
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF4 hsym4
    (ret_pc := entry + 1780#64) (by simp [arm64_norm]) (by simp [htr, arm64_norm])
    (T := vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗
      stackAt sp' intoBoxedSliceStack)
    (φ := sp' + 312#64 = sp' + 312#64) (by simp [intoBoxedSliceSpec, VecArg.at, hsp_eq, arm64_norm])
    rfl
    (by rw [hvec_ky, hstackBox]; sep_focus)
    ?_
  clear hcallBox
  intro s5 hpc5 hrun5 hsp5 hsp5_align hF5 hsym5 hcs5
  dsimp only [intoBoxedSliceSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hx1_5, htr5⟩ => ?_
  simp only [PreKeyTryFromArgs.kyberBytes_length] at hx1_5
  rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, _, hx26_5, hx27_5, _, hx29_5⟩
  have hsp5_eq : s5.sp = sp' := by tryFromPost_sp [hsp5, hsp_eq]
  -- +1780 .. +1788 (`mov x28, x0`; `mov x25, x1`; `b #308`)
  refine SepWPp.of_sepWP_end hF5 hsym5 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun5, arm64_norm]) ?_
  intro hF6 hsym6
  refine ⟨s5.readReg64 .x0, ⟨by simp [hsp5_eq, arm64_norm],
      by simpa [State.spAligned, arm64_norm] using hsp5_align,
      hF6, hsym6, by simp [htr5, htr, arm64_norm]⟩,
    by simp [hx29_5, hx29, arm64_norm],
    by simp [arm64_norm],
    by simp [hx27_5, hx27, arm64_norm],
    by simp [hx26_5, hx26, arm64_norm],
    by simp [arm64_norm],
    by simp [hx24_5, arm64_norm],
    by simp [hx23_5, hx23, arm64_norm],
    by simp [hx22_5, hx22, arm64_norm],
    by simp [hx21_5, hx21, arm64_norm],
    by simp [hx20_5, hx20, arm64_norm],
    by simp [hx19_5, hx19, arm64_norm], ?_⟩
  have h48 : vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 x.kyberBytes.length) ∗
      memRegion (sp' + 336#64) 24 ⊢ memRegion (sp' + 312#64) 48 := by
    rw [show (48 : Nat) = 24 + 24 by decide, memRegion_split (sp' + 312#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr _)
  refine Entails.trans
    (Q := (vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 x.kyberBytes.length) ∗
      memRegion (sp' + 336#64) 24) ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' +
        68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗ spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' +
        120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' +
        136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        boxU8Buf A (s5.readReg64 .x0) x.kyberBytes ∗ A.pool ∗ stackAt sp' smallRootStack))
    (by
      simp only [hstackBox, hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left h48) ?_
  dsimp only [sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; ac_rfl
/-! ## 5. Segment 3: `0x2a360 .. 0x2a3a8` (`+2096 .. +2168`) -/
theorem memRegion32_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64,
        (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) := by
  rw [memRegion_split a 8 24 (by decide), memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]
theorem words5_memRegion8_72_entails_120 (sp' w0 w1 w2 w3 w4 : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ w0) ∗ ((sp' + 320#64) ↦₆₄ w1) ∗ ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' +
      336#64) ↦₆₄ w3) ∗
    ((sp' + 344#64) ↦₆₄ w4) ∗ memRegion (sp' + 352#64) 8 ∗ memRegion (sp' +
      360#64) 72 ⊢ memRegion (sp' + 312#64) 120 := by
  have hw5 :
      ((sp' + 312#64) ↦₆₄ w0) ∗ ((sp' + 320#64) ↦₆₄ w1) ∗ ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' +
        336#64) ↦₆₄ w3) ∗
      ((sp' + 344#64) ↦₆₄ w4) ⊢ memRegion (sp' + 312#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 312#64) w0 w1 w2 w3 w4
  rw [show (120 : Nat) = 40 + (8 + 72) by decide, memRegion_split (sp' + 312#64) 40 80 (by decide),
      memRegion_split (sp' + 312#64 + 40#64) 8 72 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (Q := (((sp' + 312#64) ↦₆₄ w0) ∗ ((sp' + 320#64) ↦₆₄ w1) ∗ ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' +
      336#64) ↦₆₄ w3) ∗
        ((sp' + 344#64) ↦₆₄ w4)) ∗ (memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left hw5
/-- Step 3: `0x2a360 .. 0x2a3a8` (`+2096 .. +2168`):
calls `IdentityKey::try_from` (`0x2c530`), copies the 32-byte `x.idPub` to `sp' + 144 .. 176`,
spills `x.regId` to `sp' + 56`, and calls `SignalMessage::try_from` (`0x25868`) on `x.inner`. -/
theorem post_seg3_360_to_3a8_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hSigTryFrom : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryFromName) (tryFromSpec A img))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' kyberBoxPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {ik0 ik1 ik2 ik3 : BitVec 64} (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hlt_in : x.inner.length < 2 ^ 32) (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2096#64)
    (hrun : s.status = .Running) (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
        52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗ logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 =
        kyberBoxPtr ∧
        sf.readReg64 .x27 = x.regId.zeroExtend 64 ∧ sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 =
        1569#64 ∧
        sf.readReg64 .x24 = sp' + 312#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗
        ((sp' + 52#64) ↦₃₂ x.regId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗ ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' +
          168#64) ↦₆₄ ik3) ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A msgCap msgPtr x.inner ∗ logOff img ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallIk := identityKeyTryFrom_ok_at_prekey (C := C) (ctl := ctl) (abs := abs) himg
  have hcallSig := signalTryFrom_ok_at_prekey hSigTryFrom
  clear hSigTryFrom
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2096 72
  clear hfn
  dsimp only [tripleRatchetProgAt] at hcallIk hcallSig hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2168#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2096#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 10752#64) _ at hcallIk
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 18446744073709534472#64) _
      at hcallSig
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstackIk := stackAt_sub_split sp' 96 smallRootStack (by decide) (by decide)
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using memRegion_split (sp' + 312#64) 40 8 (by decide)
  -- Phase 1: +2096 .. +2120 (call IdentityKey::try_from)
  refine SepWPp.mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
      52#64) ↦₃₂ x.regId) ∗
      ((sp' + 56#64) ↦₆₄ 33#64) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 144#64) 32 ∗
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ∗
      (ikPtr ↦ₛ x.ikBytes) ∗ vecU8Rest A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
      logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h48_split]
      simp only [sepConj_assoc]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (vecU8Buf_to_slice_rest A ikCap ikPtr x.ikBytes)))))))))))) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 10752#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hik_deser : PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩ := deserialize_djb_ok x.idPub
  have hik_len : (33#64 : BitVec 64).toNat = x.ikBytes.length := by simp
  refine SepWPp.call_noPanic_tryFrom (ikPtr, x.ikBytes, ⟨x.idPub⟩, sp' + 312#64) hcallIk
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 2124#64) (by simp [arm64_norm])
    (T := (ikPtr ↦ₛ x.ikBytes) ∗ memRegion (sp' + 312#64) 40 ∗ logOff img ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ (33#64 : BitVec 64).toNat = x.ikBytes.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩)
    (by simp [identityKeyTryFromSliceOkSpec, hsp_eq, arm64_norm])
    ⟨rfl, hik_len, rfl, hik_deser⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [identityKeyTryFromSliceOkSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h27_2 : s2.readReg64 .x27 = x.regId.zeroExtend 64 := by simp [hx27_2, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  -- Phase 2: +2124 .. +2164 (copy ik0..ik3 to sp'+144..176 and call SignalMessage::try_from)
  have h56_split := ProofLib.pointsTo64_split32 (sp' + 56#64) 33#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_split
  have hrepack_ik := slice_rest_to_vecU8Buf A ikCap ikPtr x.ikBytes
  refine SepWPp.mono_pre
    (P' := (∃∗ w144 : BitVec 64, ∃∗ w152 : BitVec 64, ∃∗ w160 : BitVec 64, ∃∗ w168 : BitVec 64,
        ((sp' + 144#64) ↦₆₄ w144) ∗ ((sp' + 152#64) ↦₆₄ w152) ∗ ((sp' + 160#64) ↦₆₄ w160) ∗ ((sp' +
        168#64) ↦₆₄ w168)) ∗
      ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
        52#64) ↦₃₂ x.regId) ∗
      ((sp' + 56#64) ↦₃₂ 33#32) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦₆₄ ik0) ∗ ((sp' +
        328#64) ↦₆₄ ik1) ∗
      ((sp' + 336#64) ↦₆₄ ik2) ∗ ((sp' + 344#64) ↦₆₄ ik3) ∗ memRegion (sp' + 352#64) 8 ∗
        memRegion (sp' + 360#64) 72 ∗
      Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ (msgPtr ↦ₛ x.inner) ∗
        vecU8Rest A msgCap msgPtr x.inner ∗
      logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h56_split, memRegion32_words4 (sp' + 144#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hik (sp' + 320#64)]
      simp only [hstackIk, hsp_eq,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
      refine Entails.sepExists_elim fun w168 => Entails.sepExists_elim fun w160 =>
        Entails.sepExists_elim fun w152 => Entails.sepExists_elim fun w144 => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro w144)
      refine Entails.trans ?_ (Entails.sepExists_intro w152)
      refine Entails.trans ?_ (Entails.sepExists_intro w160)
      refine Entails.trans ?_ (Entails.sepExists_intro w168)
      refine Entails.trans (Q := ((ikPtr ↦ₛ x.ikBytes) ∗ vecU8Rest A ikCap ikPtr x.ikBytes) ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
          (((sp' + 144#64) ↦₆₄ w144) ∗ ((sp' + 152#64) ↦₆₄ w152) ∗ ((sp' + 160#64) ↦₆₄ w160) ∗
          ((sp' + 168#64) ↦₆₄ w168) ∗
            ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
            52#64) ↦₃₂ x.regId) ∗
            ((sp' + 56#64) ↦₃₂ 33#32) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦₆₄ ik0) ∗ ((sp' +
            328#64) ↦₆₄ ik1) ∗
            ((sp' + 336#64) ↦₆₄ ik2) ∗ ((sp' + 344#64) ↦₆₄ ik3) ∗ memRegion (sp' + 352#64) 8 ∗
            memRegion (sp' + 360#64) 72 ∗ logOff img ∗ A.pool ∗ (memRegion (sp' -
            BitVec.ofNat 64 smallRootStack) (smallRootStack - 96) ∗ stackAt sp' 96)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono hrepack_ik (sepConj_mono_left (vecU8Buf_to_slice_rest A msgCap msgPtr
        x.inner))) ?_
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w144 => SepWPp.exists_pre fun w152 =>
    SepWPp.exists_pre fun w160 => SepWPp.exists_pre fun w168 => ?_
  refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + 18446744073709534472#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  have h120 := words5_memRegion8_72_entails_120 sp' 0xfffffffffffffffe#64 ik0 ik1 ik2 ik3
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 312#64) 120 ∗ (msgPtr ↦ₛ x.inner) ∗ vecU8Rest A msgCap msgPtr x.inner ∗
      logOff img ∗ A.pool ∗ stackAt sp' smallRootStack ∗ ((sp' +
        32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
      ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗ ((sp' +
        60#64) ↦₃₂ 0#32) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' +
        152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes)
    (by
      refine Entails.trans ?_ (sepConj_mono_left h120)
      apply entails_of_eq; ac_rfl) ?_
  have hin_toNat : (BitVec.ofNat 64 x.inner.length).toNat = x.inner.length :=
    Nat.mod_eq_of_lt (by omega)
  refine SepWPp.call_tryFrom (⟨msgPtr, x.inner, sp' + 312#64⟩ : TryFromGhost) hcallSig
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hF3 hsym3
    (ret_pc := entry + 2168#64) (by simp [arm64_norm]) (by simp [htr2, htr, arm64_norm])
    (T := (msgPtr ↦ₛ x.inner) ∗ memRegion (sp' + 312#64) 120 ∗ logOff img ∗
      stackAt sp' smallRootStack ∗ A.pool)
    (φ := (img.FrozenLoaded _ ∧ s2.symtab = img.symtab) ∧ msgPtr = msgPtr ∧
      (BitVec.ofNat 64 x.inner.length).toNat = x.inner.length ∧
      x.inner.length < 2 ^ 32 ∧ sp' + 312#64 = sp' + 312#64)
    (by simp [tryFromSpec, Spec.inImage, hsp2_eq, arm64_norm])
    ⟨⟨hF3, hsym2⟩, rfl, hin_toNat, hlt_in, rfl⟩ (by sep_focus)
    ?_
  clear hcallSig
  intro s4 hpc4 hrun4 hsp4 hsp4_align hF4 hsym4 hcs4
  dsimp only [tryFromSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr4 => ?_
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    hx29_4, _⟩
  have hsp4_eq : s4.sp = sp' := by tryFromPost_sp [hsp4, hsp2_eq]
  refine SepWPp.of_sepWP_end hF4 hsym4 ?_
  refine SepWP.done hpc4 hrun4 ?_
  intro hF5 hsym5
  refine ⟨⟨hsp4_eq, hsp4_align, hF5, hsym5, by simp [htr4, htr2, htr, arm64_norm]⟩,
    by simp [hx29_4, h29_2, arm64_norm],
    by simp [hx28_4, hx28_2, hx28, arm64_norm],
    by simp [hx27_4, h27_2, arm64_norm],
    by simp [hx26_4, hx26_2, hx26, arm64_norm],
    by simp [hx25_4, hx25_2, hx25, arm64_norm],
    by simp [hx24_4, h24_2, arm64_norm],
    by simp [hx23_4, hx23_2, hx23, arm64_norm],
    by simp [hx22_4, hx22_2, hx22, arm64_norm],
    by simp [hx21_4, hx21_2, hx21, arm64_norm],
    by simp [hx20_4, hx20_2, hx20, arm64_norm],
    by simp [hx19_4, hx19_2, hx19, arm64_norm], ?_⟩
  have hrepack_msg := slice_rest_to_vecU8Buf A msgCap msgPtr x.inner
  refine Entails.trans
    (Q := ((msgPtr ↦ₛ x.inner) ∗ vecU8Rest A msgCap msgPtr x.inner) ∗
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        logOff img ∗ stackAt sp' smallRootStack ∗ A.pool ∗ ((sp' +
        32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 60#64) ↦₃₂ 0#32) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' +
        152#64) ↦₆₄ ik1) ∗ ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes))
    (by
      simp only [hsp2_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hrepack_msg) ?_
  apply entails_of_eq; ac_rfl
/-! ## 5. Segment 4: `0x2a3a8 .. 0x2a588` → `0x2a034` (`+2168 .. +2648` → `+1284`) -/
theorem deserialize_error_cases {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PublicKey.deserialize bs = .error e) :
    e = .noKeyTypeIdentifier ∨ (∃ t, e = .badKeyType t) ∨ (∃ n, e = .badKeyLength n) := by
  unfold PublicKey.deserialize at h
  rcases bs with _ | ⟨t, rest⟩
  · simp at h; exact Or.inl h.symm
  · by_cases ht : t ≠ djbType
    · simp [ht] at h; exact Or.inr (Or.inl ⟨t, h.symm⟩)
    · by_cases hlen : 32 ≤ rest.length
      · simp [ht, hlen] at h
      · simp [ht, hlen] at h; exact Or.inr (Or.inr ⟨rest.length + 1, h.symm⟩)
theorem tryFrom_error_cases {codec : SignalMessageProtoCodec} {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : SignalMessage.tryFrom codec bs = .error e) : (∃ n, e = .ciphertextMessageTooShort n) ∨
    (∃ v, e = .legacyCiphertextVersion v) ∨ (∃ v, e = .unrecognizedCiphertextVersion v) ∨
    e = .invalidProtobufEncoding ∨ e = .noKeyTypeIdentifier ∨ (∃ t, e = .badKeyType t) ∨
    (∃ n, e = .badKeyLength n) := by
  simp only [SignalMessage.tryFrom, Bind.bind, Except.bind, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at h
  split_ifs at h
  · injection h with h; exact Or.inl ⟨_, h.symm⟩
  · injection h with h; exact Or.inr (Or.inl ⟨_, h.symm⟩)
  · injection h with h; exact Or.inr (Or.inr (Or.inl ⟨_, h.symm⟩))
  · rcases hdec : codec.decode ((bs.take (bs.length - macLength)).drop 1) with _ | p
    · rw [hdec] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
    · rw [hdec] at h; dsimp only at h
      rcases hrk : p.ratchetKey with _ | rk
      · rw [hrk] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
      · rw [hrk] at h; dsimp only at h
        rcases hpk : PublicKey.deserialize rk with e' | pk
        · rw [hpk] at h; injection h with h; subst h
          rcases deserialize_error_cases hpk with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl⟩)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, rfl⟩)))))
        · rw [hpk] at h; dsimp only at h
          rcases hcnt : p.counter with _ | cnt
          · rw [hcnt] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
          · rw [hcnt] at h; dsimp only at h
            rcases hct : p.ciphertext with _ | ct
            · rw [hct] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
            · rw [hct] at h; contradiction
private theorem speAt_words2_u64 (a tag val : BitVec 64) :
    (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ val) ∗ memRegion (a + 16#64) 32 ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₆₄ val) ∗ memRegion (b + 16#64) 32⌝ := by
  refine Entails.trans ?_ (Entails.sepExists_intro tag)
  refine Entails.trans ?_ (Entails.sepExists_intro val)
  rw [pure_true_emp (fun _ => Entails.refl _), sepConj_emp]
  exact Entails.refl _
private theorem speAt_words2_unit (a tag : BitVec 64) : (a ↦₆₄ tag) ∗ memRegion (a + 8#64) 40 ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            (b ↦₆₄ tag) ∗ memRegion (b + 8#64) 40⌝ := by
  rw [memRegion_split (a + 8#64) 8 32 (by decide), ProofLib.memRegion_eight (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ew1 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro tag)
  refine Entails.trans ?_ (Entails.sepExists_intro ew1)
  have hp : ∀ b : BitVec 64, (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
        (b ↦₆₄ tag) ∗ memRegion (b + 8#64) 40 := fun b => by
    rw [memRegion_split (b + 8#64) 8 32 (by decide), ProofLib.memRegion_eight (b + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro ew1))
  rw [pure_true_emp hp, sepConj_emp]
  exact Entails.refl _
private theorem speAt_words2_u8 (a tag : BitVec 64) (v : BitVec 8) :
    (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₈ v) ∗ memRegion (b + 9#64) 39⌝ := by
  rw [memRegion_split (a + 9#64) 7 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1 := pointsTo8_memRegion7_to_64 (a + 8#64) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  rw [← sepConj_assoc ((a + 8#64) ↦₈ v)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun hi56 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro tag)
  refine Entails.trans ?_ (Entails.sepExists_intro (hi56 ++ v))
  have hp : ∀ b : BitVec 64, (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₆₄ (hi56 ++ v)) ∗ memRegion (b + 16#64) 32 ⊢
        (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₈ v) ∗ memRegion (b + 9#64) 39 := fun b => by
    rw [memRegion_split (b + 9#64) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h2 := pointsTo64_to_8_memRegion7 (b + 8#64) hi56 v
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2
    rw [← sepConj_assoc ((b + 8#64) ↦₈ v)]
    exact sepConj_mono_right (sepConj_mono_left h2)
  rw [pure_true_emp hp, sepConj_emp]
  exact Entails.refl _
theorem speAt_tryFrom_words2 (A : RustAlloc) (a : BitVec 64)
    {codec : SignalMessageProtoCodec} {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : SignalMessage.tryFrom codec bs = .error e) :
    speAt A [] a e ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            speAt A [] b e⌝ := by
  rcases tryFrom_error_cases h with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · exact speAt_words2_u64 a (speWord 3) (BitVec.ofNat 64 n)
  · exact speAt_words2_u8 a (speWord 4) v
  · exact speAt_words2_u8 a (speWord 5) v
  · exact speAt_words2_unit a (speWord 2)
  · exact speAt_words2_unit a (speWord 7)
  · exact speAt_words2_u8 a (speWord 8) t
  · exact speAt_words2_u64 a (speWord 9) (BitVec.ofNat 64 n)
theorem words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion32_words4 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (sepConj_mono (Entails.sepExists_intro w2)
        (Entails.sepExists_intro w3)))
theorem boxU8Buf_kyber_dealloc (A : RustAlloc) (ptr : BitVec 64) (x : PreKeyTryFromArgs) :
    boxU8Buf A ptr x.kyberBytes ⊢ ⌜ptr ≠ 0#64⌝ ∗ A.live ptr 1569 1 ∗ memRegion ptr 1569 := by
  unfold boxU8Buf
  have hne : x.kyberBytes ≠ [] := by simp [PreKeyTryFromArgs.kyberBytes]
  simp only [hne, ↓reduceIte, PreKeyTryFromArgs.kyberBytes_length]
  refine Entails.pure_left fun ⟨hptr, _⟩ => ?_
  rw [pure_true_emp hptr, emp_sepConj]
  exact sepConj_mono_right (by simpa using pointsToBytes_entails_memRegion ptr x.kyberBytes)
theorem memRegion48_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64,
        (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗ (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) ∗ (∃∗
        w5 : BitVec 64, (a + 40#64) ↦₆₄ w5) := by
  rw [show (48 : Nat) = 8 + (8 + 32) by decide, memRegion_split a 8 40 (by decide),
    memRegion_split (a + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    memRegion32_words4 (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem words6_entails_memRegion48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a +
      32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion a 48 := by
  rw [memRegion48_words6 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono (Entails.sepExists_intro w3) (sepConj_mono (Entails.sepExists_intro w4)
            (Entails.sepExists_intro w5)))))
theorem words7_memRegion64_entails_memRegion120 (a w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a +
      32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
    ((a + 48#64) ↦₆₄ w6) ∗ memRegion (a + 56#64) 64 ⊢ memRegion a 120 := by
  rw [show (120 : Nat) = 8 + (48 + 64) by decide, memRegion_split a 8 112 (by decide),
    memRegion_split (a + 8#64) 48 64 (by decide),
    ProofLib.memRegion_eight a, memRegion48_words6 (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono (Entails.sepExists_intro w3) (sepConj_mono (Entails.sepExists_intro w4)
            (sepConj_mono (Entails.sepExists_intro w5) (sepConj_mono (Entails.sepExists_intro w6)
                (Entails.refl _)))))))
theorem err_result_entails_preKeyResultAt (A : RustAlloc) (x : PreKeyTryFromArgs)
    {e : SignalProtocolError} (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .error e)
    (ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64) (hpack : ∀ b : BitVec 64,
      (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢ speAt A [] b e) :
    (x.sret ↦₆₄ 18446744073709551615#64) ∗ ((x.sret + 8#64) ↦₆₄ ew0) ∗ ((x.sret + 16#64) ↦₆₄ ew1) ∗
    ((x.sret + 24#64) ↦₆₄ ew2) ∗ ((x.sret + 32#64) ↦₆₄ ew3) ∗ ((x.sret + 40#64) ↦₆₄ ew4) ∗
      ((x.sret + 48#64) ↦₆₄ ew5) ∗
    memRegion (x.sret + 56#64) 192 ⊢ preKeyResultAt A x.sret x := by
  unfold preKeyResultAt
  rw [hsig]
  have hm32 := words4_entails_memRegion32 (x.sret + 24#64) ew2 ew3 ew4 ew5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm32
  have hsp_b := hpack (x.sret + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp_b
  have h1 :
      ((x.sret + 8#64) ↦₆₄ ew0) ∗ ((x.sret + 16#64) ↦₆₄ ew1) ∗ ((x.sret + 24#64) ↦₆₄ ew2) ∗
        ((x.sret + 32#64) ↦₆₄ ew3) ∗
      ((x.sret + 40#64) ↦₆₄ ew4) ∗ ((x.sret + 48#64) ↦₆₄ ew5) ⊢
        speAt A [] (x.sret + 8#64) e :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) hsp_b
  have h2 :
      (((x.sret + 8#64) ↦₆₄ ew0) ∗ ((x.sret + 16#64) ↦₆₄ ew1) ∗ ((x.sret + 24#64) ↦₆₄ ew2) ∗
        ((x.sret + 32#64) ↦₆₄ ew3) ∗
        ((x.sret + 40#64) ↦₆₄ ew4) ∗ ((x.sret + 48#64) ↦₆₄ ew5)) ∗ memRegion (x.sret + 56#64) 192 ⊢
        speAt A [] (x.sret + 8#64) e ∗ memRegion (x.sret + 56#64) 192 :=
    sepConj_mono_left h1
  simpa [sepConj_assoc, errTag] using sepConj_mono_right (P :=
    x.sret ↦₆₄ 18446744073709551615#64) h2
theorem memRegion248_split_err (r : BitVec 64) :
    memRegion r 248 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64,
        (r + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗ (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗ (∃∗
        w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 := by
  rw [show (248 : Nat) = 8 + (48 + 192) by decide, memRegion_split r 8 240 (by decide),
    memRegion_split (r + 8#64) 48 192 (by decide),
    ProofLib.memRegion_eight r, memRegion48_words6 (r + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem post_seg4_err_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)} (hS : TripleRatchetHooks C A S abs)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {e : SignalProtocolError}
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .error e)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 2168#64)
    (hrun : s.status = .Running) (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 176#64) 48 ∗ signalMessageResultAt A [] (sp' +
        312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion x.sret 248 ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗
        stackAt sp' smallRootStack)
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧ (Pf ⊢ preKeyResultAt A x.sret x ∗ ((sp' +
        80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 176#64) 48 ∗
          memRegion (sp' + 312#64) 120 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hdealloc := dealloc_ok_at_prekey hS.alloc (b := img.base) (C := C) (ctl := ctl)
  have h554 := @cleanup_554_wp img C A S ctl abs hS s0
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have hfn := libsignalSessionCode_fnOff_0x29c14
  responder_wire_fetches_from img.base H hfn 0x29c14 2168 32
  responder_wire_fetches_from img.base H hfn 0x29c14 2544 52
  clear hfn
  dsimp only [tripleRatchetProgAt] at hdealloc h554 hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 2168#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) _ at hdealloc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  rw [hsig]
  dsimp only [signalMessageResultAt, errResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  -- 1. Unpack boxU8Buf A kyberBoxPtr x.kyberBytes
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (boxU8Buf_kyber_dealloc A kyberBoxPtr x))))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hky_ne => ?_
  -- 2. Unpack speAt A [] (sp' + 320#64) e
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (speAt_tryFrom_words2 A (sp' + 320#64) hsig)))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew0 => SepWPp.exists_pre fun ew1 => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hpack => ?_
  -- 3. Unpack memRegion (sp' + 336#64) 32 in precondition
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (entails_of_eq (memRegion32_words4 (sp' + 336#64)))))))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew5 => SepWPp.exists_pre fun ew4 =>
    SepWPp.exists_pre fun ew3 => SepWPp.exists_pre fun ew2 => ?_
  -- 4. Unpack memRegion (sp' + 176#64) 48 in precondition
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion48_words6 (sp' + 176#64)))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun t5 => SepWPp.exists_pre fun t4 =>
    SepWPp.exists_pre fun t3 => SepWPp.exists_pre fun t2 =>
    SepWPp.exists_pre fun t1 => SepWPp.exists_pre fun t0 => ?_
  -- 5. Unpack memRegion x.sret 248 in precondition
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (entails_of_eq (memRegion248_split_err x.sret))))))))))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun s0_6 => SepWPp.exists_pre fun s0_5 =>
    SepWPp.exists_pre fun s0_4 => SepWPp.exists_pre fun s0_3 =>
    SepWPp.exists_pre fun s0_2 => SepWPp.exists_pre fun s0_1 =>
    SepWPp.exists_pre fun s0_0 => ?_
  have hky_beq : (kyberBoxPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hky_ne
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_noPanic_tryFrom (kyberBoxPtr, 1569, 1) hdealloc
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2596#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live kyberBoxPtr 1569 1 ∗ memRegion kyberBoxPtr 1569 ∗
      stackAt s.sp allocHookStack)
    (φ := kyberBoxPtr = kyberBoxPtr ∧ (1569#64 : BitVec 64).toNat = 1569 ∧
      (1#64 : BitVec 64).toNat = 1)
    (by simp [rustDeallocSpec, hsp_eq, arm64_norm])
    ⟨rfl, rfl, rfl⟩
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hdealloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [rustDeallocSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨_, _, _, _, hx23_2, _, _, hx26_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_2, hx23, arm64_norm]
  have h26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_2, hx26, arm64_norm]
  have herr_res := err_result_entails_preKeyResultAt A x hsig ew0 ew1 ew2 ew3 ew4 ew5 hpack
  have hm48 :
      ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗ ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' +
        200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
        memRegion (sp' + 176#64) 48 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words6_entails_memRegion48 (sp' + 176#64) ew0 ew1 ew2 ew3 ew4 ew5
  have hm120 :
      ((sp' + 312#64) ↦₆₄ errTag) ∗ ((sp' + 320#64) ↦₆₄ ew0) ∗ ((sp' + 328#64) ↦₆₄ ew1) ∗
      ((sp' + 336#64) ↦₆₄ ew2) ∗ ((sp' + 344#64) ↦₆₄ ew3) ∗ ((sp' + 352#64) ↦₆₄ ew4) ∗ ((sp' +
        360#64) ↦₆₄ ew5) ∗
      memRegion (sp' + 368#64) 64 ⊢
        memRegion (sp' + 312#64) 120 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words7_memRegion64_entails_memRegion120 (sp' + 312#64) errTag ew0 ew1 ew2 ew3 ew4 ew5
  have hcomb := sepConj_mono_right
    (P := ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (sepConj_mono herr_res (sepConj_mono hm48 hm120))
  refine SepWPp.mono_pre (P' :=
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack) ∗ (preKeyResultAt A x.sret x ∗ memRegion (sp' +
        176#64) 48 ∗
        memRegion (sp' + 312#64) 120))
    (by
      refine Entails.trans ?_ hcomb
      simp only [hstack, hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (h554 x.inner x.ikBytes x.bkBytes
      ⟨hsp2_eq, hsp2_align, hF2, hsym2, by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 h23_2 h26_2)
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; ac_rfl
end CryptoVerification.E2E.Pqxdh.ResponderWire
