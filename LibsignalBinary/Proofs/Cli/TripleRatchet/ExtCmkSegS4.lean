/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSeams
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FrameAndKeyBytes
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segment S4 (`CmkS4SpecX`) for `consume_message_key`

Proves the advance-path epilogue (`s4_ok_x : CmkS4SpecX`) of `RatchetState::consume_message_key` on
`SP2Ext img.base ext` at `cmkStackX = 20480` bytes.
-/

@[expose] public section

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession.AdvanceEpilogue
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Int64_mk_toBitVec UInt64_ofNat_toBitVec UInt64_mk_toBitVec BitVec_ofFin_eq_ofNat

theorem L1_SegS4 : True := trivial

/-! ## Stack Splits -/

theorem stackAt_20000_split_18432 (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 1568 ∗ stackAt sp hmacStackX :=
  stackAt_split_bottom sp 18432 1568 (by decide)

theorem stackAt_20000_split_17408 (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 2592 ∗ stackAt sp findIndexStackX :=
  stackAt_split_bottom sp 17408 2592 (by decide)

theorem stackAt_20000_split_16384 (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 3616 ∗ stackAt sp extHookStack :=
  stackAt_split_bottom sp 16384 3616 (by decide)

theorem stackAt_cmkStackX_repack (sp0 : BitVec 64) (s0 : State) :
    stackAt (sp0 - 480#64) 20000 ∗ memRegion (sp0 - 480#64) 384 ∗ cmkSavedRegs sp0 s0 ⊢
      stackAt sp0 cmkStackX := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (cmkSavedRegs_entails_memRegion96 sp0 s0))) ?_
  have h96 : sp0 - 480#64 + 384#64 = sp0 - 96#64 := by bv_arith
  rw [← h96, ← memRegion_split (sp0 - 480#64) 384 96 (by decide)]
  change memRegion (sp0 - 480#64 - 20000#64) 20000 ∗ memRegion (sp0 - 480#64) 480 ⊢
    memRegion (sp0 - 20480#64) 20480
  have h20480 : sp0 - 480#64 - 20000#64 = sp0 - 20480#64 := by bv_arith
  have h480 : sp0 - 20480#64 + 20000#64 = sp0 - 480#64 := by bv_arith
  rw [h20480, ← h480, ← memRegion_split (sp0 - 20480#64) 20000 480 (by decide)]
  exact Entails.refl _

def advanceEpiloguePostX (F : ShaCompress) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cmkSpecX F A img).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def advanceEpiloguePanicX (F : ShaCompress) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cmkSpecX F A img).onPanic x s0 sf ∗ R)

theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

/-! ## State-Specialized Callee Wrappers -/

theorem shim_ok_at_state_x {b : BitVec 64}
    {ext : String → Option (State → State)} {img : Obj.Image}
    {entry : BitVec 64} {s : State}
    (hshim : subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      { pre := fun (_ : Unit) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab⌝ ∗ stackAt s'.sp extHookStack
        post := fun (_ : Unit) s0 sf =>
          ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack } := by
  refine subroutine_ok_outcome_intro fun u R s0 hpc hrun hm hsp => ?_
  have hpre' : s0.mem ⊨ (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img).pre u s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack,
      emp_sepConj]
    apply Entails.pure_left
    rintro ⟨hmem, hsym'⟩
    exact Entails.pure_right ⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩ (Entails.refl _)
  refine hshim.mono_outcome u R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hpost⟩ | hout
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simpa only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] using hpost
  · exact Or.inr hout

theorem alloc_ok_at_state_x {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    {entry : BitVec 64} {s : State}
    (halloc : subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      { pre := fun (size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            LayoutOk size align⌝ ∗
          A.pool ∗ stackAt s'.sp extHookStack
        post := (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack).post } := by
  refine subroutine_ok_outcome_intro fun ⟨size, align⟩ R s0 hpc hrun hm hsp => ?_
  refine halloc.mono_outcome (size, align) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem dealloc_ok_at_state_x {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    {entry : BitVec 64} {s : State}
    (hdealloc : subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      { pre := fun (p, size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool ∗ stackAt s'.sp extHookStack
        post := (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).post } := by
  refine subroutine_ok_outcome_intro fun ⟨p, size, align⟩ R s0 hpc hrun hm hsp => ?_
  refine hdealloc.mono_outcome (p, size, align) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem hmac_ok_at_state_x {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64} {s : State}
    (hhmac : subroutine_ok (SP2Ext b ext) (entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) ((hmacSpecX F).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) (entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp hmacStackX
        post := (hmacSpecX F).post } := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine hhmac.mono_outcome (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, hmacSpecX]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem findIndex_ok_at_state_x {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    {entry : BitVec 64} {s : State}
    (hfind : subroutine_ok (SP2Ext b ext) (entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) ((findIndexSpecX img A).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext) (entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s'.sp findIndexStackX
        post := (findIndexSpecX img A).post } := by
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp => ?_
  refine hfind.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, findIndexSpecX]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

/-! ## OOM Panic and Shared Return Epilogue (`+0x9b4` and `+0x77c`) -/

theorem advanceEpilogue_oom_panic_x {b : BitVec 64} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    (x : ConsumeMessageKeyGhost) (R P : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 2484#64)
    (hrun : s.status = .Running)
    (_hsp : s.spAligned = true)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hfail : allocFailedIn s0 s ∧ s0.trace <+: s.trace) :
    SepWPp (SP2Ext b ext) (s0.readReg64 Reg.lr) s P
      (advanceEpiloguePostX F A img x R s0) (advanceEpiloguePanicX F A img x R s0) := by
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hpanic := panic_at_handle_error_ext (b := b) (ext := ext) hfn
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  advanceEpilogue_fetches b (Rust.withPanics ext) hfn 0x9b4 3
  clear hfn
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) hfrozen hsym
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro _hfrozen' _hsym'
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by simpa using hpanic) fun hm' => ?_
  simpa only [cmkSpecX, consumeMessageKeySpec, Spec.inImage, sepConj_assoc] using
    allowPanic_panicked (⟨Or.inr (by simpa [allocFailedIn, Rust.panicked] using hfail.1),
      by simpa [Rust.panicked] using hfail.2⟩) hm'

theorem advanceEpilogue_ret_epilogue_x {b : BitVec 64} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1916#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmodel_ok : (x.model F).1 ≠ .error .panic)
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp (SP2Ext b ext) (s0.readReg64 Reg.lr) s
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 20000 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostX F A img x R s0) (advanceEpiloguePanicX F A img x R s0) := by
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  advanceEpilogue_fetches b (Rust.withPanics ext) hfn 0x77c 8
  clear hfn
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  unfold cmkSavedRegs
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen hsym
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro _hfrozen' _hsym'
  refine SepWPp.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨fun hm => ?_, rfl, by advanceEpilogue_cc_close⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold cmkSpecX Spec.inImage
  dsimp only
  have hstk := stackAt_cmkStackX_repack s0.sp s0
  unfold cmkSavedRegs at hstk
  have hex :
      ratchetAt A x.self G' (x.model F).2 ⊢
        ∃∗ G'' : RatchetGhost,
          ⌜x.G.AgreeExcept G'' (x.touched F)⌝ ∗ ratchetAt A x.self G'' (x.model F).2 :=
    Entails.sepExists_right G' (Entails.pure_right hagree (Entails.refl _))
  refine Entails.pure_right ⟨hmodel_ok, htr⟩ ?_
  refine Entails.trans ?_ (sepConj_mono_left hex)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))))
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by ac_rfl)

/-! ## Post-HMAC(1) Epilogue (`+0x5a8 .. +0x5e0`) -/

set_option maxHeartbeats 800000 in
theorem advanceEpilogue_after_hmac1_x {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (ckc : ChainKey) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1448#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s
      (ratchetAt A x.self G' (x.model F).2 ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 20000 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ [1#8]) ∗
       memRegion (s0.sp - 319#64) 31 ∗
       ((s0.sp - 224#64) ↦ₛ (ckc.messageKeys F).seed) ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostX F A img x R s0) (advanceEpiloguePanicX F A img x R s0) := by
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hshim := hA.shim_ok_at cmkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have halloc := hA.alloc_ok_at cmkName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hoom_fn := @advanceEpilogue_oom_panic_x img.base F A ext img x R
  have hret_fn := @advanceEpilogue_ret_epilogue_x img.base F A ext img x G' R s0
  advanceEpilogue_fetches img.base (Rust.withPanics ext) hfn 0x5a8 15
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  obtain ⟨w0, w1, w2, w3, _, hw_seed⟩ := exists_unpack64_of_length_32 (length_messageKeys_seed F ckc)
  rw [hw_seed (s0.sp - 224#64), stackAt_20000_split_16384 (s0.sp - 480#64)]
  refine SepWPp.conseq_pre (sepConj_mono_right (sepConj_mono_left (memRegion88_unpack x.ret))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun t0 => SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun p0 => SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun i0 => ?_
  have hshim0 := shim_ok_at_state_x hshim hfrozen hsym
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1456)) hfrozen hsym
  wp_steps
  wp_call hshim0 ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen0 hsym0
  have halloc0 := alloc_ok_at_state_x halloc hfrozen0 hsym0
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1468)) hfrozen0 hsym0
  wp_steps
  wp_call halloc0 (32, 1)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen1 hsym1
  have hsp_sf1 : sf_1.spAligned = true := by
    unfold State.spAligned at *
    simp only [wp_norm, arm64_norm, *]
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim fun htr_oom => ?_
    apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (2484)) hfrozen1 hsym1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfrozen2 hsym2
    exact hoom_fn _ s0 _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      hsp_sf1 hfrozen2 hsym2
      (AdvanceEpilogue.allocFailedIn_of_eq (by simp only [wp_norm, arm64_norm, *]))
  · simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_halign, htr_alloc⟩ => ?_
    have hoom' : ¬sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    rw [memRegion32_eq_exists_cells4 (sf_1.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
    apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1916)) hfrozen1 hsym1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfrozen2 hsym2
    have hmodel_ok : (x.model F).1 ≠ .error .panic := by rw [hm1]; nofun
    refine SepWPp.conseq_pre ?_
      (hret_fn _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned] using hsp_sf1)
        (by simp only [wp_norm, arm64_norm, *]) hfrozen2 hsym2
        (by simp only [wp_norm, arm64_norm, *]) hmodel_ok hagree)
    have h20480 : s0.sp - 480#64 - 20000#64 = s0.sp - 20480#64 := by bv_arith
    have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    rw [hm1, stackAt_20000_split_16384 (s0.sp - 480#64), h20480, hsf_sp]
    have hres := resultAt_ok_of_parts A x.ret (sf_1.readReg64 Reg.x0) (ckc.messageKeys F)
      (length_messageKeys_seed F ckc) hoom
    rw [hw_seed (sf_1.readReg64 Reg.x0)] at hres
    have hck_mem := chainKey_key_idx_entails_memRegion x.ckA ckc
    have hfrm_mem := cmkLoopFrame_repack s0.sp x.ret x.counter 1#8
    rw [← pointsTo8_eq_pointsToBytes1] at hfrm_mem
    have h224 :
        ((s0.sp - 224#64) ↦₆₄ w0) ∗ ((s0.sp - 216#64) ↦₆₄ w1) ∗
          ((s0.sp - 208#64) ↦₆₄ w2) ∗ ((s0.sp - 200#64) ↦₆₄ w3) ⊢
          memRegion (s0.sp - 224#64) 32 := by
      have := cells4_entails_memRegion32 (s0.sp - 224#64) w0 w1 w2 w3
      have ha1 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_arith
      have ha2 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_arith
      have ha3 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_arith
      rwa [ha1, ha2, ha3] at this
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono hres
        (sepConj_mono_right (sepConj_mono hck_mem
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hfrm_mem)))))))
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left h224))))))))))))
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by ac_rfl)

/-! ## Chain Key Update and HMAC(1) Call (`+0x578 .. +0x5a4`) -/

set_option maxHeartbeats 800000 in
theorem advanceEpilogue_set_chain_and_hmac1_x {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hhmac : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((hmacSpecX F).inImage img))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (ptr_ck c0 p0 l0 : BitVec 64) (idx0 : BitVec 32)
    (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1400#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx20 : s.readReg64 .x20 = (ckc.index + 1#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = ptr_ck)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hptr_nz : ptr_ck ≠ 0)
    (hci : ci < stc.receiverChains.length)
    (hgi : ci < Gc.chains.length)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s
      (ratchetRestAtChain A x.self Gc stc ci chc hgi ∗
       ((c_Addr + 72#64) ↦₆₄ c0) ∗
       ((c_Addr + 80#64) ↦₆₄ p0) ∗
       ((c_Addr + 88#64) ↦₆₄ l0) ∗
       ((c_Addr + 96#64) ↦₃₂ idx0) ∗
       memRegion (c_Addr + 100#64) 4 ∗
       A.live ptr_ck 32 1 ∗
       (ptr_ck ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 20000 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostX F A img x R s0) (advanceEpiloguePanicX F A img x R s0) := by
  intro c_Addr
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hafter_fn := @advanceEpilogue_after_hmac1_x F A ext img hA x
  advanceEpilogue_fetches img.base (Rust.withPanics ext) hfn 0x578 12
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  have hsplit320 :
      memRegion (s0.sp - 320#64) 32 =
        (∃∗ b0 : BitVec 8, ((s0.sp - 320#64) ↦₈ b0)) ∗ memRegion (s0.sp - 319#64) 31 := by
    have h319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_arith
    rw [show (32 : Nat) = 1 + 31 from rfl,
        memRegion_split (s0.sp - 320#64) 1 31 (by decide),
        memRegion_one (s0.sp - 320#64), h319]
  rw [hsplit320, stackAt_20000_split_18432 (s0.sp - 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) hfrozen hsym
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen1 hsym1
  have hhmac1 := hmac_ok_at_state_x hhmac hfrozen1 hsym1
  have hlen_key : (keyToBytes32 ckc.key).length = 32 := length_keyToBytes32 ckc.key
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 1#8]
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1448)) hfrozen1 hsym1
  wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen2 hsym2
  have hsp_sf : sf.spAligned = true := by
    simpa [State.spAligned, hsp_sf, hsp_eq] using hsp
  have hopt := optChainKeyAt_some_of_parts A (c_Addr + 72#64) ptr_ck (chainStepN F 1 ckc) hptr_nz
  have hrepack := repack_optChainKeyAt A x.self Gc stc ci chc hci hgi
    ⟨32#64, ptr_ck⟩ (some (chainStepN F 1 ckc))
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hsrk hmax hklen
  have hst_eq : stc.setChain ci { chc with chainKey := some (chainStepN F 1 ckc) } = (x.model F).2 := by
    rw [hm2]; rfl
  rw [hst_eq] at hrepack
  have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
  have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
  have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
  have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
  rw [hc80, hc88, hc96, hc100] at hopt
  have hidx_eq : ckc.index + 1#32 = (chainStepN F 1 ckc).index := by
    simp [chainStepN_one]
  let G' := Gc.setChain ci { Gc.chains[ci]'hgi with ck := ⟨32#64, ptr_ck⟩ }
  have hagree' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouched]
    exact RatchetGhost.AgreeExcept.setChain_of_agreeExcept hagree_Gc hgi
      { Gc.chains[ci]'hgi with ck := ⟨32#64, ptr_ck⟩ } rfl rfl
  refine SepWPp.conseq_pre ?_
    (hafter_fn G' ckc R s0 sf
      hpc_sf hrun_sf (by simp only [wp_norm, arm64_norm, *]) hsp0 hsp_sf (by simp only [wp_norm, arm64_norm, *]) hfrozen2 hsym2
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      hm1 hagree')
  have h20480 : s0.sp - 480#64 - 20000#64 = s0.sp - 20480#64 := by bv_arith
  rw [hmacWith_one_eq_messageKeys_seed F ckc,
      stackAt_20000_split_18432 (s0.sp - 480#64), h20480, hidx_eq, hsp_eq,
      pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 1#8]
  have hchain_pack :
      (((c_Addr + 72#64) ↦₆₄ 32#64) ∗
       ((c_Addr + 80#64) ↦₆₄ ptr_ck) ∗
       ((c_Addr + 88#64) ↦₆₄ 32#64) ∗
       ((c_Addr + 96#64) ↦₃₂ (chainStepN F 1 ckc).index) ∗
       memRegion (c_Addr + 100#64) 4 ∗
       A.live ptr_ck 32 1 ∗
       (ptr_ck ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key)) ∗
      ratchetRestAtChain A x.self Gc stc ci chc hgi ⊢
      ratchetAt A x.self G' (x.model F).2 :=
    Entails.trans (sepConj_mono_left hopt) hrepack
  refine Entails.trans ?_ (sepConj_mono_left hchain_pack)
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by ac_rfl)

/-! ## Post-`find_receiver_chain_index` Allocation Diamond (`+0x520 .. +0x578`) -/

theorem ule_false_of_lt {a b : BitVec 64} (h : a < b) : b.ule a = false := by
  rw [BitVec.lt_def] at h
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  omega

set_option maxHeartbeats 800000 in
theorem advanceEpilogue_after_find_index_x {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hhmac : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((hmacSpecX F).inImage img))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1312#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = Gc.chainsPtr)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 stc.receiverChains.length)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hci : ci < stc.receiverChains.length)
    (hgi : ci < Gc.chains.length)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s
      (optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey (c_Addr + 72#64) ∗
       ratchetRestAtChain A x.self Gc stc ci chc hgi ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 20000 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       memRegion (s0.sp - 224#64) 32 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostX F A img x R s0) (advanceEpiloguePanicX F A img x R s0) := by
  intro c_Addr
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hshim := hA.shim_ok_at cmkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have halloc := hA.alloc_ok_at cmkName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hdealloc := hA.dealloc_ok_at cmkName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hoom_fn := @advanceEpilogue_oom_panic_x img.base F A ext img x R
  have hset_fn := @advanceEpilogue_set_chain_and_hmac1_x F A ext img hA hhmac x Gc stc ckc ci chc
  advanceEpilogue_fetches img.base (Rust.withPanics ext) hfn 0x520 22
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  obtain ⟨w0, w1, w2, w3, _, hw_ck⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 (chainStepN F 1 ckc).key)
  rw [hw_ck (s0.sp - 320#64), stackAt_20000_split_16384 (s0.sp - 480#64)]
  have hshim0 := shim_ok_at_state_x hshim hfrozen hsym
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1328)) hfrozen hsym
  wp_steps
  wp_call hshim0 ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen0 hsym0
  have halloc0 := alloc_ok_at_state_x halloc hfrozen0 hsym0
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1340)) hfrozen0 hsym0
  wp_steps
  wp_call halloc0 (32, 1)
  apply SepWP.done hpc_sf_1 hrun_sf_1
  intro hfrozen1 hsym1
  have hsp_sf1 : sf_1.spAligned = true := by
    simpa [State.spAligned, hsp_sf_1, hsp_sf, hsp_eq] using _hsp
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim fun htr_oom => ?_
    apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (2484)) hfrozen1 hsym1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfrozen2 hsym2
    exact hoom_fn _ s0 _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned] using hsp_sf1) hfrozen2 hsym2
      (AdvanceEpilogue.allocFailedIn_of_eq (by simp only [wp_norm, arm64_norm, *]))
  · simp only [hoom, ite_false, sepConj_assoc]
    have hoom_false : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
      beq_false_of_ne hoom
    have hoom_not_true : ¬((sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true) := by
      rw [hoom_false]; decide
    refine SepWPp.pure_elim fun ⟨_halign, htr_alloc⟩ => ?_
    rw [memRegion32_eq_exists_cells4 (sf_1.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
    have hci_bv : BitVec.ofNat 64 ci < BitVec.ofNat 64 stc.receiverChains.length := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hci
    have hci_not_le : ¬(BitVec.ofNat 64 stc.receiverChains.length ≤ BitVec.ofNat 64 ci) := by
      bv_omega
    have hci_ule : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
      ule_false_of_lt hci_bv
    have hci_not_ule : ¬((BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = true) := by
      rw [hci_ule]; decide
    apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1376)) hfrozen1 hsym1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfrozen2 hsym2
    have hc_addr_eq :
        Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = c_Addr := by
      change Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
      rw [BitVec.ofNat_mul]
    have h20480 : s0.sp - 480#64 - 20000#64 = s0.sp - 20480#64 := by bv_arith
    have h320_mem :
        ((s0.sp - 320#64) ↦₆₄ w0) ∗ ((s0.sp - 312#64) ↦₆₄ w1) ∗
          ((s0.sp - 304#64) ↦₆₄ w2) ∗ ((s0.sp - 296#64) ↦₆₄ w3) ⊢
          memRegion (s0.sp - 320#64) 32 := by
      have := cells4_entails_memRegion32 (s0.sp - 320#64) w0 w1 w2 w3
      have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
      have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
      have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
      rwa [ha1, ha2, ha3] at this
    simp only [sepConj_assoc]
    cases hck_opt : chc.chainKey with
    | none =>
      have hnone_unpack := optChainKeyAt_none_unpack A (Gc.chains[ci]'hgi).ck (c_Addr + 72#64)
      have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
      have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
      have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
      have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
      rw [hc80, hc88, hc96, hc100] at hnone_unpack
      refine SepWPp.conseq_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hnone_unpack)))))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun idx0 => SepWPp.exists_elim fun l0 =>
        SepWPp.exists_elim fun p0 => ?_
      have hslt_none : BitVec.slt optChainKeyNone 1#64 = true := by decide
      apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1400)) hfrozen2 hsym2
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfrozen3 hsym3
      refine SepWPp.conseq_pre ?_
        (hset_fn (sf_1.readReg64 Reg.x0) optChainKeyNone p0 l0 idx0 R s0 _
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hsp0
          (by simpa [State.spAligned] using hsp_sf1)
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hfrozen3 hsym3
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [c_Addr, wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          hoom hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
          hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left h320_mem)))))))))))))))))
      dsimp only [c_Addr]
      rw [hw_ck (sf_1.readReg64 Reg.x0), stackAt_20000_split_16384 (s0.sp - 480#64), h20480, hsp_sf, hsp_eq]
      have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
      exact heq (by ac_rfl)
    | some old_ck =>
      have hsome_unpack := optChainKeyAt_some_entails_dealloc A (Gc.chains[ci]'hgi).ck old_ck (c_Addr + 72#64)
      unfold vecHeader at hsome_unpack
      have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
      have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
      have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
      have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
      rw [hc80, hc88, hc96, hc100] at hsome_unpack
      refine SepWPp.conseq_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hsome_unpack)))))))) ?_
      have hpull_pure :
          (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
            (sf_1.readReg64 Reg.x0 ↦₆₄ w0) ∗
            ((sf_1.readReg64 Reg.x0 + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 Reg.x0 + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 Reg.x0 + 24#64) ↦₆₄ w3) ∗
            A.pool ∗
            stackAt sf.sp extHookStack ∗
            (((c_Addr + 72#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.cap ∗
              (c_Addr + 80#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.ptr ∗
              (c_Addr + 88#64) ↦₆₄ 32#64) ∗
             (c_Addr + 96#64) ↦₃₂ old_ck.index ∗
             memRegion (c_Addr + 100#64) 4 ∗
             (⌜32 ≤ (Gc.chains[ci]'hgi).ck.cap.toNat ∧
               (Gc.chains[ci]'hgi).ck.cap.toNat < 2 ^ 63 ∧
               (Gc.chains[ci]'hgi).ck.ptr ≠ 0⌝ ∗
              if (Gc.chains[ci]'hgi).ck.cap = 0 then emp
              else A.live (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat 1 ∗
                memRegion (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat))) =
          (⌜32 ≤ (Gc.chains[ci]'hgi).ck.cap.toNat ∧
            (Gc.chains[ci]'hgi).ck.cap.toNat < 2 ^ 63 ∧
            (Gc.chains[ci]'hgi).ck.ptr ≠ 0⌝ ∗
           (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
            (sf_1.readReg64 Reg.x0 ↦₆₄ w0) ∗
            ((sf_1.readReg64 Reg.x0 + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 Reg.x0 + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 Reg.x0 + 24#64) ↦₆₄ w3) ∗
            A.pool ∗
            stackAt sf.sp extHookStack ∗
            ((c_Addr + 72#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.cap) ∗
            ((c_Addr + 80#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.ptr) ∗
            ((c_Addr + 88#64) ↦₆₄ 32#64) ∗
            ((c_Addr + 96#64) ↦₃₂ old_ck.index) ∗
            memRegion (c_Addr + 100#64) 4 ∗
            (if (Gc.chains[ci]'hgi).ck.cap = 0 then emp
             else A.live (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat 1 ∗
               memRegion (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat))) := by ac_rfl
      simp only [← sepConj_assoc] at hpull_pure ⊢
      rw [hpull_pure]
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hcap32, hcap_lt63, hptr_old_ne⟩ => ?_
      have hcap_ne0 : (Gc.chains[ci]'hgi).ck.cap ≠ 0 := by
        intro h0; rw [h0] at hcap32; change 32 ≤ 0 at hcap32; omega
      simp only [hcap_ne0, ↓reduceIte]
      have hslt_some : ¬BitVec.slt (Gc.chains[ci]'hgi).ck.cap 1#64 := by
        unfold BitVec.slt
        have : (Gc.chains[ci]'hgi).ck.cap.toInt = (Gc.chains[ci]'hgi).ck.cap.toNat :=
          BitVec.toInt_eq_toNat_of_lt (by omega)
        have h1 : (1#64).toInt = 1 := rfl
        simp only [this, h1, decide_eq_true_eq]
        omega
      have hlayout_old : LayoutOk (Gc.chains[ci]'hgi).ck.cap.toNat 1 :=
        ⟨by omega, hpow1, by omega⟩
      have hdealloc0 := dealloc_ok_at_state_x hdealloc hfrozen2 hsym2
      apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1400)) hfrozen2 hsym2
      wp_steps
      wp_call hdealloc0 ((Gc.chains[ci]'hgi).ck.ptr, (Gc.chains[ci]'hgi).ck.cap.toNat, 1)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfrozen3 hsym3
      refine SepWPp.conseq_pre ?_
        (hset_fn (sf_1.readReg64 Reg.x0) (Gc.chains[ci]'hgi).ck.cap (Gc.chains[ci]'hgi).ck.ptr 32#64 old_ck.index R s0 _
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hsp0
          (by unfold State.spAligned at *; simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hfrozen3 hsym3
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [c_Addr, wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          hoom hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
          hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left h320_mem)))))))))))))))))
      dsimp only [c_Addr]
      rw [hw_ck (sf_1.readReg64 Reg.x0), stackAt_20000_split_16384 (s0.sp - 480#64), h20480, hsp_sf_1, hsp_sf, hsp_eq]
      have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
      exact heq (by ac_rfl)

/-! ## Epilogue Entry (`+0x4dc .. +0x520`) and Main Theorem -/

theorem leBytes4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.extractLsb' 0 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = w.extractLsb' 8 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = w.extractLsb' 16 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = w.extractLsb' 24 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change [BitVec.ofNat 8 (w.toNat / 256 ^ 0), BitVec.ofNat 8 (w.toNat / 256 ^ 1),
          BitVec.ofNat 8 (w.toNat / 256 ^ 2), BitVec.ofNat 8 (w.toNat / 256 ^ 3)] = _
  rw [h0, h1, h2, h3]

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  rw [pointsToBytes_append, length_keyToBytes32, leBytes4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

set_option maxHeartbeats 800000 in
theorem advanceEpilogue_entry_x {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hfind : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((findIndexSpecX img A).inImage img))
    (hhmac : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((hmacSpecX F).inImage img))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1244#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx26 : s.readReg64 .x26 = x.theirA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hck_eq : ckc.index = x.counter)
    (hc_max : x.counter ≠ BitVec.allOnes 32)
    (hci_find : stc.findReceiverChainIndex x.their = some ci)
    (hchc_get : stc.receiverChains[ci]? = some chc)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    SepWPp (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s
      (cmkLoopHeapX A img x Gc stc ckc s0)
      (advanceEpiloguePostX F A img x R s0) (advanceEpiloguePanicX F A img x R s0) := by
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hafter_find_fn := @advanceEpilogue_after_find_index_x F A ext img hA hhmac x Gc stc ckc ci chc R s0
  advanceEpilogue_fetches img.base (Rust.withPanics ext) hfn 0x4dc 17
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  have ⟨hci, hchc_eq⟩ := List.getElem?_eq_some_iff.mp hchc_get
  unfold cmkLoopHeapX
  rw [chainKeyBytes_pointsTo x.ckA ckc, stackAt_20000_split_18432 (s0.sp - 480#64)]
  refine SepWPp.conseq_pre
    (sepConj_mono (ratchetAt_expose_for_findIndex A x.self Gc stc hci)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (cmkLoopFrame_unpack s0.sp x.ret x.counter)))))))) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _hcap_ne⟩ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) hfrozen hsym
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen1 hsym1
  have hhmac1 := hmac_ok_at_state_x hhmac hfrozen1 hsym1
  have hlen_key : (keyToBytes32 ckc.key).length = 32 := length_keyToBytes32 ckc.key
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 2#8]
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1276)) hfrozen1 hsym1
  wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  apply SepWP.done hpc_sf hrun_sf
  intro hfrozen2 hsym2
  rw [← keyToBytes32_chainStepN_one F ckc,
      pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 2#8, hsp_eq]
  obtain ⟨w0, w1, w2, w3, _, hw_ck⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 (chainStepN F 1 ckc).key)
  have h20480 : s0.sp - 480#64 - 20000#64 = s0.sp - 20480#64 := by bv_arith
  have h320_cells :
      ((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31 ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
          ((s0.sp - 320#64) ↦₆₄ d0) ∗ ((s0.sp - 312#64) ↦₆₄ d1) ∗
          ((s0.sp - 304#64) ↦₆₄ d2) ∗ ((s0.sp - 296#64) ↦₆₄ d3) := by
    have h319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_arith
    have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
    have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
    have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
    have h := pointsToBytes1_31_entails_cells4 (s0.sp - 320#64) 2#8
    rwa [h319, ha1, ha2, ha3] at h
  have hprep :
      (((s0.sp - 224#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) hmacStackX ∗
       ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
       ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
       arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
       ratchetTail A x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 20480#64) 1568 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       memRegion (s0.sp - 319#64) 31 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) ⊢
      ((∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
          ((s0.sp - 320#64) ↦₆₄ d0) ∗ ((s0.sp - 312#64) ↦₆₄ d1) ∗
          ((s0.sp - 304#64) ↦₆₄ d2) ∗ ((s0.sp - 296#64) ↦₆₄ d3)) ∗
       (((s0.sp - 224#64) ↦₆₄ w0) ∗
        ((s0.sp - 224#64 + 8#64) ↦₆₄ w1) ∗
        ((s0.sp - 224#64 + 16#64) ↦₆₄ w2) ∗
        ((s0.sp - 224#64 + 24#64) ↦₆₄ w3)) ∗
       ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
       ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
       arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
       ratchetTail A x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 20000 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by
    rw [hw_ck (s0.sp - 224#64), stackAt_20000_split_18432 (s0.sp - 480#64), h20480]
    refine Entails.trans ?_ (sepConj_mono_left h320_cells)
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by ac_rfl)
  refine SepWPp.conseq_pre hprep ?_
  rw [stackAt_20000_split_17408 (s0.sp - 480#64), h20480]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  have hadd1_ne0 : x.counter + 1#32 ≠ 0#32 := by
    have hc_ne : x.counter ≠ 0xffffffff#32 := hc_max
    bv_omega
  have hadd1_beq0 : (x.counter + 1#32 == 0#32) = false :=
    beq_false_of_ne hadd1_ne0
  have hadd1_not_beq0 : ¬((x.counter + 1#32 == 0#32) = true) := by
    rw [hadd1_beq0]; decide
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) hfrozen2 hsym2
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen3 hsym3
  have hfind1 := findIndex_ok_at_state_x hfind hfrozen3 hsym3
  have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
    simp [hchains_len]
  have hlen_bv_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat =
      (Gc.chains.zip stc.receiverChains).length := by
    rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hzip_cap_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
    rw [hzip_len]; omega
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (1312)) hfrozen3 hsym3
  wp_call hfind1 (Gc.chainsPtr, Gc.chains.zip stc.receiverChains, x.theirA, x.their)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfrozen4 hsym4
  have hmap_find :
      ((Gc.chains.zip stc.receiverChains).map (·.2)).findIdx? (fun c => c.senderRatchetKey == x.their) =
        some ci := by
    rw [map_snd_zip_chains hchains_len]
    exact hci_find
  rw [hmap_find] at hpost_1
  rcases hpost_1 with ⟨hx0_sf1, hx1_toNat_sf1⟩
  have hx1_sf1 : sf_1.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
    rw [← hx1_toNat_sf1, BitVec.ofNat_toNat]; rfl
  have hgi : ci < Gc.chains.length := hchains_len ▸ hci
  have hfocus := focus_optChainKeyAt A x.self Gc stc ci chc hci hgi hchc_eq
  have hpull_focus :
      (arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt sf.sp findIndexStackX ∗
        ((s0.sp - 320#64) ↦₆₄ w0) ∗
        ((s0.sp - 312#64) ↦₆₄ w1) ∗
        ((s0.sp - 304#64) ↦₆₄ w2) ∗
        ((s0.sp - 296#64) ↦₆₄ w3) ∗
        ((s0.sp - 224#64) ↦₆₄ w0) ∗
        ((s0.sp - 216#64) ↦₆₄ w1) ∗
        ((s0.sp - 208#64) ↦₆₄ w2) ∗
        ((s0.sp - 200#64) ↦₆₄ w3) ∗
        ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
        ratchetTail A x.self Gc stc ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 20480#64) 2592 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        cmkLoopFrameRest s0.sp ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) ⊢
      ((⌜PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey ∧
          chc.messageKeys.length ≤ maxMessageKeys ∧
          (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length⌝ ∗
        optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey
          (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64) ∗
        ratchetRestAtChain A x.self Gc stc ci chc hgi) ∗
        memRegion x.ret 88 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 20000 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
        memRegion (s0.sp - 224#64) 32 ∗
        cmkLoopFrameRest s0.sp ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) := by
    have h224_mem :
        ((s0.sp - 224#64) ↦₆₄ w0) ∗ ((s0.sp - 216#64) ↦₆₄ w1) ∗
          ((s0.sp - 208#64) ↦₆₄ w2) ∗ ((s0.sp - 200#64) ↦₆₄ w3) ⊢
          memRegion (s0.sp - 224#64) 32 := by
      have := cells4_entails_memRegion32 (s0.sp - 224#64) w0 w1 w2 w3
      have hb1 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_arith
      have hb2 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_arith
      have hb3 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_arith
      rwa [hb1, hb2, hb3] at this
    have h320_ck :
        ((s0.sp - 320#64) ↦₆₄ w0) ∗ ((s0.sp - 312#64) ↦₆₄ w1) ∗
          ((s0.sp - 304#64) ↦₆₄ w2) ∗ ((s0.sp - 296#64) ↦₆₄ w3) =
          ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) := by
      have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
      have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
      have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
      rw [hw_ck (s0.sp - 320#64), ha1, ha2, ha3]
    refine Entails.trans ?_ (sepConj_mono_left hfocus)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h224_mem)))))))))))
    rw [hsp_sf, hsp_eq, stackAt_20000_split_17408 (s0.sp - 480#64), h20480, ← h320_ck]
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by ac_rfl)
  refine SepWPp.conseq_pre hpull_focus ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hsrk, hmax, hklen⟩ => ?_
  exact hafter_find_fn sf_1
    hpc_sf_1 hrun_sf_1 (by simp only [wp_norm, arm64_norm, *]) hsp0
    (by simpa [State.spAligned, hsp_sf_1, hsp_sf, hsp_eq] using _hsp)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hfrozen4 hsym4
    (by simp only [wp_norm, arm64_norm, *])
    hx0_sf1 hx1_sf1 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
    hsrk hmax hklen hagree_Gc hm1 hm2 htouched

theorem s4_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS4SpecX F A ext img := by
  intro hA himg hfind hhmac x Gc stc ckc ci chc R s0 s
    hck_eq hc_max hci_find hchc_get hagree_Gc hm1 hm2 htouched hstate
  rcases hstate with ⟨hpc, ⟨hrun, hsp_eq, hsp0, hsp, hx29, htr, hfrozen, hsym, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _hx19, hmem⟩
  rw [← sepConj_assoc, cmkLoopHeap_sep_low_eq] at hmem
  have hcmk : cmkEntry img =
      (SP2Ext img.base ext).fnAddr cmkName := by
    rw [cmkEntry_eq himg, Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]
  have hfind' : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((findIndexSpecX img A).inImage img) := by
    have h := hfind
    unfold FindIndexOkX at h
    rw [SP2Ext_fnAddr] at h
    exact sub_ok_at_caller (k := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm]) h
  have hhmac' : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((hmacSpecX F).inImage img) := by
    have h := hhmac
    unfold HmacOkX at h
    rw [SP2Ext_fnAddr] at h
    exact sub_ok_at_caller (k := num% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm]) h
  have hpc' : s.pc =
      (SP2Ext img.base ext).fnAddr cmkName + 1244#64 := by
    rw [hpc]; unfold cmkEpiloguePC; rw [hcmk]
  exact reaches_outcome_of_sepWPp hmem
    (advanceEpilogue_entry_x hA hfind' hhmac' x Gc stc ckc ci chc R s0 s
      hpc' hrun hsp_eq hsp0 hsp hx29 htr hfrozen hsym hvregs
      hx21 hx23 hx26 hx27 hx28 hck_eq hc_max hci_find hchc_get
      hagree_Gc hm1 hm2 htouched)

end Proofs.libsignal.Stage1X.CmkX
