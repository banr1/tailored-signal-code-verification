/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeed
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segment S3 Part A (`DeriveSeedSpecX`)

Proves `storeLoop_deriveSeed_ok_x` (`+0x334 → +0x394`) for `RatchetState::consume_message_key` on
`SP2Ext img.base ext` at `cmkLoopStackX = 20000` bytes.
-/

@[expose] public section

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession.StoreLoop
open ProofLib.ProgramReflection
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_SegS3PartA : True := trivial

/-! ## Stack Splits -/

private theorem stackAt_20000_eq_hmac (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 1568 ∗ stackAt sp hmacStackX :=
  stackAt_split_bottom sp 18432 1568 (by decide)

private theorem stackAt_20000_eq_alloc (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 3616 ∗ stackAt sp extHookStack :=
  stackAt_split_bottom sp 16384 3616 (by decide)

private theorem stackAt_20000_eq_find (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 2592 ∗ stackAt sp findIndexStackX :=
  stackAt_split_bottom sp 17408 2592 (by decide)

/-! ## State-Specialized Callee Wrappers -/

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

private theorem shim_ok_at_state_x {b : BitVec 64}
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
  apply subroutine_ok.of_codeLoaded
  intro u R s0 hpc hrun hm hsp _
  have hpre' : s0.mem ⊨ (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img).pre u s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack,
      emp_sepConj]
    apply Entails.pure_left
    rintro ⟨hmem, hsym'⟩
    exact Entails.pure_right ⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩ (Entails.refl _)
  exact subroutine_ok.mono_outcome hshim u R s0 hpc hrun hpre' hsp fun sf hout => by
    rcases hout with ⟨hret, hcs, hpost⟩ | hout
    · refine Or.inl ⟨hret, hcs, ?_⟩
      simpa only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack] using hpost
    · exact Or.inr hout

private theorem alloc_ok_at_state_x {b : BitVec 64} {A : RustAlloc}
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
  apply subroutine_ok.of_codeLoaded
  intro ⟨size, align⟩ R s0 hpc hrun hm hsp _
  refine subroutine_ok.mono_outcome halloc (size, align) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

private theorem findIndex_ok_at_state_x {b : BitVec 64}
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
  apply subroutine_ok.of_codeLoaded
  intro ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp _
  refine subroutine_ok.mono_outcome hfind (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, findIndexSpecX]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

/-! ## Main Theorem -/

abbrev StoreLoopDeriveSeedSpecX := DeriveSeedSpecX

set_option maxHeartbeats 1600000 in
theorem storeLoop_deriveSeed_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    StoreLoopDeriveSeedSpecX F A ext img := by
  intro hA himg hfind_ok hhmac_ok x Gc stc ckc ci chc R s0 s _hlt hfind_idx hchc hstate hL
  rcases hstate with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hfl, hsym, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hx19_fn, hmem⟩
  rw [← sepConj_assoc, cmkLoopHeap_sep_low_eq] at hmem
  have hx19 : s.readReg64 .x19 = 1#64 := hx19_fn rfl
  clear hx19_fn
  rw [cmkLoopPC_eq_fnAddr_x himg ext] at hpc
  have hfn : libsignalSessionCode.fnOff cmkName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hhmac := hmac_ok_at_cmk_x hhmac_ok
  have hshim := shim_ok_at_x (img := img) (ext := ext) hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have halloc := alloc_ok_at_x (img := img) (ext := ext) hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hfind := find_index_ok_at_cmk_x hfind_ok
  have hpanic := panic_at_handle_error_ext (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  unfold Spec.inImage hmacSpecX at hhmac
  cmk_fetches_range img.base (Rust.withPanics ext) hfn 205 229
  cmk_fetches_range img.base (Rust.withPanics ext) hfn 621 624
  clear hfn
  have hpartB_eq := cmkInsertKeyPC_eq_fnAddr_x himg ext
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hchains_pos : 0 < stc.receiverChains.length := by omega
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have hmsg1_len : ([1#8] : List (BitVec 8)).length = 1 := rfl
  have hseed_eq : (ckc.messageKeys F).seed = hmacWith F (keyToBytes32 ckc.key) [1#8] :=
    messageKeys_seed_eq F ckc
  have hseed_len : (hmacWith F (keyToBytes32 ckc.key) [1#8]).length = 32 :=
    hmacWith_length F (keyToBytes32 ckc.key) [1#8]
  obtain ⟨sw0, sw1, sw2, sw3, hseed_unpack, hseed_pts⟩ := exists_unpack64_of_length_32 hseed_len
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨Nat.zero_lt_succ 31, ⟨0, rfl⟩, by decide⟩
  have hwp : SepWPp (SP2Ext img.base ext) (entry + bv% (916)) s
      (cmkLoopHeapX A img x Gc stc ckc s0)
      (fun sA P_f =>
        sA.sp = s0.sp - 480#64 ∧ sA.spAligned = true ∧
        sA.readReg64 .x29 = s0.sp - 96#64 ∧
        (sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0) ∧
        ∃ seedPtr, InsertKeyRegs x Gc ckc ci seedPtr s0 sA ∧ seedPtr ≠ 0#64 ∧
          (sA.mem ⊨ P_f ∗ R →
            sA.mem ⊨ (cmkLoopHeapX A img x Gc stc ckc s0 ∗
              vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ∗ R))
      (fun sA P_f => (sA.mem ⊨ P_f ∗ R) → (sA.mem ⊨ (cmkSpecX F A img).onPanic x s0 sA ∗ R)) := by
    conv =>
      arg 4
      unfold cmkLoopHeapX
      rw [← hsp, pointsToBytes_chainKeyBytes x.ckA ckc, cmkLoopFrame_eq_deriveSeed s0.sp x.ret x.counter]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro b0
    apply ProofLib.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl1 hsym1
    rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 1#8,
        stackAt_20000_eq_hmac s.sp]
    apply ProofLib.SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (848))
    wp_call hhmac (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
    apply SepWP.fold (Entails.of_eq (stackAt_20000_eq_hmac s.sp).symm) (by sep_focus)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl2 hsym2
    have hshim0 := shim_ok_at_state_x hshim hfl2 hsym2
    rw [stackAt_20000_eq_alloc s.sp]
    apply ProofLib.SepWPp.of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (852))
    wp_steps
    wp_call hshim0 ()
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl3 hsym3
    have hsp1 : sf_1.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    have halloc0 := alloc_ok_at_state_x halloc hfl3 hsym3
    apply ProofLib.SepWPp.of_sepWP_inv hfl3 hsym3 (mid := entry + bv% (864))
    wp_steps
    wp_call halloc0 (32, 1)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl4 hsym4
    have hsp2 : sf_2.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    rw [hsp1]
    apply SepWPp.fold (Entails.of_eq (stackAt_20000_eq_alloc s.sp).symm) (by sep_focus)
    by_cases hoom : sf_2.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_pure_left_comm, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      simpa only [cmkSpecX, consumeMessageKeySpec, Spec.inImage, sepConj_assoc] using
        allowPanic_panicked (StoreLoop.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom' : sf_2.readReg64 Reg.x0 ≠ 0 := hoom
      have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_pure_left_comm, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_halign_alloc, htrace_alloc⟩ => ?_
      apply SepWPp.fold (ratchetAt_expose_for_findIndex A x.self Gc stc hchains_pos) (by sep_focus)
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩ => ?_
      have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
        simp [hchains_len]
      have hzip_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
        rw [hzip_len]; omega
      have hlen_lt_64 : stc.receiverChains.length < 2 ^ 64 := by omega
      have hlen_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat = (Gc.chains.zip stc.receiverChains).length := by
        rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt_64]
      have ⟨_, hfind_zip⟩ := ci_lt_and_find_match hchains_len hfind_idx hchc
      rw [hseed_pts (s0.sp - 224#64),
          memRegion_32_eq_exists_words (sf_2.readReg64 Reg.x0)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro dw0
      apply SepWPp.exists_elim; intro dw1
      apply SepWPp.exists_elim; intro dw2
      apply SepWPp.exists_elim; intro dw3
      apply ProofLib.SepWPp.of_sepWP_inv hfl4 hsym4 (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl5 hsym5
      have hfind0 := findIndex_ok_at_state_x hfind hfl5 hsym5
      rw [stackAt_20000_eq_find s.sp]
      apply SepWPp.of_sepWP_ret
      wp_call hfind0 (Gc.chainsPtr, Gc.chains.zip stc.receiverChains, x.theirA, x.their)
      rw [hsp2]
      apply SepWP.fold (Entails.of_eq (stackAt_20000_eq_find s.sp).symm) (by sep_focus)
      rw [hsp]
      have ⟨hx0_sf3, hx1_sf3⟩ : sf_3.readReg64 Reg.x0 = 1#64 ∧ (sf_3.readReg64 Reg.x1).toNat = ci := by
        simpa only [hfind_zip] using hpost_2
      have hx1_eq : sf_3.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
        apply BitVec.eq_of_toNat_eq
        rw [hx1_sf3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hcs_false : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
        bitvec_ofNat_lt_eq_false hci_lt hlen_lt_64
      wp_steps
      apply SepWP.fold
        (ratchetAt_reassemble_after_findIndex A x.self Gc stc
          hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hcap_ne)
        (by sep_focus)
      apply SepWP.fold
        (words_entails_vecU8Buf_32 A (sf_2.readReg64 Reg.x0) (ckc.messageKeys F).seed
          hoom' (hseed_eq ▸ hseed_len) (hseed_eq ▸ hseed_pts))
        (by sep_focus)
      apply SepWP.fold
        (cmkLoopFrame_of_deriveSeed s0.sp x.ret x.counter 1#8 sw0 sw1 sw2 sw3)
        (by sep_focus)
      apply SepWP.fold
        (Entails.of_eq (pointsToBytes_chainKeyBytes x.ckA ckc).symm)
        (by sep_focus)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
         by simpa [State.spAligned, hsp_sf_3, hsp2, hsp] using hsp_align,
         by simp only [wp_norm, arm64_norm, *],
         ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
         sf_2.readReg64 Reg.x0, ?_, hoom, fun hm => ?_⟩
      · unfold InsertKeyRegs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
      · exact Satisfies.mono (Entails.of_eq (by unfold cmkLoopHeapX; ac_rfl)) hm
  obtain ⟨sA, hsteps, ⟨hpcA, hrunA, hflA, hsymA, P_f, hmf, hspA, hsp_alignA, hx29A, ⟨htraceA, hvregsA⟩,
      seedPtr, hregsA, hseed_ne, hmemA⟩ | ⟨hpanA, P_f, hmf, hqp⟩⟩ :=
    steps_of_sepWPp hfl hsym hmem hL hwp
  · refine ⟨sA, hsteps, Or.inl ⟨seedPtr, ?_⟩⟩
    exact ⟨hpartB_eq.symm ▸ hpcA, ⟨hrunA, hspA, hsp0_align, hsp_alignA, hx29A, htraceA, hflA, hsymA, hvregsA⟩,
      hregsA, hseed_ne, hmemA hmf⟩
  · exact ⟨sA, hsteps, Or.inr ⟨hpanA, hqp hmf⟩⟩

end Proofs.libsignal.Stage1X.CmkX
