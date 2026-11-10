/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `MessageDecrypt` Identity-Trust Segment (`SegTrust`)

Verifies the `is_trusted_identity` call, future poll, drop/dealloc, and branch dispatch segment
(`+0x1fcc → +0x2150 / +0x21b0 / +0x2294`) of `session_message_decrypt_signal_with_stores` and its
relocatable `[LibsignalPlacement]` counterpart.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Core Call-Block Lemma (`+0x1fcc → +0x2144`) -/

set_option maxHeartbeats 1600000 in
theorem segTrust_call_wp {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {img : Obj.Image}
    {ikit : IdentityStoreSpec A b}
    (hA : AllocHooks A abs) (hikit : IdentityStoreKitOkI img ikit C ctl abs)
    (hb : b &&& 0xfff#64 = 0#64)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp}
    (hinv : ImgCallInv img s)
    {self addrA c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 : BitVec 64} {d5 : BitVec 32}
    {ist : ikit.IdState} {addr : AddrGhost} {k : IdentityKey} {Q : Prop}
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x1fcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList))
    (hfs : FsAt ikit.envOk Q (tripleRatchetProgAt b C ctl abs) s) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2144#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (b + ikit.trustShimOff)) ∗
        ((b + ikit.trustFutVtOff) ↦₆₄ᵣ (b + ikit.trustFutDropOff)) ∗
        ((b + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((b + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((b + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.trustPollOff)) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2a8#64) ↦₆₄ a0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ a1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ a2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ a3) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x4f0#64) ↦₆₄ d0) ∗ ((s.sp + 0x4f8#64) ↦₆₄ d1) ∗
        ((s.sp + 0x500#64) ↦₆₄ d2) ∗ ((s.sp + 0x508#64) ↦₆₄ d3) ∗
        ((s.sp + 0x510#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
        ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
        logOff img ∗ protocolAddressAt A addr addrA ∗ A.pool ∗
        stackAt s.sp (trustCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Bool,
          ∃∗ box : BitVec 64,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist addr.val k .receiving ans ∧
            sf.trace = s.trace ++ ikit.trustEvs addr.val k .receiving ans ∧
            trustPollOutRel b o2 o3 o4 o5 b0 b3 h1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          ((s.sp + 0x108#64) ↦₆₄ self) ∗
          ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
          ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (b + ikit.trustShimOff)) ∗
          ((b + ikit.trustFutVtOff) ↦₆₄ᵣ (b + ikit.trustFutDropOff)) ∗
          ((b + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
          ((b + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((b + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.trustPollOff)) ∗
          ikit.identityAt self (ikit.trustUpdate ist addr.val k .receiving ans) ∗
          ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ (b + ikit.trustFutVtOff)) ∗
          ((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ trustPollTag ans) ∗
          ((s.sp + 0x5f8#64) ↦₈ b0) ∗ ((s.sp + 0x5f9#64) ↦₁₆ h1) ∗
          ((s.sp + 0x5fb#64) ↦₈ b3) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗
          ((s.sp + 0x60c#64) ↦₆₄ o4) ∗ ((s.sp + 0x614#64) ↦₆₄ o5) ∗
          ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
          (if ans.isOk then emp else ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
          logOff img ∗ protocolAddressAt A addr addrA ∗ A.pool ∗
          stackAt s.sp (trustCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x19 = s.sp + 0x2a8#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by
    simp only [decWithStoresName, arm64_norm]
  have hshim := subroutine_ok_withStepsPost_inImage hikit.trustShim
  have hdrop := hikit.trustFutDrop
  have hdealloc := dealloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := decWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x3a58c)) hA
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x1fcc 0x50
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x20f0 0x58
  dsimp only [tripleRatchetProgAt] at hpc hshim hdrop hdealloc hfs ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  refine SepWPp.congr_pre (by rw [stack_trustCall_to_trustShim ikit s.sp hstack_lt]) ?_
  apply SepWPp.of_sepWP_inImage (mid := b + ikit.trustShimOff) hinv
  clear hinv
  wp_steps
  apply SepWP.fold (Entails.of_eq hk_2a8) (by sep_focus)
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv1
  messageDecrypt_call_panic_p_inImage hshim hinv1 ((⟨self, addrA, s.sp + 680#64⟩ : IdentityShimCall), 1#8)
  clear hinv1 hshim
  apply SepWPp.of_sepWP_inImage (mid := b + ikit.trustPollOff) hinv_sf
  clear hinv_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  have henv : ikit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_trustShim_to_trustPoll ikit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv2
  have hpoll := hikit.trustPoll
  dsimp only [tripleRatchetProgAt] at hpoll
  messageDecrypt_call_panic_inImage hpoll hinv2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, s.sp + 680#64, k⟩⟩, Direction.receiving, self, ist)
  clear hinv2 hpoll hikit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz := ikit.trustFutDrop_ne_zero hb
  have hdz' : (b + ikit.trustFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := ikit.trustBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 ikit.trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 ikit.trustBoxSize).toNat = ikit.trustBoxSize :=
    Nat.mod_eq_of_lt ikit.trustBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | t
  · dsimp only [trustPollOutAt]
    wp_simp_pre [errTailAt, ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro (w5 : BitVec 64)
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp (b + bv% (ls_reloc% 0x77cc)) 10#64 1#64 (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w5))
      (by sep_focus)
    apply SepWP.fold
      (Entails.of_eq (pointsTo32_split_1_2_1_sp s.sp ((b + bv% (ls_reloc% 0x77cc)).extractLsb' 0 32)))
      (by sep_focus)
    wp_steps
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.trustBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = trustPollTag (.error ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right (10#32 ++ (b + bv% (ls_reloc% 0x77cc)).extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right ((b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)).extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)).extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32)
      (Entails.sepExists_right (((b + bv% (ls_reloc% 0x77cc)).extractLsb' 0 32).extractLsb' 0 8)
      (Entails.sepExists_right (((b + bv% (ls_reloc% 0x77cc)).extractLsb' 0 32).extractLsb' 24 8)
      (Entails.sepExists_right (((b + bv% (ls_reloc% 0x77cc)).extractLsb' 0 32).extractLsb' 8 16) ?_)))))))))
    refine Entails.pure_right ⟨by simp_all, by simp_all; bv_bits, by simp_all; bv_bits,
      by simp_all, h_20, by simp_all,
      ⟨by bv_bits, by bv_bits, by bv_bits, savePollOutRel_err b w5⟩⟩ ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [trustPollOutAt]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.fold (memRegion_39_entails_cells_sp s.sp) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (h1 : BitVec 16)
    apply SepWP.exists_elim; intro (b3 : BitVec 8)
    apply SepWP.exists_elim; intro (o2 : BitVec 64)
    apply SepWP.exists_elim; intro (o3 : BitVec 64)
    apply SepWP.exists_elim; intro (o4 : BitVec 64)
    apply SepWP.exists_elim; intro (o5 : BitVec 64)
    apply SepWP.exists_elim; intro (o6 : BitVec 32)
    wp_steps
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.trustBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte,
        show (18446744073709551614#64 : BitVec 64) = trustPollTag (.ok false) from rfl] at *
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (.ok false)
        (Entails.sepExists_right box
        (Entails.sepExists_right o2
        (Entails.sepExists_right o3
        (Entails.sepExists_right o4
        (Entails.sepExists_right o5
        (Entails.sepExists_right o6
        (Entails.sepExists_right 0#8
        (Entails.sepExists_right b3
        (Entails.sepExists_right h1 ?_)))))))))
      refine Entails.pure_right (by simp_all) ?_
      dsimp only [Except.isOk, Except.toBool]
      simp only [↓reduceIte, emp_sepConj, BitVec.add_assoc]
      exact Entails.of_eq (by ac_rfl)
    · simp only [↓reduceIte,
        show (18446744073709551614#64 : BitVec 64) = trustPollTag (.ok true) from rfl] at *
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (.ok true)
        (Entails.sepExists_right box
        (Entails.sepExists_right o2
        (Entails.sepExists_right o3
        (Entails.sepExists_right o4
        (Entails.sepExists_right o5
        (Entails.sepExists_right o6
        (Entails.sepExists_right 1#8
        (Entails.sepExists_right b3
        (Entails.sepExists_right h1 ?_)))))))))
      refine Entails.pure_right (by simp_all) ?_
      dsimp only [Except.isOk, Except.toBool]
      simp only [↓reduceIte, emp_sepConj, BitVec.add_assoc]
      exact Entails.of_eq (by ac_rfl)

/-! ## 2. Frame Split/Join Lemmas & `segTrustV_ok` -/

def wsTrustFixedEnv (A : RustAlloc) (img : Obj.Image) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
  ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
  ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  logOff img ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (trustCallStack ikit)

def wsTrustFixedRest (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (st : kit.StoreState) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decLoadVtableAtV kit ∗ decStoreVtableAtV kit ∗ decSaveVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  kit.storeAt (s0.readReg64 .x3) st ∗
  memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
    (wsCalleeStackV kit ikit - trustCallStack ikit)

theorem wsFixed_wsEnv_trust_split (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) :
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        wsTrustFixedEnv A img ikit x s0 sp ist ∗ wsTrustFixedRest A img kit ikit x s0 sp st := by
  subst hsp
  have hjoin := wsCalleeStack_join_extra kit ikit st ist s0
  refine Entails.trans (Entails.of_eq (show
    wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗ wsEnv A img x (s0.sp - 0xee0#64) ∗
      decStoreExtra kit ikit st ist s0 =
    (stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtra kit ikit st ist s0) ∗
      (wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗ A.pool) by
    unfold wsEnv; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hjoin) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  have hlt := s0.sp.isLt
  have hle : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by omega
  refine Entails.pure_right hbound ?_
  unfold wsFixedV wsArgCellsV decVtablesAtV decTrustVtableAtV wsTrustFixedEnv wsTrustFixedRest
  rw [stack_wsCalleeV_trustCall kit ikit (s0.sp - 0xee0#64) hn]
  exact Entails.of_eq (by ac_rfl)

theorem wsFixed_wsEnv_trust_join (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsTrustFixedEnv A img ikit x s0 sp ist ∗ wsTrustFixedRest A img kit ikit x s0 sp st ⊢
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0 := by
  subst hsp
  have hlt := s0.sp.isLt
  have hle : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by omega
  have hsplit := wsCalleeStack_split_extra kit ikit st ist s0 hbound
  refine Entails.trans (Entails.of_eq (show
    wsTrustFixedEnv A img ikit x s0 (s0.sp - 0xee0#64) ist ∗
      wsTrustFixedRest A img kit ikit x s0 (s0.sp - 0xee0#64) st =
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - trustCallStack ikit) ∗
        stackAt (s0.sp - 0xee0#64) (trustCallStack ikit))) ∗
    (wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗ logOff img ∗ A.pool) by
    unfold wsTrustFixedEnv wsTrustFixedRest wsFixedV wsArgCellsV decVtablesAtV decTrustVtableAtV
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_trustCall kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold wsEnv
  exact Entails.of_eq (by ac_rfl)

def wsTrustCallPre (A : RustAlloc) (img : Obj.Image) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState)
    (c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 : BitVec 64) (d5 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
  ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
  ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  ((sp + 0x2a8#64) ↦₆₄ a0) ∗ ((sp + 0x2b0#64) ↦₆₄ a1) ∗
  ((sp + 0x2b8#64) ↦₆₄ a2) ∗ ((sp + 0x2c0#64) ↦₆₄ a3) ∗
  ((sp + 0x2d0#64) ↦₆₄ c0) ∗ ((sp + 0x2d8#64) ↦₆₄ c1) ∗
  ((sp + 0x4f0#64) ↦₆₄ d0) ∗ ((sp + 0x4f8#64) ↦₆₄ d1) ∗
  ((sp + 0x500#64) ↦₆₄ d2) ∗ ((sp + 0x508#64) ↦₆₄ d3) ∗ ((sp + 0x510#64) ↦₃₂ d5) ∗
  memRegion (sp + 0x5f0#64) 48 ∗
  ((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
  ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3) ∗
  logOff img ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (trustCallStack ikit)

def wsTrustFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) : SepProp :=
  wsTrustFixedRest A img kit ikit x s0 sp st ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x680) ∗
  memRegion (sp + 0xcc0#64) 0x140 ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem keyReady_entails_trustCallPre (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (k0 k1 k2 k3 : BitVec 64)
    (hsp : sp = s0.sp - 0xee0#64)
    (hk_ca0 :
      ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) =
        (((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
          ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3))) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0) ⊢
    ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      wsTrustCallPre A img ikit x s0 sp ist c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 d5 ∗
      wsTrustFrame C A ctl img kit ikit x ans s0 sp st rec' pt := by
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_trust_split A img kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  refine Entails.pure_right hbound ?_
  rw [hk_ca0, memRegion_300_9a0_split, memRegion_300_280_trust_split, memRegion_5a4_6fc_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x4f0#64) 0x24) ∗
    (wsTrustFixedEnv A img ikit x s0 sp ist ∗
      (((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
        ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3)) ∗
      memRegion (sp + 0x5f0#64) 48 ∗
      wsTrustFrame C A ctl img kit ikit x ans s0 sp st rec' pt) by
    unfold wsTrustFrame; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_32_entails_cells (sp + 0x2a8#64))
    (sepConj_mono (memRegion_16_entails_cells (sp + 0x2d0#64))
      (memRegion_36_entails_cells (sp + 0x4f0#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1; apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right c0 (Entails.sepExists_right c1
        (Entails.sepExists_right d0 (Entails.sepExists_right d1
          (Entails.sepExists_right d2 (Entails.sepExists_right d3
            (Entails.sepExists_right d5 ?_))))))))))
  unfold wsTrustCallPre wsTrustFixedEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def wsTrustCallPostSpatial (A : RustAlloc) (img : Obj.Image) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState)
    (k : IdentityKey) (ans_trust : Except Unit Bool)
    (box o2 o3 o4 o5 k0 k1 k2 k3 : BitVec 64) (b0 b3 : BitVec 8) (h1 : BitVec 16)
    (o6 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
  ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
  ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
  ikit.identityAt (s0.readReg64 .x5) (ikit.trustUpdate ist x.rem.val k .receiving ans_trust) ∗
  ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (img.base + ikit.trustFutVtOff)) ∗
  ((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
  ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗ ((sp + 0x510#64) ↦₃₂ o6) ∗
  ((sp + 0x5f0#64) ↦₆₄ trustPollTag ans_trust) ∗
  ((sp + 0x5f8#64) ↦₈ b0) ∗ ((sp + 0x5f9#64) ↦₁₆ h1) ∗ ((sp + 0x5fb#64) ↦₈ b3) ∗
  ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
  ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗ ((sp + 0x61c#64) ↦₃₂ o6) ∗
  ((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
  ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3) ∗
  (if ans_trust.isOk then emp else ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
  logOff img ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (trustCallStack ikit)

def wsTrustPostCommonRest (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (k : IdentityKey) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
  decStoreExtra kit ikit st ist' s0

theorem trustCallPost_entails_common (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (ans_trust : Except Unit Bool)
    (box o2 o3 o4 o5 k0 k1 k2 k3 : BitVec 64) (b0 b3 : BitVec 8) (h1 : BitVec 16)
    (o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsTrustCallPostSpatial A img ikit x s0 sp ist k ans_trust box o2 o3 o4 o5 k0 k1 k2 k3 b0 b3 h1 o6 ∗
      wsTrustFrame C A ctl img kit ikit x ans s0 sp st rec' pt ⊢
    (((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗
      ((sp + 0x510#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_trust.isOk then emp else ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
    wsTrustPostCommonRest C A ctl img kit ikit x ans s0 sp st
      (ikit.trustUpdate ist x.rem.val k .receiving ans_trust) rec' pt k := by
  let ist' := ikit.trustUpdate ist x.rem.val k .receiving ans_trust
  refine Entails.trans (Entails.of_eq (show _ =
    ((((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (img.base + ikit.trustFutVtOff))) ∗
      (((sp + 0x5f0#64) ↦₆₄ trustPollTag ans_trust) ∗
        (((sp + 0x5f8#64) ↦₈ b0) ∗ ((sp + 0x5f9#64) ↦₁₆ h1) ∗ ((sp + 0x5fb#64) ↦₈ b3)) ∗
        (((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
          ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
          ((sp + 0x61c#64) ↦₃₂ o6))) ∗
      (((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
        ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3)) ∗
      (wsTrustFixedEnv A img ikit x s0 sp ist' ∗ wsTrustFixedRest A img kit ikit x s0 sp st)) ∗
    ((((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗
      ((sp + 0x510#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_trust.isOk then emp else ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
      wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗
      (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x680) ∗
      memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsTrustCallPostSpatial wsTrustFrame wsTrustFixedEnv
    ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box (img.base + ikit.trustFutVtOff)
  have h48 := cells_48_trust_entails_memRegion (sp + 0x5f0#64) (trustPollTag ans_trust)
    o2 o3 o4 o5 b0 b3 h1 o6
  have h32 := cells_32_entails_memRegion (sp + 0xca0#64) k0 k1 k2 k3
  have hjoin := wsFixed_wsEnv_trust_join A img kit ikit x s0 sp st ist' hsp hbound
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48 h32
  refine Entails.trans (sepConj_mono_left
    (sepConj_mono h16 (sepConj_mono h48 (sepConj_mono h32 hjoin)))) ?_
  unfold wsTrustPostCommonRest
  rw [← memRegion_5a4_85c_merge]
  exact Entails.of_eq (by ac_rfl)

theorem trustPostCommon_ok_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    (((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗
      ((sp + 0x510#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    wsTrustPostCommonRest C A ctl img kit ikit x ans s0 sp st ist' rec' pt k ⊢
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist' s0 := by
  have h36 := cells_36_entails_memRegion (sp + 0x4f0#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36
  refine Entails.trans (sepConj_mono_left h36) ?_
  unfold wsTrustPostCommonRest
  rw [memRegion_300_b00_split, memRegion_300_280_trust_split]
  exact Entails.of_eq (by ac_rfl)

theorem trustPostCommon_err_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (k : IdentityKey)
    (x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : savePollOutRel img.base o2 o3 o4 o5 o1 (.error ())) :
    ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
    ((((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗ ((sp + 0x510#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    wsTrustPostCommonRest C A ctl img kit ikit x ans s0 sp st ist' rec' pt k) ⊢
    ∃∗ G : SessionGhost,
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist' s0 := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    ((((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗ ((sp + 0x510#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist' s0)) by
    unfold wsTrustPostCommonRest; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x4f0#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_savePollOutRel A img.base x28 w20 w21 (sp + 0x580#64)
    o2 o3 o4 o5 o1 o6 hx28 hw1 hrel
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono hpt
      (sepConj_mono_left (key_entails_memRegion_32 (sp + 0x2a8#64) k)))))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_trust_split]
  exact Entails.of_eq (by ac_rfl)

theorem segTrust_tail_ok_true {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s : State} {R : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2144#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok true))
    (hx21 : s.readReg64 .x21 = (1#8 : BitVec 8).zeroExtend 64) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2150#64) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by
    simp only [decWithStoresName, arm64_norm]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x2144 0xc
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

theorem segTrust_tail_ok_false {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s : State} {R : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2144#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok false))
    (hx21 : s.readReg64 .x21 = (0#8 : BitVec 8).zeroExtend 64) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x21b0#64) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by
    simp only [decWithStoresName, arm64_norm]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x2144 0xc
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

theorem segTrust_tail_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s : State} {R : SepProp}
    {o2 o3 o4 o5 e0 e1 e2 e3 : BitVec 64} {o6 e4 : BitVec 32}
    {b0 b3 : BitVec 8} {h1 : BitVec 16}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2144#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = trustPollTag (.error ()))
    (hx21 : s.readReg64 .x21 = b0.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = b3.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = h1.zeroExtend 64) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2294#64) s
      (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
        ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
        ((s.sp + 0x510#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₆₄ e2) ∗ ((s.sp + 0x598#64) ↦₆₄ e3) ∗
        ((s.sp + 0x5a0#64) ↦₃₂ e4))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
          ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
          ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (h1.zeroExtend 32 ||| (b3.zeroExtend 32 <<< 16#32)).zeroExtend 64 ∧
        sf.readReg64 .x21 = b0.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by
    simp only [decWithStoresName, arm64_norm]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x2144 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x2190 0x20
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

attribute [local semireducible] SepWP in
theorem segTrustV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegTrustSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htr, hm⟩
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, -⟩ := hq
      simp only [hl]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hfr, hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads hyps.loads
  have hpc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x1fcc#64 := by
    rw [← entryOf_eq_tripleRatchetProgAt hyps.loads, hpc]
  rw [← hsp] at hx26 hx22 hm
  obtain ⟨k0, k1, k2, k3, _, hk_unpack⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length k.publicKey.bytes)
  have hk_ca0 :
      ((s.sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) =
        (((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3)) := by
    have h := hk_unpack (s.sp + 0xca0#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) := by
    have h := (hk_unpack (s.sp + 0x2a8#64)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsTrustCallPre A img ikit x s0 s.sp ist0 c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 d5 ∗
          wsTrustFrame C A ctl img kit ikit x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (keyReady_entails_trustCallPre C A ctl img kit ikit x ans s0 s.sp
        st0 ist0 rec' pt k k0 k1 k2 k3 hsp hk_ca0)) ?_
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have htrust_lt : trustCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := trustCallStack_le_wsCalleeV kit ikit
    have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨a0, a1, a2, a3, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segTrust_call_wp hyps.hooks.toTripleRatchetHooks.alloc hyps.ikit hb htrust_lt
      (R := wsTrustFrame C A ctl img kit ikit x ans s0 s.sp st0 rec' pt ∗ R)
      ⟨hfr, hsym⟩ haddr hpc' hrun hsp_align hk_2a8 hfsAt
      (wsTrustFrame C A ctl img kit ikit x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx19_1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_trust : Except Unit Bool,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans_trust ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist0 x.rem.val k .receiving ans_trust ∧
            sf.trace = s.trace ++ ikit.trustEvs x.rem.val k .receiving ans_trust ∧
            trustPollOutRel img.base o2 o3 o4 o5 b0 b3 h1 ans_trust⌝ ∗
          (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
            ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
            ((s.sp + 0x510#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_trust.isOk then emp else ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
          wsTrustPostCommonRest C A ctl img kit ikit x ans s0 s.sp st0
            (ikit.trustUpdate ist0 x.rem.val k .receiving ans_trust)
            rec' pt k) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_trust
      apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3
      apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5
      apply Entails.sepExists_elim; intro o6
      apply Entails.sepExists_elim; intro b0
      apply Entails.sepExists_elim; intro b3
      apply Entails.sepExists_elim; intro h1
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_trust
        (Entails.sepExists_right o2 (Entails.sepExists_right o3
          (Entails.sepExists_right o4 (Entails.sepExists_right o5
            (Entails.sepExists_right o6 (Entails.sepExists_right b0
              (Entails.sepExists_right b3 (Entails.sepExists_right h1
                (Entails.pure_right hpure ?_)))))))))
      exact trustCallPost_entails_common C A ctl img kit ikit x ans s0 s.sp st0 ist0
        rec' pt k ans_trust box o2 o3 o4 o5 k0 k1 k2 k3 b0 b3 h1 o6 hsp hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_trust, o2, o3, o4, o5, o6, b0, b3, h1, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hx23_1, hx24_1, htrustRel, htr1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_trust with ⟨⟨⟩⟩ | t
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      rcases hrel1 with ⟨hb0, hh1, hb3, hsave_rel⟩
      let o1 := (img.base + bv% (ls_reloc% 0x77cc)).extractLsb' 0 32
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sf.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x500#64) ↦₆₄ o4) ∗ ((sf.sp + 0x508#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x510#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
              wsTrustPostCommonRest C A ctl img kit ikit x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R := by
        rw [hsp1]
        refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0
        apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2
        apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segTrust_tail_err
          (R := (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRest C A ctl img kit ikit x ans s0 s.sp st0 ist1 rec' pt k) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1 hx23_1 hx24_1
          ((((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRest C A ctl img kit ikit x ans s0 s.sp st0 ist1 rec' pt k) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
              ((s.sp + 0x510#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
              ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsTrustPostCommonRest C A ctl img kit ikit x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, hb0, hb3, hh1, resWord1_trust_err]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_err_entails C A ctl img kit ikit x ans s0 s.sp st0 ist1
          rec' ses hcur pt k
          (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hsave_rel)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_trust_err C S x
        { ans with isTrustedIdentity := .error () } (kit.ScopeAt Scope st0 x.rem.val) rec rec' pt ses k
        hload hscope hdec hcur hrem rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with isTrustedIdentity := .error () }) (ans := ans) rfl
      refine ⟨?_, hmeta2, ?_, ?_, { ans with isTrustedIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpc2, ← entryOf_eq_tripleRatchetProgAt hyps.loads]; rfl
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_load_trust,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.ok t)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_ok_entails C A ctl img kit ikit x ans s0 s.sp st0 ist1
          rec' pt k o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedV kit ikit x s0 s.sp ∗ wsEnv A img x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A (s.sp + 0x120#64) g rec') ∗
            vecU8 A (s.sp + 0x290#64) pt ∗ ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtra kit ikit st0 ist1 s0) ∗ R) := by
        rwa [emp_sepConj]
      cases t
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_ok_false (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok false }, false, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok false }) (ans := ans) rfl
        refine ⟨?_, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hpc2, ← entryOf_eq_tripleRatchetProgAt hyps.loads]; rfl
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_ok_true (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok true }, true, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok true }) (ans := ans) rfl
        refine ⟨?_, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hpc2, ← entryOf_eq_tripleRatchetProgAt hyps.loads]; rfl
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedIn ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segTrust_ok_pf {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegTrustSpec img C A ctl uuidTryParse S encRecord abs :=
  segTrustV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

set_option maxHeartbeats 1600000 in
theorem segTrust_call_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ikit : IdentityStoreSpec A 0#64}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hikit : IdentityStoreKitPlacedOkI ikit H)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {self addrA c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 : BitVec 64} {d5 : BitVec 32}
    {ist : ikit.IdState} {addr : AddrGhost} {k : IdentityKey} {Q : Prop}
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = keyReadyPCPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList))
    (hfs : FsAt ikit.envOk Q (lsProg_197 H) s) :
    SepWPp (lsProg_197 H) ((blkPl_197).base + 8516#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
        (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
        ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2a8#64) ↦₆₄ a0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ a1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ a2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ a3) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x4f0#64) ↦₆₄ d0) ∗ ((s.sp + 0x4f8#64) ↦₆₄ d1) ∗
        ((s.sp + 0x500#64) ↦₆₄ d2) ∗ ((s.sp + 0x508#64) ↦₆₄ d3) ∗
        ((s.sp + 0x510#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
        ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
        FromRecordCallees.lsLogOff ∗ protocolAddressAt A addr addrA ∗ A.pool ∗
        stackAt s.sp (trustCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Bool,
          ∃∗ box : BitVec 64, ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist addr.val k .receiving ans ∧
            sf.trace = s.trace ++ ikit.trustEvs addr.val k .receiving ans ∧
            trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 b0 b3 h1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          ((s.sp + 0x108#64) ↦₆₄ self) ∗
          ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
          ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
          (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
          ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
          ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
          ikit.identityAt self (ikit.trustUpdate ist addr.val k .receiving ans) ∗
          ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ ikit.trustFutVtOff) ∗
          ((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ trustPollTag ans) ∗
          ((s.sp + 0x5f8#64) ↦₈ b0) ∗ ((s.sp + 0x5f9#64) ↦₁₆ h1) ∗
          ((s.sp + 0x5fb#64) ↦₈ b3) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗
          ((s.sp + 0x60c#64) ↦₆₄ o4) ∗ ((s.sp + 0x614#64) ↦₆₄ o5) ∗
          ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          FromRecordCallees.lsLogOff ∗ protocolAddressAt A addr addrA ∗ A.pool ∗
          stackAt s.sp (trustCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x19 = s.sp + 0x2a8#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := shim_197 (hikit.trustShim (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  have hdrop := futDrop_197 (hikit.trustFutDrop (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  unfold keyReadyPCPlaced at hpc
  dsimp only [lsProg_197] at hfs ⊢
  have hdealloc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_trustCall_to_trustShim ikit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.trustShimOff) hcrl
  clear hcrl
  wp_steps
  apply SepWP.fold (Entails.of_eq hk_2a8) (by sep_focus)
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl1
  messageDecrypt_call_panic_p_lscro hshim hcrl1 ((⟨self, addrA, s.sp + 680#64⟩ : IdentityShimCall), 1#8)
  clear hcrl1 hshim
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.trustPollOff) hcrl_sf
  clear hcrl_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  have henv : ikit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_trustShim_to_trustPoll ikit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl2
  have hpoll := box_lscro_197 (hikit.trustPoll (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  messageDecrypt_call_panic_lscro hpoll hcrl2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, s.sp + 680#64, k⟩⟩, Direction.receiving, self, ist)
  clear hcrl2 hpoll hikit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz : ikit.trustFutDropOff ≠ 0#64 := by
    simpa only [BitVec.zero_add] using ikit.trustFutDrop_ne_zero (by decide)
  have hdz' : (ikit.trustFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := ikit.trustBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 ikit.trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 ikit.trustBoxSize).toNat = ikit.trustBoxSize :=
    Nat.mod_eq_of_lt ikit.trustBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | t
  · dsimp only [StoreKit.trustPollPlacedOutAt]
    wp_simp_pre [StoreKit.errTailPlacedAt, ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro (strPtr : BitVec 64)
    apply SepWP.exists_elim; intro (vt : BitVec 64)
    apply SepWP.exists_elim; intro (w5 : BitVec 64)
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
      (by sep_focus)
    apply SepWP.fold
      (Entails.of_eq (pointsTo32_split_1_2_1_sp s.sp (strPtr.extractLsb' 0 32)))
      (by sep_focus)
    apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.trustFutDropOff)
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.trustBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (0x800000000000001A#64 : BitVec 64) = trustPollTag (.error ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right strPtr
      (Entails.sepExists_right vt
      (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32)
      (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 0 8)
      (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 24 8)
      (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 8 16) ?_)))))))))))
    refine Entails.pure_right ⟨by simp_all, by simp_all; bv_bits, by simp_all; bv_bits,
      by simp_all, h_20, by simp_all,
      ⟨by bv_bits, by bv_bits, by bv_bits, pollOutPlacedRel_err strPtr vt w5⟩⟩ ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [StoreKit.trustPollPlacedOutAt]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.fold (memRegion_39_entails_cells_sp s.sp) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (h1 : BitVec 16)
    apply SepWP.exists_elim; intro (b3 : BitVec 8)
    apply SepWP.exists_elim; intro (o2 : BitVec 64)
    apply SepWP.exists_elim; intro (o3 : BitVec 64)
    apply SepWP.exists_elim; intro (o4 : BitVec 64)
    apply SepWP.exists_elim; intro (o5 : BitVec 64)
    apply SepWP.exists_elim; intro (o6 : BitVec 32)
    apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.trustFutDropOff)
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.trustBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte,
        show (bv% (2 ^ 64 - 2) : BitVec 64) = trustPollTag (.ok false) from rfl] at *
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (.ok false)
        (Entails.sepExists_right box
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right o2
        (Entails.sepExists_right o3
        (Entails.sepExists_right o4
        (Entails.sepExists_right o5
        (Entails.sepExists_right o6
        (Entails.sepExists_right 0#8
        (Entails.sepExists_right b3
        (Entails.sepExists_right h1 ?_)))))))))))
      refine Entails.pure_right (by simp_all) ?_
      dsimp only [Except.isOk, Except.toBool]
      simp only [↓reduceIte, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · simp only [↓reduceIte,
        show (bv% (2 ^ 64 - 2) : BitVec 64) = trustPollTag (.ok true) from rfl] at *
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (.ok true)
        (Entails.sepExists_right box
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right o2
        (Entails.sepExists_right o3
        (Entails.sepExists_right o4
        (Entails.sepExists_right o5
        (Entails.sepExists_right o6
        (Entails.sepExists_right 1#8
        (Entails.sepExists_right b3
        (Entails.sepExists_right h1 ?_)))))))))))
      refine Entails.pure_right (by simp_all) ?_
      dsimp only [Except.isOk, Except.toBool]
      simp only [↓reduceIte, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)

theorem segTrust_tail_placed_ok_true [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    (hpc : s.pc = (blkPl_197).base + 8516#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok true))
    (hx21 : s.readReg64 .x21 = (1#8 : BitVec 8).zeroExtend 64) :
    SepWP (lsProg_197 H) (trustedPCPlaced true) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold trustedPCPlaced saveCallPCPlaced
  dsimp only [lsProg_197]
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

theorem segTrust_tail_placed_ok_false [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    (hpc : s.pc = (blkPl_197).base + 8516#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok false))
    (hx21 : s.readReg64 .x21 = (0#8 : BitVec 8).zeroExtend 64) :
    SepWP (lsProg_197 H) (trustedPCPlaced false) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  simp only [trustedPCPlaced, Bool.false_eq_true, ↓reduceIte, untrustedPCPlaced]
  dsimp only [lsProg_197]
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

theorem segTrust_tail_placed_err [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    {o2 o3 o4 o5 e0 e1 e2 e3 : BitVec 64} {o6 e4 : BitVec 32}
    {b0 b3 : BitVec 8} {h1 : BitVec 16}
    (hpc : s.pc = (blkPl_197).base + 8516#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = trustPollTag (.error ()))
    (hx21 : s.readReg64 .x21 = b0.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = b3.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = h1.zeroExtend 64) :
    SepWP (lsProg_197 H) (errJoinPCPlaced true) s
      (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
        ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
        ((s.sp + 0x510#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₆₄ e2) ∗ ((s.sp + 0x598#64) ↦₆₄ e3) ∗
        ((s.sp + 0x5a0#64) ↦₃₂ e4))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
          ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
          ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (h1.zeroExtend 32 ||| (b3.zeroExtend 32 <<< 16#32)).zeroExtend 64 ∧
        sf.readReg64 .x21 = b0.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold errJoinPCPlaced
  dsimp only [lsProg_197]
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

attribute [local semireducible] SepWP in
theorem segTrustVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegTrustSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htr, hm⟩
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_197 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, -⟩ := hq
      simp only [hl]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hx22 hm
  obtain ⟨k0, k1, k2, k3, _, hk_unpack⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length k.publicKey.bytes)
  have hk_ca0 :
      ((s.sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) =
        (((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3)) := by
    have h := hk_unpack (s.sp + 0xca0#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) := by
    have h := (hk_unpack (s.sp + 0x2a8#64)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsTrustCallPrePlaced A ikit x s0 s.sp ist0 c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 d5 ∗
          wsTrustFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (keyReady_entails_trustCallPre_placed C A ctl kit ikit x ans s0 s.sp
        st0 ist0 rec' pt k k0 k1 k2 k3 hsp hk_ca0)) ?_
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have htrust_lt : trustCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := trustCallStack_le_wsCalleeV kit ikit
    have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨a0, a1, a2, a3, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segTrust_call_placed_wp hyps.hooks.dealloc hyps.ikit htrust_lt
      (R := wsTrustFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt ∗ R)
      hcrl haddr hpc hrun hsp_align hk_2a8 hfsAt
      (wsTrustFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx19_1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_trust : Except Unit Bool,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans_trust ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist0 x.rem.val k .receiving ans_trust ∧
            sf.trace = s.trace ++ ikit.trustEvs x.rem.val k .receiving ans_trust ∧
            trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 b0 b3 h1 ans_trust⌝ ∗
          (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
            ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
            ((s.sp + 0x510#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_trust.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0
            (ikit.trustUpdate ist0 x.rem.val k .receiving ans_trust)
            rec' pt k) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_trust
      apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro strPtr
      apply Entails.sepExists_elim; intro vt
      apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3
      apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5
      apply Entails.sepExists_elim; intro o6
      apply Entails.sepExists_elim; intro b0
      apply Entails.sepExists_elim; intro b3
      apply Entails.sepExists_elim; intro h1
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_trust
        (Entails.sepExists_right strPtr (Entails.sepExists_right vt
          (Entails.sepExists_right o2 (Entails.sepExists_right o3
            (Entails.sepExists_right o4 (Entails.sepExists_right o5
              (Entails.sepExists_right o6 (Entails.sepExists_right b0
                (Entails.sepExists_right b3 (Entails.sepExists_right h1
                  (Entails.pure_right hpure ?_)))))))))))
      exact trustCallPost_entails_common_placed C A ctl kit ikit x ans s0 s.sp st0 ist0
        rec' pt k ans_trust box strPtr o2 o3 o4 o5 k0 k1 k2 k3 b0 b3 h1 o6 hsp hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_trust, strPtr, vt, o2, o3, o4, o5, o6, b0, b3, h1, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hx23_1, hx24_1, htrustRel, htr1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_trust with ⟨⟨⟩⟩ | t
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      rcases hrel1 with ⟨hb0, hh1, hb3, hsave_rel⟩
      let o1 := strPtr.extractLsb' 0 32
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sf.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x500#64) ↦₆₄ o4) ∗ ((sf.sp + 0x508#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x510#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((strPtr ↦ᵣ storeHookStr) ∗
              wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R := by
        rw [hsp1]
        refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0
        apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2
        apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segTrust_tail_placed_err
          (R := ((strPtr ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1 hx23_1 hx24_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
              ((s.sp + 0x510#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
              ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, hb0, hb3, hh1, resWord1_trust_err]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_err_entails_placed C A ctl kit ikit x ans s0 s.sp st0 ist1
          rec' ses hcur pt k strPtr vt
          (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hsave_rel)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_trust_err C S x
        { ans with isTrustedIdentity := .error () } (kit.ScopeAt Scope st0 x.rem.val) rec rec' pt ses k
        hload hscope hdec hcur hrem rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with isTrustedIdentity := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with isTrustedIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_load_trust,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.ok t)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_ok_entails_placed C A ctl kit ikit x ans s0 s.sp st0 ist1
          rec' pt k o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A (s.sp + 0x120#64) g rec') ∗
            vecU8 A (s.sp + 0x290#64) pt ∗ ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtraPlaced kit ikit st0 ist1 s0) ∗ R) := by
        rwa [emp_sepConj]
      cases t
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_placed_ok_false (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok false }, false, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok false }) (ans := ans) rfl
        refine ⟨hpc2, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_placed_ok_true (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok true }, true, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok true }) (ans := ans) rfl
        refine ⟨hpc2, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
