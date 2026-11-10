/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStoreAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.StoreSession.Decodes
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `segStore_call_wp` (`+0x2388 → +0x2428`) -/

theorem segStore_call_wp {A : RustAlloc}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hA : AllocHooks A abs)
    (hkit : SessionOnlyKitOkS kit Scope C encRecord ctl abs)
    (hb : img.base &&& 0xfff#64 = 0#64) {s : State} {R : SepProp} {self addrA : BitVec 64}
    {addr : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    {st : kit.StoreState} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hinv : ImgCallInv img s)
    (haddr : kit.addrOk addr.val)
    (hrecOk : kit.RecOk record)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x2388#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hstack_lt : storeCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Q (tripleRatchetProgAt img.base C ctl abs) s) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x2428#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x550#64) ↦₆₄ d0) ∗ ((s.sp + 0x558#64) ↦₆₄ d1) ∗ ((s.sp + 0x560#64) ↦₆₄ d2) ∗
        ((s.sp + 0x568#64) ↦₆₄ d3) ∗ ((s.sp + 0x570#64) ↦₃₂ d5) ∗ memRegion (s.sp + 0x5f0#64) 48 ∗
        protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
        kit.storeAt self st ∗ A.pool ∗ stackAt s.sp (storeCallStack kit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Unit, ∃∗ box : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st addr.val record ans ∧
            sf.readReg64 .x28 = pollTag ans ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord addr.val record ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            storePollOutRel img.base o2 o3 o4 o5 o1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
          ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
          ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
          ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ (img.base + kit.storeFutVtOff)) ∗
          ((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
          ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ pollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗ ((s.sp + 0x60c#64) ↦₆₄ o4) ∗
          ((s.sp + 0x614#64) ↦₆₄ o5) ∗ ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
          kit.storeAt self (kit.storeUpdate st addr.val record ans) ∗
          (if ans.isOk then emp else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
          A.pool ∗ stackAt s.sp (storeCallStack kit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = num% (ls_off% "session_message_decrypt_signal") := by simp only [decWithStoresName, arm64_norm]
  have hshim := subroutine_ok_withStepsPost_inImage hkit.storeShim
  have hdrop := hkit.storeFutDrop
  have hdealloc := dealloc_ok_at_norm (b := img.base) (C := C) (ctl := ctl)
    (name := decWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "session_message_decrypt_signal")) hA
  code_fetches_range CryptoVerification.libsignalSessionCode storeSessionBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x2388 0xa8
  dsimp only [tripleRatchetProgAt] at hpc hshim hdrop hdealloc hfs ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  refine SepWPp.congr_pre (by rw [stack_storeCall_to_storeShim kit s.sp hstack_lt]) ?_
  apply SepWPp.of_sepWP_inImage (mid := img.base + kit.storeShimOff) hinv
  clear hinv
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv1
  messageDecrypt_call_panic_p_inImage hshim hinv1
    (⟨self, addrA, s.readReg64 .x26 + 0x80#64⟩ : StoreShimCall)
  clear hinv1 hshim
  apply SepWPp.of_sepWP_inImage (mid := img.base + kit.storePollOff) hinv_sf
  clear hinv_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  -- `kit.envOk` on the files at the poll: the shim adds no event and the code before keeps `fs`.
  have henv : kit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_storeShim_to_storePoll kit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv2
  have hpoll := hkit.storePoll
  dsimp only [tripleRatchetProgAt] at hpoll
  messageDecrypt_call_panic_inImage hpoll hinv2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 0x5f0#64,
    ⟨addrA, addr, s.readReg64 .x26 + 0x80#64, g, record⟩⟩, self, st)
  clear hinv2 hpoll hkit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz := kit.storeFutDrop_ne_zero hb
  have hdz' : (img.base + kit.storeFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := kit.storeBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 kit.storeBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 kit.storeBoxSize).toNat = kit.storeBoxSize :=
    Nat.mod_eq_of_lt kit.storeBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [storePollOutAt]
    wp_simp_pre [ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro w5
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp (img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) 10#64 1#64 (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)) w5))
      (by sep_focus)
    wp_steps
    wp_apply
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_apply
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = pollTag (.error ()) from rfl,
      storePollOutRel] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32)
      (Entails.sepExists_right (10#32 ++ (img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32) ?_)))))))
    refine Entails.pure_right (by simp_all; exact BitVec.extractLsb'_append_eq_right) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [storePollOutAt]
    have hm40 : memRegion (s.sp + 1528#64) 40 =
        ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
          ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
          ((s.sp + 1528#64) ↦₆₄ w5) ∗ ((s.sp + 1536#64) ↦₆₄ w4) ∗
            ((s.sp + 1544#64) ↦₆₄ w3) ∗ ((s.sp + 1552#64) ↦₆₄ w2) ∗
            ((s.sp + 1560#64) ↦₆₄ w1) := by
      rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl,
        memRegion_split (s.sp + 1528#64) 8 32 (by decide),
        memRegion_split (s.sp + 1528#64 + 8#64) 8 24 (by decide),
        memRegion_split (s.sp + 1528#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (s.sp + 1528#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        ProofLib.memRegion_eight, ProofLib.memRegion_eight]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, hm40, sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4
    apply SepWP.exists_elim; intro w5
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp w5 w4 w3 w2 w1))
      (by sep_focus)
    wp_steps
    wp_apply
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_apply
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = pollTag (.ok ()) from rfl,
      storePollOutRel] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.ok ())
      (Entails.sepExists_right box
      (Entails.sepExists_right (w5.extractLsb' 0 32)
      (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
      (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 32 32) ?_)))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [↓reduceIte, emp_sepConj, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)

/-! ## 2. Framing & Entailment Helpers for `segStoreV_ok` -/

def wsStoreFixedEnv (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (x : DecryptGhost) (s0 : State)
    (sp : BitVec 64) (st : kit.StoreState) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
  ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
  ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
  protocolAddressAt A x.rem x.remA ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStoreFixedRest (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decLoadVtableAtV kit ∗ decSaveVtableAtV ikit ∗ decTrustVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗ logOff img ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
    (wsCalleeStackV kit ikit - storeCallStack kit)

theorem wsFixed_wsEnv_store_split (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) :
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreFixedEnv A img kit x s0 sp st ∗ wsStoreFixedRest A img kit ikit x s0 sp ist := by
  subst hsp
  have hj := wsCalleeStack_join_extra kit ikit st ist s0
  refine Entails.trans (Entails.of_eq (show
    wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗ wsEnv A img x (s0.sp - 0xee0#64) ∗ decStoreExtra kit ikit st ist s0 =
    (stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtra kit ikit st ist s0) ∗
    (wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      logOff img ∗ A.pool) by
    unfold wsEnv; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hj) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  refine Entails.pure_right hbound ?_
  unfold wsFixedV wsArgCellsV decVtablesAtV decStoreVtableAtV wsStoreFixedEnv wsStoreFixedRest
  rw [stack_wsCalleeV_storeCall kit ikit (s0.sp - 0xee0#64) hn]
  exact Entails.of_eq (by ac_rfl)

theorem wsFixed_wsEnv_store_join (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreFixedEnv A img kit x s0 sp st ∗ wsStoreFixedRest A img kit ikit x s0 sp ist ⊢
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0 := by
  subst hsp
  have hsplit := wsCalleeStack_split_extra kit ikit st ist s0 hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  refine Entails.trans (Entails.of_eq (show
    wsStoreFixedEnv A img kit x s0 (s0.sp - 0xee0#64) st ∗
      wsStoreFixedRest A img kit ikit x s0 (s0.sp - 0xee0#64) ist =
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeCallStack kit) ∗
        stackAt (s0.sp - 0xee0#64) (storeCallStack kit))) ∗
    (wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      logOff img ∗ A.pool) by
    unfold wsFixedV wsArgCellsV decVtablesAtV decStoreVtableAtV wsStoreFixedEnv wsStoreFixedRest
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeCall kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold wsEnv
  exact Entails.of_eq (by ac_rfl)

def wsStoreCallPre (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (x : DecryptGhost) (s0 : State)
    (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (c0 c1 d0 d1 d2 d3 : BitVec 64) (d5 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
  ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
  ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
  ((sp + 0x2d0#64) ↦₆₄ c0) ∗ ((sp + 0x2d8#64) ↦₆₄ c1) ∗
  ((sp + 0x550#64) ↦₆₄ d0) ∗ ((sp + 0x558#64) ↦₆₄ d1) ∗ ((sp + 0x560#64) ↦₆₄ d2) ∗
  ((sp + 0x568#64) ↦₆₄ d3) ∗ ((sp + 0x570#64) ↦₃₂ d5) ∗
  memRegion (sp + 0x5f0#64) 48 ∗ protocolAddressAt A x.rem x.remA ∗
  sessionRecordAt A (r26 + 0x80#64) g rec' ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStoreFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) (pt : List (BitVec 8)) : SepProp :=
  wsStoreFixedRest A img kit ikit x s0 sp ist ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem storeCall_entails_storeCallPre (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0) ⊢
    ∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreCallPre A img kit x s0 sp r26 g rec' st c0 c1 d0 d1 d2 d3 d5 ∗
      wsStoreFrame C A ctl img kit ikit x ans s0 sp ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_store_split A img kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  rw [memRegion_300_b00_split, memRegion_300_280_store_split, memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      (memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x550#64) 0x24) ∗
      (wsStoreFixedEnv A img kit x s0 sp st ∗ memRegion (sp + 0x5f0#64) 48 ∗
        wsStoreFrame C A ctl img kit ikit x ans s0 sp ist pt) by
    unfold wsStoreFrame; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono
    (memRegion_16_entails_cells (sp + 0x2d0#64))
    (memRegion_36_entails_cells (sp + 0x550#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g (Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d5 (Entails.pure_right hbound ?_))))))))
  unfold wsStoreCallPre wsStoreFixedEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def wsStoreCallPostSpatial (A : RustAlloc) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (x : DecryptGhost) (s0 : State)
    (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ans_store : Except Unit Unit)
    (box o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
  ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
  ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
  ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (img.base + kit.storeFutVtOff)) ∗
  ((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
  ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
  ((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
  ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
  ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗ ((sp + 0x61c#64) ↦₃₂ o6) ∗
  protocolAddressAt A x.rem x.remA ∗
  sessionRecordAt A (r26 + 0x80#64) g rec' ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  (if ans_store.isOk then emp else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStorePostCommonRest (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
  decStoreExtra kit ikit st ist s0

theorem storeCallPost_entails_common (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (ans_store : Except Unit Unit)
    (box o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreCallPostSpatial A img kit x s0 sp r26 g rec' st ans_store box o2 o3 o4 o5 o1 o6 ∗
      wsStoreFrame C A ctl img kit ikit x ans s0 sp ist pt ⊢
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_store.isOk then emp else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRest C A ctl img kit ikit x ans s0 sp st ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    ((((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (img.base + kit.storeFutVtOff))) ∗
      (((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
        ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
        ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
        ((sp + 0x61c#64) ↦₃₂ o6))) ∗
    (wsStoreFixedEnv A img kit x s0 sp st ∗ wsStoreFixedRest A img kit ikit x s0 sp ist) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_store.isOk then emp else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
      sessionRecordAt A (sp + 0x120#64) g rec' ∗
      wsMsgCells x sp ∗ vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
      memRegion (sp + 0x2a8#64) 0x20 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsStoreCallPostSpatial wsStoreFrame wsStoreFixedEnv
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box (img.base + kit.storeFutVtOff)
  have h48 := cells_48_poll_entails_memRegion (sp + 0x5f0#64) (pollTag ans_store)
    o2 o3 o4 o5 o1 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48
  refine Entails.trans (sepConj_mono (sepConj_mono h16 h48)
    (sepConj_mono_left (wsFixed_wsEnv_store_join A img kit ikit x s0 sp st ist hsp hbound))) ?_
  unfold wsStorePostCommonRest
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

theorem storePostCommon_err_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : storePollOutRel img.base o2 o3 o4 o5 o1 (.error ())) :
    ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRest C A ctl img kit ikit x ans s0 sp st ist pt) ⊢
    ∃∗ G : SessionGhost,
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0 := by
  have hrel' : savePollOutRel img.base o2 o3 o4 o5 o1 (.error ()) := hrel
  have hrec0 : sessionRecordAt A (sp + 0x120#64) g rec' ⊢
      ∃∗ G : SessionGhost, droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) :=
    Entails.trans (Entails.sepExists_right g (Entails.refl _))
      (sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur)
  refine Entails.trans (Entails.of_eq (show _ =
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0)) by
    unfold wsStorePostCommonRest; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_savePollOutRel A img.base x28 w20 w21 (sp + 0x580#64)
    o2 o3 o4 o5 o1 o6 hx28 hw1 hrel'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec0 (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono_left hpt)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_store_split]
  exact Entails.of_eq (by ac_rfl)

def wsStoreTailOkPre (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s0_580 s1_588 : BitVec 64) (s2_lo s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (t0_300 t1_308 t2_310 t3_318 : BitVec 64) (t4_320 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  (if prevCap = 0#64 then emp
   else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
  sessionStateAt A (sp + 0x138#64) G st ∗
  ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗ ((sp + 0x29c#64) ↦₆₄ v3) ∗
  ((sp + 0x2a4#64) ↦₃₂ v4) ∗ ((sp + 0x300#64) ↦₆₄ t0_300) ∗ ((sp + 0x308#64) ↦₆₄ t1_308) ∗
  ((sp + 0x310#64) ↦₆₄ t2_310) ∗ ((sp + 0x318#64) ↦₆₄ t3_318) ∗ ((sp + 0x320#64) ↦₃₂ t4_320) ∗
  ((sp + 0x580#64) ↦₆₄ s0_580) ∗ ((sp + 0x588#64) ↦₆₄ s1_588) ∗ ((sp + 0x590#64) ↦₃₂ s2_lo) ∗
  ((sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
  A.pool ∗ stackAt sp storeSegStack

def wsStoreTailOkPost (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x138#64) 344 ∗
  ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗ ((sp + 0x29c#64) ↦₆₄ v3) ∗
  ((sp + 0x2a4#64) ↦₃₂ v4) ∗ ((sp + 0x300#64) ↦₆₄ v2) ∗ ((sp + 0x308#64) ↦₆₄ v3) ∗
  ((sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((sp + 0x318#64) ↦₆₄ s3_598) ∗ ((sp + 0x320#64) ↦₃₂ s4_5a0) ∗
  ((sp + 0x580#64) ↦₆₄ v2) ∗ ((sp + 0x588#64) ↦₆₄ v3) ∗ ((sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
  ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗ A.pool ∗ stackAt sp storeSegStack

def wsStoreTailOkFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp cap ptr : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit)) (wsCalleeStackV kit ikit - storeSegStack)) ∗
  wsMsgCells x sp ∗ vecU8BufPure A cap ptr pt ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem storePostCommon_ok_pre_tail (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) :
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗ sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRest C A ctl img kit ikit x ans s0 sp st ist pt ⊢
    ∃∗ G : SessionGhost, ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ∃∗ s0_580 : BitVec 64, ∃∗ s1_588 : BitVec 64, ∃∗ s2_lo : BitVec 32, ∃∗ s2_hi : BitVec 32,
    ∃∗ s3_598 : BitVec 64, ∃∗ s4_5a0 : BitVec 32,
    ∃∗ t0_300 : BitVec 64, ∃∗ t1_308 : BitVec 64, ∃∗ t2_310 : BitVec 64,
    ∃∗ t3_318 : BitVec 64, ∃∗ t4_320 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0⌝ ∗
      wsStoreTailOkPre A sp g.prevCap g.prevPtr G ses.state
        (cap.extractLsb' 0 32) (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
        s0_580 s1_588 s2_lo s2_hi s3_598 s4_5a0 t0_300 t1_308 t2_310 t3_318 t4_320 ∗
      wsStoreTailOkFrame C A ctl img kit ikit x ans s0 sp cap ptr st ist pt := by
  have h550 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h550
  refine Entails.trans (sepConj_mono_left h550) ?_
  unfold wsStorePostCommonRest
  have hrejoin :
      (memRegion (sp + 0x550#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗
        (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
          vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
          memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
          decStoreExtra kit ikit st ist s0)) =
      ((stackAt sp wsCalleeStack ∗ decStoreExtra kit ikit st ist s0) ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗ vecU8 A (sp + 0x290#64) pt ∗
        memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        (wsFixedV kit ikit x s0 sp ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          logOff img ∗ A.pool ∗ wsMsgCells x sp ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x324#64) 0x25c ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans))) := by
    unfold wsEnv
    rw [memRegion_split (sp + 0x300#64) 0x24 0x22c (by decide),
      memRegion_split (sp + 0x324#64) 0x22c 0x30 (by decide),
      memRegion_split (sp + 0x324#64 + 0x22c#64) 0x24 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  rw [hrejoin]
  have hj := wsCalleeStack_join_extra kit ikit st ist s0
  rw [← hsp] at hj
  refine Entails.trans (sepConj_mono hj
    (sepConj_mono (sessionRecordAt_some_expose A (sp + 0x120#64) g rec' ses hcur)
      (sepConj_mono (vecU8_290_expose A sp pt)
        (sepConj_mono (memRegion_36_entails_cells (sp + 0x300#64))
          (sepConj_mono_left (memRegion_36_entails_cells_split16 (sp + 0x580#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro s0_580; apply Entails.sepExists_elim; intro s1_588
  apply Entails.sepExists_elim; intro s2_lo; apply Entails.sepExists_elim; intro s2_hi
  apply Entails.sepExists_elim; intro s3_598; apply Entails.sepExists_elim; intro s4_5a0
  apply Entails.sepExists_elim; intro t0_300; apply Entails.sepExists_elim; intro t1_308
  apply Entails.sepExists_elim; intro t2_310; apply Entails.sepExists_elim; intro t3_318
  apply Entails.sepExists_elim; intro t4_320; apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr; apply Entails.sepExists_elim; intro G
  rw [sepConj_assoc (⌜_⌝)]; apply Entails.pure_left; intro hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  rw [sepConj_assoc (⌜_⌝), sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpure
  refine Entails.sepExists_right G (Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right s0_580 (Entails.sepExists_right s1_588 (Entails.sepExists_right s2_lo
      (Entails.sepExists_right s2_hi (Entails.sepExists_right s3_598 (Entails.sepExists_right s4_5a0
        (Entails.sepExists_right t0_300 (Entails.sepExists_right t1_308 (Entails.sepExists_right t2_310
           (Entails.sepExists_right t3_318 (Entails.sepExists_right t4_320
             (Entails.pure_right ⟨hbound, hpure⟩ ?_))))))))))))))
  unfold wsStoreTailOkPre wsStoreTailOkFrame
  rw [stack_wsCalleeV_storeSeg kit ikit sp hn]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)

theorem storePost_ok_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp prevCap prevPtr cap ptr : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (x28 w20 w21 : BitVec 64) (hx28 : x28 = okTagVec)
    (hw20 : w20 = (v1 >>> 8#32).zeroExtend 64) (hw21 : w21 = v1.zeroExtend 64)
    (hv1 : v1 = cap.extractLsb' 0 32) (hv2 : v2 = ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    (hv3 : v3 = (BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    (hv4 : v4 = (BitVec.ofNat 64 pt.length).extractLsb' 32 32)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreTailOkPost A sp prevCap prevPtr v1 v2 v3 v4 s2_hi s3_598 s4_5a0 ∗
      wsStoreTailOkFrame C A ctl img kit ikit x ans s0 sp cap ptr st ist pt ⊢
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) (.ok pt) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0 := by
  subst hx28 hw20 hw21 hsp
  have h120 := memRegion_120_1a8_join (s0.sp - 0xee0#64) prevCap prevPtr v1 v2 v3 v4
  have h580 := cells_36_entails_memRegion (s0.sp - 0xee0#64 + 0x580#64) v2 v3 (s2_hi ++ v4) s3_598 s4_5a0
  have hst := stagedRes_ok_pt A (s0.sp - 0xee0#64 + 0x300#64) cap ptr pt s2_hi s3_598 s4_5a0
    v1 v2 v3 v4 hv1 hv2 hv3 hv4
  have hsplit := wsCalleeStack_split_extra kit ikit st ist s0 hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h120 h580 hst
  refine Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 0xee0#64 + 0x120#64) ↦₆₄ prevCap) ∗ ((s0.sp - 0xee0#64 + 0x128#64) ↦₆₄ prevPtr) ∗
      ((s0.sp - 0xee0#64 + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xee0#64 + 0x138#64) 344 ∗
      ((s0.sp - 0xee0#64 + 0x290#64) ↦₃₂ v1) ∗ ((s0.sp - 0xee0#64 + 0x294#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x29c#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x2a4#64) ↦₃₂ v4) ∗ memRegion (s0.sp - 0xee0#64 + 0x2a8#64) 0x20) ∗
    ((((s0.sp - 0xee0#64 + 0x300#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x308#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((s0.sp - 0xee0#64 + 0x318#64) ↦₆₄ s3_598) ∗
      ((s0.sp - 0xee0#64 + 0x320#64) ↦₃₂ s4_5a0)) ∗ vecU8BufPure A cap ptr pt) ∗
    (((s0.sp - 0xee0#64 + 0x580#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x588#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((s0.sp - 0xee0#64 + 0x598#64) ↦₆₄ s3_598) ∗
      ((s0.sp - 0xee0#64 + 0x5a0#64) ↦₃₂ s4_5a0)) ∗
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeSegStack) ∗
        stackAt (s0.sp - 0xee0#64) storeSegStack)) ∗
    (wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗ A.pool) ∗
      wsMsgCells x (s0.sp - 0xee0#64) ∗ memRegion (s0.sp - 0xee0#64) 0xa0 ∗ memRegion (s0.sp - 0xee0#64 + 0x2d0#64) 0x10 ∗
      memRegion (s0.sp - 0xee0#64 + 0x324#64) 0x25c ∗ memRegion (s0.sp - 0xee0#64 + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsStoreTailOkPost wsStoreTailOkFrame
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeSeg kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst
    (sepConj_mono h580 (sepConj_mono_left hsplit)))) ?_
  unfold wsEnv; rw [memRegion_324_adc_split (s0.sp - 0xee0#64)]
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. `segStoreV_ok` and `segStore_ok_pf` -/

attribute [local semireducible] SepWP in
theorem segStoreV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegStoreSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hyps hdrop2 x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, c, hload, hscope, hdec, hcur, hrem, htrust, hsave, htrustRel, hsaveRel, htr, hm⟩
  -- The trace since `s0` is the load, trust and save events: quiet when the kits are.
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (tripleRatchetProgAt img.base C ctl abs) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, hs⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, hs, and_self]).mono (fun _ h => h.1) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hfr, hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads hyps.loads
  have hpc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x2388#64 := by
    rw [← entryOf_eq_tripleRatchetProgAt hyps.loads, hpc]
  have hrecOk : kit.RecOk rec' := hyps.recOk x st0 rec rec' pt hscope hdec
  rw [← hsp] at hx26 hx22 hm
  let ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
    x.rem.val k ans.saveIdentity
  have hm_pre : s.mem ⊨
      (∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
          wsStoreCallPre A img kit x s0 s.sp (s.readReg64 .x26) g rec' st0 c0 c1 d0 d1 d2 d3 d5 ∗
          wsStoreFrame C A ctl img kit ikit x ans s0 s.sp ist2 pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (storeCall_entails_storeCallPre C A ctl img kit ikit x ans s0 s.sp (s.readReg64 .x26)
        st0 ist2 rec' pt hsp hx26)) ?_
    simpa only [sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨g, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  have hstack_lt : storeCallStack kit ≤ 2 ^ 64 := by
    have h1 := storeCallStack_le kit ikit
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segStore_call_wp hyps.hooks.toTripleRatchetHooks.alloc hyps.kit hb
      (self := s0.readReg64 .x3) (addrA := x.remA) (addr := x.rem)
      (g := g) (record := rec') (st := st0)
      (c0 := c0) (c1 := c1) (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d5 := d5)
      (R := wsStoreFrame C A ctl img kit ikit x ans s0 s.sp ist2 pt ∗ R)
      ⟨hfr, hsym⟩ haddr hrecOk hpc' hrun hsp_align hstack_lt hfsAt
      (wsStoreFrame C A ctl img kit ikit x ans s0 s.sp ist2 pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx22_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_store : Except Unit Unit,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st0 x.rem.val rec' ans_store ∧
            sf.readReg64 .x28 = pollTag ans_store ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans_store ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            storePollOutRel img.base o2 o3 o4 o5 o1 ans_store⌝ ∗
          (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
            ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_store.isOk then emp else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
          sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
          wsStorePostCommonRest C A ctl img kit ikit x ans s0 s.sp
            (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_store; apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro o1; apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3; apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5; apply Entails.sepExists_elim; intro o6
      rw [sepConj_assoc]; apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_store (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right o3
          (Entails.sepExists_right o4 (Entails.sepExists_right o5
            (Entails.sepExists_right o6 (Entails.pure_right hpure ?_)))))))
      exact storeCallPost_entails_common C A ctl img kit ikit x ans s0 s.sp (s.readReg64 .x26) g rec'
        (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt
        ans_store box o2 o3 o4 o5 o1 o6 hsp hx26 hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_store, o1, o2, o3, o4, o5, o6, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hstoreRel, hx28_1, htr1, hx21_1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_store with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x550#64) ↦₆₄ o2) ∗ ((sf.sp + 0x558#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x560#64) ↦₆₄ o4) ∗ ((sf.sp + 0x568#64) ↦₆₄ o5) ∗ ((sf.sp + 0x570#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗ ((sf.sp + 0x590#64) ↦₆₄ e2) ∗
              ((sf.sp + 0x598#64) ↦₆₄ e3) ∗ ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            (((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
              sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
              wsStorePostCommonRest C A ctl img kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R := by
        rw [hsp1]; refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0; apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2; apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_err (R := (((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRest C A ctl img kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          ((((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRest C A ctl img kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          (((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
              ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRest C A ctl img kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (storePostCommon_err_entails C A ctl img kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_store_err C S x
        { ans with storeSession := .error () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .error () }) (ans := ans) rfl
      refine ⟨?_, hmeta2, ?_, ?_, { ans with storeSession := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpc2, ← entryOf_eq_tripleRatchetProgAt hyps.loads]; rfl
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.ok ())
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (storePostCommon_ok_pre_tail C A ctl img kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt o2 o3 o4 o5 o6 hsp)) hm1_common
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_ok
      rcases hm1_ok with ⟨G, cap, ptr, s0_580, s1_588, s2_lo, s2_hi, s3_598, s4_5a0,
        t0_300, t1_308, t2_310, t3_318, t4_320, hm1_ok⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_ok
      rcases hm1_ok with ⟨⟨_, hprev_lt, hprev_ptr⟩, hm1_ok⟩
      rw [sepConj_assoc, ← hsp1] at hm1_ok
      have hx26_sf : sf.readReg64 .x26 = sf.sp + 0xa0#64 := by rw [hx26_1, hx26, hsp1]
      have hx22_sf : sf.readReg64 .x22 = sf.sp + 0x294#64 := by rw [hx22_1, hx22, hsp1]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_ok hyps.hooks.toTripleRatchetHooks.alloc hdrop2
          (R := wsStoreTailOkFrame C A ctl img kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx26_sf hx22_sf hprev_lt hprev_ptr
          (wsStoreTailOkFrame C A ctl img kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R) hm1_ok hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1, ← sepConj_assoc] at hm2'
      have hm2_ok := Satisfies.mono (sepConj_mono_left
        (storePost_ok_entails C A ctl img kit ikit x ans s0 s.sp g.prevCap g.prevPtr cap ptr
          st1 ist2 pt
          (cap.extractLsb' 0 32)
          (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
          s2_hi s3_598 s4_5a0 (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          hx28_2 hx20_2 hx21_2 rfl rfl rfl rfl hsp hbound)) hm2'
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ?_)⟩
      have hmod := model_of_store_ok C S x
        { ans with storeSession := .ok () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .ok () }) (ans := ans) rfl
      refine ⟨?_, hmeta2, { ans with storeSession := .ok () }, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpc2, ← entryOf_eq_tripleRatchetProgAt hyps.loads]
      · rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [hsp, sepConj_assoc] using hm2_ok
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedIn ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

theorem segStore_ok_pf {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegStoreSpec img C A ctl uuidTryParse S encRecord abs :=
  segStoreV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

attribute [local semireducible] SepWP in
theorem segStoreVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegStoreSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps hdrop2 x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, c, hload, hscope, hdec, hcur, hrem, htrust, hsave, htrustRel, hsaveRel, htr, hm⟩
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_197 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, hs⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, hs, and_self]).mono (fun _ h => h.1) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hrecOk : kit.RecOk rec' := hyps.recOk x st0 rec rec' pt hscope hdec
  rw [← hsp] at hx26 hx22 hm
  let ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
    x.rem.val k ans.saveIdentity
  have hm_pre : s.mem ⊨
      (∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
          wsStoreCallPrePlaced A kit x s0 s.sp (s.readReg64 .x26) g rec' st0 c0 c1 d0 d1 d2 d3 d5 ∗
          wsStoreFramePlaced C A ctl kit ikit x ans s0 s.sp ist2 pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (storeCall_entails_storeCallPre_placed C A ctl kit ikit x ans s0 s.sp (s.readReg64 .x26)
        st0 ist2 rec' pt hsp hx26)) ?_
    simpa only [sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨g, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  have hstack_lt : storeCallStack kit ≤ 2 ^ 64 := by
    have h1 := storeCallStack_le kit ikit
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segStore_call_placed_wp hyps.hooks.dealloc hyps.kit hstack_lt
      (self := s0.readReg64 .x3) (addrA := x.remA) (addr := x.rem)
      (g := g) (record := rec') (st := st0)
      (c0 := c0) (c1 := c1) (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d5 := d5)
      (R := wsStoreFramePlaced C A ctl kit ikit x ans s0 s.sp ist2 pt ∗ R)
      hcrl haddr hrecOk hpc hrun hsp_align hfsAt
      (wsStoreFramePlaced C A ctl kit ikit x ans s0 s.sp ist2 pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx22_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_store : Except Unit Unit,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st0 x.rem.val rec' ans_store ∧
            sf.readReg64 .x28 = pollTag ans_store ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans_store ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 ans_store⌝ ∗
          (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
            ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
          wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp
            (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_store; apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro strPtr; apply Entails.sepExists_elim; intro vt
      apply Entails.sepExists_elim; intro o1; apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3; apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5; apply Entails.sepExists_elim; intro o6
      rw [sepConj_assoc]; apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_store (Entails.sepExists_right strPtr
        (Entails.sepExists_right vt (Entails.sepExists_right o1
          (Entails.sepExists_right o2 (Entails.sepExists_right o3
            (Entails.sepExists_right o4 (Entails.sepExists_right o5
              (Entails.sepExists_right o6 (Entails.pure_right hpure ?_)))))))))
      exact storeCallPost_entails_common_placed C A ctl kit ikit x ans s0 s.sp (s.readReg64 .x26) g rec'
        (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt
        ans_store box strPtr o2 o3 o4 o5 o1 o6 hsp hx26 hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_store, strPtr, vt, o1, o2, o3, o4, o5, o6, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hstoreRel, hx28_1, htr1, hx21_1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    have hcrl1 := hcrl.of_keepsFrozen hsteps1.keepsFrozen
    rcases ans_store with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x550#64) ↦₆₄ o2) ∗ ((sf.sp + 0x558#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x560#64) ↦₆₄ o4) ∗ ((sf.sp + 0x568#64) ↦₆₄ o5) ∗ ((sf.sp + 0x570#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗ ((sf.sp + 0x590#64) ↦₆₄ e2) ∗
              ((sf.sp + 0x598#64) ↦₆₄ e3) ∗ ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((strPtr ↦ᵣ storeHookStr) ∗
              sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
              wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R := by
        rw [hsp1]; refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0; apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2; apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_placed_err (R := ((strPtr ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
              ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (storePostCommon_err_entails_placed C A ctl kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt strPtr vt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_store_err C S x
        { ans with storeSession := .error () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with storeSession := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.ok ())
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (storePostCommon_ok_pre_tail_placed C A ctl kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt o2 o3 o4 o5 o6 hsp)) hm1_common
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_ok
      rcases hm1_ok with ⟨G, cap, ptr, s0_580, s1_588, s2_lo, s2_hi, s3_598, s4_5a0,
        t0_300, t1_308, t2_310, t3_318, t4_320, hm1_ok⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_ok
      rcases hm1_ok with ⟨⟨_, hprev_lt, hprev_ptr⟩, hm1_ok⟩
      rw [sepConj_assoc, ← hsp1] at hm1_ok
      have hx26_sf : sf.readReg64 .x26 = sf.sp + 0xa0#64 := by rw [hx26_1, hx26, hsp1]
      have hx22_sf : sf.readReg64 .x22 = sf.sp + 0x294#64 := by rw [hx22_1, hx22, hsp1]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_placed_ok hyps.hooks.dealloc hdrop2
          (R := wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R)
          hcrl1 hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx26_sf hx22_sf hprev_lt hprev_ptr
          (wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R) hm1_ok hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1, ← sepConj_assoc] at hm2'
      have hm2_ok := Satisfies.mono (sepConj_mono_left
        (storePost_ok_entails_placed C A ctl kit ikit x ans s0 s.sp g.prevCap g.prevPtr cap ptr
          st1 ist2 pt
          (cap.extractLsb' 0 32)
          (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
          s2_hi s3_598 s4_5a0 (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          hx28_2 hx20_2 hx21_2 rfl rfl rfl rfl hsp hbound)) hm2'
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ?_)⟩
      have hmod := model_of_store_ok C S x
        { ans with storeSession := .ok () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .ok () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, { ans with storeSession := .ok () }, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [hsp, sepConj_assoc] using hm2_ok
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
