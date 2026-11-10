/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.StoreCallSite
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAux
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSave
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Ext-Generic `SegSave` (`+0x2150 → +0x2388 / +0x2294`)

Proves ext-generic `save_identity` shim/poll and tail dispatch `segSaveVX_ok_ext` over
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Postcondition packaging helpers -/

private abbrev saveErrHookRelocOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))

private abbrev saveErrXrefOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620)
    (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)

private def wsSaveCallPostBody {A : RustAlloc} (b : BitVec 64) (img : Obj.Image)
    (ikit : IdentityStoreSpec A b) (sp self addrA keyA : BitVec 64)
    (ist : ikit.IdState) (addr : AddrGhost) (k : IdentityKey) (sf : State) (s_tr : List TraceEvent) : SepProp :=
  ∃∗ ans : Except Unit IdentityChange, ∃∗ box : BitVec 64,
    ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
    ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
    ⌜sf.readReg64 .x28 = savePollTag ans ∧
      sf.readReg64 .x21 = o1.zeroExtend 64 ∧
      ikit.saveRel ist addr.val k ans ∧
      sf.trace = s_tr ++ ikit.saveEvs addr.val k ans ∧
      savePollOutRel b o2 o3 o4 o5 o1 ans⌝ ∗
    ((sp + 0xe8#64) ↦₆₄ addrA) ∗ ((sp + 0x108#64) ↦₆₄ self) ∗
    ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
    ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
    ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
    ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
    ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff)) ∗
    ikit.identityAt self (ikit.saveUpdate ist addr.val k ans) ∗
    ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (b + ikit.saveFutVtOff)) ∗
    ((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
    ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
    ((sp + 0x540#64) ↦₃₂ o6) ∗
    ((sp + 0x5f0#64) ↦₆₄ savePollTag ans) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
    ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
    ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
    ((sp + 0x61c#64) ↦₃₂ o6) ∗
    (if ans.isOk then emp else ((b + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
    logOff img ∗ protocolAddressAt A addr addrA ∗
    (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool ∗
    stackAt sp (saveCallStack ikit)

/-! ## Save shim, poll, and drop/dealloc (`+0x2150..+0x2380`) -/

set_option maxHeartbeats 1200000 in
private theorem segSave_call_wp_ext4K {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {img : Obj.Image}
    {ikit : IdentityStoreSpec A b}
    (hA : AllocContracts4K b A ext)
    (hikit : IdentityStoreKitOkIE img ikit ext)
    (hb : b &&& 0xfff#64 = 0#64)
    (hstack_lt : saveCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA keyA : BitVec 64} {ist : ikit.IdState}
    {addr : AddrGhost} {k : IdentityKey} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hinv : ImgCallInv img s)
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2150#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = keyA)
    (hfs : FsAt ikit.envOk Q (tripleRatchetProgAtExt b ext) s) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2380#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
        ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
        ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff)) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x520#64) ↦₆₄ d0) ∗ ((s.sp + 0x528#64) ↦₆₄ d1) ∗ ((s.sp + 0x530#64) ↦₆₄ d2) ∗
        ((s.sp + 0x538#64) ↦₆₄ d3) ∗ ((s.sp + 0x540#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        logOff img ∗ protocolAddressAt A addr addrA ∗
        (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool ∗
        stackAt s.sp (saveCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ wsSaveCallPostBody b img ikit s.sp self addrA keyA ist addr k sf s.trace ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hshim := subroutine_ok_withStepsPost_inImage hikit.saveShim
  have hdrop := hikit.saveFutDrop
  have hdealloc := msgDecrypt_dealloc_ok_ext4K hA
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2150 0x40
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2334 0x54
  dsimp only [tripleRatchetProgAtExt] at hpc hshim hdrop hdealloc hfs ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches
  refine SepWPp.congr_pre (by rw [stack_saveCall_to_saveShim ikit s.sp hstack_lt]) ?_
  apply SepWPp.of_sepWP_inImage (mid := b + ikit.saveShimOff) hinv
  clear hinv
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv1
  messageDecrypt_call_panic_p_inImage hshim hinv1 (⟨self, addrA, keyA⟩ : IdentityShimCall)
  clear hinv1 hshim
  apply SepWPp.of_sepWP_inImage (mid := b + ikit.savePollOff) hinv_sf
  clear hinv_sf
  wp_simp_pre [sepConj_assoc]
  first
  | (apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩)
  | (apply SepWP.pure_elim; intro hsteps_sh; apply SepWP.pure_elim; rintro ⟨hx1_sf, hx0_ne, hx0_al, htr_sf⟩)
  have henv : ikit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_saveShim_to_savePoll ikit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv2
  have hpoll := hikit.savePoll
  dsimp only [tripleRatchetProgAtExt] at hpoll
  messageDecrypt_call_panic_inImage hpoll hinv2
    (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, keyA, k⟩⟩, self, ist)
  clear hinv2 hpoll hikit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz := ikit.saveFutDrop_ne_zero hb
  have hdz' : (b + ikit.saveFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := ikit.saveBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 ikit.saveBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 ikit.saveBoxSize).toNat = ikit.saveBoxSize :=
    Nat.mod_eq_of_lt ikit.saveBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | c
  · dsimp only [savePollOutAt]
    wp_simp_pre [errTailAt, ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro (w5 : BitVec 64)
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp (b + saveErrHookRelocOff) 10#64 1#64 (b + saveErrXrefOff) w5))
      (by sep_focus)
    wp_steps
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.saveBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = savePollTag (.error ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    unfold wsSaveCallPostBody
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right ((b + saveErrHookRelocOff).extractLsb' 0 32)
      (Entails.sepExists_right (10#32 ++ (b + saveErrHookRelocOff).extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right ((b + saveErrXrefOff).extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ (b + saveErrXrefOff).extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32) ?_)))))))
    refine Entails.pure_right (by simp_all [saveErrHookRelocOff, saveErrXrefOff]) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [savePollOutAt]
    apply SepWP.fold (memRegion_36_entails_cells (s.sp + 1520#64 + 0xc#64)) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro (o2 : BitVec 64)
    apply SepWP.exists_elim; intro (o3 : BitVec 64)
    apply SepWP.exists_elim; intro (o4 : BitVec 64)
    apply SepWP.exists_elim; intro (o5 : BitVec 64)
    apply SepWP.exists_elim; intro (o6 : BitVec 32)
    wp_steps
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.saveBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = savePollTag (.ok c) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    unfold wsSaveCallPostBody
    refine Entails.sepExists_right (.ok c)
      (Entails.sepExists_right box
      (Entails.sepExists_right (if c == .replacedExisting then 1#32 else 0#32)
      (Entails.sepExists_right o2
      (Entails.sepExists_right o3
      (Entails.sepExists_right o4
      (Entails.sepExists_right o5
      (Entails.sepExists_right o6 ?_)))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [↓reduceIte, emp_sepConj, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)

private theorem segSave_call_wp_ext {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {img : Obj.Image}
    {ikit : IdentityStoreSpec A b}
    (hA : AllocContracts b A ext) (hikit : IdentityStoreKitOkIE img ikit ext)
    (hb : b &&& 0xfff#64 = 0#64) (hstack_lt : saveCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA keyA : BitVec 64} {ist : ikit.IdState}
    {addr : AddrGhost} {k : IdentityKey} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hinv : ImgCallInv img s) (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2150#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = keyA)
    (hfs : FsAt ikit.envOk Q (tripleRatchetProgAtExt b ext) s) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2380#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
        ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
        ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff)) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x520#64) ↦₆₄ d0) ∗ ((s.sp + 0x528#64) ↦₆₄ d1) ∗ ((s.sp + 0x530#64) ↦₆₄ d2) ∗
        ((s.sp + 0x538#64) ↦₆₄ d3) ∗ ((s.sp + 0x540#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        logOff img ∗ protocolAddressAt A addr addrA ∗
        (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool ∗
        stackAt s.sp (saveCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ wsSaveCallPostBody b img ikit s.sp self addrA keyA ist addr k sf s.trace ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  segSave_call_wp_ext4K hA.toAllocContracts4K hikit hb hstack_lt hinv haddr hpc hrun hsp_align hx19 hfs

/-! ## Spatial split and join lemmas -/

private def wsSaveFrameExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) : SepProp :=
  wsSaveFixedRest A img kit ikit x s0 sp st ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)

private theorem trusted_entails_saveCallPre_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (k : IdentityKey)
    (hsp : sp = s0.sp - 0xee0#64) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0) ⊢
    ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      wsSaveCallPre A img ikit x s0 sp ist k c0 c1 d0 d1 d2 d3 d5 ∗
      wsSaveFrameExt C A img kit ikit x ans s0 sp st rec' pt := by
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_save_split A img kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  refine Entails.pure_right hbound ?_
  rw [memRegion_300_b00_split, memRegion_300_280_split, memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x520#64) 0x24) ∗
      (wsSaveFixedEnv A img ikit x s0 sp ist ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x5f0#64) 48 ∗ wsSaveFrameExt C A img kit ikit x ans s0 sp st rec' pt) by
    unfold wsSaveFrameExt; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_16_entails_cells (sp + 0x2d0#64))
    (memRegion_36_entails_cells (sp + 0x520#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1
  refine Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d5 ?_))))))
  unfold wsSaveCallPre wsSaveFixedEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private def wsSavePostCommonRestExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
  decStoreExtra kit ikit st ist' s0

private theorem saveCallPost_entails_common_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (k : IdentityKey)
    (ans_save : Except Unit IdentityChange)
    (box o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsSaveCallPostSpatial A img ikit x s0 sp ist k ans_save box o2 o3 o4 o5 o1 o6 ∗
      wsSaveFrameExt C A img kit ikit x ans s0 sp st rec' pt ⊢
    (((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
      ((sp + 0x540#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_save.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
    wsSavePostCommonRestExt C A img kit ikit x ans s0 sp st
      (ikit.saveUpdate ist x.rem.val k ans_save) rec' pt := by
  let ist' := ikit.saveUpdate ist x.rem.val k ans_save
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      (((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (img.base + ikit.saveFutVtOff))) ∗
      (((sp + 0x5f0#64) ↦₆₄ savePollTag ans_save) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
        ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
        ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
        ((sp + 0x61c#64) ↦₃₂ o6)) ∗
      (wsSaveFixedEnv A img ikit x s0 sp ist' ∗ wsSaveFixedRest A img kit ikit x s0 sp st)) ∗
    ((((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
      ((sp + 0x540#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_save.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
      wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
      (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) by
    unfold wsSaveCallPostSpatial wsSaveFrameExt wsSaveFixedEnv saveErrHookRelocOff
    ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box (img.base + ikit.saveFutVtOff)
  have h48 := cells_48_poll_entails_memRegion (sp + 0x5f0#64) (savePollTag ans_save)
    o2 o3 o4 o5 o1 o6
  have hjoin := wsFixed_wsEnv_save_join A img kit ikit x s0 sp st ist' hsp hbound
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48
  refine Entails.trans (sepConj_mono_left (sepConj_mono (key_entails_memRegion_32 (sp + 0x2a8#64) k)
    (sepConj_mono h16 (sepConj_mono h48 hjoin)))) ?_
  unfold wsSavePostCommonRestExt
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

private theorem savePostCommon_ok_entails_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    (((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
      ((sp + 0x540#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    wsSavePostCommonRestExt C A img kit ikit x ans s0 sp st ist' rec' pt ⊢
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist' s0 := by
  have h36 := cells_36_entails_memRegion (sp + 0x520#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36
  refine Entails.trans (sepConj_mono_left h36) ?_
  unfold wsSavePostCommonRestExt
  rw [memRegion_300_b00_split, memRegion_300_280_split]
  exact Entails.of_eq (by ac_rfl)

private theorem savePostCommon_err_entails_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : savePollOutRel img.base o2 o3 o4 o5 o1 (.error ())) :
    ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
    ((((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗ ((sp + 0x540#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    wsSavePostCommonRestExt C A img kit ikit x ans s0 sp st ist' rec' pt) ⊢
    ∃∗ G : SessionGhost,
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist' s0 := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    ((((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗ ((sp + 0x540#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist' s0)) by
    unfold wsSavePostCommonRestExt; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x520#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_savePollOutRel A img.base x28 w20 w21 (sp + 0x580#64)
    o2 o3 o4 o5 o1 o6 hx28 hw1 hrel
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono_left hpt)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_split]
  exact Entails.of_eq (by ac_rfl)

/-! ## Tail steps (`+0x2380 → +0x2388 / +0x2294`) and `segSaveVX_ok_ext` -/

theorem segSave_tail_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {s : State} {R : SepProp} {c : IdentityChange}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2380#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = savePollTag (.ok c)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2388#64) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2380 0x8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches
  simp only [savePollTag] at hx28
  wp_steps
  wp_done

theorem segSave_tail_err_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {s : State} {R : SepProp}
    {o2 o3 o4 o5 e0 e1 e2 e3 : BitVec 64} {o1 o6 e4 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2380#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = savePollTag (.error ()))
    (hx21 : s.readReg64 .x21 = o1.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2294#64) s
      (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
        ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
        ((s.sp + 0x540#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₆₄ e2) ∗ ((s.sp + 0x598#64) ↦₆₄ e3) ∗
        ((s.sp + 0x5a0#64) ↦₃₂ e4))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
          ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
          ((s.sp + 0x540#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
          ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
          ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (o1 >>> 8#32).zeroExtend 64 ∧
        sf.readReg64 .x21 = o1.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2380 0x8
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x23c8 0x14
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x21a0 0x10
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches
  simp only [savePollTag] at hx28
  wp_steps
  wp_done

attribute [local semireducible] SepWP in
set_option maxHeartbeats 800000 in
theorem segSaveVX_ok_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans true R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => (∃ ans', CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x true R s0 s') := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, and_self]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hfr, hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads hyps.loads
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext hyps.loads
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName
  have hpc' : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2150#64 := by
    rw [hpc]; exact congrArg (· + 0x2150#64) hentry
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  rw [← hsp] at hx26 hx19 hx22 hm
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsSaveCallPre A img ikit x s0 s.sp ist1 k c0 c1 d0 d1 d2 d3 d5 ∗
          wsSaveFrameExt C A img kit ikit x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_saveCallPre_ext C A img kit ikit x ans s0 s.sp st0 ist1 rec' pt k hsp)) ?_
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have hstack_lt : saveCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := saveCallStack_le_wsCalleeV kit ikit
    have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segSave_call_wp_ext4K hyps.alloc hyps.ikit hb hstack_lt
      (R := wsSaveFrameExt C A img kit ikit x ans s0 s.sp st0 rec' pt ∗ R)
      ⟨hfr, hsym⟩ haddr hpc' hrun hsp_align hx19 hfsAt
      (wsSaveFrameExt C A img kit ikit x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    unfold wsSaveCallPostBody at hm1'
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_save : Except Unit IdentityChange,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜sf.readReg64 .x28 = savePollTag ans_save ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist1 x.rem.val k ans_save ∧
            sf.trace = s.trace ++ ikit.saveEvs x.rem.val k ans_save ∧
            savePollOutRel img.base o2 o3 o4 o5 o1 ans_save⌝ ∗
          (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
            ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
            ((s.sp + 0x540#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_save.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
          wsSavePostCommonRestExt C A img kit ikit x ans s0 s.sp st0
            (ikit.saveUpdate ist1 x.rem.val k ans_save) rec' pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_save
      apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro o1
      apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3
      apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5
      apply Entails.sepExists_elim; intro o6
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_save (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right o3
          (Entails.sepExists_right o4 (Entails.sepExists_right o5
            (Entails.sepExists_right o6 (Entails.pure_right hpure ?_)))))))
      exact saveCallPost_entails_common_ext C A img kit ikit x ans s0 s.sp st0 ist1 rec' pt k
        ans_save box o2 o3 o4 o5 o1 o6 hsp hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_save, o1, o2, o3, o4, o5, o6, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hsaveRel, htr1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_save with ⟨⟨⟩⟩ | c
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.error ())
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x520#64) ↦₆₄ o2) ∗ ((sf.sp + 0x528#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x530#64) ↦₆₄ o4) ∗ ((sf.sp + 0x538#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x540#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestExt C A img kit ikit x ans s0 s.sp st0 ist2 rec' pt) ∗ R := by
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
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_err_ext (R := (((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestExt C A img kit ikit x ans s0 s.sp st0 ist2 rec' pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          ((((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestExt C A img kit ikit x ans s0 s.sp st0 ist2 rec' pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          (((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
              ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗ ((s.sp + 0x540#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsSavePostCommonRestExt C A img kit ikit x ans s0 s.sp st0 ist2 rec' pt)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (savePostCommon_err_entails_ext C A img kit ikit x ans s0 s.sp st0 ist2 rec' ses hcur pt
          (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_save_err C S x
        { ans with saveIdentity := .error () } rec rec' pt ses k
        hload hdec hcur hrem htrust rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .error () }) (ans := ans) rfl
      refine ⟨?_, hmeta2, ?_, ?_, { ans with saveIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpc2, ← hentry]; rfl
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_load_trust_save,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.ok c)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (savePostCommon_ok_entails_ext C A img kit ikit x ans s0 s.sp st0 ist2 rec' pt o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedV kit ikit x s0 s.sp ∗ wsEnv A img x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A (s.sp + 0x120#64) g rec') ∗
            vecU8 A (s.sp + 0x290#64) pt ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
            decStoreExtra kit ikit st0 ist2 s0) ∗ R) := by
        rwa [emp_sepConj]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
        hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_ok_ext (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1) _ hm1_emp hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with saveIdentity := .ok c }, ?_⟩)⟩
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .ok c }) (ans := ans) rfl
      refine ⟨?_, hmeta2, ?_, ?_, rec, rec', pt, ses, k, c,
        hload, hscope, hdec, hcur, hrem, htrust, rfl, htrustRel, hsaveRel, ?_, ?_⟩
      · rw [hpc2, ← hentry]
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx22_2, hx22_1, hx22, hsp]
      · rw [htr2, htr1, htr, List.append_assoc]
      · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVX_ext ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

theorem segSaveVX_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans true R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => (∃ ans', CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x true R s0 s') :=
  segSaveVX_ok_ext4K hyps.toDecHypsExt4K x ans R s0 s haddr hfs hst

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
