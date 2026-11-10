/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKey
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segment S3 Part C (`EvictOldestKeySpecX`)

Proves `evictOldestKey_ok_x` (`+0x3fc → +0x474`) for `RatchetState::consume_message_key` on
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
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X
open ProofLib.ProgramReflection

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_SegS3PartC : True := trivial

def evictOldestKeyFootprintX (A : RustAlloc) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (sp : BitVec 64) : SepProp :=
  ((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
  ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
  ((chainPtr + 64#64) ↦₆₄ 2001#64) ∗
  msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
  pinDealloc A gk.1.cipher ∗
  pinDealloc A gk.1.mac ∗
  pinDealloc A gk.1.iv ∗
  pinDealloc A gk.1.seed ∗
  A.pool ∗
  stackAt sp extHookStack

def evictOldestKeyPostFootprintX (A : RustAlloc) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (sp : BitVec 64) : SepProp :=
  ((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
  ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
  ((chainPtr + 64#64) ↦₆₄ 2000#64) ∗
  msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
  A.pool ∗
  stackAt sp extHookStack

theorem stackAt_20000_split_partC (sp : BitVec 64) :
    stackAt sp 20000 = memRegion (sp - 20000#64) 3616 ∗ stackAt sp extHookStack :=
  stackAt_split_bottom sp 16384 3616 (by decide)

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

private theorem dealloc_ok_at_state_s3_x {b : BitVec 64} {A : RustAlloc}
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

theorem sepWP_inv_of_mem_symtab {img : Obj.Image} {P : Program} {mid pc_post : BitVec 64} {s0 s : State}
    {Pre : SepProp} {Post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (h : SepWP P mid s Pre (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP P pc_post sm Pm Post))
    (hmem : s.mem = s0.mem := by rfl) (hsym' : s.symtab = s0.symtab := by rfl) :
    SepWP P pc_post s Pre Post :=
  ProofLib.SepWP.of_sepWP_inv (by unfold Obj.Image.FrozenLoaded at *; rwa [hmem]) (hsym'.trans hsym) h

set_option maxHeartbeats 1600000 in
theorem evictOldestKey_wp_x {_F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (x : ConsumeMessageKeyGhost) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1020#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ [])
    (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (_hmac_lt : gk.1.mac.cap.toNat < 2 ^ 63)
    (_hiv_lt : gk.1.iv.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (_hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1140#64) s
      (evictOldestKeyFootprintX A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ evictOldestKeyPostFootprintX A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  unfold evictOldestKeyFootprintX evictOldestKeyPostFootprintX msgKeyPopSlots pinDealloc
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hdealloc := dealloc_ok_at_x hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
  cmk_fetches_range img.base (Rust.withPanics ext) hfn 255 285
  unfold SP2Ext cmkName at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  examples_hide_fetches
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, hcip_ne_max⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hseed_cap_ne, ↓reduceIte]
  apply sepWP_inv_of_mem_symtab hfl hsym (mid := entry + bv% (1044))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl hsym
  wp_step
  wp_if hcmn
  · exfalso; exact hcip_add1 hcmn
  · wp_steps
    wp_if hcip0 <;> (
      simp only [hcip0, ↓reduceIte, emp_sepConj, sepConj_assoc]
      try (
        have hdealloc1 := dealloc_ok_at_state_s3_x hdealloc hfl hsym
        apply sepWP_inv_of_mem_symtab hfl hsym (mid := entry + bv% (1076))
        wp_steps
        wp_call hdealloc1 (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1)
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        intro hfl hsym)
      wp_steps)
    all_goals (
      wp_if hmac0 <;> (
        simp only [hmac0, ↓reduceIte, emp_sepConj, sepConj_assoc]
        try (
          have hdealloc2 := dealloc_ok_at_state_s3_x hdealloc hfl hsym
          apply sepWP_inv_of_mem_symtab hfl hsym (mid := entry + bv% (1096))
          wp_steps
          wp_call hdealloc2 (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1)
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          intro hfl hsym)
        wp_steps))
    all_goals (
      wp_if hiv0 <;> (
        simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
        try (
          have hdealloc3 := dealloc_ok_at_state_s3_x hdealloc hfl hsym
          apply sepWP_inv_of_mem_symtab hfl hsym (mid := entry + bv% (1116))
          wp_steps
          wp_call hdealloc3 (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1)
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          intro hfl hsym)
        wp_steps))
    all_goals (
      wp_if hseed0
      · exfalso; exact hseed_cap_ne hseed0
      · have hdealloc4 := dealloc_ok_at_state_s3_x hdealloc hfl hsym
        wp_steps
        wp_call hdealloc4 (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1)
        wp_done)

def evictOldestKeyFrameX (F : ShaCompress)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
  arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
  memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 480#64 - 20000#64) 3616 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0

theorem evictOldestKeyHeapX_entails_evictOldestKeyFootprintX
    (F : ShaCompress)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hmk_len : chc.messageKeys.length = 2000)
    (hgk_len : cg.keys.length = 2000) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
    have hgks1_len : gks1.length = 2000 + 1 := by
      simp [gks1, List.length_zip, hgk_len, hmk_len]
    let gk := gks1[2000]'(by omega)
    evictOldestKeyHeapX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ⊢
      ⌜gk.2.seed ≠ [] ∧
        gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
        gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
        gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
        gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
      evictOldestKeyFootprintX A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗
      evictOldestKeyFrameX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  intro chainPtr gks1 hgks1_len gk
  unfold evictOldestKeyHeapX evictOldestKeyFootprintX evictOldestKeyFrameX
  dsimp only
  have hpop := vecBuf_messageKeyAt_pop_split A mkCap1 mkPtr1 gks1 hgks1_len
  change vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1 gks1 ⊢
    ⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
      A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
      messageKeyAt A gk (mkPtr1 + 208000#64) ∗
      memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) at hpop
  have hpop2 := Entails.trans hpop
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (messageKeyAt_entails_pop A gk (mkPtr1 + 208000#64))))))
  rw [vecHeader_chainPtr_48 chainPtr mkCap1 mkPtr1 2001#64, stackAt_20000_split_partC (s0.sp - 480#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpop2))))) ?_
  have hpull :
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗ ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗ ((chainPtr + 64#64) ↦₆₄ 2001#64)) ∗
        (⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
          A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
          (⌜gk.2.seed ≠ [] ∧
            gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
            gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
            gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
            gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
            msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
            pinDealloc A gk.1.cipher ∗
            pinDealloc A gk.1.mac ∗
            pinDealloc A gk.1.iv ∗
            pinDealloc A gk.1.seed) ∗
          memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104)) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        ratchetContextAt A x.self Gc stc ci ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 480#64 - 20000#64) 3616 ∗ stackAt (s0.sp - 480#64) extHookStack) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) =
      (⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
        ⌜gk.2.seed ≠ [] ∧
          gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
          gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
          gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
          gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
        ((((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
          ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
          ((chainPtr + 64#64) ↦₆₄ 2001#64) ∗
          msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
          pinDealloc A gk.1.cipher ∗
          pinDealloc A gk.1.mac ∗
          pinDealloc A gk.1.iv ∗
          pinDealloc A gk.1.seed ∗
          A.pool ∗
          stackAt (s0.sp - 480#64) extHookStack) ∗
         (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
          vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
          memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
          ratchetContextAt A x.self Gc stc ci ∗
          (x.theirA ↦ₛ x.their.bytes.toList) ∗
          (x.ckA ↦ₛ chainKeyBytes ckc) ∗
          memRegion x.ret 88 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 480#64 - 20000#64) 3616 ∗
          cmkLoopFrame s0.sp x.ret x.counter ∗
          cmkSavedRegs s0.sp s0))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro hpure
  exact Entails.pure_right hpure (Entails.refl _)

theorem evictOldestKeyPost_entails_cmkLoopHeapX
    (F : ShaCompress)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (hci_stc : ci < stc.receiverChains.length)
    (hsrk : PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey)
    (hmk_len : chc.messageKeys.length = 2000)
    (hgk_len : cg.keys.length = 2000)
    (hmk_cap_le : 2001 ≤ mkCap1.toNat)
    (hmk_cap_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hmk_ptr_ne : mkPtr1 ≠ 0#64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    let cg' : ChainGhost :=
      { cg with mkCap := mkCap1, mkPtr := mkPtr1,
                keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
    (evictOldestKeyPostFootprintX A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗
      evictOldestKeyFrameX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0) ⊢
      cmkLoopHeapX A img x (Gc.setChain ci cg') (updatedRatchetState F stc ci chc ckc) ckc s0 := by
  intro chainPtr cg'
  unfold evictOldestKeyPostFootprintX evictOldestKeyFrameX cmkLoopHeapX
  dsimp only
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  set keys' := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys
  set messageKeys' := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  have hkeys'_len : keys'.length = 2000 := by
    simp [keys', hgk_len, maxMessageKeys]
  have hmk'_len : messageKeys'.length = 2000 := by
    simp [messageKeys', hmk_len, maxMessageKeys]
  have hzip_eq : gks1.take 2000 = keys'.zip messageKeys' := by
    simpa [gks1, keys', messageKeys', maxMessageKeys] using
      (zip_take_cons_eq (newMsgKeyGhost seedPtr) cg.keys (ckc.messageKeys F) chc.messageKeys 2000).symm
  have hhdr_len : (2000#64 : BitVec 64) = BitVec.ofNat 64 (keys'.zip messageKeys').length := by
    simp [List.length_zip, hkeys'_len, hmk'_len]
  have hslot_mem : msgKeyPopSlots gk (mkPtr1 + 208000#64) ⊢
      memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 :=
    msgKeyPopSlots_entails_memRegion gk (mkPtr1 + 208000#64)
  have hvec_reasm := vecBuf_messageKeyAt_pop_reassemble A mkCap1 mkPtr1 gks1
    hgks1_len hmk_cap_le hmk_cap_lt hmk_ptr_ne
  rw [hzip_eq] at hvec_reasm
  have hrat := chainAt_sep_ratchetContextAt_entails_ratchetAt A x.self Gc stc hci_stc
    cg' (updatedReceiverChain F chc ckc)
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hslot_mem))))) ?_
  have hpull :
      ((((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ 2000#64) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 ∗
        A.pool ∗
        stackAt (s0.sp - 480#64) extHookStack) ∗
       (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        ratchetContextAt A x.self Gc stc ci ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 480#64 - 20000#64) 3616 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0)) =
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       (((vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 2000#64 ∗
           (A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
            arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
            memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 ∗
            memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104))) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
         ratchetContextAt A x.self Gc stc ci) ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 20000 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by
    rw [vecHeader_chainPtr_48 chainPtr mkCap1 mkPtr1 2000#64, stackAt_20000_split_partC (s0.sp - 480#64)]
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  rintro ⟨hsrk_len, hpriv⟩
  have hchain := chainAt_of_update_messageKeys A cg chc chainPtr mkCap1 mkPtr1 keys' messageKeys'
    hsrk (by simp [hmk'_len, maxMessageKeys]) (by omega) hsrk_len hpriv
  apply sepConj_mono_left
  rw [hzip_eq, hhdr_len]
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right hvec_reasm))))) ?_
  refine Entails.trans (sepConj_mono_left hchain) ?_
  exact hrat

theorem evictOldestKey_ok_x {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)} {img : Obj.Image} :
    EvictOldestKeySpecX F A ext img := by
  intro hA himg x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB hchc_get hSB hL
  rcases hSB with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hfrozen, hsymtab, hvregs⟩,
    ⟨hx19, hx21, hx22, hx23, hx25, hx26, _hx28⟩,
    ⟨hci_gc, hcg_eq⟩, hsrk, hmk_len, hgk_len, hmk_cap_le, hmk_cap_lt, hmk_ptr_ne, hmem⟩
  have hci_stc : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc_get).1
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  set gk := gks1[2000]'(by omega)
  have hsplit := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyHeapX_entails_evictOldestKeyFootprintX F A img x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 hmk_len hgk_len)) hmem
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hseed_ne, hcip_lt, _, hmac_lt, _, hiv_lt, _, hseed_le, hseed_lt, _⟩, hmem_pre⟩
  have hpc' : sB.pc = (SP2Ext img.base ext).fnAddr cmkName + 1020#64 := by
    rwa [cmkEvictOldestKeyPC_eq_fnAddr_x himg ext] at hpc
  have hwp := evictOldestKey_wp_x (_F := F) hA x chainPtr mkCap1 mkPtr1 gk
    (evictOldestKeyFrameX F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R)
    s0 sB hpc' hrun hsp hsp0_align hsp_align hx29 hfrozen hsymtab hx19 hx21 hx22 hx23 hx25 hx26
    hseed_ne hcip_lt hmac_lt hiv_lt hseed_le hseed_lt
  rcases hwp.elim hmem_pre hL with ⟨sC, hsteps, ⟨hpc_sC, hrun_sC, P_f, hmf,
    himp, hsp_sC, hsp_align_sC, ⟨htrace_sC, hvregs_sC⟩, hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC, hx29_sC⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  rw [← cmkAdvanceChainKeyPC_eq_fnAddr_x himg ext] at hpc_sC
  have hpost_fp := himp hmf
  rw [← sepConj_assoc] at hpost_fp
  set cg' : ChainGhost :=
    { cg with mkCap := mkCap1, mkPtr := mkPtr1,
              keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
  have hmem_sC := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyPost_entails_cmkLoopHeapX F A img x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 gk hci_stc hsrk hmk_len hgk_len hmk_cap_le hmk_cap_lt hmk_ptr_ne))
    hpost_fp
  have hagree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
    RatchetGhost.AgreeExcept.setChain Gc hci_gc cg' (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
  refine ⟨sC, hsteps, Gc.setChain ci cg', hagree,
    hpc_sC,
    ⟨hrun_sC, hsp_sC, hsp0_align, hsp_align_sC, hx29_sC, htrace_sC.trans htrace,
      hfrozen.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hsymtab, hvregs_sC.trans hvregs⟩,
    ⟨hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC⟩,
    hmem_sC⟩

end Proofs.libsignal.Stage1X.CmkX
