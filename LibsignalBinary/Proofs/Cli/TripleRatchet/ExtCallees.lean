/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Contract-Backed Callee Bridges on `tripleRatchetProgAtExt`

Layout-independent stack splits and `ChainKey::next_chain_key` verification (`NextChainKeyOkX`) on
`tripleRatchetProgAtExt` under `extHookStack`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Encrypt

/-- Stack split of `rootStack` (`262,144` B) into `dropChainStackX` (`16,464` B) plus frame. -/
theorem stackAt_rootStack_split_dropChainX (sp : BitVec 64) :
    stackAt sp rootStack =
      stackAt sp dropChainStackX ∗ memRegion (sp - 262144#64) (rootStack - dropChainStackX) := by
  rw [stackAt_sub sp rootStack dropChainStackX (by decide) (by decide), sepConj_comm]
  simp only [rootStack]
  rfl

abbrev hmacStackX : Nat := 2048 + extHookStack

abbrev nextChainKeyStackX : Nat := nextChainKeyStack + extHookStack

def nextChainKeySpecX (F : ShaCompress) (img : Obj.Image) : Spec ChainKeyGhost :=
  Spec.inImage
    { pre := fun (self, ck, ret) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s.sp nextChainKeyStackX
      post := fun (self, ck, ret) s0 sf =>
        ⌜ck.nextChainKey F ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗
        (match ck.nextChainKey F with
          | .ok ck' => ret ↦ₛ chainKeyBytes ck'
          | .error _ => ⌜False⌝) ∗
        stackAt s0.sp nextChainKeyStackX
      onPanic := fun (_, ck, _) s0 sf =>
        ⌜ck.nextChainKey F = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

def NextChainKeyOkX (img : Obj.Image) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName)
    (nextChainKeySpecX F img)

theorem stackAt_split_ge (sp : BitVec 64) {small big : Nat}
    (hle : small ≤ big) (hmax : big < 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small :=
  stackAt_sub sp big small hle hmax

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_nextChainKeyX (sp : BitVec 64) :
    stackAt sp nextChainKeyStackX =
      memRegion (sp - 20480#64) 1968 ∗
      stackAt (sp - 80#64) hmacStackX ∗
      memRegion (sp - 80#64) 12 ∗
      memRegion (sp - 68#64) 32 ∗
      (∃∗ b0 : BitVec 8, (sp - 36#64) ↦₈ b0) ∗
      memRegion (sp - 35#64) 3 ∗
      (∃∗ v29 : BitVec 64, (sp - 32#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 24#64) ↦₆₄ v30) ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  show memRegion (sp - BitVec.ofNat 64 20480) 20480 = _
  rw [LibsignalTripleRatchet.mr_cut' sp 20480 18512 1968 18512 20480 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 18512 80 18432 80 18512 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 80 68 12 68 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 68 36 32 36 68 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 36 35 1 35 36 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 35 32 3 32 35 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_one (sp - 36#64), ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]
  have h18512 : sp - 80#64 - 18432#64 = sp - 18512#64 := by bv_arith
  unfold stackAt
  change _ =
    memRegion (sp - 20480#64) 1968 ∗
    memRegion (sp - 80#64 - 18432#64) 18432 ∗
    memRegion (sp - 80#64) 12 ∗
    memRegion (sp - 68#64) 32 ∗
    (∃∗ b0 : BitVec 8, (sp - 36#64) ↦₈ b0) ∗
    memRegion (sp - 35#64) 3 ∗
    (∃∗ v29 : BitVec 64, (sp - 32#64) ↦₆₄ v29) ∗
    (∃∗ v30 : BitVec 64, (sp - 24#64) ↦₆₄ v30) ∗
    (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
    (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19)
  rw [h18512]

private theorem stackAt_nextChainKeyX_repack (sp : BitVec 64) (w0 w1 w2 w3 v29 v30 v20 v19 : BitVec 64)
    (b0 : BitVec 8) :
    memRegion (sp - 20480#64) 1968 ∗
    stackAt (sp - 80#64) hmacStackX ∗
    memRegion (sp - 80#64) 12 ∗
    ((sp - 68#64) ↦₆₄ w0) ∗
    ((sp - 60#64) ↦₆₄ w1) ∗
    ((sp - 52#64) ↦₆₄ w2) ∗
    ((sp - 44#64) ↦₆₄ w3) ∗
    ((sp - 36#64) ↦₈ b0) ∗
    memRegion (sp - 35#64) 3 ∗
    ((sp - 32#64) ↦₆₄ v29) ∗
    ((sp - 24#64) ↦₆₄ v30) ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp nextChainKeyStackX := by
  rw [stackAt_nextChainKeyX sp]
  have hw0 := pointsTo64_entails_memRegion (sp - 68#64) w0
  have hw1 := pointsTo64_entails_memRegion (sp - 60#64) w1
  have hw2 := pointsTo64_entails_memRegion (sp - 52#64) w2
  have hw3 := pointsTo64_entails_memRegion (sp - 44#64) w3
  have h60 : sp - 68#64 + 8#64 = sp - 60#64 := by bv_arith
  have h52 : sp - 60#64 + 8#64 = sp - 52#64 := by bv_arith
  have h44 : sp - 52#64 + 8#64 = sp - 44#64 := by bv_arith
  have h32 :
      ((sp - 68#64) ↦₆₄ w0) ∗ ((sp - 60#64) ↦₆₄ w1) ∗ ((sp - 52#64) ↦₆₄ w2) ∗ ((sp - 44#64) ↦₆₄ w3) ⊢
        memRegion (sp - 68#64) 32 := by
    refine Entails.trans (sepConj_mono hw0 (sepConj_mono hw1 (sepConj_mono hw2 hw3))) ?_
    rw [← h44, ← memRegion_split (sp - 52#64) 8 8 (by decide),
        ← h52, ← memRegion_split (sp - 60#64) 8 16 (by decide),
        ← h60, ← memRegion_split (sp - 68#64) 8 24 (by decide)]
    exact Entails.refl _
  have hb0 : ((sp - 36#64) ↦₈ b0) ⊢ ∃∗ b : BitVec 8, (sp - 36#64) ↦₈ b :=
    Entails.sepExists_right b0 (Entails.refl _)
  have hv29 : ((sp - 32#64) ↦₆₄ v29) ⊢ ∃∗ v : BitVec 64, (sp - 32#64) ↦₆₄ v :=
    Entails.sepExists_right v29 (Entails.refl _)
  have hv30 : ((sp - 24#64) ↦₆₄ v30) ⊢ ∃∗ v : BitVec 64, (sp - 24#64) ↦₆₄ v :=
    Entails.sepExists_right v30 (Entails.refl _)
  have hv20 : ((sp - 16#64) ↦₆₄ v20) ⊢ ∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v :=
    Entails.sepExists_right v20 (Entails.refl _)
  have hv19 : ((sp - 8#64) ↦₆₄ v19) ⊢ ∃∗ v : BitVec 64, (sp - 8#64) ↦₆₄ v :=
    Entails.sepExists_right v19 (Entails.refl _)
  have hpull :
      (memRegion (sp - 20480#64) 1968 ∗
        stackAt (sp - 80#64) hmacStackX ∗
        memRegion (sp - 80#64) 12 ∗
        ((sp - 68#64) ↦₆₄ w0) ∗
        ((sp - 60#64) ↦₆₄ w1) ∗
        ((sp - 52#64) ↦₆₄ w2) ∗
        ((sp - 44#64) ↦₆₄ w3) ∗
        ((sp - 36#64) ↦₈ b0) ∗
        memRegion (sp - 35#64) 3 ∗
        ((sp - 32#64) ↦₆₄ v29) ∗
        ((sp - 24#64) ↦₆₄ v30) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) =
      (memRegion (sp - 20480#64) 1968 ∗
        stackAt (sp - 80#64) hmacStackX ∗
        memRegion (sp - 80#64) 12 ∗
        (((sp - 68#64) ↦₆₄ w0) ∗ ((sp - 60#64) ↦₆₄ w1) ∗
         ((sp - 52#64) ↦₆₄ w2) ∗ ((sp - 44#64) ↦₆₄ w3)) ∗
        ((sp - 36#64) ↦₈ b0) ∗
        memRegion (sp - 35#64) 3 ∗
        ((sp - 32#64) ↦₆₄ v29) ∗
        ((sp - 24#64) ↦₆₄ v30) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) := by ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h32 (sepConj_mono hb0 (sepConj_mono_right
      (sepConj_mono hv29 (sepConj_mono hv30 (sepConj_mono hv20 hv19))))))))

private theorem panic_at_add_overflow_trExt {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : CryptoVerification.libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow")) :
    (tripleRatchetProgAtExt b ext).externAt? ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by decide)
    (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
    (by simp [Rust.isPanicSymbol])

private theorem hmac_ok_at_nextChainKey_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hhmac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256")
      ((hmacSpecWithStack F hmacStackX).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName +
        bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"))
      ((hmacSpecWithStack F hmacStackX).inImage img) := by
  have haddr :
      (tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName +
        bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") =
      (tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256" := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"),
        (ls_lemma% fnOff "libsignal_protocol::crypto::hmac_sha256"),
        BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hhmac

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

private theorem hmacX_ok_at_state {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {img : Obj.Image} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok (tripleRatchetProgAtExt b ext) addr ((hmacSpecWithStack F hmacStackX).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (tripleRatchetProgAtExt b ext) addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp hmacStackX
        post := (hmacSpecWithStack F hmacStackX).post } := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, hmacSpecWithStack]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

set_option maxHeartbeats 800000 in
theorem nextChainKey_ok_of_hmacX
    {img : Obj.Image} {F : ShaCompress} {ext : String → Option (State → State)}
    (hhmac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256")
      ((hmacSpecWithStack F hmacStackX).inImage img)) :
    NextChainKeyOkX img F ext := by
  unfold NextChainKeyOkX
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")
  have hhmac_at := hmac_ok_at_nextChainKey_x hhmac
  have hpan_ovf := panic_at_add_overflow_trExt (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) (by simp only [arm64_norm])
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  simp only [nextChainKeySpecX, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen, hsym⟩, ⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s0.sp nextChainKeyStackX,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck, memRegion36_unpack ret, stackAt_nextChainKeyX s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun b0 =>
    SepWPp.exists_elim fun v29 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v19 => ?_
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalSession.libsignalSessionBin
    img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) 116
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName = entry
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) hfrozen hsym
  wp_steps
  examples_hide_fetches
  apply SepWP.done (by simp_all) (by simp_all)
  intro hfrozen1 hsym1
  have hhmac1 := hmacX_ok_at_state hhmac_at hfrozen1 hsym1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 36#64) 2#8]
  apply ProofLib.SepWPp.of_sepWP_frozen (mid := entry + bv% (56)) hfrozen1 hsym1
  wp_call hhmac1 (s0.sp - 68#64, self, keyToBytes32 ck.key, s0.sp - 36#64, [2#8])
  examples_hide_fetches
  apply SepWP.done (by simp_all) (by simp_all)
  intro hfrozen2 hsym2
  by_cases hidx : ck.index = BitVec.allOnes 32
  · have hidx_max : ck.index = 0xffffffff#32 := hidx
    rw [hidx_max]
    code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalSession.libsignalSessionBin
      img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) 116
    subst hentry
    generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName = entry
    apply ProofLib.SepWPp.of_sepWP_frozen
      (mid := entry + bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"))
      hfrozen2 hsym2
    wp_steps
    examples_hide_fetches
    apply SepWP.done (by simp_all) (by simp_all)
    intro _ _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_ovf) fun hm' => ?_
    simpa only [nextChainKeySpecX, Spec.inImage, sepConj_assoc] using
      allowPanic_panicked ⟨nextChainKey_panic_of_eq F ck hidx,
        by simp_all [Rust.panicked]⟩ hm'
  · have hz2 : (ck.index + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hidx; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := ck.index.isLt
      rw [BitVec.toNat_add] at h1
      change (ck.index.toNat + 1) % 4294967296 = 0 at h1
      change ck.index.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (nck_length_hmacWith F (keyToBytes32 ck.key) [2#8])
    have hw_sp := hw32 (s0.sp - 68#64)
    have h60 : s0.sp - 68#64 + 8#64 = s0.sp - 60#64 := by bv_arith
    have h52 : s0.sp - 68#64 + 16#64 = s0.sp - 52#64 := by bv_arith
    have h44 : s0.sp - 68#64 + 24#64 = s0.sp - 44#64 := by bv_arith
    rw [h60, h52, h44] at hw_sp
    rw [hw_sp]
    code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalSession.libsignalSessionBin
      img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) 116
    subst hentry
    generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName = entry
    apply ProofLib.SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen2 hsym2
    wp_steps
    examples_hide_fetches
    apply SepWP.done (by simp_all) (by simp_all)
    intro _ _
    refine SepWPp.done (by simp_all) (by simp_all) ⟨fun hm => ?_, rfl, by ck_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    have hok := nextChainKey_ok_of_ne F ck hidx
    rw [hok]
    dsimp only
    refine Entails.pure_right ⟨by nofun, by simp_all⟩ ?_
    let ck' : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩
    have hkey_eq : keyToBytes32 ck'.key = hmacWith F (keyToBytes32 ck.key) [2#8] := by
      show keyToBytes32 (bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed)) = _
      rw [← hmacWith_two_eq_chainStep]
      exact keyToBytes32_bytesToKey32 _ (nck_length_hmacWith F _ _)
    rw [pointsToBytes_chainKeyBytes_eq self ck, pointsToBytes_chainKeyBytes_eq ret ck',
        hkey_eq, hw32 ret]
    have hstk := stackAt_nextChainKeyX_repack s0.sp w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 2#8
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hstk))
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by dsimp only [ck', Reg.x19, Reg.x20, Reg.lr, Reg.x29]; ac_rfl)

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees
