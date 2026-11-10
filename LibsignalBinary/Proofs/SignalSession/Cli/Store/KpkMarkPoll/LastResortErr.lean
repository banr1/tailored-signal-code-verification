/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoData
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Drops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Varint

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

private theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

private theorem vecU8At_of_flat (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A cap ptr bs) ⊢
      vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader vecU8Tail SpqrV1.ChainProofs.bytesAt
  simp only [Bool.false_eq_true, ite_false]
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero]
  by_cases hc : cap = 0#64
  · subst hc
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hbs
    simp only [ite_true, pointsToBytes_nil, sepConj_emp]
    rw [show ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 [].length)) ∗
          ⌜[].length ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ =
        ⌜[].length ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 [].length)) by
          ac_rfl]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)
  · simp only [hc, ite_false]
    rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by
          ac_rfl]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

private theorem vecU8At_unpack_pos (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hc : cap ≠ 0#64) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8At vecHeader
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, hc, ite_false, sepConj_assoc]
  ac_rfl

private theorem vecU8_of_grown (A : RustAlloc) (v v8 v16 cap ptr : BitVec 64)
    (bs : List (BitVec 8))
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16)
    (hc : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
      vecU8 A v bs := by
  subst hv8; subst hv16
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, hc, ite_false, sepConj_assoc]
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by
        ac_rfl]
  exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

/-! ## 1. `reused` Exit (`+560 .. +628`, OOM `+1104 .. +1112`, Cleanup `+744`) -/

/-- Allocates the 15-byte `"reused base key"` `String`, populates `strSpeAt A x.out 24`,
drops `used` / `seen` / `file`, and returns through `kpk_err_cleanup_2e8`. -/
theorem kpk_reused_230 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (x : KpkMarkPollGhost) (s0 s : State)
    (wR0 wR7 : BitVec 64)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (560))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hfoc : P ⊢
      ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
      ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
      ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
      vecU8Tail A usedCap usedPtr usedBs ∗
      SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
      vecU8Tail A seenCap seenPtr seenBs ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
      vecU8Tail A fileCap filePtr fileBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A x.out .reused ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗ A.pool ∗ F) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  obtain ⟨hpos15, hpow15, hhi15⟩ : LayoutOk 15 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have hshim := kpk_shim_ok_at hC
  have halloc := kpk_alloc_ok_at hC
  have hpanic := kpk_panic_handle_error (b := img.base) (ext := ext)
  have hclean := @kpk_err_cleanup_2e8 img A ext hC
  clear hC
  have he_fn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr kpkMarkPollName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") := by
    simp only [Program.fnAddr_rebase, kpkMarkPollName, kpkMarkPoll_fnOff]
  have hr_addr := adrp_add_reused_eq hb he_fn
  clear he_fn
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    560 72
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    1104 12
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hclean hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  refine sepWPp_conseq hfoc ?_
  apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (576)) hinv
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_alloc"))
    hinv1
  wp_apply
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_al
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    rw [pull_alloc_pure]
    refine SepWPp.pure_elim fun htrace => ?_
    have htr_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htrace, hpost, htr]
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    apply bind_sepWPp_state_mark; intro st_pan
    refine SepWPp.panic (by kpk_norm) (by kpk_norm) (hpan _ _ ?_)
    have htr_pan : (Rust.panicked st_pan).trace = s0.trace ++ [allocFailedEvent] := by
      dsimp only [st_pan]; simpa only [Rust.panicked, wp_norm, arm64_norm] using htr_oom
    exact allocFailedIn_of_eq htr_pan
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    rw [pull_alloc_pure]
    refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
    have htr_sf1 : sf_1.trace = s0.trace := by
      rw [htr1]; kpk_norm
    apply SepWPp.of_sepWP_ret
    have hafter_adrp : ∀ (sm : State) (Q_m : SepProp),
        sm.pc = fnBase + bv% (588) →
        sm.status = .Running →
        sm.sp = s0.sp - 0xf0#64 →
        sm.readReg64 .x29 = s0.sp - 0x60#64 →
        ImgCallInv img sm →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        sm.readReg64 .x0 = sf_1.readReg64 .x0 →
        sm.readReg64 .x8 = reusedStrAddr img.base →
        sm.readReg64 .x19 = x.fut →
        sm.readReg64 .x20 = x.out →
        sm.readReg64 .x27 = seenCap →
        (Q_m ⊢
          memRegion (sf_1.readReg64 .x0) 15 ∗
          A.live (sf_1.readReg64 .x0) 15 1 ∗
          ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
          ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
          ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
          SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
          vecU8Tail A usedCap usedPtr usedBs ∗
          SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
          vecU8Tail A seenCap seenPtr seenBs ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
          vecU8Tail A fileCap filePtr fileBs ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          epiloguePre s0 x ∗ A.pool ∗ F) →
        SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
          (s0.readReg64 .lr) sm Q_m Q := by
      intro sm Q_m hpcm hrunm hspm hfpm hinvm htrm hvm r0 r8 r19 r20 r27 hQm
      have hsp_alm : sm.spAligned = true := spAligned_sub_f0 hsp_align hspm
      refine SepWP.weaken_pre hQm ?_
      rw [ProofLib.memRegion_split (sf_1.readReg64 .x0) 8 7 (by decide),
          ProofLib.memRegion_eight]
      simp only [sepConj_assoc, sepExists_sepConj_left]
      refine SepWP.exists_elim fun z0 => ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (624)) hinvm
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_mid
      refine SepWP.fold (write_15_overlap_mid (sf_1.readReg64 .x0) wR0) (by sep_focus) ?_
      rw [ProofLib.memRegion_eight]
      (try simp only [sepExists_sepConj_right])
      (try simp only [sepExists_sepConj_left])
      simp only [sepConj_assoc]
      refine SepWP.exists_elim fun z7 => ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (744)) hinv_mid
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_2e8
      refine SepWP.fold (write_15_overlap_done (sf_1.readReg64 .x0) wR0 wR7) (by sep_focus) ?_
      have hlen15 : ((unpack64 wR0).take 7 ++ unpack64 wR7).length = 15 := by
        simp [unpack64_length]
      have hspe24 : (0x8000000000000018#64 : BitVec 64) = speWord 24 := by decide
      refine hclean x s0 _ 24 (sf_1.readReg64 .x0) ((unpack64 wR0).take 7 ++ unpack64 wR7)
        3#64 _ usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr fileBs _
        (((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
          ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
          ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗ F)
        (by rw [hlen15]; decide)
        (by rw [hlen15]; decide)
        hoom
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by kpk_norm)
        (by kpk_norm)
        hinv_2e8
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by rw [← hspe24]; kpk_norm)
        (by rw [hlen15]; kpk_norm)
        rfl
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by rw [hlen15]; unfold epiloguePre; kpk_sep_focus)
        fun sf_e P_e htr_e hsp_e hcs_e hPe =>
          hk sf_e P_e (htr_e.trans htrm) hsp_e hcs_e
            (Entails.trans hPe (by dsimp [kpkMarkOutAt]; sep_focus))
    apply SepWP.seq_inImage (mid := fnBase + bv% (588)) hinv_al
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_adrp
    exact hafter_adrp _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      hinv_adrp (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by rw [← hr_addr]; kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by rw [hsp_sf, hsp]; unfold epiloguePre; kpk_sep_focus)

/-! ## 2. `malformed` Exit (`+676 .. +740`, OOM `+1068 .. +1076`, Cleanup `+744`) -/

/-- Allocates the 14-byte `"malformed file"` `String`, populates `strSpeAt A x.out 1`,
drops `used` / `seen` / `file`, and returns through `kpk_err_cleanup_2e8`. -/
theorem kpk_malformed_2a4 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (x : KpkMarkPollGhost) (s0 s : State)
    (wM0 wM6 : BitVec 64)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (676))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx25 : s.readReg64 .x25 = seenPtr)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hfoc : P ⊢
      ((malformedStrAddr img.base) ↦₆₄ᵣ wM0) ∗
      ((malformedStrAddr img.base + 6#64) ↦₆₄ᵣ wM6) ∗
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
      vecU8Tail A usedCap usedPtr usedBs ∗
      SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
      vecU8Tail A seenCap seenPtr seenBs ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
      vecU8Tail A fileCap filePtr fileBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A x.out .malformed ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        ((malformedStrAddr img.base) ↦₆₄ᵣ wM0) ∗
        ((malformedStrAddr img.base + 6#64) ↦₆₄ᵣ wM6) ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗ A.pool ∗ F) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  obtain ⟨hpos14, hpow14, hhi14⟩ : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have hshim := kpk_shim_ok_at hC
  have halloc := kpk_alloc_ok_at hC
  have hpanic := kpk_panic_handle_error (b := img.base) (ext := ext)
  have hclean := @kpk_err_cleanup_2e8 img A ext hC
  clear hC
  have he_fn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr kpkMarkPollName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") := by
    simp only [Program.fnAddr_rebase, kpkMarkPollName, kpkMarkPoll_fnOff]
  have hm_addr := adrp_add_malformed_eq hb he_fn
  clear he_fn
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    676 68
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    1068 12
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hclean hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  refine sepWPp_conseq hfoc ?_
  apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (692)) hinv
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
      "__rustc::__rust_alloc"))
    hinv1
  wp_apply
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_al
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    rw [pull_alloc_pure]
    refine SepWPp.pure_elim fun htrace => ?_
    have htr_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htrace, hpost, htr]
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    apply bind_sepWPp_state_mark; intro st_pan
    refine SepWPp.panic (by kpk_norm) (by kpk_norm) (hpan _ _ ?_)
    have htr_pan : (Rust.panicked st_pan).trace = s0.trace ++ [allocFailedEvent] := by
      dsimp only [st_pan]; simpa only [Rust.panicked, wp_norm, arm64_norm] using htr_oom
    exact allocFailedIn_of_eq htr_pan
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    rw [pull_alloc_pure]
    refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
    have htr_sf1 : sf_1.trace = s0.trace := by
      rw [htr1]; kpk_norm
    apply SepWPp.of_sepWP_ret
    have hafter_adrp : ∀ (sm : State) (Q_m : SepProp),
        sm.pc = fnBase + bv% (712) →
        sm.status = .Running →
        sm.sp = s0.sp - 0xf0#64 →
        sm.readReg64 .x29 = s0.sp - 0x60#64 →
        ImgCallInv img sm →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        sm.readReg64 .x0 = sf_1.readReg64 .x0 →
        sm.readReg64 .x8 = malformedStrAddr img.base →
        sm.readReg64 .x19 = x.fut →
        sm.readReg64 .x20 = x.out →
        sm.readReg64 .x25 = seenPtr →
        sm.readReg64 .x27 = seenCap →
        (Q_m ⊢
          memRegion (sf_1.readReg64 .x0) 14 ∗
          A.live (sf_1.readReg64 .x0) 14 1 ∗
          ((malformedStrAddr img.base) ↦₆₄ᵣ wM0) ∗
          ((malformedStrAddr img.base + 6#64) ↦₆₄ᵣ wM6) ∗
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
          SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
          vecU8Tail A usedCap usedPtr usedBs ∗
          SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
          vecU8Tail A seenCap seenPtr seenBs ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
          vecU8Tail A fileCap filePtr fileBs ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          epiloguePre s0 x ∗ A.pool ∗ F) →
        SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
          (s0.readReg64 .lr) sm Q_m Q := by
      intro sm Q_m hpcm hrunm hspm hfpm hinvm htrm hvm r0 r8 r19 r20 r25 r27 hQm
      have hsp_alm : sm.spAligned = true := spAligned_sub_f0 hsp_align hspm
      refine SepWP.weaken_pre hQm ?_
      rw [ProofLib.memRegion_split (sf_1.readReg64 .x0) 8 6 (by decide),
          ProofLib.memRegion_eight]
      simp only [sepConj_assoc, sepExists_sepConj_left]
      refine SepWP.exists_elim fun z0 => ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (740)) hinvm
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_mid
      refine SepWP.fold (write_14_overlap_mid (sf_1.readReg64 .x0) wM0) (by sep_focus) ?_
      rw [ProofLib.memRegion_eight]
      (try simp only [sepExists_sepConj_right])
      (try simp only [sepExists_sepConj_left])
      simp only [sepConj_assoc]
      refine SepWP.exists_elim fun z6 => ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (744)) hinv_mid
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_2e8
      refine SepWP.fold (write_14_overlap_done (sf_1.readReg64 .x0) wM0 wM6) (by sep_focus) ?_
      have hlen14 : ((unpack64 wM0).take 6 ++ unpack64 wM6).length = 14 := by
        simp [unpack64_length]
      have hspe1 : (0x8000000000000001#64 : BitVec 64) = speWord 1 := by decide
      refine hclean x s0 _ 1 (sf_1.readReg64 .x0) ((unpack64 wM0).take 6 ++ unpack64 wM6)
        (sm.readReg64 .x28) _ usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr fileBs _
        (((malformedStrAddr img.base) ↦₆₄ᵣ wM0) ∗
          ((malformedStrAddr img.base + 6#64) ↦₆₄ᵣ wM6) ∗ F)
        (by rw [hlen14]; decide)
        (by rw [hlen14]; decide)
        hoom
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by kpk_norm)
        (by kpk_norm)
        hinv_2e8
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by rw [← hspe1]; kpk_norm)
        (by rw [hlen14]; kpk_norm)
        rfl
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by rw [hlen14]; unfold epiloguePre; kpk_sep_focus)
        fun sf_e P_e htr_e hsp_e hcs_e hPe =>
          hk sf_e P_e (htr_e.trans htrm) hsp_e hcs_e
            (Entails.trans hPe (by dsimp [kpkMarkOutAt]; sep_focus))
    apply SepWP.seq_inImage (mid := fnBase + bv% (712)) hinv_al
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_adrp
    exact hafter_adrp _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      hinv_adrp (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by rw [← hm_addr]; kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by rw [hsp_sf, hsp]; unfold epiloguePre; kpk_sep_focus)

/-! ## 3. `seen ++ used` Append & `last_resort.put` Exit (`+892 .. +984` & `+1024 .. +1052`) -/

set_option maxHeartbeats 1200000 in
/-- Reserves 37 bytes in `seen` if needed (`+1024 .. +1052`), `memcpy`s `used` to `seen + seenLen`,
drops `used`, writes `file` + `seen ++ used` descriptors into `[sp + 0x40]` / `[sp + 0x28]`,
and chains into `kpk_put_and_epilogue_b8`. -/
theorem kpk_append_37c {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {decStk getStk putStk : Nat}
    (hC : AllocContractsX img A ext)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (x : KpkMarkPollGhost) (s0 s : State)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hu_eq : usedBs.length = 37)
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (_hu_ptr : usedPtr ≠ 0#64)
    (hseen32 : seenBs.length < 2 ^ 32)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (892))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 seenBs.length)
    (hx24 : s.readReg64 .x24 = usedPtr)
    (hx26 : s.readReg64 .x26 = x.self)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hx28 : s.readReg64 .x28 = 37#64)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hfoc : P ⊢
      ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
      ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
      ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
      ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
      vecU8Tail A usedCap usedPtr usedBs ∗
      SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
      vecU8Tail A seenCap seenPtr seenBs ∗
      SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
      vecU8Tail A fileCap filePtr fileBs ∗
      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      epiloguePre s0 x ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A x.out .ok ∗
        dirAt A (x.self + 0x28#64) (x.kg.lastResort.put fileBs (seenBs ++ usedBs)) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗ A.pool ∗ F) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hres_le : doReserveStackX ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hres := kpkReserve_ok hC (le_refl doReserveStackX)
  rw [← cliDoReserve_fnAddr_eq] at hres
  have hmc := kpk_memcpy_ok_at hC
  have hdealloc := kpk_dealloc_ok_at hC
  have hput_ep := @kpk_put_and_epilogue_b8 img A ext decStk getStk putStk hPut
  clear hC hPut
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    892 96
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    1024 32
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hres hmc hdealloc hput_ep hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  refine sepWPp_conseq hfoc ?_
  have hjoin : ∀ (sj : State) (curCap curPtr : BitVec 64) (Q_j : SepProp),
      seenBs.length + 37 ≤ curCap.toNat →
      curCap.toNat < 2 ^ 63 →
      curPtr ≠ 0#64 →
      sj.pc = fnBase + bv% (912) →
      sj.status = .Running →
      sj.sp = s0.sp - 0xf0#64 →
      sj.readReg64 .x29 = s0.sp - 0x60#64 →
      sj.trace = s0.trace →
      ImgCallInv img sj →
      calleeSavedVRegs sj = calleeSavedVRegs s0 →
      sj.readReg64 .x8 = curPtr →
      sj.readReg64 .x19 = x.fut →
      sj.readReg64 .x20 = x.out →
      sj.readReg64 .x21 = usedCap →
      sj.readReg64 .x22 = BitVec.ofNat 64 seenBs.length →
      sj.readReg64 .x24 = usedPtr →
      sj.readReg64 .x26 = x.self →
      sj.readReg64 .x28 = 37#64 →
      (Q_j ⊢
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ curCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ curPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
        vecU8Tail A usedCap usedPtr usedBs ∗
        A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ seenBs) ∗
        memRegion (curPtr + BitVec.ofNat 64 seenBs.length) (curCap.toNat - seenBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
        vecU8Tail A fileCap filePtr fileBs ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        epiloguePre s0 x ∗ A.pool ∗ F) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) sj Q_j Q Qp := by
    intro sj curCap curPtr Q_j hcur_ge hcur_lt hcur_ptr hpc_j hrun_j hsp_j hfp_j htr_j hinv_j
      hv_j j8 j19 j20 j21 j22 j24 j26 j28 hQj
    have hcur_ne0 : curCap ≠ 0#64 :=
      fun h0 => by have : curCap.toNat = 0 := by subst h0; rfl
                   omega
    have hsp_alj : sj.spAligned = true := spAligned_sub_f0 hsp_align hsp_j
    refine sepWPp_conseq hQj ?_
    rw [subStack_split s0.sp hext_le hhi]
    have hsplit37 :
        memRegion (curPtr + BitVec.ofNat 64 seenBs.length) (curCap.toNat - seenBs.length) =
        memRegion (curPtr + BitVec.ofNat 64 seenBs.length) usedBs.length ∗
          memRegion (curPtr + BitVec.ofNat 64 (seenBs ++ usedBs).length)
            (curCap.toNat - (seenBs ++ usedBs).length) := by
      have hn : curCap.toNat - seenBs.length =
          usedBs.length + (curCap.toNat - (seenBs ++ usedBs).length) := by
        rw [List.length_append, hu_eq]; omega
      rw [ProofLib.memRegion_split' (b := curPtr + BitVec.ofNat 64 seenBs.length)
            (n := usedBs.length) (k := curCap.toNat - (seenBs ++ usedBs).length)
            (b' := curPtr + BitVec.ofNat 64 (seenBs ++ usedBs).length)
            hn (by rw [List.length_append, BitVec.ofNat_add]; bv_omega) (by omega)]
    rw [hsplit37]
    have hused_bytes : SpqrV1.ChainProofs.bytesAt false usedPtr usedBs = (usedPtr ↦ₛ usedBs) := rfl
    rw [hused_bytes]
    have hpost_drop : ∀ (sd : State) (Q_d : SepProp),
        sd.pc = fnBase + bv% (956) →
        sd.status = .Running →
        sd.sp = s0.sp - 0xf0#64 →
        sd.trace = s0.trace →
        ImgCallInv img sd →
        calleeSavedVRegs sd = calleeSavedVRegs s0 →
        sd.readReg64 .x19 = x.fut →
        sd.readReg64 .x20 = x.out →
        sd.readReg64 .x26 = x.self →
        (Q_d ⊢
          ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
          ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          vecU8 A (s0.sp - 0xc8#64) (seenBs ++ usedBs) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
          SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
          vecU8Tail A fileCap filePtr fileBs ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          epiloguePre s0 x ∗ A.pool ∗ F) →
        SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) sd Q_d Q Qp := by
      intro sd Q_d hpc_d hrun_d hsp_d htr_d hinv_d hv_d d19 d20 d26 hQd
      have hsp_ald : sd.spAligned = true := spAligned_sub_f0 hsp_align hsp_d
      refine sepWPp_conseq hQd ?_
      rw [ProofLib.memRegion_split' (b := s0.sp - 0xb0#64) (n := 24) (k := 24)
            (b' := s0.sp - 0x98#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 0xb0#64) (n := 8) (k := 16)
            (b' := s0.sp - 0xa8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 0xa8#64) (n := 8) (k := 8)
            (b' := s0.sp - 0xa0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
      kpk_sep_norm
      refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
        SepWPp.exists_elim fun w2 => ?_
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (184)) hinv_d
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_b8
      refine hput_ep x s0 _ (x.self + 0x28#64) (s0.sp - 0xb0#64) (s0.sp - 0xc8#64)
        x.kg.lastResort fileBs (seenBs ++ usedBs) _
        (((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
          ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0x98#64) 24 ∗
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗ F)
        hhi hlr_chg
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by kpk_norm)
        (by kpk_norm)
        hinv_b8
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        hpan
        (by
          refine Entails.trans ?_
            (sepConj_mono_right
              (sepConj_mono_left
                (vecU8_of_bytes_tail A (s0.sp - 0xb0#64) (s0.sp - 0xa8#64) (s0.sp - 0xa0#64)
                  fileCap filePtr fileBs (by bv_omega) (by bv_omega) hf_len hf_lt hf_ptr)))
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_p P_p htr_p hsp_p hcs_p hPp =>
          hk sf_p P_p htr_p hsp_p hcs_p <| by
            refine Entails.trans hPp ?_
            have hm48 := slot_b0_24_24_merge s0.sp
            kpk_sep_norm
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left hm48))))))))
            sep_focus
    have hlen_app : BitVec.ofNat 64 seenBs.length + 37#64 =
        BitVec.ofNat 64 (seenBs ++ usedBs).length := by
      rw [List.length_append, hu_eq, BitVec.ofNat_add]
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (928)) hinv_j
    apply SepWP.seq_inImage
      (mid := fnBase +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "memcpy"))
      hinv_j
    wp_steps
    apply SepWP.done (by kpk_norm) (by wp_norm_lhs)
    intro hinv_mc
    have ⟨hF_mc, hsym_mc⟩ := hinv_mc
    have h37 : (37#64 : BitVec 64).toNat = usedBs.length := hu_eq.symm
    rw [← hsp_j]
    wp_apply using hmc
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_928
    apply bind_sepWPp_state_mark; intro st_928
    have hst_928_sp : st_928.sp = s0.sp - 0xf0#64 := by dsimp only [st_928]; kpk_norm
    have hsp_al_928 : st_928.spAligned = true := spAligned_sub_f0 hsp_align hst_928_sp
    dsimp only [st_928] at *
    by_cases hucap : usedCap = 0#64
    · subst hucap
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (956)) hinv_928
      rw [← hused_bytes, hsp_j]
      refine SepWP.fold
        (Entails.of_eq (pointsToBytes_append curPtr seenBs usedBs).symm)
        (by sep_focus) ?_
      refine SepWP.fold (vecU8_free_zero A usedPtr hu_len) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_956
      refine hpost_drop _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        hinv_956 (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) ?_
      rw [subStack_split s0.sp hext_le hhi]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (vecU8_of_grown A (s0.sp - 0xc8#64) (s0.sp - 0xc0#64) (s0.sp - 0xb8#64)
              curCap curPtr (seenBs ++ usedBs) (by bv_omega) (by bv_omega) hcur_ne0
              (by rw [List.length_append, hu_eq]; omega) hcur_lt hcur_ptr))))))
      unfold epiloguePre
      kpk_sep_norm
      sep_focus
    · obtain ⟨hu_pos, hu_pow1, hu_hi⟩ := layoutOk_u8_of_ne_zero hucap hu_lt
      have hucap_beq : (usedCap == 0#64) = false := beq_eq_false_iff_ne.mpr hucap
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (956)) hinv_928
      rw [← hused_bytes, hsp_j]
      refine SepWP.fold
        (Entails.of_eq (pointsToBytes_append curPtr seenBs usedBs).symm)
        (by sep_focus) ?_
      refine SepWP.fold (vecU8_free_ne A (ptr := usedPtr) hucap hu_len hu_lt) (by sep_focus) ?_
      apply SepWP.seq_inImage
        (mid := fnBase +
          bv% (ls_rel%
            "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
            "__rustc::__rust_dealloc"))
        hinv_928
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_da
      have ⟨hF_da, hsym_da⟩ := hinv_da
      wp_call hdealloc (usedPtr, usedCap.toNat, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hinv_956
      refine hpost_drop _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        hinv_956 (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) ?_
      rw [subStack_split s0.sp hext_le hhi]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (vecU8_of_grown A (s0.sp - 0xc8#64) (s0.sp - 0xc0#64) (s0.sp - 0xb8#64)
              curCap curPtr (seenBs ++ usedBs) (by bv_omega) (by bv_omega) hcur_ne0
              (by rw [List.length_append, hu_eq]; omega) hcur_lt hcur_ptr))))))
      unfold epiloguePre
      kpk_sep_norm
      sep_focus
  by_cases hult : (seenCap - BitVec.ofNat 64 seenBs.length).ult 37#64 = true
  · have hbound37 := reserve_seen_bound hseen32 hs_len hs_lt hult
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase - bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) hinv
    wp_steps
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hinv_res
    apply bind_sepWPp_state_mark; intro st_res
    have hsp_res : st_res.sp = s0.sp - 0xf0#64 := by
      dsimp only [st_res]; kpk_norm
    dsimp only [st_res] at *
    have hlen_seen_nat : (BitVec.ofNat 64 seenBs.length).toNat = seenBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine kpk_call_reserve hres ⟨s0.sp - 0xc8#64, seenCap, seenPtr, seenBs, 37⟩
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - doReserveStackX) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 fileBs.length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        SpqrV1.ChainProofs.bytesAt false usedPtr usedBs ∗
        vecU8Tail A usedCap usedPtr usedBs ∗
        SpqrV1.ChainProofs.bytesAt false filePtr fileBs ∗
        vecU8Tail A fileCap filePtr fileBs ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x ∗ F)
      (ret_pc := fnBase + bv% (1048))
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_res)
      (by kpk_norm)
      (by kpk_norm)
      hinv_res
      (by kpk_norm)
      hlen_seen_nat
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      hbound37
      hpan
      (by
        rw [hsp_res, subStack_split s0.sp hres_le hhi]
        have hv_flat := vecU8At_of_flat A (s0.sp - 0xc8#64) seenCap seenPtr seenBs hs_len hs_lt hs_ptr
        have e1 : s0.sp - 0xc8#64 + 8#64 = s0.sp - 0xc0#64 := by bv_omega
        have e2 : s0.sp - 0xc8#64 + 16#64 = s0.sp - 0xb8#64 := by bv_omega
        rw [e1, e2] at hv_flat
        refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left hv_flat))
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
      fun sm p' hpcm hrunm hspm hcsm hinvm htrm hp'_ne => ?_
    let newCapN := reserveCap seenCap.toNat seenBs.length 37
    have hnew_lt : newCapN < 2 ^ 63 := by dsimp [newCapN] at *; omega
    have hnew_pos : 0 < newCapN := by dsimp [newCapN, reserveCap]; omega
    have hnew_bv_ne : BitVec.ofNat 64 newCapN ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      change newCapN = 0 at ht; omega
    have hnew_toNat : (BitVec.ofNat 64 newCapN).toNat = newCapN := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecU8At_unpack_pos A (s0.sp - 0xc8#64) (BitVec.ofNat 64 newCapN) p' seenBs hnew_bv_ne]
    kpk_sep_norm
    refine SepWPp.pure_elim fun _ => ?_
    have e1 : s0.sp - 0xc8#64 + 8#64 = s0.sp - 0xc0#64 := by bv_omega
    have e2 : s0.sp - 0xc8#64 + 16#64 = s0.sp - 0xb8#64 := by bv_omega
    rw [e1, e2]
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_res
    have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (912)) hinvm
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_912
    refine hjoin _ (BitVec.ofNat 64 newCapN) p' _
      (by rw [hnew_toNat]; dsimp [newCapN, reserveCap]; omega)
      (by rw [hnew_toNat]; exact hnew_lt)
      hp'_ne
      (by kpk_norm)
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [htrm]; kpk_norm))
      hinv_912
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x21 hcsm)]; kpk_norm))
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcsm)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)]; kpk_norm))
      (by
        rw [hsp_res, subStack_split s0.sp hres_le hhi]
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
  · have hult_f : (seenCap - BitVec.ofNat 64 seenBs.length).ult 37#64 = false :=
      Bool.eq_false_iff.mpr hult
    have hfast_ge := fast_seen_cap_ge hseen32 hs_len hult_f
    have hs_ne0 : seenCap ≠ 0#64 :=
      fun h0 => by have : seenCap.toNat = 0 := by subst h0; rfl
                   omega
    have hseen_live : ∀ R : SepProp,
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗ (vecU8Tail A seenCap seenPtr seenBs ∗ R) =
        A.live seenPtr seenCap.toNat 1 ∗ ((seenPtr ↦ₛ seenBs) ∗
          (memRegion (seenPtr + BitVec.ofNat 64 seenBs.length) (seenCap.toNat - seenBs.length) ∗ R)) := by
      intro R
      unfold SpqrV1.ChainProofs.bytesAt vecU8Tail
      simp only [Bool.false_eq_true, hs_ne0, ite_false]
      ac_rfl
    rw [hseen_live]
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (912)) hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_912
    exact hjoin _ seenCap seenPtr _
      hfast_ge hs_lt hs_ptr
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      hinv_912
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by unfold epiloguePre; kpk_sep_focus)

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
