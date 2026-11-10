/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import all Init.Data.String.Defs

/-!
# Relocatable CLI `MessageEncrypt` `WithStoresVT` (Part 6): `SegSignal` Ok/Err and `SegPreKey`

Completes `h45_segSignal_placed_okVT` and proves `h45_segPreKey_placed_okVT` on Block `464`
(`lsProg_464 Hk`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems (subroutine_ok_merge_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (lsRetAddr624_of_lr_eq_blockPlacement_base_add)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] blkPl_198_ρ_lanon122

section SegSignal

private theorem pqCap_add_one_ne_zero_placed {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem segSignal_list_len3_placed {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

private theorem signalMessageWordsAt_eq_words64At_placed (gm : SignalMessageGhost) (sm : SignalMessage)
    (a : BitVec 64) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt gm sm a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [gm.pqCap, gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
        BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
        m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem signalMessageAt_relocate_placed (A : RustAlloc) (gm : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A gm src sm ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) := by
  have hm' := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A gm src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨hpq, hm'⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨m7, m8, m9, m10, m11, m12, m14, hm'⟩ := hm'
  rw [signalMessageWordsAt_eq_words64At_placed, sepConj_assoc] at hm'
  refine ⟨gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
    BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A gm sm m7 m8 m9 m10 m11 m12 m14,
    pqCap_add_one_ne_zero_placed hpq, hm', ?_⟩
  intro dst
  rw [← signalMessageWordsAt_eq_words64At_placed]
  exact signalMessageAt_pack A gm dst sm m7 m8 m9 m10 m11 m12 m14

private def segSignalOkFramePlaced [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (draws : Nat) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x3f0#64) 120 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5f8#64) 0x508 ∗
  memRegion (sp + 0xb18#64) 0x68 ∗
  memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_ok_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (k : IdentityKey) (sm : SignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp)
    (s0 s : State)
    (hm : s.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R) :
    ∃ (pqCap' pqPtr' : BitVec 64) (gm : SignalMessageGhost)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) ∧
      (s.mem ⊨ (words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗
          words64At (sp + 0xb00#64) [v0, v1, v2] ∗
          words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
            d14, d15]) ∗
        (segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr' pqCap' pqPtr'
          k draws sp H s0 ∗ R)) := by
  unfold signalMessageResultAt at hm
  dsimp only at hm
  have hm1 : s.mem ⊨
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqCap', hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqPtr', hm1⟩ := hm1
  have hm2 : s.mem ⊨
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨gm, hm2⟩ := hm2
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H, hpq, hm3, hpack⟩ :=
    signalMessageAt_relocate_placed A gm (sp + 0x580#64) sm hm2
  have h370 : memRegion (sp + 0x370#64) 0xf8 =
      memRegion (sp + 0x370#64) 128 ∗ memRegion (sp + 0x3f0#64) 120 :=
    segSignal_memRegion_cut (sp + 0x370#64) (sp + 0x3f0#64) 0xf8 128 120 (by bv_omega) (by decide) (by decide)
  have h5f8 : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗
        (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68) := by
    rw [segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  rw [h370, h5f8] at hm3
  have hm_d : s.mem ⊨ memRegion (sp + 0x370#64) (8 * 16) ∗
      (memRegion (sp + 0xb00#64) (8 * 3) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) := by
    unfold segSignalOkFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm3
  obtain ⟨ds, hds_len, hm_d⟩ := memRegion_exists_words64At 16 (sp + 0x370#64) (by decide) hm_d
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :=
    segSignal_list_len16 ds hds_len
  have hm_v : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗
      (words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15] ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_d
  obtain ⟨vs, hvs_len, hm_v⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm_v
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3_placed vs hvs_len
  refine ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_v

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_ok_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (sm : SignalMessage) (gm : SignalMessageGhost)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (draws : Nat) (sp : BitVec 64) (H R Pm : SepProp) (s0 s1 : State)
    (hpack : ∀ dst : BitVec 64,
      words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ⊢ signalMessageAt A gm dst sm)
    (hPm : Pm ⊢ words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗
      words64At (sp + 0xb00#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14])
    (hm : s1.mem ⊨ Pm ∗ (segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr'
      pqCap' pqPtr' k draws sp H s0 ∗ R)) :
    s1.mem ⊨ cmSlots A sp sess taken otr' pqCap' pqPtr' k (.signalMessage sm) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold segSignalOkFramePlaced at hm1
  have h370_hd :
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14] =
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
        words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          w12, w13, w14] := rfl
  rw [h370_hd] at hm1
  have h580 :
      words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14] ⊢ memRegion (sp + 0x580#64) 120 :=
    words64At_entails_memRegion
      [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
      (sp + 0x580#64) (by simp only [List.length_cons, List.length_nil]; decide)
  have hb00 :
      words64At (sp + 0xb00#64) [w4, w5, w6] ⊢ memRegion (sp + 0xb00#64) 24 :=
    words64At_entails_memRegion [w4, w5, w6] (sp + 0xb00#64)
      (by simp only [List.length_cons, List.length_nil]; decide)
  have hsm_ex :
      words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗ H ⊢
      ∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm :=
    Entails.trans (hpack ((sp + 0x370#64) + 8#64)) (Entails.sepExists_right gm (Entails.refl _))
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.sepExists_right g (Entails.refl _)
  have hm_rearr : s1.mem ⊨
      ((words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        words64At (sp + 0xb00#64) [w4, w5, w6]) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗ memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x508 ∗
      memRegion (sp + 0xb18#64) 0x68 ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hsm_ex (sepConj_mono hrec_ex (sepConj_mono h580 hb00))))
    hm_rearr
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68))) := by
    rw [segSignal_memRegion_cut (sp + 0x46a#64) (sp + 0x580#64) 0x716 0x116 0x600 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x580#64) (sp + 0x5f8#64) 0x600 120 0x588 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  have h3f0 : (sp + 0x370#64) + 0x80#64 = sp + 0x3f0#64 := by bv_omega
  have hm_poll : s1.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68)))) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
      (∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm) ∗
      memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold cmSlots takenSlots apiEncResultAt
  dsimp only
  rw [h3f0]
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm_poll

theorem h45_segSignal_ok_path_placed [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (sm : SignalMessage) (hok : (segSignalRes C S x otr).1 = .ok sm)
    (hs : SegSignalRetStateVPlaced kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx25, hx26, hx28, hpt, hrest, hloc, hnow, hstk, g, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]
    change s0.sp - 0x60#64 = (s0.sp - 0xbe0#64) + 0xb80#64
    bv_omega
  rw [hok] at hm
  obtain ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, hm_unp⟩ :=
    segSignal_placed_ok_unpack A ctl x g sess taken (segSignalRes C S x otr).2 k sm
      (S.draws otr.pqrState x.rest) sp R s0 s hm
  refine SegExitPlaced.of_sepWP hm_unp
    (segSignal_placed_step_ok hs_pc hrun hsp hal hx25 hx26 hx29' hpq) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x19, hs1_x20, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_ok := segSignal_placed_ok_pack A ctl x g sess taken (segSignalRes C S x otr).2 pqCap' pqPtr' k sm gm
    w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
    (S.draws otr.pqrState x.rest) sp H R Pm1 s0 s1 hpack hPm1 hm1
  have hstep5 : EncEncryptStep C S uuidTryParse x sess otr (.signalMessage sm) (segSignalRes C S x otr).2 := by
    unfold EncEncryptStep
    rw [hnone]
    exact ⟨sm, execOk_of_exec_ok hok, rfl⟩
  refine SegExitPlaced.next ⟨.signalMessage sm, (segSignalRes C S x otr).2, pqCap', pqPtr',
    ⟨hcur, hsc, hfrom, hrem, hstep5⟩, ?_⟩
  exact ⟨hs1_pc, ⟨hs1_run, hs1_sp, hal0, hs1_al, hs1_x29.trans hx29, hs1_x19.trans hx19,
      hcrl1, hs1_vregs.trans hvregs⟩, hs1_tr.trans htr,
    ⟨hs1_x20.trans hx20, hs1_x25.trans hx25, hs1_x26.trans hx26, hs1_x28.trans hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm1_ok⟩

set_option maxHeartbeats 800000 in
theorem h45_segSignal_err_path_pf_placed [LibsignalPlacement]
    {F0 : SepProp} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateVPlaced kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s (fun _ => False) := by
  let envF := h45_envF_placed hEnv
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hnp, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr, _hx20, hx25, hx26, hx28,
    _hpt, _hrest, _hloc, _hnow, hstk, g, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hp_pan : p ≠ .panic := by
    rintro rfl
    exact hnp herr
  rw [herr] at hm
  simp only [signalMessageResultAt, errResultAt, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨pqCap', pqPtr', hm⟩ := hm
  have hst : speAt A (utf8 "encrypt") (sp + 0x588#64) p ⊢
      ∃∗ ws : List (BitVec 64), ∃∗ H : SepProp,
        ⌜SpeStaged A x.ret (.protocol p) ws H⌝ ∗ words64At (sp + 0x588#64) ws ∗ H :=
    speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol p) (by intro h; cases h)
  have hm1 := segSignal_apply hst (by sep_focus) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨ws, H, hm1⟩ := hm1
  obtain ⟨hstg, hm1⟩ := segSignal_pure_front hm1
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := segSignal_list_len6 ws hstg.2.1
  have hsplit : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb00#64) 24 ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    rw [show (0x588 : Nat) = 0x508 + (24 + 0x68) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x508 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x508) 24 _ (by decide)]
  have hm2 := segSignal_apply (Entails.of_eq_explicit hsplit) (by sep_focus) hm1
  have hm2' : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗ _ :=
    segSignal_apply (Entails.refl _) (by sep_focus) hm2
  obtain ⟨vs, hvs, hm3⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm2'
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3_placed vs hvs
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, hsp0]
    bv_omega
  have hm4 := segSignal_focusR (T := ((sp + 0x580#64) ↦₆₄ errTag) ∗
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗ words64At (sp + 0xb00#64) [v0, v1, v2])
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm3
  refine SegExitPlaced.of_sepWP hm4 (segSignal_placed_step_err hs_pc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 _hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  have hs3_al : s3.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm6 := Satisfies.mono (sepConj_mono_left hPm3) hm5
  rw [← sepConj_assoc] at hm6
  have hm7 := segSignal_apply (segSignal_err_tail_ent A sp g sess taken k pqCap' pqPtr' (segSignalRes C S x otr).2
    w0 w1 w2 w3 w4 w5) (by sep_focus) hm6
  have hmod := segSignal_model_err (C := C) (S := S) (x := x) hcur hnone hfrom hrem
    (execOk_of_exec_error herr)
  have hdraws := (segSignal_sendState (S := S) (x := x) (c := .newOrUnchanged) hcur hnone hfrom hrem).2
  have hstf : kit.storeFinal st0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = st0 := by
    rw [hmod]; rfl
  have histf : ikit.idFinal ist0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = ist0 := by
    rw [hmod]; rfl
  rw [← h45_segExit_kitF_placed]
  refine tailSignalEncryptErr_placed_ok envF x R0 s0 s3
    (okAnswers r .newOrUnchanged) (.protocol p)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) g (takenRecord sess taken)
    (some (pqCap', pqPtr', (segSignalRes C S x otr).2)) ?_ hstg ?_
  · rw [h45_tailModel_kitF_placed]
    refine ⟨⟨by rw [hmod, segSignal_ofProtocol hp_pan], by rw [hmod]; exact ⟨hsc.2, trivial⟩,
      by rw [hmod]; trivial⟩, ?_⟩
    rw [hs3_tr, htr, hmod, ikit.traceOfWith_load]; rfl
  · rw [h45_encTailV_kitF_placed]
    refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19,
      hcrl3, hs3_vregs.trans hvregs⟩, ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstk, ?_⟩
    rw [hdraws, hstf, histf]
    dsimp only
    rw [← hsp0]
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm7

theorem h45_segSignal_placed_okVT [LibsignalPlacement]
    {F0 : SepProp} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R_frame : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hpk : sess.pendingPreKey = none)
    (hs : KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
      (F0 ∗ R_frame) s0 s) :
    h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R_frame s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' (F0 ∗ R_frame) s0 s') := by
  refine h45_segExitVT_trans_placed
    (h45_segExitVT_of_segExit_placed (h45_segSignal_to_ack_placed hEnv x r sess otr taken pqCap pqPtr k
      (F0 ∗ R_frame) s0 s hpk hs))
    fun sm h =>
      h45_segExitVT_trans_placed
        (h45_segExitVT_of_segExit_placed (h45_segSignal_ack_to_enc_placed hEnv x r sess otr taken pqCap pqPtr k
          (F0 ∗ R_frame) s0 sm h))
        fun sn h' =>
          h45_segExitVT_trans_placed
            (h45_segSignal_enc_to_ret_pf_placed hEnv x r sess otr taken pqCap pqPtr k R_frame s0 sn h64 h')
            fun sr hret => ?_
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact h45_segExitVT_of_false_placed
      (h45_segExitVT_of_segExit_placed (h45_segSignal_err_path_pf_placed hEnv x r sess otr taken k
        (F0 ∗ R_frame) s0 sr p hres hret))
  · exact h45_segExitVT_of_segExit_placed
      (h45_segSignal_ok_path_placed hEnv x r sess otr taken k (F0 ∗ R_frame) s0 sr m hres hret)

end SegSignal

section SegPreKeyPrefix

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_unackItems_to_dur_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        StalenessDurStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hkey with ⟨hcur, hscope, hotr, hrem, hpc, hmeta, htr, hregs, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hregs with ⟨hx0, hx8, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  rw [sp_sub_60_eq_add_b80 s0.sp] at hx29
  set sp := s0.sp - 0xbe0#64
  unfold keyPCPlaced encEntryPlaced at hpc
  have hunack := hEnv.callees.unack
  clear hEnv
  apply segExitPlaced_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 0x6c4#64)
    (encSeam_mem_group hmem)
  dsimp only [takenSlots, encCommonPlaced]
  rw [poll_unackItems_regions sp, encSubStack_split_unack hsp]
  refine SepWPp.fold (takenRecord_sessionRecordAt_unpack A sp sess taken) (by sep_focus) ?_
  refine sepWPp_elim_ex fun prevCap => sepWPp_elim_ex fun prevPtr => sepWPp_elim_ex fun G => ?_
  dsimp only [lsProg_464, ite_true] at hunack ⊢
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsmpl.base 36)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine SepWPp.call_frame_rocl hunack
    (x := (⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ : UnackCall))
    (by wp_norm_goal) (by wp_norm_goal) hspAl
    (show _ = (blkPl_464).base + 0x348#64 by rfl)
    hcrl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      exact onPanic_of_unack_placed htr hcur hscope hotr hrem hpk hm)
    fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
  dsimp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (unackOutAt_taken_some sp G.kyber sess items hpk) (by sep_focus) ?_
  refine sepWPp_elim_ex fun ts => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hts => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack32 (sp + 0x580#64) items.preKeyId) (by sep_focus)
    fun pkVal hpkVal => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack64 (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)))
    (by sep_focus) fun kyIdVal hkyIdVal => ?_
  refine sepWPp_fold_ex5 (baseKeyShift_unpack_59c sp items.baseKey) (by sep_focus)
    fun bk0 bk1 bk2 bk3 bk4 hbk => ?_
  refine sepWPp_fold_ex2 (unackKyberSliceAt_unpack (sp + 0x5c0#64) G.kyber) (by sep_focus)
    fun kyPtr kyLen hkySlice => ?_
  refine SepWPp.fold (curScratch_unackItems_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun s48 => sepWPp_elim_ex fun s40 => sepWPp_elim_ex fun s38 =>
    sepWPp_elim_ex fun s34 => sepWPp_elim_ex fun s28 => sepWPp_elim_ex fun s24 =>
    sepWPp_elim_ex fun s18 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0x870#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w890 => sepWPp_elim_ex fun w888 => sepWPp_elim_ex fun w880 =>
    sepWPp_elim_ex fun w878 => sepWPp_elim_ex fun w870 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0xab0#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wad0 => sepWPp_elim_ex fun wac8 => sepWPp_elim_ex fun wac0 =>
    sepWPp_elim_ex fun wab8 => sepWPp_elim_ex fun wab0 => ?_
  refine SepWPp.fold (memRegion_16_ts_unpack_b00 sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wb08 => sepWPp_elim_ex fun wb00 => ?_
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (baseKeyShift_pack_ab0 sp items.baseKey bk0 bk1 bk2 bk3 bk4 hbk) (by sep_focus) ?_
  refine SepWP.fold (cells36_entails_memRegion_36_870 sp bk0 bk1 bk2 bk3 bk4) (by sep_focus) ?_
  refine SepWP.fold
    (unackOut_cells_entails_memRegion_88_580 sp _ pkVal _ ts.tvSec ts.tvNsec bk0 bk1 bk2 bk3 bk4 kyPtr kyLen items.signedPreKeyId)
    (by sep_focus) ?_
  refine SepWP.fold (poll_unackItems_pack_pollWithBaseKey_trap sp items ts) (by sep_focus) ?_
  refine sepWP_fold_preKeyScratch sp kyLen _ items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey
    (by sep_focus) (by rfl) ?_
  refine SepWP.fold (encSubStack_pack_unack hsp _ _) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_f hmf
  dsimp only [StalenessDurStatePlaced, encEntryPlaced, sp]
    at hsp1 hx19_1 hx20_1 hx22_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
  refine ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen,
    hts, hpkVal, hkyIdVal, hkySlice, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · wp_norm_goal
  · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
      by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
      by wp_norm_goal, hcrl_f, by wp_norm_goal⟩
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · cases items.preKeyId <;> wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · dsimp only [encCommonPlaced, encSpillsAtV] at hmf ⊢; arm64_sep_close

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_staleness_to_add_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : StalenessDurStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => ∃ expiry,
        StalenessAddStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  let envF := h45_envF_placed hEnv
  rcases hdur with ⟨hts, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx2, hx8, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hts_nsec : ts.tvNsec.toNat < 10 ^ 9 := (unixEpoch_checkedAddSecs_tvNsec hts).2
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hdur_call := subroutine_ok_merge_withLsRet (fun _ _ => rfl) (durationSince_placed_ok_at_enc envF)
  have hadd_call := subroutine_ok_merge_withLsRet (fun _ _ => rfl) (timeAdd_placed_ok_at_enc envF)
  clear envF hEnv
  apply segExitPlaced_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 0x6fc#64)
    (dur_mem_group hmem)
  dsimp only [encCommonPlaced]
  rw [pollWithBaseKey_dur_unpack_trap sp items ts, encSubStack_split_ext hsp]
  refine SepWPp.fold (durationSinceBounded_b00_intro_trap sp ts.tvSec ts.tvNsec hts_nsec) (by sep_focus) ?_
  dsimp only [lsProg_464, ite_true] at hdur_call hadd_call ⊢
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsρ lsDurationSinceSym)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.call_frame hdur_call
    (x := (sp + 0xb00#64, sp + 0x580#64))
    (by wp_norm_goal) (by wp_norm_goal) hspAl
    (show _ = (blkPl_464).base + 0x6c8#64 by rfl)
    rfl
    ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 464 1736#64 rfl,
      by simp_all, by simp_all, by dsimp [State.setPC, State.writeReg64, State.readReg64, Reg.x2] at hx2 ⊢; rw [hx2]; decide⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ hm => by
      dsimp only [durationSinceBoundedSpec, Spec.onPanic] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [durationSinceBoundedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  have hx21_1' : (s1.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s1.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_1]; exact hx21
  have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (dur_ret_24_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  refine SepWPp.fold (memRegion_8_898_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w898 => ?_
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsρ lsTimeAddSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.call_frame hadd_call
    (x := (ts, maxUnacknowledgedSessionAge))
    (by wp_norm_goal) (by wp_norm_goal)
    (by unfold State.spAligned at hsp1_al ⊢; rw [hsp1] at hsp1_al; wp_norm_goal)
    (show _ = (blkPl_464).base + 0x6fc#64 by wp_norm_goal)
    rfl
    ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 464 1788#64 (by wp_norm_goal),
      by wp_norm_goal, by wp_norm_goal, hts_nsec, by wp_norm_goal, by wp_norm_goal⟩
    (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      refine onPanic_of_timeAdd_placed (s := _) ?_ hcur hscope hotr hrem hpk hts hm
      wp_norm_goal)
    fun s2 hpc2 hstat2 hsp2 hcs2 => ?_
  dsimp only [timeAddSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hexp, htr2⟩ => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp2) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2 hsp2 htr2
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
  rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx28_1] at hx28_2; rw [hx29_1] at hx29_2; rw [hvregs_1] at hvregs_2
  have hx21_2' : (s2.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s2.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_2]; exact hx21_1'
  have hx24_2' : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s2.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_2]; exact hx24_1'
  rw [hsp1] at hsp2
  rw [htr1] at htr2
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
  refine SepWP.fold (pollWithBaseKey_dur_pack sp items w580 w588 _) (by sep_focus) ?_
  have hsp2_pack :
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt s2.sp extHookStack) ⊢ stackAt sp encSubStack := by
    rw [hsp2, ← encSubStack_split_ext rfl]
    exact Entails.refl _
  refine SepWP.fold hsp2_pack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_f hmf
  dsimp only [StalenessAddStatePlaced, encEntryPlaced, sp]
    at hsp2 hx19_2 hx20_2 hx22_2 hx25_2 hx26_2 hx28_2 hx29_2 hvregs_2 hmf ⊢
  refine ⟨⟨s2.readReg64 .x0, (s2.readReg64 .x1).setWidth 32⟩,
    hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc2, ?_, htr2, rfl, rfl,
    hx20_2, hx21_2', hx22_2, hx23_2, hx24_2', hx25_2, hx26_2, hx27_2, hx28_2,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · refine ⟨hstat2, hsp2, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; rw [hsp2]; wp_norm_goal,
      hx29_2, hx19_2, hcrl_f, hvregs_2⟩
  · dsimp only [encCommonPlaced] at hmf ⊢; arm64_sep_close

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_stale_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = true)
    (hadd : StalenessAddStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  let envF := h45_envF_placed hEnv
  rcases hadd with ⟨hts, hexp, _hpkVal, _hkyIdVal, _hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, _hx23, _hx24, hx25, hx26, _hx27, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have ⟨hmod, hdraws⟩ := model_of_stale (C := C) (S := S) (x := x)
    hcur hotr hrem hpk hts hexp hlt
  set sp := s0.sp - 0xbe0#64
  apply segExitPlaced_trans
    (mid := fun sf =>
      ∃ cap ptr devWord,
        devWord.setWidth 8 = x.rem.device ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
        EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r)
          (encEntryPlaced + 0x46c#64)
          (tailRegs cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length))
          (fun sp => dropRecordSlots A sp curScratch ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
            (some (pqCap, pqPtr, otr)) none
            (pollWith sp 0x9d0 [devWord, lsmpl.ρ lsMessageEncryptRodataSym, 15#64]) ∗
            (vecU8Body A cap ptr x.rem.name.bytes ∗
              ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt")))
          R s0 sf)
  · unfold encEntryPlaced at hpc
    have hclone_call := stringClone_placed_ok_at_enc envF
    apply segExitPlaced_of_sepWPp_lscro hcrl
      (target := (blkPl_464).base + 0x46c#64)
      (dur_mem_group hmem)
    refine rodata_message_encrypt_placed_sepWPp hcrl.2 ?_
    refine SepWPp.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
      (by sep_focus) ?_
    refine SepWPp.fold (pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64))
      (by sep_focus) ?_
    refine SepWPp.fold (cmSlotAt_none_pack A sp k) (by sep_focus) ?_
    refine SepWPp.fold
      (preKeyScratch_stale_weaken sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
      (by sep_focus) ?_
    refine SepWPp.fold (pollWithBaseKey_stale_weaken sp items) (by sep_focus) ?_
    dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, protocolAddressAt, lsLogOff_eq]
    rw [poll_stale_split sp, encSubStack_split_ext hsp]
    refine SepWPp.fold (memRegion_16_unpack_598 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w5a0 => sepWPp_elim_ex fun w598 => ?_
    refine SepWPp.fold (memRegion_24_unpack_9d0 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w9e0 => sepWPp_elim_ex fun w9d8 => sepWPp_elim_ex fun w9d0 => ?_
    dsimp only [lsProg_464, ite_true] at hclone_call ⊢
    apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 623)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcrl_call
    refine SepWPp.call_frame_rocl hclone_call
      (x := (x.remA, sp + 1408#64, x.rem.name))
      (by wp_norm_goal) (by wp_norm_goal) hspAl
      (show _ = (blkPl_464).base + 0x79c#64 by wp_norm_goal)
      hcrl_call
      rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
      (by dsimp only [State.sp, State.setPC, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun sf _ hm => by
        rw [sepConj_assoc] at hm
        refine onPanic_of_alloc_placed (s := _) ?_ hm
        change s0.trace <+: s.trace
        rw [htr]
        exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
      fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
    dsimp only [stringCloneSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm]
      at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
    rw [hx19] at hx19_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned at hspAl ⊢; rwa [hsp1]
    rw [hsp] at hsp1
    rw [htr] at htr1
    refine SepWPp.fold (vecU8_580_unpack A sp x.rem.name.bytes) (by sep_focus) ?_
    refine sepWPp_elim_ex fun ptr => sepWPp_elim_ex fun cap => ?_
    apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold (curScratch_stale_pack sp) (by sep_focus) ?_
    refine SepWP.fold (pollWith_9d0_pack sp cap ptr _ _ _ _ _ _) (by sep_focus) ?_
    have hsp1_pack :
        (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt s1.sp extHookStack) ⊢ stackAt sp encSubStack := by
      rw [hsp1, ← encSubStack_split_ext rfl]
      exact Entails.refl _
    refine SepWP.fold hsp1_pack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1 hmf
    have hfinal :
        kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    have hidfinal :
        ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    dsimp only [EncTailVPlaced, Pf.TailCommon.EncTailVPlaced, encEntryPlaced, encStoreExtraPlaced,
      tailRegs, dropRecordSlots, otrSlotAt, encSpillsAt, encSpillsAtV, encCommonPlaced,
      protocolAddressAt, lsLogOff_eq, sp]
      at hsp1 hx19_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
    refine ⟨cap, ptr, (w598 &&& 0xffffffffffffff00#64) ||| BitVec.zeroExtend 64 x.rem.device,
      by ext i hi; simp, by wp_norm_goal, ?_, ?_, ?_, hstack, ?_⟩
    · wp_norm_goal
    · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al, hsp1_al,
        by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
        by wp_norm_goal, hcrl1, by wp_norm_goal⟩
    · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · rw [hdraws, hfinal, hidfinal]
      arm64_sep_close
  · intro sf ⟨cap, ptr, devWord, hdev, htr_sf, htail⟩
    have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf := by
      refine ⟨⟨congrArg Prod.fst hmod, by rw [congrArg Prod.snd hmod]; exact ⟨hscope.2, trivial⟩,
        by rw [congrArg Prod.snd hmod]; trivial⟩, ?_⟩
      rw [congrArg Prod.snd hmod, htr_sf, ikit.traceOfWith_load]
      rfl
    have h15 : 15#64 = BitVec.ofNat 64 (utf8 "message_encrypt").length := by rfl_kernel
    have hst : SpeStaged A x.ret (.sessionNotFound x.rem.val "message_encrypt")
        [cap, ptr, BitVec.ofNat 64 x.rem.name.bytes.length, devWord,
          lsmpl.ρ lsMessageEncryptRodataSym, 15#64]
        (vecU8Body A cap ptr x.rem.name.bytes ∗
          ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt")) :=
      speStaged_sessionNotFound A x.ret x.rem.val "message_encrypt"
        cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
        (lsmpl.ρ lsMessageEncryptRodataSym) 15#64
        rfl hdev h15
    rw [← h45_segExit_kitF_placed]
    exact tailDropRecord_placed_ok envF x R s0 sf (preKeyErrAnswers r)
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
      (lsmpl.ρ lsMessageEncryptRodataSym) 15#64
      (vecU8Body A cap ptr x.rem.name.bytes ∗
        ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt"))
      curScratch (Or.inl rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
      (some (pqCap, pqPtr, otr))
      ((h45_tailModel_kitF_placed kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf).mpr hm)
      hst
      ((h45_encTailV_kitF_placed kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r) _ _ _ R s0 sf).mpr htail)

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_regId_kyber_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hlt : expiry.lt x.now = false)
    (hadd : StalenessAddStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (PreKeyEncryptStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0) := by
  rcases hadd with ⟨hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hky_bound := (hEnv.scopeIn r hscope sess hcur).2.2.2
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hkyber_call := hEnv.callees.kyber
  clear hEnv
  apply segExitPlaced_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 2228#64)
    (dur_mem_group hmem)
  refine SepWPp.fold (sessionAt_regId_unpack A sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq]
  rw [encSubStack_split_kyber hsp]
  dsimp only [lsProg_464, ite_true] at hkyber_call ⊢
  cases hky : sess.pendingKyberPreKey with
  | none =>
    cases hGky : G.kyber with
    | some g =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | none =>
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      subst hkySlice
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      refine SepWPp.call_frame_rocl hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine onPanic_of_alloc_placed (s := _) ?_ hm
          change s0.trace <+: s.trace
          rw [htr]
          exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold (kyberPost_unpack A (sp + 0x8a0#64) (sp + 0x580#64) 0#64 none) (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_none_to_memRegion sp) (by sep_focus) ?_
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      rw [← hGky]
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp kyLen _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold (pollPreKeyEncrypt_pack A sp bp items sess.pendingKyberPreKey none (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      dsimp only [PreKeyEncryptStatePlaced, PreKeyEncryptState'Placed, preKeyEncryptScratch,
        preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced, encEntryPlaced,
        encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close
  | some ky =>
    cases hGky : G.kyber with
    | none =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | some g =>
      rw [hGky, hky] at hkyRel
      dsimp only [KyberRel] at hkyRel
      rcases hkyRel with ⟨hkyBytes, _⟩
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      rcases hkySlice with ⟨rfl, rfl⟩
      have hkyId_eq : kyIdVal = ky.preKeyId := hkyIdVal ky.preKeyId (by simp [hky])
      subst hkyId_eq
      have hct_lt : ky.ciphertext.length < 2 ^ 32 := hky_bound ky hky
      rw [hkyBytes]
      refine SepWPp.fold (optTailVecAt_borrow A (sp + 0x250#64) g) (by sep_focus) ?_
      rw [sepConj_assoc, sepConj_assoc]
      refine SepWPp.pure_elim fun hptr => ?_
      rw [hkyBytes]
      dsimp only [Option.map, Option.isSome]
      have hptr_beq : (g.vec.ptr == 0#64) = false := _root_.beq_false_of_ne hptr
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      refine SepWPp.call_frame_rocl hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, g.vec.ptr,
          some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine onPanic_of_alloc_placed (s := _) ?_ hm
          change s0.trace <+: s.trace
          rw [htr]
          exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold
        (kyberPost_unpack A (sp + 0x8a0#64) (sp + 0x580#64) g.vec.ptr
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)))
        (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_some_unpack sp g.vec.ptr ky) (by sep_focus) ?_
      rw [← hkyBytes]
      refine SepWPp.fold (optTailVecAt_unborrow A (sp + 0x250#64) g) (by sep_focus) ?_
      rw [hkyBytes, ← hGky]
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp _ _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold
        (pollPreKeyEncrypt_pack A sp bp items sess.pendingKyberPreKey
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)) (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      dsimp only [PreKeyEncryptStatePlaced, PreKeyEncryptState'Placed, preKeyEncryptScratch,
        preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced, encEntryPlaced,
        encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close

end SegPreKeyPrefix

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
