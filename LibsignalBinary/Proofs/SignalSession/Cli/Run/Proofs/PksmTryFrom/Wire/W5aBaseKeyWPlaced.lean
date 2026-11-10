/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` `base_key` Deserialization (`+0x5b4 → +0x684` / `+0x7a8`)

Proves the `[LibsignalPlacement]` `PublicKey::deserialize(base_key)` call, `Ok` branch to
`+0x684`, `Err` branch to `+0x7a8`, and deallocation-slot bridge on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev call_noPanic_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_noPanic_pk

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## 1. (`+0x5b4 .. +0x5dc`, `+0x700 .. +0x714`, `+0x790 .. +0x7a8`): `PublicKey::deserialize(baseKey)` -/

theorem post_deser_bk_call_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (bk : List (BitVec 8))
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1472#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff)
      (fun sf Pf =>
        PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
          memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallDeser := hC.deserializeFull
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Buf_entails_slice_rest A bkCap bkPtr bk))))) ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre (P' :=
      ⌜bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0⌝ ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ (bkPtr ↦ₛ bk) ∗ vecU8BufRest A bkCap bkPtr bk ∗ lsLogOff))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun ⟨hbk_le, hbk_lt, _⟩ => ?_
  have hbk_len_lt : bk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hbk_le hbk_lt
  have hbk_toNat : (BitVec.ofNat 64 bk.length).toNat = bk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 201) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have h48_split := post_memRegion48_split33_15 sp'
  have hlog : lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (bkPtr, bk, sp' + 312#64) hcallDeser
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 1472#64) (by simp [arm64_norm])
    (T := (bkPtr ↦ₛ bk) ∗ memRegion (sp' + 312#64) 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64))
    (φ := bkPtr = bkPtr ∧ (BitVec.ofNat 64 bk.length).toNat = bk.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ bk.length < 2 ^ 63)
    (by simp [deserializeFullPlacedSpec, arm64_norm]) ⟨rfl, hbk_toNat, rfl, hbk_len_lt⟩
    (by rw [h48_split, hlog]; sep_focus) ?_
  clear hcallDeser
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [deserializeFullPlacedSpec]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  have hrepack := slice_rest_entails_vecU8Buf A bkCap bkPtr bk
  rw [← hlog]
  refine Entails.trans (Q :=
      ((bkPtr ↦ₛ bk) ∗ vecU8BufRest A bkCap bkPtr bk) ∗
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
        memRegion (sp' + 345#64) 15 ∗ lsLogOff))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Entails.trans (sepConj_mono_left hrepack) (by apply entails_of_eq; ac_rfl)

theorem post_deser_bk_ok_to_684_placed_wpW [LibsignalPlacement]
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hdeser : PublicKey.deserialize bk = .ok pk)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1668#64) s
      (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hec : ecKeyParses bk = true := ecKeyParses_of_deserialize_ok hdeser
  have hpkOf : pkOf bk = pk := pkOf_of_deserialize_ok hdeser
  have hbytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1 := pkOf_bytes_of_ecKeyParses hec
  have hpk_bytes : pk.bytes.toList = (bk.take 33).drop 1 := by rw [← hpkOf, hbytes]
  rw [hdeser]; dsimp only [deserializeResult33At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩, hec, hpkOf, hbytes,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, ?_⟩
  rw [hpk_bytes]; exact Entails.refl _

theorem post_deser_bk_err_to_7a8_placed_wpE [LibsignalPlacement]
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1960#64) s
      (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  rw [herr]
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]⟩, ?_⟩
    have h33 := memRegion33_of_err_base (sp' + 312#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left h33)
  | badKeyType t =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]⟩, ?_⟩
    have h33 := memRegion33_of_err_badKeyType (sp' + 312#64) t
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left h33)
  | badKeyLength n =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]; bv_bits⟩, ?_⟩
    have h33 := memRegion33_of_err_badKeyLength (sp' + 312#64) n
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left h33)
  | _ =>
    dsimp only [deserializeResult33At]
    exact SepWPp.pure_pre fun hfalse => False.elim hfalse

theorem post_deser_bk_ok_full_to_684_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hdeser : PublicKey.deserialize bk = .ok pk)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1668#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff)
      (fun sf Pf =>
        BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff))
      (tryFromQp s0) := by
  refine SepWPp.bind (post_deser_bk_call_placed_wpW hC bk hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  let restF := ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff
  refine SepWPp.mono_pre (P' := (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
      memRegion (sp' + 345#64) 15) ∗ restF)
    (Entails.trans hent1 (by dsimp only [restF]; apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_ok_to_684_placed_wpW hdeser hst1 hpc1 hrun1)
    fun sf Pf ⟨hbst, hent2⟩ => ⟨hbst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent2) ?_
  dsimp only [restF]; apply entails_of_eq; ac_rfl

theorem post_deser_bk_err_full_to_7a8_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1960#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff)
      (fun sf Pf =>
        DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff))
      (tryFromQp s0) := by
  refine SepWPp.bind (post_deser_bk_call_placed_wpW hC bk hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  let restF := ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff
  refine SepWPp.mono_pre (P' := (deserializeResult33At (sp' + 312#64) (PublicKey.deserialize bk) ∗
      memRegion (sp' + 345#64) 15) ∗ restF)
    (Entails.trans hent1 (by dsimp only [restF]; apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_err_to_7a8_placed_wpE herr hst1 hpc1 hrun1)
    fun sf Pf ⟨hdst, hent2⟩ => ⟨hdst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent2) ?_
  dsimp only [restF]; apply entails_of_eq; ac_rfl

/-! ## 2. Dealloc-Slot Bridge (`*_placed_wpE`) -/

private theorem w5a_pl_vec_ne_noneCap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ⌜cap ≠ noneCap⌝ ∗ Wire.vecU8Buf A cap ptr bs := by
  refine Entails.trans (vecU8Buf_entails_slice_rest A cap ptr bs)
    (Entails.pure_left fun ⟨_hle, hlt, _hptr⟩ => ?_)
  have hne : cap ≠ noneCap := by rintro rfl; revert hlt; decide
  rw [pure_true_emp hne, emp_sepConj]
  exact slice_rest_entails_vecU8Buf A cap ptr bs

private theorem w5a_pl_vec_entails_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans ?_
    (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

private theorem w5a_pl_vec_ne_and_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜cap ≠ noneCap⌝ ∗ ∃∗ active : Bool, deallocSlot A cap ptr active :=
  Entails.trans (w5a_pl_vec_ne_noneCap A cap ptr bs)
    (sepConj_mono_right (w5a_pl_vec_entails_deallocSlot A cap ptr bs))

theorem post_deser_bk_err_dealloc_to_7a8_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen
      bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {vb : BitVec 8}
    {bk ik msg : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    {e : SignalProtocolError}
    (herr : PublicKey.deserialize bk = .error e)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1960#64) s
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff) ∗
        (memRegion sret 248 ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (∃ x8v x9v x10v : BitVec 64,
          sf.readReg64 .x8 = x8v ∧ sf.readReg64 .x9 = x9v ∧ sf.readReg64 .x10 = x10v ∧
          speWordsOf e x9v x8v x10v) ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          memRegion sret 248 ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ lsLogOff))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w5a_pl_vec_ne_noneCap A bkCap bkPtr bk)))))
      (sepConj_mono_right
        (sepConj_mono (w5a_pl_vec_ne_and_deallocSlot A msgCap msgPtr msg)
          (sepConj_mono_right (sepConj_mono_left (w5a_pl_vec_ne_and_deallocSlot A ikCap ikPtr ik)))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff) ∗
        (memRegion sret 248 ∗
          (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hmsg_ne =>
    SepWPp.pure_pre fun hik_ne =>
    SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_deser_bk_err_full_to_7a8_placed_wpE hC herr hst hpc hrun)
    fun sf Pf ⟨hdstE, hent⟩ =>
      ⟨hdstE, ⟨_, _, _, rfl, rfl, rfl, hdstE.2⟩, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w5a_pl_vec_entails_deallocSlot A bkCap bkPtr bk))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hky)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
