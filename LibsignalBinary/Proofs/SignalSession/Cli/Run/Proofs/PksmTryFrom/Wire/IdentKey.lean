/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6States
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6Exits
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Specifications.AsmConstants

/-!
# `PreKeySignalMessage::try_from`: `IdentityKey::try_from` Stage (`+0x830 → +0x864 / +0x978`)

Symbolic execution of the `IdentityKey::try_from` stage from `+0x830`, computing
`registration_id.unwrap_or_default()` in `w27` and branching to `IdentOkState` (`+0x864`) on
`.ok ipk` or `IdentErrState` (`+0x978`) with exact `speAt` error payload on `.error e`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost hiding memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private gen_decodes libsignalSessionCode_tree ikDec [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2096) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2152)]

local macro "ik_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.ikDec $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `registration_id.unwrap_or_default()` as computed by
`ldr w8, [sp, #0x30]; ldr w9, [sp, #0x34]; tst w8, #1; csel w27, w9, wzr, ne`. -/
def identRegId (regTag regVal : BitVec 32) : BitVec 32 :=
  if regTag &&& 1#32 = 0#32 then 0#32 else regVal

theorem identRegId_of_optU32 (regTag regVal : BitVec 32) (o : Option (BitVec 32))
    (h : if o.isSome then regTag = 1#32 ∧ some regVal = o else regTag = 0#32) :
    identRegId regTag regVal = o.getD 0#32 := by
  cases o with
  | none => subst h; rfl
  | some v => rcases h with ⟨rfl, hv⟩; cases hv; rfl

private theorem identRegId_tst (regTag : BitVec 32) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) =
      (regTag &&& 1#32 == 0#32) := by
  apply congrArg (· == 0#32)
  bv_bits

private theorem identRegId_csel (regTag regVal : BitVec 32) :
    (if ¬(BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) = true then
        BitVec.truncate 64 regVal else 0#64) = (identRegId regTag regVal).zeroExtend 64 := by
  rw [identRegId_tst]
  unfold identRegId
  by_cases h : regTag &&& 1#32 = 0#32 <;> simp [h]

/-- The untouched tail `out + 16 .. 40` of the `IdentityKey::try_from` result as words
(`ldur q0, [x24, #8]; ldur q1, [x24, #0x18]` read `sp' + 320 .. 352`). -/
theorem memRegion24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion32_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

private theorem ik_words3_to_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion24_words3 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (Entails.sepExists_intro w2))

set_option maxHeartbeats 1200000 in
/-- (``+0x830 → +0x864`, `2096 → 2148``): from the `KyberOkState` registers at `+0x830`,
loads the `identity_key` slice (`ptr @ sp' + 104`, `len @ sp' + 56`), computes
`w27 = registration_id.unwrap_or_default()`, calls `IdentityKey::try_from` into `sp' + 312`,
copies the 32 key bytes to `sp' + 144`, and (`PublicKey.deserialize ik = .ok ipk`) falls through
`b.ne +0x978` to `IdentOkState` at `+0x864`. -/
theorem preKey_ident_ok_830_to_864_wpX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hIdentOk : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceOkSpec img))
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap ikPtr ikLen : BitVec 64}
    {vb : BitVec 8} {regTag regVal : BitVec 32}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey} {S : Nat}
    (hS : 96 ≤ S) (hS64 : S ≤ 2 ^ 64)
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hik : PublicKey.deserialize ik = .ok ipk) (hik_len : ikLen.toNat = ik.length)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2096#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hx25 : s.readReg64 .x25 = kyberBoxLen)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2148#64) s
      (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
        memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
        logOff img ∗ stackAt sp' S)
      (fun sf Pf =>
        IdentOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
          (identRegId regTag regVal) bk pk ik ipk sf ∧
        (Pf ⊢ ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
          ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
          ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
          memRegion (sp' + 352#64) 8 ∗
          logOff img ∗ stackAt sp' S))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallIk : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName))
      (identityKeyTryFromSliceOkSpec img) := by
    rw [fnAddr_sub_rel
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
      (by decide)]
    exact hIdentOk
  clear hIdentOk
  let H := Rust.withPanics ext
  ik_prekey_fetches img.base H 2096 56
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallIk hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstackIk := stackAt_sub_split sp' 96 S (by omega) hS64
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48_split]
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom (ikPtr, ik, ipk, sp' + 312#64)
    (subroutine_ok_inImage_of_subroutine_ok img hcallIk)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 2124#64) (by simp [arm64_norm])
    (T := (ikPtr ↦ₛ ik) ∗ memRegion (sp' + 312#64) 40 ∗ logOff img ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ ikLen.toNat = ik.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize ik = .ok ipk)
    (by simp [identityKeyTryFromSliceOkSpec, hsp_eq, arm64_norm])
    ⟨rfl, hik_len, rfl, hik⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [identityKeyTryFromSliceOkSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  obtain ⟨ik0, ik1, ik2, ik3, -, hipk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ipk.bytes)
  rw [memRegion32_words4 (sp' + 144#64), hipk]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => ?_
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
  have h27_2 : s2.readReg64 .x27 = (identRegId regTag regVal).zeroExtend 64 := by
    rw [← identRegId_csel]
    simp [hx27_2, arm64_norm]
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik,
    by simp [h29_2, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [h27_2, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [h24_2, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  rw [← hsp2, hsp2_eq, hipk (sp' + 144#64), hipk (sp' + 320#64), hstackIk]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; ac_rfl

/-- For any `PublicKey.deserialize ik = .error e`, the 5 words left at `sp' + 312 .. 352` plus the
untouched 8-byte region `sp' + 352 .. 360` pack into `speAt A fn (sp' + 312#64) e`. -/
private theorem ik_errWords5_memRegion8_entails_speAt (A : RustAlloc) (fn : List (BitVec 8))
    {ik : List (BitVec 8)} {e : SignalProtocolError} (hik : PublicKey.deserialize ik = .error e)
    (sp' w2 w3 w4 : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
      memRegion (sp' + 352#64) 8 ⊢
      speAt A fn (sp' + 312#64) e := by
  have hm24 := ik_words3_to_memRegion24 (sp' + 328#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hm32 :
      ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8 ⊢
      memRegion (sp' + 328#64) 32 := by
    rw [show (32 : Nat) = 24 + 8 by decide,
      ProofLib.memRegion_split (sp' + 328#64) 24 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    exact sepConj_mono_left (by simpa only [sepConj_assoc] using hm24)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    ikErrWords_entails_speAt hik A fn (sp' + 312#64)

/-- Companion unpacker for `ErrTailC.e_978_wpE`: under `PublicKey.deserialize ik = .error e`,
`speAt A fn (sp' + 312#64) e` splits back into `memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8`
(since all `PublicKey::deserialize` error variants carry plain trailing bytes at `+16..+48`). -/
theorem speAt_deserialize_err_split_312 {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError} (hik : PublicKey.deserialize ik = .error e)
    (sp' : BitVec 64) :
    speAt A fn (sp' + 312#64) e ⊢
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
  have h16_40 : ∀ a : BitVec 64,
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 ⊢
        memRegion a 40 ∗ memRegion (a + 40#64) 8 := by
    intro a
    rw [show (32 : Nat) = 24 + 8 by decide,
      ProofLib.memRegion_split (a + 16#64) 24 8 (by decide),
      show (40 : Nat) = 8 + (8 + 24) by decide,
      ProofLib.memRegion_split a 8 (8 + 24) (by decide),
      ProofLib.memRegion_split (a + 8#64) 8 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · unfold speAt
    rw [show (40 : Nat) = 8 + 32 by decide,
      ProofLib.memRegion_split (sp' + 312#64 + 8#64) 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
      (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h16_40 (sp' + 312#64))
  · unfold speAt
    rw [show (39 : Nat) = 7 + 32 by decide,
      ProofLib.memRegion_split (sp' + 312#64 + asm64% (spePayloadOff + 1)) 7 32 (by decide)]
    have hb8 : ((sp' + 320#64) ↦₈ t) ∗ memRegion (sp' + 321#64) 7 ⊢ memRegion (sp' + 320#64) 8 := by
      rw [show (8 : Nat) = 1 + 7 by decide,
        ProofLib.memRegion_split (sp' + 320#64) 1 7 (by decide), ProofLib.memRegion_one]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (Entails.sepExists_intro t)
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm) (sepConj_mono_left hb8))) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h16_40 (sp' + 312#64)
  · unfold speAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _))) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h16_40 (sp' + 312#64)

set_option maxHeartbeats 1200000 in
/-- (``+0x830 → +0x978`, `2096 → 2424``): `PublicKey.deserialize ik = .error e`
writes `(ikErrWords e)` at `sp' + 312`, loads `x8 := (ikErrWords e).1`, copies `sp' + 320 .. 352`
into `sp' + 144 .. 176`, and takes `b.ne +0x978` into `IdentErrState`, keeping exact
`speAt A fn (sp' + 312#64) e` at the callee result slot together with `sf.readReg64 .x8` and the
hoisted word `(ikErrWords e).2` at `sp' + 144`. -/
theorem preKey_ident_err_830_to_978_wpE {img : Obj.Image}
    {ext : String → Option (State → State)}
    (A : RustAlloc) (fn : List (BitVec 8))
    (hIdentWordsErr : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceWordsErrSpec img))
    {s0 s : State}
    {sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap ikPtr ikLen : BitVec 64}
    {regTag regVal : BitVec 32}
    {ik : List (BitVec 8)} {e : SignalProtocolError} {S : Nat}
    (hS : 96 ≤ S) (hS64 : S ≤ 2 ^ 64)
    (hik : PublicKey.deserialize ik = .error e) (hik_len : ikLen.toNat = ik.length)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2096#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hx25 : s.readReg64 .x25 = kyberBoxLen)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2424#64) s
      (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
        memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
        logOff img ∗ stackAt sp' S)
      (fun sf Pf =>
        IdentErrState img s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf ∧
        sf.readReg64 .x8 = (ikErrWords e).1 ∧
        (Pf ⊢ ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
          ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
          speAt A fn (sp' + 312#64) e ∗
          logOff img ∗ stackAt sp' S))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcallIk : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName))
      (identityKeyTryFromSliceWordsErrSpec img) := by
    rw [fnAddr_sub_rel
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
      (by decide)]
    exact hIdentWordsErr
  clear hIdentWordsErr
  let H := Rust.withPanics ext
  ik_prekey_fetches img.base H 2096 56
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallIk hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstackIk := stackAt_sub_split sp' 96 S (by omega) hS64
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48_split]
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom (ikPtr, ik, e, sp' + 312#64)
    (subroutine_ok_inImage_of_subroutine_ok img hcallIk)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 2124#64) (by simp [arm64_norm])
    (T := (ikPtr ↦ₛ ik) ∗ memRegion (sp' + 312#64) 40 ∗ logOff img ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ ikLen.toNat = ik.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize ik = .error e)
    (by simp [identityKeyTryFromSliceWordsErrSpec, hsp_eq, arm64_norm])
    ⟨rfl, hik_len, rfl, hik⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [identityKeyTryFromSliceWordsErrSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [memRegion24_words3 (sp' + 328#64), memRegion32_words4 (sp' + 144#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun w4 => SepWPp.exists_pre fun w3 => SepWPp.exists_pre fun w2 => ?_
  have hne : ((ikErrWords e).1 + 2#64 != 0#64) = true := by
    rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩ <;>
      (dsimp only [ikErrWords, speWord]; decide)
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hF3, hsym3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [h29_2, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx19_2, hx19, arm64_norm]⟩,
    by simp [arm64_norm], ?_⟩
  rw [← hsp2, hsp2_eq]
  have hm24 := ik_words3_to_memRegion24 (sp' + 152#64) w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm24
  have hspe := ik_errWords5_memRegion8_entails_speAt A fn hik sp' w2 w3 w4
  refine Entails.trans
    (Q := ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
      ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
      ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗
      (((sp' + 152#64) ↦₆₄ w2) ∗ ((sp' + 160#64) ↦₆₄ w3) ∗ ((sp' + 168#64) ↦₆₄ w4)) ∗
      (((sp' + 312#64) ↦₆₄ (ikErrWords e).1) ∗ ((sp' + 320#64) ↦₆₄ (ikErrWords e).2) ∗
        ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' + 336#64) ↦₆₄ w3) ∗ ((sp' + 344#64) ↦₆₄ w4) ∗
        memRegion (sp' + 352#64) 8) ∗
      logOff img ∗ (memRegion (sp' - BitVec.ofNat 64 S) (S - 96) ∗ stackAt sp' 96))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hstackIk]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm24 (sepConj_mono_left hspe)))))))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
