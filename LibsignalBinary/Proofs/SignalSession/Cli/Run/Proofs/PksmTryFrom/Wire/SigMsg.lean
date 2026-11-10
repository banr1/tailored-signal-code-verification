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
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: `SignalMessage::try_from` and `try_clone_from_ref` Stage

Symbolic execution from `+0x864`: calls `SignalMessage::try_from` (`+0x864 → +0x878`),
branches to `SigMsgErrState` (`+0x9f0`) preserving the 6 error payload words on `.error e`,
or copies the 14 `Ok` words and calls `try_clone_from_ref` (`+0x878 → +0x8bc → +0x8c0 / +0xa68`).
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.call_noPanic_tryFrom := @Wire.SepWPp.call_noPanic_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private gen_decodes libsignalSessionCode_tree smDec [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2148) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2240)]

local macro "sm_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.smDec $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Local kernel-checked BitVec normalizers -/

private theorem sm_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem sm_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem sm_bv_add_neg_8 (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem sm_bv_add_neg_16 (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem sm_bv_add_neg_24 (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem sm_bv_add_neg_32 (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem sm_bv_add_neg_40 (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem sm_bv_add_neg_48 (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem sm_bv_add_neg_55 (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem sm_bv_add_neg_56 (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem sm_bv_add_neg_64 (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem sm_bv_add_neg_72 (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem sm_bv_add_neg_80 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem sm_bv_add_neg_87 (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem sm_bv_add_neg_88 (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem sm_bv_add_neg_96 (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem sm_bv_add_neg_104 (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem sm_bv_add_neg_112 (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem sm_bv_add_neg_120 (x : BitVec 64) : x + bv% (2 ^ 64 - 120) = x - 120#64 := by bv_omega
private theorem sm_bv_add_neg_128 (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem sm_bv_add_neg_136 (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem sm_bv_add_neg_144 (x : BitVec 64) : x + bv% (2 ^ 64 - 144) = x - 144#64 := by bv_omega
private theorem sm_bv_add_neg_152 (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem sm_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem sm_bv_add_neg_168 (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem sm_bv_add_neg_176 (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem sm_bv_add_neg_184 (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem sm_bv_add_neg_186 (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem sm_bv_add_neg_191 (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem sm_bv_add_neg_192 (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem sm_bv_add_neg_196 (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem sm_bv_add_neg_200 (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem sm_bv_add_neg_216 (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem sm_bv_add_neg_512 (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sm_bv_sub_add_lit' sm_bv_sub_sub_lit BitVec.toNat_zero
  sm_bv_add_neg_8 sm_bv_add_neg_16 sm_bv_add_neg_24 sm_bv_add_neg_32 sm_bv_add_neg_40
  sm_bv_add_neg_48 sm_bv_add_neg_55 sm_bv_add_neg_56 sm_bv_add_neg_64 sm_bv_add_neg_72
  sm_bv_add_neg_80 sm_bv_add_neg_87 sm_bv_add_neg_88 sm_bv_add_neg_96 sm_bv_add_neg_104
  sm_bv_add_neg_112 sm_bv_add_neg_120 sm_bv_add_neg_128 sm_bv_add_neg_136 sm_bv_add_neg_144
  sm_bv_add_neg_152 sm_bv_add_neg_160 sm_bv_add_neg_168 sm_bv_add_neg_176 sm_bv_add_neg_184
  sm_bv_add_neg_186 sm_bv_add_neg_191 sm_bv_add_neg_192 sm_bv_add_neg_196 sm_bv_add_neg_200
  sm_bv_add_neg_216 sm_bv_add_neg_512

/-! ## 1. Stack-Split & Region Packing Helpers -/

theorem stackAt_skipFieldStackX_tryCloneX (sp : BitVec 64) :
    stackAt sp (Prost.skipFieldStackX 100) =
      memRegion (sp - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - LibsignalTripleRatchet.tryCloneFromRefStackX) ∗
        stackAt sp LibsignalTripleRatchet.tryCloneFromRefStackX :=
  stackAt_sub_split sp LibsignalTripleRatchet.tryCloneFromRefStackX (Prost.skipFieldStackX 100)
    (by decide) (by decide)

theorem stackAt_smallRoot_tryCloneX (sp : BitVec 64) :
    stackAt sp smallRootStack =
      memRegion (sp - BitVec.ofNat 64 smallRootStack)
        (smallRootStack - LibsignalTripleRatchet.tryCloneFromRefStackX) ∗
        stackAt sp LibsignalTripleRatchet.tryCloneFromRefStackX :=
  stackAt_sub_split sp LibsignalTripleRatchet.tryCloneFromRefStackX smallRootStack
    (by decide) (by decide)

/-- Packing the `IdentityKey::try_from` 40-byte output slot `sp' + 312..352` plus
`memRegion (sp' + 352) 8` and `memRegion (sp' + 360) 72` into `memRegion (sp' + 312) 120`
for `SignalMessage::try_from`. -/
theorem ident_slot_entails_memRegion120 (sp' tag : BitVec 64) (ipk : PublicKey) :
    ((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
      memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ⊢
      memRegion (sp' + 312#64) 120 := by
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ipk.bytes)
  rw [hik (sp' + 320#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact words5_memRegion8_72_entails_120 sp' tag ik0 ik1 ik2 ik3

/-! ## 2. Leaf L3a (`+0x864 .. +0x878` / `2148 .. 2168`): `SignalMessage::try_from` Call -/

/-- (``+0x864 → +0x878`, dec `2148 → 2168``): From `IdentOkState` at `+0x864` (`2148`), loads `x0 = msgPtr` (`[sp' + 96]`),
`x1 = BitVec.ofNat 64 msg.length` (`[sp' + 32]`), sets `x8 = sp' + 312`, spills `w27 = regId`
to `sp' + 56`, and calls `SignalMessage::try_from` via native `tryFromSpec A img`
(`msg.length < 2 ^ 32`), returning to `+0x878` (`2168`). -/
theorem preKey_sigMsg_call_864_to_878_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSigTryFrom : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr tryFromName) (tryFromSpec A img))
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgPtr w56 : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)}
    (hlt_msg : msg.length < 2 ^ 32)
    (hst : IdentOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2148#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        memRegion (sp' + 312#64) 120 ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗
        logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        IdentOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId bk pk ik ipk sf ∧
        (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
          ((sp' + 56#64) ↦₃₂ regId) ∗
          ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗
          logOff img ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSig := signalTryFrom_ok_at_prekeyX hSigTryFrom
  clear hSigTryFrom
  let H := Rust.withPanics ext
  sm_prekey_fetches img.base H 2148 20
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallSig hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h56_split := ProofLib.pointsTo64_split32 (sp' + 56#64) w56
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_split
  refine SepWPp.mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
      ((sp' + 56#64) ↦₃₂ BitVec.truncate 32 w56) ∗
      ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      memRegion (sp' + 312#64) 120 ∗
      (msgPtr ↦ₛ msg) ∗ vecU8Rest A msgCap msgPtr msg ∗
      logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h56_split]
      simp only [sepConj_assoc]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (vecU8Buf_to_slice_rest A msgCap msgPtr msg))))))) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% ((2 ^ 64 + ls_off% tryFromName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  have hmsg_toNat : (BitVec.ofNat 64 msg.length).toNat = msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_tryFrom
    (⟨msgPtr, msg, sp' + 312#64⟩ : TryFromGhost) hcallSig
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 2168#64) (by simp [arm64_norm]) (by simp [htr, arm64_norm])
    (T := (msgPtr ↦ₛ msg) ∗ memRegion (sp' + 312#64) 120 ∗ logOff img ∗
      stackAt sp' smallRootStack ∗ A.pool)
    (φ := (img.FrozenLoaded _ ∧ s.symtab = img.symtab) ∧ msgPtr = msgPtr ∧
      (BitVec.ofNat 64 msg.length).toNat = msg.length ∧
      msg.length < 2 ^ 32 ∧ sp' + 312#64 = sp' + 312#64)
    (by simp [tryFromSpec, Spec.inImage, hsp_eq, arm64_norm])
    ⟨⟨hF1, hsym⟩, rfl, hmsg_toNat, hlt_msg, rfl⟩
    (by sep_focus) ?_
  clear hcallSig
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [tryFromSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨hsp2_eq, hsp2_align, hF3, hsym3, by simp [htr2, htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    by simp [hx29_2, hx29, arm64_norm],
    by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm],
    by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm],
    by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm],
    by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm],
    by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  have hrepack_msg := slice_rest_to_vecU8Buf A msgCap msgPtr msg
  refine Entails.trans
    (Q := ((msgPtr ↦ₛ msg) ∗ vecU8Rest A msgCap msgPtr msg) ∗
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₃₂ regId) ∗
        ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
        logOff img ∗ A.pool ∗ stackAt sp' smallRootStack))
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hrepack_msg) ?_
  apply entails_of_eq; ac_rfl

/-- Variant of `preKey_sigMsg_call_864_to_878_wpX` accepting the raw `IdentityKey::try_from`
output slot `((sp' + 312) ↦₆₄ tag) ∗ ((sp' + 320) ↦ₛ ipk.bytes.toList) ∗ memRegion (sp' + 352) 8 ∗
memRegion (sp' + 360) 72` directly. -/
theorem preKey_sigMsg_call_864_to_878_from_ident_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSigTryFrom : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr tryFromName) (tryFromSpec A img))
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgPtr w56 tag : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)}
    (hlt_msg : msg.length < 2 ^ 32)
    (hst : IdentOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2148#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
        memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗
        logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        IdentOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId bk pk ik ipk sf ∧
        (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
          ((sp' + 56#64) ↦₃₂ regId) ∗
          ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗
          logOff img ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  have h120 := ident_slot_entails_memRegion120 sp' tag ipk
  refine SepWPp.mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
      ((sp' + 56#64) ↦₆₄ w56) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      memRegion (sp' + 312#64) 120 ∗
      Wire.vecU8Buf A msgCap msgPtr msg ∗
      logOff img ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      refine Entails.trans
        (Q := (((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
            memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72) ∗
          (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
            ((sp' + 56#64) ↦₆₄ w56) ∗
            ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            Wire.vecU8Buf A msgCap msgPtr msg ∗
            logOff img ∗ A.pool ∗ stackAt sp' smallRootStack))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left h120) ?_
      apply entails_of_eq; ac_rfl) ?_
  exact preKey_sigMsg_call_864_to_878_wpX hSigTryFrom hlt_msg hst hpc hrun

/-! ## 3. Leaf L3b (`+0x878 → +0x9f0` / `2168 → 2544`): `SignalMessage::try_from` Err Branch -/

/-- (``+0x878 → +0x9f0`, dec `2168 → 2544``): When `SignalMessage.tryFrom protoSignalCodec msg = .error e`, executes `+0x878 .. +0x894`
(`2168 .. 2196`), copies the 6 error payload words (`48` B) from `sp' + 320..368` to
`sp' + 176..224`, checks `cmn x27, #1` (`x27 = errTag = -1`), and branches `b.eq +0x9f0`
(`2544`, `SigMsgErrState`), preserving the 6 copied words (with exact `speAt A []`
reconstruction) and repacking `memRegion (sp' + 312) 120` (no `anyHeap`). -/
theorem preKey_sigMsg_err_878_to_9f0_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)} {e : SignalProtocolError}
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .error e)
    (hst : IdentOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2168#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2544#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 48)
      (fun sf Pf =>
        SigMsgErrState img s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf ∧
        (Pf ⊢ ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64, ∃∗ ew2 : BitVec 64,
          ∃∗ ew3 : BitVec 64, ∃∗ ew4 : BitVec 64, ∃∗ ew5 : BitVec 64,
          ⌜∀ b : BitVec 64,
            (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
              speAt A [] b e⌝ ∗
          ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
          ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
          ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
          memRegion (sp' + 312#64) 120))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, _, _, _, _,
    hx29, hx28, _, hx26, hx25, hx24, hx23, _, _, _, hx19⟩
  let H := Rust.withPanics ext
  sm_prekey_fetches img.base H 2168 32
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rw [hsig]
  dsimp only [signalMessageResultAt, errResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (speAt_tryFrom_words2 A (sp' + 320#64) hsig))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew0 => SepWPp.exists_pre fun ew1 => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hpack => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion32_words4 (sp' + 336#64))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew5 => SepWPp.exists_pre fun ew4 =>
    SepWPp.exists_pre fun ew3 => SepWPp.exists_pre fun ew2 => ?_
  rw [memRegion48_words6 (sp' + 176#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun t5 => SepWPp.exists_pre fun t4 =>
    SepWPp.exists_pre fun t3 => SepWPp.exists_pre fun t2 =>
    SepWPp.exists_pre fun t1 => SepWPp.exists_pre fun t0 => ?_
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm],
    by simp [hx28, arm64_norm],
    by simp [hx25, arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [hx23, arm64_norm],
    by simp [hx19, arm64_norm]⟩, ?_⟩
  have hm120 :
      ((sp' + 312#64) ↦₆₄ errTag) ∗ ((sp' + 320#64) ↦₆₄ ew0) ∗ ((sp' + 328#64) ↦₆₄ ew1) ∗
      ((sp' + 336#64) ↦₆₄ ew2) ∗ ((sp' + 344#64) ↦₆₄ ew3) ∗ ((sp' + 352#64) ↦₆₄ ew4) ∗
      ((sp' + 360#64) ↦₆₄ ew5) ∗ memRegion (sp' + 368#64) 64 ⊢
        memRegion (sp' + 312#64) 120 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words7_memRegion64_entails_memRegion120 (sp' + 312#64) errTag ew0 ew1 ew2 ew3 ew4 ew5
  refine Entails.trans ?_ (Entails.sepExists_intro ew0)
  refine Entails.trans ?_ (Entails.sepExists_intro ew1)
  refine Entails.trans ?_ (Entails.sepExists_intro ew2)
  refine Entails.trans ?_ (Entails.sepExists_intro ew3)
  refine Entails.trans ?_ (Entails.sepExists_intro ew4)
  refine Entails.trans ?_ (Entails.sepExists_intro ew5)
  rw [pure_true_emp hpack, emp_sepConj]
  refine Entails.trans
    (Q := (((sp' + 312#64) ↦₆₄ errTag) ∗ ((sp' + 320#64) ↦₆₄ ew0) ∗
        ((sp' + 328#64) ↦₆₄ ew1) ∗ ((sp' + 336#64) ↦₆₄ ew2) ∗
        ((sp' + 344#64) ↦₆₄ ew3) ∗ ((sp' + 352#64) ↦₆₄ ew4) ∗
        ((sp' + 360#64) ↦₆₄ ew5) ∗ memRegion (sp' + 368#64) 64) ∗
      (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hm120) ?_
  apply entails_of_eq; ac_rfl

/-! ## 4. Leaf L4 (`+0x878 → +0x8bc → +0x8c0 / +0xa68`): `Ok(innerMsg)` + `try_clone_from_ref` -/

set_option maxHeartbeats 1200000 in
/-- (``+0x878 → +0x8bc`, dec `2168 → 2236``): When `SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg` and `b.length < 2 ^ 32`,
copies the 14 inner words (`112` B) from `sp' + 320..432` into `sp' + 176..288`
(`x27 = msgG.pqCap ≠ errTag`), and calls `try_clone_from_ref(ptr0, BitVec.ofNat 64 b.length)`
at `+0x8b8` (`2232`) via `tryCloneFromRef_ok_at_prekeyX`, returning to `+0x8bc` (`2236`,
right at `cbz x0, +0xa68`). -/
theorem preKey_sigMsg_ok_878_to_8bc_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hTryClone : TryCloneFromRefOkX img A ext)
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {b msg : List (BitVec 8)} {innerMsg : SignalMessage}
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hlen_lt : b.length < 2 ^ 32)
    (hst : IdentOkState img s0 sp' sret (BitVec.ofNat 64 b.length) ptr0 kyberBoxPtr kyberBoxLen
      ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2168#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2236#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 112 ∗
        (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        sf.sp = sp' ∧ sf.spAligned = true ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
        PublicKey.deserialize ik = .ok ipk ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 b.length ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
        sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 = kyberBoxLen ∧
        sf.readReg64 .x24 = sp' + 312#64 ∧ sf.readReg64 .x23 = ikCap ∧
        sf.readReg64 .x22 = vb.zeroExtend 64 ∧ sf.readReg64 .x21 = ptr0 ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 b.length ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ (∃∗ msgG : SignalMessageGhost,
          ∃∗ rk0 : BitVec 64, ∃∗ rk1 : BitVec 64, ∃∗ rk2 : BitVec 64, ∃∗ rk3 : BitVec 64,
          ∃∗ addrW0 : BitVec 64, ∃∗ addrW1 : BitVec 64, ∃∗ verHi56 : BitVec 56,
          ⌜sf.readReg64 .x27 = msgG.pqCap ∧
            (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
              (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))⌝ ∗
          ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
          ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
          ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
          ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
          ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
          ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
          ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
          ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
          ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
          ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
          ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
          msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
          (if sf.readReg64 .x0 = 0#64 then
            ⌜b ≠ [] ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else
            ⌜sf.trace = s0.trace⌝ ∗ boxU8Buf A (sf.readReg64 .x0) b) ∗
          memRegion (sp' + 312#64) 120 ∗
          (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    hx29, hx28, _, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallClone := tryCloneFromRef_ok_at_prekeyX hTryClone
  clear hTryClone
  have hlen_le63 : b.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 b.length).toNat = b.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstackClone := stackAt_skipFieldStackX_tryCloneX sp'
  let H := Rust.withPanics ext
  sm_prekey_fetches img.base H 2168 68
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcallClone hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rw [hsig]
  refine SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion112_words14 (sp' + 176#64))))) ?_
  dsimp only [signalMessageResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w280 => SepWPp.exists_pre fun w272 =>
    SepWPp.exists_pre fun w264 => SepWPp.exists_pre fun w256 =>
    SepWPp.exists_pre fun w248 => SepWPp.exists_pre fun w240 =>
    SepWPp.exists_pre fun w232 => SepWPp.exists_pre fun w224 =>
    SepWPp.exists_pre fun w216 => SepWPp.exists_pre fun w208 =>
    SepWPp.exists_pre fun w200 => SepWPp.exists_pre fun w192 =>
    SepWPp.exists_pre fun w184 => SepWPp.exists_pre fun w176 =>
    SepWPp.exists_pre fun msgG => ?_
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length innerMsg.senderRatchetKey.bytes)
  refine SepWPp.mono_pre
    (sepConj_mono_left
      (signalMessageAt_unpack A msgG (sp' + 312#64) innerMsg rk0 rk1 rk2 rk3 hrk)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun addrW0 => SepWPp.exists_pre fun addrW1 =>
    SepWPp.exists_pre fun verHi56 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (msgHeapAt_pqCap_lt A msgG innerMsg addrW0 addrW1))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine SepWPp.pure_pre fun hpq_lt => ?_
  have hpq_eq := cap_add1_eq_of_lt hpq_lt
  dsimp only [msgWords15At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% ((2 ^ 64 + ls_off% tryCloneFromRefName - ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  have hm312 :
      ((sp' + 312#64) ↦₆₄ msgG.pqCap) ∗
      ((sp' + 320#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 328#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 336#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 344#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 352#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 360#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 368#64) ↦₆₄ rk0) ∗ ((sp' + 376#64) ↦₆₄ rk1) ∗
      ((sp' + 384#64) ↦₆₄ rk2) ∗ ((sp' + 392#64) ↦₆₄ rk3) ∗
      ((sp' + 400#64) ↦₆₄ addrW0) ∗ ((sp' + 408#64) ↦₆₄ addrW1) ∗
      ((sp' + 416#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 424#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ⊢
        memRegion (sp' + 312#64) 120 := by
    simpa [msgWords15At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      msgWords15At_entails_memRegion (sp' + 312#64)
        msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter)
        (verHi56 ++ innerMsg.messageVersion)
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 312#64) 120 ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
      ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
      ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
      ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
      ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
      (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hm312)
      simp only [sepConj_assoc]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_noPanic_tryFrom (⟨ptr0, b⟩ : TryCloneSliceCall) hcallClone
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + 2236#64) (by simp [arm64_norm])
    (T := (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' LibsignalTripleRatchet.tryCloneFromRefStackX)
    (φ := ptr0 = ptr0 ∧ (BitVec.ofNat 64 b.length).toNat = b.length ∧
      b.length + 1 ≤ 2 ^ 63)
    (by simp [LibsignalTripleRatchet.tryCloneFromRefSpecX, hsp_eq, arm64_norm])
    ⟨rfl, hlen_toNat, hlen_le63⟩
    (by rw [hstackClone]; sep_focus) ?_
  clear hcallClone
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [LibsignalTripleRatchet.tryCloneFromRefSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun hx1_2 => ?_
  rcases hcs2 with
    ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, hx29_cs⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have hx27_2 : s2.readReg64 .x27 = msgG.pqCap := by simp [hx27_cs, arm64_norm]
  refine SepWPp.of_sepWP_end hF2 hsym2 (SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_)
  refine ⟨hsp2_eq, hsp2_align, hF3, hsym3,
    hbk_ok, hpk_eq, hpk_bytes, hik_deser, hx1_2,
    by simp [hx29_cs, hx29, arm64_norm],
    by simp [hx28_cs, hx28, arm64_norm],
    by simp [hx26_cs, hx26, arm64_norm],
    by simp [hx25_cs, hx25, arm64_norm],
    by simp [hx24_cs, hx24, arm64_norm],
    by simp [hx23_cs, hx23, arm64_norm],
    by simp [hx22_cs, hx22, arm64_norm],
    by simp [hx21_cs, hx21, arm64_norm],
    by simp [hx20_cs, hx20, arm64_norm],
    by simp [hx19_cs, hx19, arm64_norm], ?_⟩
  have hpack_words :
      ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
      ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
      ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
      ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1 ⊢
      ∃∗ msgG' : SignalMessageGhost,
        ∃∗ rk0' : BitVec 64, ∃∗ rk1' : BitVec 64, ∃∗ rk2' : BitVec 64, ∃∗ rk3' : BitVec 64,
        ∃∗ addrW0' : BitVec 64, ∃∗ addrW1' : BitVec 64, ∃∗ verHi56' : BitVec 56,
        ⌜s2.readReg64 .x27 = msgG'.pqCap ∧
          (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
            (a ↦₆₄ rk0') ∗ ((a + 8#64) ↦₆₄ rk1') ∗ ((a + 16#64) ↦₆₄ rk2') ∗ ((a + 24#64) ↦₆₄ rk3'))⌝ ∗
        ((sp' + 176#64) ↦₆₄ msgG'.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG'.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG'.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0') ∗ ((sp' + 232#64) ↦₆₄ rk1') ∗
        ((sp' + 240#64) ↦₆₄ rk2') ∗ ((sp' + 248#64) ↦₆₄ rk3') ∗
        ((sp' + 256#64) ↦₆₄ addrW0') ∗ ((sp' + 264#64) ↦₆₄ addrW1') ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56' ++ innerMsg.messageVersion)) ∗
        msgHeapAt A msgG' innerMsg addrW0' addrW1' := by
    refine Entails.trans ?_ (Entails.sepExists_intro msgG)
    refine Entails.trans ?_ (Entails.sepExists_intro rk0)
    refine Entails.trans ?_ (Entails.sepExists_intro rk1)
    refine Entails.trans ?_ (Entails.sepExists_intro rk2)
    refine Entails.trans ?_ (Entails.sepExists_intro rk3)
    refine Entails.trans ?_ (Entails.sepExists_intro addrW0)
    refine Entails.trans ?_ (Entails.sepExists_intro addrW1)
    refine Entails.trans ?_ (Entails.sepExists_intro verHi56)
    rw [pure_true_emp ⟨hx27_2, hrk⟩, emp_sepConj]
    exact Entails.refl _
  refine Entails.trans
    (Q := (((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
        msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
      ((if s2.readReg64 .x0 = 0#64 then
          ⌜b ≠ [] ∧ s2.trace = s0.trace ++ [allocFailedEvent]⌝
         else
          ⌜s2.trace = s0.trace⌝ ∗ boxU8Buf A (s2.readReg64 .x0) b) ∗
        memRegion (sp' + 312#64) 120 ∗
        (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by
      simp only [hstackClone, hsp_eq, htr, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hpack_words) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  exact Entails.refl _

/-- (``+0x8bc → +0x8c0`, dec `2236 → 2240``): When `s.readReg64 .x0 = clonePtr` and `clonePtr ≠ 0#64`, steps `cbz x0, +0xa68` (not taken)
from `+0x8bc` (`2236`) to `+0x8c0` (`2240`), establishing `SigMsgOkState`. -/
theorem preKey_sigMsg_clone_ok_8bc_to_8c0_wpX {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgW0 clonePtr : BitVec 64}
    {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    (hclone_ne : clonePtr ≠ 0#64)
    (hsp_eq : s.sp = sp') (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hik_deser : PublicKey.deserialize ik = .ok ipk)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = clonePtr)
    (hx1 : s.readReg64 .x1 = len)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx27 : s.readReg64 .x27 = msgW0) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberBoxLen) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2240#64) s emp
      (fun sf Pf =>
        SigMsgOkState img s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
          msgW0 clonePtr bk pk ik ipk sf ∧
        (Pf ⊢ emp))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  sm_prekey_fetches img.base H 2236 4
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hbeq : (clonePtr == 0#64) = false := beq_false_of_ne hclone_ne
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
      by simp [htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik_deser, hclone_ne,
    by simp [hx0, arm64_norm], by simp [hx1, arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
    by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
    by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm],
    by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
    by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

/-- (``+0x8bc → +0xa68`, dec `2236 → 2664``): When `s.readReg64 .x0 = 0#64` and `s.trace = s0.trace ++ [allocFailedEvent]`, steps
`cbz x0, +0xa68` (taken) from `+0x8bc` (`2236`) to `+0xa68` (`2664`), stopping at
`CloneAllocFail img s0 sp' sf`. -/
theorem preKey_sigMsg_clone_oom_8bc_to_a68_wpX {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' len : BitVec 64}
    (hsp_eq : s.sp = sp') (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace ++ [allocFailedEvent])
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = len) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2664#64) s emp
      (fun sf Pf =>
        CloneAllocFail img s0 sp' sf ∧
        sf.readReg64 .x20 = len ∧
        (Pf ⊢ emp))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  sm_prekey_fetches img.base H 2236 4
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  have halloc : allocFailedIn s0 (s.setPC (entry + 2664#64)) := by
    simp [allocFailedIn, htr, arm64_norm]
  have hpref : s0.trace <+: (s.setPC (entry + 2664#64)).trace := by
    refine ⟨[allocFailedEvent], ?_⟩
    simpa [arm64_norm] using htr.symm
  refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
    halloc, hpref⟩, by simp [hx20, arm64_norm], Entails.refl _⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
