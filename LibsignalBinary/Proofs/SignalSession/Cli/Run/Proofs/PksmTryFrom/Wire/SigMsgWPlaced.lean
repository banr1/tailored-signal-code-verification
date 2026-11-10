/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsg
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKeyWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6StatesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6ExitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` `SignalMessage::try_from` and `try_clone_from_ref` Stage

Proves the `SignalMessage::try_from` call (`+0x864 → +0x878`), `.error e` branch (`+0x878 → +0x9f0`),
and `.ok innerMsg` + `try_clone_from_ref` stage (`+0x878 → +0x8bc → +0x8c0 / +0xa68`) on
`preKeyPlacedProg H`.
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev smw_SepWPp := @Wire.SepWPp
private abbrev smw_done := @Wire.SepWP.done
private abbrev smw_pure_pre := @Wire.SepWPp.pure_pre
private abbrev smw_exists_pre := @Wire.SepWPp.exists_pre
private abbrev smw_mono_pre := @Wire.SepWPp.mono_pre
private abbrev smw_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev smw_of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev smw_call_noPanic_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_noPanic_pk
private abbrev smw_call_tryFrom_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_tryFrom_pk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp

/-! ## Local kernel-checked BitVec normalizers -/

private theorem smw_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem smw_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem smw_bv_add_neg_8 (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem smw_bv_add_neg_16 (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem smw_bv_add_neg_24 (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem smw_bv_add_neg_32 (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem smw_bv_add_neg_40 (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem smw_bv_add_neg_48 (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem smw_bv_add_neg_55 (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem smw_bv_add_neg_56 (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem smw_bv_add_neg_64 (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem smw_bv_add_neg_72 (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem smw_bv_add_neg_80 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem smw_bv_add_neg_87 (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem smw_bv_add_neg_88 (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem smw_bv_add_neg_96 (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem smw_bv_add_neg_104 (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem smw_bv_add_neg_112 (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem smw_bv_add_neg_120 (x : BitVec 64) : x + bv% (2 ^ 64 - 120) = x - 120#64 := by bv_omega
private theorem smw_bv_add_neg_128 (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem smw_bv_add_neg_136 (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem smw_bv_add_neg_144 (x : BitVec 64) : x + bv% (2 ^ 64 - 144) = x - 144#64 := by bv_omega
private theorem smw_bv_add_neg_152 (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem smw_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem smw_bv_add_neg_168 (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem smw_bv_add_neg_176 (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem smw_bv_add_neg_184 (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem smw_bv_add_neg_186 (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem smw_bv_add_neg_191 (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem smw_bv_add_neg_192 (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem smw_bv_add_neg_196 (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem smw_bv_add_neg_200 (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem smw_bv_add_neg_216 (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem smw_bv_add_neg_512 (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit smw_bv_sub_add_lit' smw_bv_sub_sub_lit BitVec.toNat_zero
  smw_bv_add_neg_8 smw_bv_add_neg_16 smw_bv_add_neg_24 smw_bv_add_neg_32 smw_bv_add_neg_40
  smw_bv_add_neg_48 smw_bv_add_neg_55 smw_bv_add_neg_56 smw_bv_add_neg_64 smw_bv_add_neg_72
  smw_bv_add_neg_80 smw_bv_add_neg_87 smw_bv_add_neg_88 smw_bv_add_neg_96 smw_bv_add_neg_104
  smw_bv_add_neg_112 smw_bv_add_neg_120 smw_bv_add_neg_128 smw_bv_add_neg_136 smw_bv_add_neg_144
  smw_bv_add_neg_152 smw_bv_add_neg_160 smw_bv_add_neg_168 smw_bv_add_neg_176 smw_bv_add_neg_184
  smw_bv_add_neg_186 smw_bv_add_neg_191 smw_bv_add_neg_192 smw_bv_add_neg_196 smw_bv_add_neg_200
  smw_bv_add_neg_216 smw_bv_add_neg_512

/-! ## 1. Leaf L3a (`+0x864 .. +0x878` / `2148 .. 2168`): `SignalMessage::try_from` Call -/

theorem preKey_sigMsg_call_864_to_878_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgPtr w56 : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)}
    (hlt_msg : msg.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
      bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2148#64)
    (hrun : s.status = .Running) :
    smw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        memRegion (sp' + 312#64) 120 ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
          bk pk ik ipk sf ∧
        (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
          ((sp' + 56#64) ↦₃₂ regId) ∗
          ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have h56_split := ProofLib.pointsTo64_split32 (sp' + 56#64) w56
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_split
  refine smw_mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
      ((sp' + 56#64) ↦₃₂ BitVec.truncate 32 w56) ∗
      ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      memRegion (sp' + 312#64) 120 ∗
      (msgPtr ↦ₛ msg) ∗ vecU8Rest A msgCap msgPtr msg ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h56_split]
      simp only [sepConj_assoc]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (vecU8Buf_to_slice_rest A msgCap msgPtr msg))))))) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine smw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 85) ?_
  wp_steps
  refine smw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have hmsg_toNat : (BitVec.ofNat 64 msg.length).toNat = msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlog_eq : logOff tryFromPlacedImg = lsLogOff := logOff_tryFromPlacedImg
  refine smw_call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    (⟨msgPtr, msg, sp' + 312#64⟩ : TryFromGhost) hC.sigTryFrom
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 2168#64) (by simp [arm64_norm]) (by simp [htr, arm64_norm])
    (T := (msgPtr ↦ₛ msg) ∗ memRegion (sp' + 312#64) 120 ∗ lsLogOff ∗
      stackAt sp' smallRootStack ∗ A.pool)
    (φ := msgPtr = msgPtr ∧ (BitVec.ofNat 64 msg.length).toNat = msg.length ∧
      msg.length < 2 ^ 32 ∧ sp' + 312#64 = sp' + 312#64)
    (by simp [tryFromPlacedSpec, hlog_eq, hsp_eq, arm64_norm])
    ⟨rfl, hmsg_toNat, hlt_msg, rfl⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [tryFromPlacedSpec]
  rw [hlog_eq, sepConj_assoc]
  refine smw_pure_pre fun htr2 => ?_
  rcases hcs2 with
    ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  refine smw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (smw_done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨hsp2_eq, hsp2_align, hcl3, by simp [htr2, htr, arm64_norm]⟩,
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
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack))
    (by
      simp only [hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hrepack_msg) ?_
  apply entails_of_eq; ac_rfl

theorem preKey_sigMsg_call_864_to_878_from_ident_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgPtr w56 tag : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)}
    (hlt_msg : msg.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
      bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2148#64)
    (hrun : s.status = .Running) :
    smw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
        memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A msgCap msgPtr msg ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
          bk pk ik ipk sf ∧
        (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
          ((sp' + 56#64) ↦₃₂ regId) ∗
          ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  have h120 := ident_slot_entails_memRegion120 sp' tag ipk
  refine smw_mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
      ((sp' + 56#64) ↦₆₄ w56) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      memRegion (sp' + 312#64) 120 ∗
      Wire.vecU8Buf A msgCap msgPtr msg ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      refine Entails.trans
        (Q := (((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
            memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72) ∗
          (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
            ((sp' + 56#64) ↦₆₄ w56) ∗
            ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            Wire.vecU8Buf A msgCap msgPtr msg ∗
            lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left h120) ?_
      apply entails_of_eq; ac_rfl) ?_
  exact preKey_sigMsg_call_864_to_878_placed_wpX hC hlt_msg hst hpc hrun

/-! ## 2. Leaf L3b (`+0x878 → +0x9f0` / `2168 → 2544`): `SignalMessage::try_from` Err Branch -/

theorem preKey_sigMsg_err_878_to_9f0_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)} {e : SignalProtocolError}
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .error e)
    (hst : IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
      bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running) :
    smw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2544#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 48)
      (fun sf Pf =>
        SigMsgErrStatePlaced s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf ∧
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
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, _, _, _, _,
    hx29, hx28, _, hx26, hx25, hx24, hx23, _, _, _, hx19⟩
  rw [hsig]
  dsimp only [signalMessageResultAt, errResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  refine smw_mono_pre
    (sepConj_mono_right (sepConj_mono_left (speAt_tryFrom_words2 A (sp' + 320#64) hsig))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine smw_exists_pre fun ew0 => smw_exists_pre fun ew1 => ?_
  simp only [sepConj_pure_left_comm]
  refine smw_pure_pre fun hpack => ?_
  refine smw_mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion32_words4 (sp' + 336#64))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine smw_exists_pre fun ew5 => smw_exists_pre fun ew4 =>
    smw_exists_pre fun ew3 => smw_exists_pre fun ew2 => ?_
  rw [memRegion48_words6 (sp' + 176#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine smw_exists_pre fun t5 => smw_exists_pre fun t4 =>
    smw_exists_pre fun t3 => smw_exists_pre fun t2 =>
    smw_exists_pre fun t1 => smw_exists_pre fun t0 => ?_
  refine smw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine smw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
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

/-! ## 3. Leaf L4 (`+0x878 → +0x8bc → +0x8c0 / +0xa68`): `Ok(innerMsg)` + `try_clone_from_ref` -/

set_option maxHeartbeats 1200000 in
theorem preKey_sigMsg_ok_878_to_8bc_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {b msg : List (BitVec 8)} {innerMsg : SignalMessage}
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hlen_lt : b.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret (BitVec.ofNat 64 b.length) ptr0 kyberBoxPtr kyberBoxLen
      ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running) :
    smw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2236#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 112 ∗
        (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        sf.sp = sp' ∧ sf.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
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
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    hx29, hx28, _, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hlen_le63 : b.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 b.length).toNat = b.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstackClone := stackAt_skipFieldStackX_tryCloneX sp'
  rw [hsig]
  refine smw_mono_pre
    (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion112_words14 (sp' + 176#64))))) ?_
  dsimp only [signalMessageResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine smw_exists_pre fun w280 => smw_exists_pre fun w272 =>
    smw_exists_pre fun w264 => smw_exists_pre fun w256 =>
    smw_exists_pre fun w248 => smw_exists_pre fun w240 =>
    smw_exists_pre fun w232 => smw_exists_pre fun w224 =>
    smw_exists_pre fun w216 => smw_exists_pre fun w208 =>
    smw_exists_pre fun w200 => smw_exists_pre fun w192 =>
    smw_exists_pre fun w184 => smw_exists_pre fun w176 =>
    smw_exists_pre fun msgG => ?_
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length innerMsg.senderRatchetKey.bytes)
  refine smw_mono_pre
    (sepConj_mono_left
      (signalMessageAt_unpack A msgG (sp' + 312#64) innerMsg rk0 rk1 rk2 rk3 hrk)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine smw_exists_pre fun addrW0 => smw_exists_pre fun addrW1 =>
    smw_exists_pre fun verHi56 => ?_
  refine smw_mono_pre
    (sepConj_mono_right (sepConj_mono_left (msgHeapAt_pqCap_lt A msgG innerMsg addrW0 addrW1))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine smw_pure_pre fun hpq_lt => ?_
  have hpq_eq := cap_add1_eq_of_lt hpq_lt
  dsimp only [msgWords15At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine smw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 23) ?_
  wp_steps
  refine smw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
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
  refine smw_mono_pre
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
  refine smw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (⟨ptr0, b⟩ : TryCloneSliceCall)
    hC.tryCloneX (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 2236#64) (by simp [arm64_norm])
    (T := (ptr0 ↦ₛ b) ∗ A.pool ∗ stackAt sp' LibsignalTripleRatchet.tryCloneFromRefStackX)
    (φ := ptr0 = ptr0 ∧ (BitVec.ofNat 64 b.length).toNat = b.length ∧
      b.length + 1 ≤ 2 ^ 63)
    (by simp [LibsignalTripleRatchet.tryCloneFromRefSpecX, hsp_eq, arm64_norm])
    ⟨rfl, hlen_toNat, hlen_le63⟩
    (by rw [hstackClone]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [LibsignalTripleRatchet.tryCloneFromRefSpecX]
  rw [sepConj_assoc]
  refine smw_pure_pre fun hx1_2 => ?_
  rcases hcs2 with
    ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs,
      hx29_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have hx27_2 : s2.readReg64 .x27 = msgG.pqCap := by simp [hx27_cs, arm64_norm]
  refine smw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (smw_done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨hsp2_eq, hsp2_align, hcl3,
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

theorem preKey_sigMsg_clone_ok_8bc_to_8c0_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgW0 clonePtr : BitVec 64}
    {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    (hclone_ne : clonePtr ≠ 0#64)
    (hsp_eq : s.sp = sp') (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hik_deser : PublicKey.deserialize ik = .ok ipk)
    (hpc : s.pc = (blkPl_111).base + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = clonePtr)
    (hx1 : s.readReg64 .x1 = len)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx27 : s.readReg64 .x27 = msgW0) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberBoxLen) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    smw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2240#64) s emp
      (fun sf Pf =>
        SigMsgOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
          msgW0 clonePtr bk pk ik ipk sf ∧
        (Pf ⊢ emp))
      (tryFromQp s0) := by
  have hbeq : (clonePtr == 0#64) = false := beq_false_of_ne hclone_ne
  refine smw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine smw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik_deser, hclone_ne,
    by simp [hx0, arm64_norm], by simp [hx1, arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
    by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
    by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm],
    by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
    by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

theorem preKey_sigMsg_clone_oom_8bc_to_a68_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' len : BitVec 64}
    (hsp_eq : s.sp = sp') (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace ++ [allocFailedEvent])
    (hpc : s.pc = (blkPl_111).base + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = len) :
    smw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2664#64) s emp
      (fun sf Pf =>
        CloneAllocFailPlaced s0 sp' sf ∧
        sf.readReg64 .x20 = len ∧
        (Pf ⊢ emp))
      (tryFromQp s0) := by
  refine smw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine smw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have halloc : allocFailedIn s0 (s.setPC ((blkPl_111).base + 2664#64)) := by
    simp [allocFailedIn, htr, arm64_norm]
  have hpref : s0.trace <+: (s.setPC ((blkPl_111).base + 2664#64)).trace := by
    refine ⟨[allocFailedEvent], ?_⟩
    simpa [arm64_norm] using htr.symm
  refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
    halloc, hpref⟩, by simp [hx20, arm64_norm], Entails.refl _⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
