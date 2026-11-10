/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyber
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: `+0x830` Continuation via `identity_key` Deserialization

Proves `preKey830OkW_of_864`, discharging `PreKey830OkW` (`+0x830 → ret`) by case analysis
on `PublicKey.deserialize ik` into `preKey_ident_ok_830_to_864_wpX` + `PreKey864OkW` (`Ok`)
and `PreKeyIdentErrW` (`Err`).
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
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. Opening the `identity_key` buffer -/

/-- `Wire.vecU8Buf` as its pure fact, the byte slice and the remainder `vecU8Rest` (equality form of
`vecU8Buf_to_slice_rest` / `slice_rest_to_vecU8Buf`, keeping the pure fact). -/
theorem w8b_vecU8Buf_open_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs) := by
  have h1 := vecU8Buf_to_slice_rest A cap ptr bs
  have h2 := slice_rest_to_vecU8Buf A cap ptr bs
  refine ProofLib.Entails.antisymm ?_ (Entails.pure_left fun _ => h2)
  conv_lhs => unfold Wire.vecU8Buf
  refine Entails.pure_left fun hφ => Entails.pure_right hφ ?_
  refine Entails.trans ?_ h1
  unfold Wire.vecU8Buf
  exact Entails.pure_right hφ (Entails.refl _)

theorem w8b_memRegion152_split (sp' : BitVec 64) :
    memRegion (sp' + 144#64) 152 =
      memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 176#64) 120 := by
  rw [show (152 : Nat) = 32 + 120 by decide,
    Prost.memRegion_split (sp' + 144#64) 32 120 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## 2. Frames and the `+0x864` continuation -/

/-- `identity_key` `Ok` post-frame at `+0x864` (`2148`): the `Pf` of `preKey_ident_ok_830_to_864_wpX` (with
`ikLen = ik.length`, `S = Prost.skipFieldStackX 100`). -/
def w8bRowIPost (img : Obj.Image) (sp' ikPtr : BitVec 64) (regTag regVal : BitVec 32)
    (ik : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
    ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
    ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
    memRegion (sp' + 352#64) 8 ∗
    logOff img ∗ stackAt sp' (Prost.skipFieldStackX 100)

/-- The part of `w8bRowYPost ∗ w8bRowYFrame` untouched by `identity_key` deserialization (`+0x830 → +0x864`): the
`kyberSpillsAtW` cells other than `sp' + 48 / 52 / 56 / 104`, the Kyber stage output, the
`identity_key` buffer remainder `vecU8Rest`, and the rest of the frame. -/
def w8bRowIFrame (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 12#64) ↦₃₂ p7.zeroExtend 32) ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ p8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
    ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗
    spUnused112 sp' ∗
    ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ p31) ∗
    ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
    sevenBytesHeadAt (sp' + 136#64) p0 p1 p2 p3 p4 p5 p6 ∗
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗ A.pool ∗
    vecU8Rest A ikCap ikPtr ik ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    memRegion sp' 12 ∗ memRegion (sp' + 176#64) 120 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes) ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- `+0x864` (`2148`) → `ret` after `identity_key` deserialization succeeds. -/
def PreKey864OkW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk ipk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    PublicKey.deserialize ik = .ok ipk →
    IdentOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb (identRegId regTag regVal) bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2148#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bRowIPost img (s0.sp - 608#64) ikPtr regTag regVal ik ipk ∗
        w8bRowIFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap
          msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31
          w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-- `PreKey830OkW` restricted to `identity_key` deserialization failure
(`PublicKey.deserialize ik = .error e`; `identity_key` `Err` edge `+0x830 → +0x978` → ret). -/
def PreKeyIdentErrW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk : PublicKey) (e : SignalProtocolError)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    PublicKey.deserialize ik = .error e →
    KyberOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2096#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bRowYPost A (s0.sp - 608#64) bkCap bkPtr kyberLen ikPtr msgPtr kyberBoxPtr kyberBoxLen
          regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23
          vb m.kyberPreKeyId m.kyberCiphertext ik msg ∗
        w8bRowYFrame img A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap ikPtr msgCap msgPtr
          bk ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-! ## 3. Regrouping `w8bRowYPost ∗ w8bRowYFrame` for `identity_key` Deserialization -/

/-- `w8bRowYPost ∗ w8bRowYFrame` = the `identity_key` buffer's pure fact ∗ the
`preKey_ident_ok_830_to_864_wpX` pre ∗ `w8bRowIFrame`. -/
theorem w8bRowY_open_ident (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) :
    (w8bRowYPost A sp' bkCap bkPtr kyberLen ikPtr msgPtr kyberBoxPtr kyberBoxLen
        regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23
        vb kpkOpt kyberOpt ik msg ∗
      w8bRowYFrame img A s0 sp' sret ptr bkCap bkPtr ikCap ikPtr msgCap msgPtr bk ik msg bytes) =
    (⌜ik.length ≤ ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0⌝ ∗
      ((((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (ikPtr ↦ₛ ik) ∗
          memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
          logOff img ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
        w8bRowIFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
          kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31
          w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes)) := by
  unfold w8bRowYPost w8bRowYFrame w8bRowIFrame kyberSpillsAtW
  rw [w8b_memRegion152_split sp', w8b_vecU8Buf_open_eq A ikCap ikPtr ik]
  ac_rfl

/-! ## 4. `PreKey830OkW` -/

theorem w8b_skipFieldStackX100_bounds :
    96 ≤ Prost.skipFieldStackX 100 ∧ Prost.skipFieldStackX 100 ≤ 2 ^ 64 := by
  decide

/-- the `+0x830` continuation, from `identity_key` `Ok`, `+0x864`, and `PreKeyIdentErrW`. -/
theorem preKey830OkW_of_864 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hIdentOk : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceOkSpec img))
    (hErr : PreKeyIdentErrW img A ext) (hOk : PreKey864OkW img A ext) :
    PreKey830OkW img A ext := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY hpkb
    hkst hbkC hikC hmsgC hpc hrun
  cases hik : PublicKey.deserialize ik with
  | error e =>
    exact hErr x s0 sf vb b1 bs1 m bk ik msg spkId pk e bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5
      p6 p7 p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd
      hokY hpkb hik hkst hbkC hikC hmsgC hpc hrun
  | ok ipk =>
    rw [w8bRowY_open_ident]
    refine SepWPp.pure_pre fun ⟨hikLe, hikLt, _⟩ => ?_
    have hik_len : (BitVec.ofNat 64 ik.length).toNat = ik.length := by
      have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rcases hkst with ⟨hpost, hbk_ok, hpk_eq, hpk_bytes, hx29, hx28, _hx27, hx26, hx25, hx24, hx23,
      hx22, hx21, hx20, hx19⟩
    refine SepWPp.bind_frame_tryFrom
      (preKey_ident_ok_830_to_864_wpX (ext := ext) (ikLen := BitVec.ofNat 64 ik.length)
        (regTag := regTag) (regVal := regVal) (ikPtr := ikPtr)
        hIdentOk w8b_skipFieldStackX100_bounds.1 w8b_skipFieldStackX100_bounds.2 hbk_ok hpk_eq
        hpk_bytes hik hik_len hpost hpc hrun hx29 hx28 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19) ?_
    rintro sm Pm hpcm hrunm ⟨hist, hPm⟩
    exact SepWPp.mono_pre (sepConj_mono_left hPm)
      (hOk x s0 sm vb b1 bs1 m bk ik msg spkId pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr
        kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4
        p5 p6 p7 p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk
        hkpk hd hokY hpkb hik hist hbkC hikC hmsgC hpcm hrunm)

/-- Convenience wrapper for `preKey830OkW_of_864` discharging `hIdentOk` directly from `himg`. -/
theorem preKey830OkW_of_864_loads {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hErr : PreKeyIdentErrW img A ext) (hOk : PreKey864OkW img A ext) :
    PreKey830OkW img A ext :=
  preKey830OkW_of_864 (identityKeyTryFromSlice_okX himg) hErr hOk

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
