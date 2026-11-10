/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKeyWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyberPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` `+0x830` Continuation (`preKey830OkW_placed_of_864`)

Defines `w8bRowIPostPlaced`, `PreKey864OkWPlaced`, and `PreKeyIdentErrWPlaced`, and
proves `preKey830OkW_placed_of_864` on `preKeyPlacedProg H`.
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
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Frames and the `+0x864` continuation (`[LibsignalPlacement]`) -/

/-- `identity_key` `Ok` post-frame at `+0x864` (`2148`): the `Pf` of `preKey_ident_ok_830_to_864_placed_wpX`. -/
def w8bRowIPostPlaced [LibsignalPlacement] (sp' ikPtr : BitVec 64) (regTag regVal : BitVec 32)
    (ik : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
    ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
    ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
    memRegion (sp' + 352#64) 8 ∗
    lsLogOff ∗ stackAt sp' (Prost.skipFieldStackX 100)

/-- `+0x864` (`2148`) → `ret` after `identity_key` deserialization succeeds. -/
def PreKey864OkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
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
    IdentOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb (identRegId regTag regVal) bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 2148#64 →
    sf.status = .Running →
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowIPostPlaced (s0.sp - 608#64) ikPtr regTag regVal ik ipk ∗
        w8bRowIFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap
          msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31
          w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf'))
      (tryFromQp s0)

/-- `PreKey830OkWPlaced` restricted to `identity_key` deserialization failure
(`PublicKey.deserialize ik = .error e`; `identity_key` `Err` edge `+0x830 → +0x978` → ret). -/
def PreKeyIdentErrWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
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
    KyberOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 2096#64 →
    sf.status = .Running →
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowYPost A (s0.sp - 608#64) bkCap bkPtr kyberLen ikPtr msgPtr kyberBoxPtr kyberBoxLen
          regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23
          vb m.kyberPreKeyId m.kyberCiphertext ik msg ∗
        w8bRowYFramePlaced A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap ikPtr msgCap msgPtr
          bk ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf'))
      (tryFromQp s0)

/-! ## 2. Regrouping `w8bRowYPost ∗ w8bRowYFramePlaced` for `identity_key` Deserialization -/

theorem w8bRowY_open_ident_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) :
    (w8bRowYPost A sp' bkCap bkPtr kyberLen ikPtr msgPtr kyberBoxPtr kyberBoxLen
        regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23
        vb kpkOpt kyberOpt ik msg ∗
      w8bRowYFramePlaced A s0 sp' sret ptr bkCap bkPtr ikCap ikPtr msgCap msgPtr bk ik msg bytes) =
    (⌜ik.length ≤ ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0⌝ ∗
      ((((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (ikPtr ↦ₛ ik) ∗
          memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
          lsLogOff ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
        w8bRowIFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
          kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31
          w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes)) := by
  unfold w8bRowYPost w8bRowYFramePlaced w8bRowIFrame kyberSpillsAtW
  rw [w8b_memRegion152_split sp', w8b_vecU8Buf_open_eq A ikCap ikPtr ik]
  ac_rfl

/-! ## 3. `PreKey830OkWPlaced` -/

theorem preKey830OkW_placed_of_864 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    (hErr : PreKeyIdentErrWPlaced A H) (hOk : PreKey864OkWPlaced A H) :
    PreKey830OkWPlaced A H := by
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
    rw [w8bRowY_open_ident_placed]
    refine SepWPp.pure_pre fun ⟨hikLe, hikLt, _⟩ => ?_
    have hik_len : (BitVec.ofNat 64 ik.length).toNat = ik.length := by
      have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rcases hkst with ⟨hpost, hbk_ok, hpk_eq, hpk_bytes, hx29, hx28, _hx27, hx26, hx25, hx24, hx23,
      hx22, hx21, hx20, hx19⟩
    refine Wire.SepWPp.bind_frame_tryFrom
      (preKey_ident_ok_830_to_864_placed_wpX (ikLen := BitVec.ofNat 64 ik.length)
        (regTag := regTag) (regVal := regVal) (ikPtr := ikPtr)
        hC w8b_skipFieldStackX100_bounds.1 w8b_skipFieldStackX100_bounds.2 hbk_ok hpk_eq
        hpk_bytes hik hik_len hpost hpc hrun hx29 hx28 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19) ?_
    rintro sm Pm hpcm hrunm ⟨hist, hPm⟩
    exact SepWPp.mono_pre (sepConj_mono_left hPm)
      (hOk x s0 sm vb b1 bs1 m bk ik msg spkId pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr
        kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4
        p5 p6 p7 p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk
        hkpk hd hokY hpkb hik hist hbkC hikC hmsgC hpcm hrunm)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
