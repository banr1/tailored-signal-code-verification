/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyber
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKybercWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bBaseKeyPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` `+0x684` Continuation (`preKey684OkW_placed_of_830`)

Defines `w8bRowYFramePlaced`, `PreKey830OkWPlaced`, and `PreKeyKyberErrWPlaced`, and
proves `preKey684OkW_placed_of_830` on `preKeyPlacedProg H`.
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

/-! ## 1. Frames and the `+0x830` continuation (`[LibsignalPlacement]`) -/

/-- The part of `w8bRowKPostPlaced ∗ w8bRowKFrame` untouched by Kyber dispatch (`+0x684 → +0x830`). -/
def w8bRowYFramePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64)
    (bk ik msg bytes : List (BitVec 8)) : SepProp :=
  Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    memRegion sp' 12 ∗ memRegion (sp' + 144#64) 152 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes) ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- `+0x830` (`2096`) → `ret` on the Kyber Ok dispatch. -/
def PreKey830OkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk : PublicKey)
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

/-- `PreKey684OkWPlaced` restricted to the Kyber Err dispatch (`isSome` mismatch,
or both `none` with `0x40 ≤ vb.toNat`; Kyber `Err` edges `+0x684 → +0xa24` / `+0xa74` / `+0xa80` → ret). -/
def PreKeyKyberErrWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap kyberPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome != m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ 0x40 ≤ vb.toNat)) →
    BaseKeyOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 1668#64 →
    sf.status = .Running →
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowKPostPlaced A (s0.sp - 608#64) bkCap bkPtr bk ∗
        w8bRowKFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr kyberLen
          ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
          m.kyberCiphertext ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf'))
      (tryFromQp s0)

/-! ## 2. `PreKey684OkWPlaced` -/

/-- the `+0x684` continuation, from Kyber `Ok`, `+0x830`, and `PreKeyKyberErrWPlaced`. -/
theorem preKey684OkW_placed_of_830 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    (hErr : PreKeyKyberErrWPlaced A H) (hOk : PreKey830OkWPlaced A H) :
    PreKey684OkWPlaced A H := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons hv3 hv4 hlen hdec hbkO hikO
    hmsgO hspkO hreg hopk hkpk hd hst hbkC hikC hmsgC hpc hrun
  rcases w8b_kyber_dispatch m.kyberPreKeyId m.kyberCiphertext vb with hokY | herrY
  swap
  · exact hErr x s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberCap kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons hv3 hv4 hlen hdec
      hbkO hikO hmsgO hspkO hreg hopk hkpk hd herrY hst hbkC hikC hmsgC hpc hrun
  refine SepWPp.mono_pre (P' :=
      (memRegion (s0.sp - 608#64 + 12#64) 4 ∗
        seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
          ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
          regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 112#64) 32 ∗
        ((s0.sp - 608#64 + 312#64) ↦₈ 0#8) ∗
        ((s0.sp - 608#64 + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (s0.sp - 608#64 + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen m.kyberCiphertext ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
      w8bRowYFramePlaced A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap ikPtr msgCap msgPtr
        bk ik msg x.bytes)
    (by
      unfold w8bRowKPostPlaced w8bRowKFrame w8bRowYFramePlaced seg1SpillsAtW
      rw [w8b_memRegion16_split (s0.sp - 608#64), w8b_memRegion184_split (s0.sp - 608#64)]
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_tryFrom
    (w5b_kyber_ok_placed_wpW (kpkOpt := m.kyberPreKeyId) (kyberOpt := m.kyberCiphertext) hC
      (by revert hkpk; cases m.kyberPreKeyId <;> exact fun h => h) hokY hst hpc hrun) ?_
  rintro sm Pm hpcm hrunm ⟨kyberBoxPtr, kyberBoxLen, p0, p1, p2, p3, p4, p5, p6, p7, p8, p31,
    w9, w13, w15, w23, hpkb, hkst, hPm⟩
  exact SepWPp.mono_pre (sepConj_mono_left hPm)
    (hOk x s0 sm vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
      regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7
      p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY
      hpkb hkst hbkC hikC hmsgC hpcm hrunm)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
