/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoop
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: `+0x5b4` Continuation via `base_key` Deserialization

Proves `preKey5b4OkW_of_684`, discharging `PreKey5b4OkW` (`+0x5b4 → ret`) by case analysis
on `PublicKey.deserialize bk` into `post_deser_bk_ok_full_to_684_wpW` + `PreKey684OkW` (`Ok`)
and `PreKeyBaseKeyErrW` (`Err`).
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
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. Frames and the `+0x684` continuation -/

/-- `base_key` `Ok` post-frame at `+0x684` (`1668`): the `Pf` of `post_deser_bk_ok_full_to_684_wpW`
(tag byte `0`, the 32 key bytes `(bk.take 33).drop 1`, 15 bytes of padding). -/
def w8bRowKPost (img : Obj.Image) (A : RustAlloc) (sp' bkCap bkPtr : BitVec 64)
    (bk : List (BitVec 8)) : SepProp :=
  ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
    memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img

/-- The part of `w8bXokPost ∗ w8bPostLoopFrame` untouched by `base_key` deserialization (`+0x5b4 → +0x684`): everything
except `sp' + 72`, `sp' + 80`, `memRegion (sp' + 312) 48`, the `bk` buffer and `logOff img`. -/
def w8bRowKFrame (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (ik msg bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
    memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes) ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- `+0x684` (`1668`) → `ret` when `PublicKey.deserialize bk = .ok pk`. -/
def PreKey684OkW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
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
    BaseKeyOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bRowKPost img A (s0.sp - 608#64) bkCap bkPtr bk ∗
        w8bRowKFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr kyberLen
          ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
          m.kyberCiphertext ik msg x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-- `PreKey5b4OkW` restricted to `PublicKey.deserialize bk = .error e`
(`base_key` `Err` edge `+0x5b4 → +0x7a8` → ErrTailB → ret). -/
def PreKeyBaseKeyErrW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (e : SignalProtocolError)
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
    PublicKey.deserialize bk = .error e →
    PresenceOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bXokPost A (s0.sp - 608#64) bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap
          msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal m.kyberCiphertext bk ik msg ∗
        w8bPostLoopFrame img s0 (s0.sp - 608#64) x.ret x.ptr x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-! ## 2. `PreKey5b4OkW` -/

/-- the `+0x5b4` continuation, from `base_key` `Ok`, `+0x684`, and `PreKeyBaseKeyErrW`. -/
theorem preKey5b4OkW_of_684 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hb : (img.base &&& 0xfff#64) = 0#64)
    (hErr : PreKeyBaseKeyErrW img A ext) (hOk : PreKey684OkW img A ext) :
    PreKey5b4OkW img A ext := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons hv3 hv4 hlen hdec hbkO hikO
    hmsgO hspkO hreg hopk hkpk hst hbkC hikC hmsgC hpc hrun
  rcases hd : PublicKey.deserialize bk with e | pk
  · exact hErr x s0 sf vb b1 bs1 m bk ik msg spkId e bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberCap kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons hv3 hv4 hlen hdec
      hbkO hikO hmsgO hspkO hreg hopk hkpk hd hst hbkC hikC hmsgC hpc hrun
  refine SepWPp.mono_pre (P' :=
      (((s0.sp - 608#64 + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img) ∗
      w8bRowKFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr kyberLen
        ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
        m.kyberCiphertext ik msg x.bytes)
    (by
      unfold w8bXokPost w8bPostLoopFrame w8bRowKFrame seg1SpillsAtW
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom (post_deser_bk_ok_full_to_684_wpW hb hd hst hpc hrun) ?_
  rintro sm Pm hpcm hrunm ⟨hbst, hPm⟩
  exact SepWPp.mono_pre (sepConj_mono_left hPm)
    (hOk x s0 sm vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
      kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons hv3 hv4 hlen hdec hbkO
      hikO hmsgO hspkO hreg hopk hkpk hd hbst hbkC hikC hmsgC hpcm hrunm)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
