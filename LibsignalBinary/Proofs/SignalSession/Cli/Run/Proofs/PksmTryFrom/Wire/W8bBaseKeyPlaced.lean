/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bBaseKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKeyWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoopPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` `+0x5b4` Continuation (`preKey5b4OkW_placed_of_684`)

Defines `w8bRowKPostPlaced`, `PreKey684OkWPlaced`, and `PreKeyBaseKeyErrWPlaced`, and
proves `preKey5b4OkW_placed_of_684` on `preKeyPlacedProg H`.
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

/-! ## 1. Frames and the `+0x684` continuation (`[LibsignalPlacement]`) -/

def w8bRowKPostPlaced [LibsignalPlacement] (A : RustAlloc) (sp' bkCap bkPtr : BitVec 64)
    (bk : List (BitVec 8)) : SepProp :=
  ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
    memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff

def PreKey684OkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
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

def PreKeyBaseKeyErrWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
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
    PresenceOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 1460#64 →
    sf.status = .Running →
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bXokPost A (s0.sp - 608#64) bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap
          msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal m.kyberCiphertext bk ik msg ∗
        w8bPostLoopFramePlaced s0 (s0.sp - 608#64) x.ret x.ptr x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf'))
      (tryFromQp s0)

/-! ## 2. `PreKey5b4OkWPlaced` -/

theorem preKey5b4OkW_placed_of_684 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    (hErr : PreKeyBaseKeyErrWPlaced A H) (hOk : PreKey684OkWPlaced A H) :
    PreKey5b4OkWPlaced A H := by
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
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff) ∗
      w8bRowKFrame A s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr kyberLen
        ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
        m.kyberCiphertext ik msg x.bytes)
    (by
      unfold w8bXokPost w8bPostLoopFramePlaced w8bRowKFrame seg1SpillsAtW
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_tryFrom (post_deser_bk_ok_full_to_684_placed_wpW hC hd hst hpc hrun) ?_
  rintro sm Pm hpcm hrunm ⟨hbst, hPm⟩
  exact SepWPp.mono_pre (sepConj_mono_left hPm)
    (hOk x s0 sm vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
      kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons hv3 hv4 hlen hdec hbkO
      hikO hmsgO hspkO hreg hopk hkpk hd hbst hbkC hikC hmsgC hpcm hrunm)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
