/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bBaseKey
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: `base_key` Deserialization Error Continuation (`PreKeyBaseKeyErrW`)

Proves `preKeyBaseKeyErrW_proof` (`+0x5b4 → +0x7a8 → +0x504 → ret`) from
`post_deser_bk_err_dealloc_to_7a8_wpE`, `ErrTailB.entry_7a8_wpE`, and `w8b_errTail_close`.
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

/-- The part of the BaseKey Err (`+0x5b4`) precondition outside `base_key` deserialization and the dealloc-chain cells
(framed across `post_deser_bk_err_dealloc_to_7a8_wpE` and `entry_7a8_wpE`). -/
def w8bBkErrRest (s0 : State) (sp' ptr msgLen kyberLen ikLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ kpkTag) ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ (ptr ↦ₛ bytes) ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Final BaseKey Err regroup at `+0x504` (`1284`): the `entry_7a8_wpE` post frame ∗
`w8bBkErrRest` entails the `w8b_errTail_close` precondition (residue `emp`). -/
theorem w8bBkErr_pack {img : Obj.Image} {A : RustAlloc} {s0 : State}
    {sp' sret ptr msgLen kyberLen ikLen msgPtr ikPtr bkPtr bkCap bkLenV : BitVec 64}
    {regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32}
    {e : SignalProtocolError} {bytes : List (BitVec 8)} :
    (pksmErrE A [] sret e ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        (((sp' + 72#64) ↦₆₄ bkLenV) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ logOff img)) ∗
      w8bBkErrRest s0 sp' ptr msgLen kyberLen ikLen regTag regVal opkTag opkVal spkId
        kpkTag kpkVal bytes ⊢
    pksmErrE A [] sret e ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  have h48 : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 33 15 (by decide)
  have h88 : memRegion (sp' + 360#64) 88 =
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗ memRegion (sp' + 440#64) 8 := by
    rw [ProofLib.memRegion_split (sp' + 360#64) 72 16 (by decide),
      ProofLib.memRegion_split (sp' + 360#64 + 72#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [emp_sepConj, stackAt_preKeyTryFromSubStack_skipField sp',
    w8bMemRegion296_split_16_96 sp', w8bMemRegion152_split sp', h48, h88]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_left
        (w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr bkLenV kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkId kpkTag kpkVal))))))
  unfold w8bBkErrRest
  apply entails_of_eq; ac_rfl

/-- `PreKeyBaseKeyErrW` from `post_deser_bk_err_dealloc_to_7a8_wpE`, `entry_7a8_wpE`, and
`w8b_errTail_close`. -/
theorem preKeyBaseKeyErrW_proof {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hb : (img.base &&& 0xfff#64) = 0#64) (hC : PksmCallees img A ext) :
    PreKeyBaseKeyErrW img A ext := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId e bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons _hv3 _hv4 _hlen hdec
    hbkO _hikO _hmsgO _hspkO _hreg _hopk _hkpk hd hst _hbkC _hikC _hmsgC hpc hrun
  have hparse : Pksm.pksmParse x.bytes = none := hcons ▸ pksmParse_bkErr hdec hbkO hd
  refine SepWPp.mono_pre (P' :=
      ((((s0.sp - 608#64 + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (s0.sp - 608#64 + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img) ∗
        (memRegion x.ret 248 ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗ ((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikPtr) ∗
          ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen m.kyberCiphertext ∗
          A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100))) ∗
      w8bBkErrRest s0 (s0.sp - 608#64) x.ptr (BitVec.ofNat 64 msg.length) kyberLen
        (BitVec.ofNat 64 ik.length) regTag regVal opkTag opkVal spkId kpkTag kpkVal x.bytes)
    (by
      unfold w8bXokPost w8bPostLoopFrame seg1SpillsAtW w8bBkErrRest
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom (post_deser_bk_err_dealloc_to_7a8_wpE hb hd hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1
    ⟨⟨⟨hpost1, _hx29, hx28, _hx27, hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩, _⟩,
      ⟨x8v, x9v, x10v, hx8, hx9, hx10, hwords⟩, hmsgNe, hikNe, hbkNe, hP1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hP1) ?_
  refine w8bErrW_exists_pre_frame fun msgAct => w8bErrW_exists_pre_frame fun ikAct =>
    w8bErrW_exists_pre_frame fun bkAct => w8bErrW_exists_pre_frame fun kyAct => ?_
  refine SepWPp.bind_frame_tryFrom
    (entry_7a8_wpE hC msgAct ikAct bkAct kyAct hpost1 hpc1 hrun1 hx19 hx8 hx9 hx10 hwords hx26 hx23
      hx28 hx25 hmsgNe hikNe hbkNe) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _hx19', hP2⟩
  exact SepWPp.mono_pre (Entails.trans (sepConj_mono_left hP2) w8bBkErr_pack)
    (w8b_errTail_close hparse hst2 hpc2 hrun2)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
