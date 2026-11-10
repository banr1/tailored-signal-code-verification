/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWIdent
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` `identity_key` Deserialization Error Continuation

Proves `preKeyIdentErrW_placed_proof` (`+0x830 → +0x978 → +0x504 → ret`) on
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-- The part of the Ident Err (`+0x978`) state framed across `ErrTailCWPlaced.e_978_placed_wpE` (`R`). -/
def w8bIdErrRestPlaced [LibsignalPlacement] (s0 : State)
    (sp' ptr kyberLen ikLen msgLen w15 w23 : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 12#64) ↦₃₂ p7.zeroExtend 32) ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ p8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
    spUnused112 sp' ∗
    ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ p31) ∗
    ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
    sevenBytesHeadAt (sp' + 136#64) p0 p1 p2 p3 p4 p5 p6 ∗
    memRegion sp' 12 ∗ memRegion (sp' + 176#64) 120 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ (ptr ↦ₛ bytes) ∗ lsLogOff ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Regroups the `identity_key` `Err` cells (`preKey_ident_err_830_to_978_placed_wpE` post) ∗ `w8bRowIFrame`
into the four existential slots of `e_978_placed_wpE` ∗ its remaining pre (with
`R := w8bIdErrRestPlaced …`). -/
theorem w8bIdErr_open_placed [LibsignalPlacement] {A : RustAlloc} {s0 : State}
    {sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kbPtr kbLen ikLen : BitVec 64}
    {regTag regVal opkTag opkVal spkId kpkVal : BitVec 32}
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8} {w9 : BitVec 32} {w13 : BitVec 16}
    {w15 w23 : BitVec 64} {vb : BitVec 8}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk ik msg bytes : List (BitVec 8)} {e : SignalProtocolError} :
    (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
        ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
        speAt A [] (sp' + 312#64) e ∗
        lsLogOff ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      w8bRowIFrame A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        kbPtr kbLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31
        w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ⊢
    (∃∗ boxAct : Bool, boxSlot A kbPtr kbLen boxAct) ∗
      (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗
      (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗
      (∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
      (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
        speAt A [] (sp' + 312#64) e ∗ memRegion sret 248 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        w8bIdErrRestPlaced s0 sp' ptr kyberLen ikLen (BitVec.ofNat 64 msg.length) w15 w23
          regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13
          bytes) := by
  have hbox := w8bIdErr_kyberStageOut_boxSlot A kpkVal vb kpkOpt kyberOpt kbPtr kbLen
  have hmsg := w8bIdErr_vecU8Buf_dealloc A msgCap msgPtr msg
  have hik := Entails.trans (slice_rest_to_vecU8Buf A ikCap ikPtr ik)
    (w8bIdErr_vecU8Buf_dealloc A ikCap ikPtr ik)
  have hbk := w8bIdErr_vecU8Buf_dealloc A bkCap bkPtr bk
  refine Entails.trans ?_
    (sepConj_mono hbox (sepConj_mono hmsg (sepConj_mono hik (sepConj_mono_left hbk))))
  unfold w8bRowIFrame w8bIdErrRestPlaced
  apply entails_of_eq; ac_rfl

/-- Final Ident Err regroup at `+0x504` (`1284`): the `e_978_placed_wpE` post frame (with
`R := w8bIdErrRestPlaced`) entails the `w8b_errTail_close_placed` precondition (residue `emp`). -/
theorem w8bIdErr_placed_pack [LibsignalPlacement] {A : RustAlloc} {s0 : State}
    {sp' sret ptr kyberLen ikLen msgLen w15 w23 msgPtr ikPtr bkPtr bkCap : BitVec 64}
    {regTag regVal opkTag opkVal spkId kpkVal : BitVec 32}
    {p0 p1 p2 p3 p5 p6 p7 p8 p31 p4 : BitVec 8} {w9 : BitVec 32} {w13 : BitVec 16}
    {e : SignalProtocolError} {bytes : List (BitVec 8)} :
    pksmErrE A [] sret e ∗ memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      w8bIdErrRestPlaced s0 sp' ptr kyberLen ikLen msgLen w15 w23 regTag regVal opkTag opkVal
        spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 bytes ⊢
    pksmErrE A [] sret e ∗ SepProp.emp ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ lsLogOff ∗ A.pool := by
  rw [emp_sepConj, stackAt_preKeyTryFromSubStack_skipField sp',
    w8bIdErr_memRegion296_split sp', w8bIdErr_memRegion152_split48 sp']
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 12#64) (p7.zeroExtend 32))
        (sepConj_mono
          (w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr w15 kyberLen ikPtr ikLen msgPtr msgLen
            regTag regVal opkTag opkVal spkId (p8.zeroExtend 32) kpkVal)
          (sepConj_mono_left
            (memRegion32_112_pack sp' w23 w9 w13 p31 p0 p1 p2 p3 p4 p5 p6))))))))
  unfold w8bIdErrRestPlaced
  apply entails_of_eq; ac_rfl

/-- `PreKeyIdentErrWPlaced` from `preKey_ident_err_830_to_978_placed_wpE`, `e_978_placed_wpE`,
and `w8b_errTail_close_placed`. -/
theorem preKeyIdentErrW_placed_proof [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) :
    PreKeyIdentErrWPlaced A H := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk e bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 hcons _hv3 _hv4 _hlen hdec _hbkO hikO _hmsgO _hspkO _hreg _hopk _hkpk
    _hd _hokY _hpkb hik hkst hbkC hikC hmsgC hpc hrun
  have hparse : Pksm.pksmParse x.bytes = none := hcons ▸ pksmParse_ikErr hdec hikO hik
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  rw [w8bRowY_open_ident_placed]
  refine SepWPp.pure_pre fun ⟨hikLe, hikLt, _⟩ => ?_
  have hik_len : (BitVec.ofNat 64 ik.length).toNat = ik.length := by
    have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rcases hkst with ⟨hpost, _hbk_ok, _hpk_eq, _hpk_bytes, hx29, hx28, _hx27, hx26, hx25, hx24,
    hx23, _hx22, _hx21, _hx20, hx19⟩
  refine Wire.SepWPp.bind_frame_tryFrom
    (preKey_ident_err_830_to_978_placed_wpE A [] hC
      w8b_skipFieldStackX100_bounds.1 w8b_skipFieldStackX100_bounds.2 hik hik_len hpost
      hpc hrun hx29 hx28 hx26 hx25 hx24 hx23 hx19) ?_
  rintro sm Pm hpcm hrunm ⟨hist, hx8, hPm⟩
  refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left hPm) w8bIdErr_open_placed) ?_
  refine w8bIdErr_exists4_pre fun boxAct msgAct ikAct bkAct => ?_
  refine SepWPp.bind
    (SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
      (e_978_placed_wpE (msgPtr := msgPtr) (ikPtr := ikPtr) (bkPtr := bkPtr)
        (R := w8bIdErrRestPlaced s0 (s0.sp - 608#64) x.ptr kyberLen (BitVec.ofNat 64 ik.length)
          (BitVec.ofNat 64 msg.length) w15 w23 regTag regVal opkTag opkVal spkId kpkVal
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 x.bytes)
        hC [] boxAct msgAct ikAct bkAct hik hist hpcm hrunm hx8 hmsgNe hikNe hbkNe)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _hx19', hP2⟩
  exact SepWPp.mono_pre (Entails.trans hP2 w8bIdErr_placed_pack)
    (w8b_errTail_close_placed hparse hst2 hpc2 hrun2)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
